"use strict";

import express from "express";
import pino from "pino";
import Database from "better-sqlite3";
import fs from "node:fs";
import path from "node:path";
import crypto from "node:crypto";
import { fileURLToPath } from "node:url";

import makeWASocket, {
    DisconnectReason,
    BufferJSON,
    proto,
    initAuthCreds,
    jidNormalizedUser,
    fetchLatestWaWebVersion
} from "@whiskeysockets/baileys";

// =====================================================
// CONFIGURATION
// =====================================================

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const PORT = Number(process.env.PORT || 10000);

const PAIRING_NUMBER = String(
    process.env.PAIRING_NUMBER || ""
).replace(/\D/g, "");

const DATA_DIR =
    process.env.DATA_DIR || path.join(__dirname, "data");

const DB_PATH = path.join(DATA_DIR, "jontez.sqlite");

const MAX_STORED_MESSAGES = Math.max(
    100,
    Number(process.env.MAX_STORED_MESSAGES || 5000)
);

const ANTI_DELETE_NOTICE =
    String(process.env.ANTI_DELETE_NOTICE || "true").toLowerCase() === "true";

const ACCESS_TOKEN =
    process.env.ACCESS_TOKEN || crypto.randomBytes(32).toString("hex");

const logger = pino({ level: "silent" });

fs.mkdirSync(DATA_DIR, { recursive: true });

console.log("Baileys package:", "@whiskeysockets/baileys");
console.log("Database:", DB_PATH);

// =====================================================
// SQLITE DATABASE
// =====================================================

const db = new Database(DB_PATH);

db.pragma("journal_mode = WAL");
db.pragma("synchronous = NORMAL");
db.pragma("foreign_keys = ON");

db.exec(`
    CREATE TABLE IF NOT EXISTS auth_kv (
        key TEXT PRIMARY KEY,
        value TEXT NOT NULL
    );

    CREATE TABLE IF NOT EXISTS messages (
        chat_id TEXT NOT NULL,
        message_id TEXT NOT NULL,
        sender_jid TEXT,
        timestamp INTEGER NOT NULL,
        message_json TEXT NOT NULL,
        PRIMARY KEY (chat_id, message_id)
    );

    CREATE INDEX IF NOT EXISTS idx_messages_timestamp
    ON messages(timestamp);
`);

const authRead = db.prepare(
    "SELECT value FROM auth_kv WHERE key = ?"
);

const authWrite = db.prepare(`
    INSERT INTO auth_kv (key, value)
    VALUES (?, ?)
    ON CONFLICT(key) DO UPDATE SET value = excluded.value
`);

const authDelete = db.prepare(
    "DELETE FROM auth_kv WHERE key = ?"
);

const saveMessageStatement = db.prepare(`
    INSERT INTO messages
        (chat_id, message_id, sender_jid, timestamp, message_json)
    VALUES
        (@chat_id, @message_id, @sender_jid, @timestamp, @message_json)
    ON CONFLICT(chat_id, message_id)
    DO UPDATE SET
        sender_jid = excluded.sender_jid,
        timestamp = excluded.timestamp,
        message_json = excluded.message_json
`);

const findMessageStatement = db.prepare(`
    SELECT *
    FROM messages
    WHERE chat_id = ? AND message_id = ?
`);

const pruneMessagesStatement = db.prepare(`
    DELETE FROM messages
    WHERE rowid NOT IN (
        SELECT rowid
        FROM messages
        ORDER BY timestamp DESC
        LIMIT ?
    )
`);

// =====================================================
// SQLITE AUTHENTICATION
// =====================================================

function useSQLiteAuthState() {
    const credsRow = authRead.get("creds");

    const creds = credsRow
        ? JSON.parse(credsRow.value, BufferJSON.reviver)
        : initAuthCreds();

    const saveCreds = () => {
        authWrite.run(
            "creds",
            JSON.stringify(creds, BufferJSON.replacer)
        );
    };

    const keys = {
        get: async (type, ids) => {
            const result = {};

            for (const id of ids) {
                const row = authRead.get(`${type}-${id}`);

                if (!row) continue;

                let value = JSON.parse(
                    row.value,
                    BufferJSON.reviver
                );

                if (type === "app-state-sync-key") {
                    value =
                        proto.Message.AppStateSyncKeyData.fromObject(value);
                }

                result[id] = value;
            }

            return result;
        },

        set: async (data) => {
            const transaction = db.transaction((items) => {
                for (const category of Object.keys(items)) {
                    const values = items[category] || {};

                    for (const id of Object.keys(values)) {
                        const value = values[id];
                        const key = `${category}-${id}`;

                        if (value) {
                            authWrite.run(
                                key,
                                JSON.stringify(
                                    value,
                                    BufferJSON.replacer
                                )
                            );
                        } else {
                            authDelete.run(key);
                        }
                    }
                }
            });

            transaction(data);
        }
    };

    return {
        state: {
            creds,
            keys
        },
        saveCreds
    };
}

// =====================================================
// EXPRESS SERVER
// =====================================================

const app = express();

app.disable("x-powered-by");
app.use(express.json({ limit: "1mb" }));

let sock = null;
let isConnected = false;
let reconnectTimer = null;
let reconnectAttempts = 0;
let starting = false;
let pairingRequested = false;

let accountJid = null;
let accountPhone = null;
let lastGroupCount = 0;
let lastConnectionTime = null;
let lastDisconnectReason = null;

// =====================================================
// TOKEN AUTHENTICATION
// =====================================================

function safeTokenEqual(a, b) {
    if (typeof a !== "string" || typeof b !== "string") {
        return false;
    }

    const first = Buffer.from(a);
    const second = Buffer.from(b);

    if (first.length !== second.length) {
        return false;
    }

    return crypto.timingSafeEqual(first, second);
}

function getRequestToken(req) {
    const header = req.headers.authorization || "";

    if (header.toLowerCase().startsWith("bearer ")) {
        return header.slice(7).trim();
    }

    return String(req.headers["x-access-token"] || "");
}

function requireToken(req, res, next) {
    if (!safeTokenEqual(getRequestToken(req), ACCESS_TOKEN)) {
        return res.status(401).json({
            success: false,
            error: "Unauthorized. Provide a valid access token."
        });
    }

    next();
}

// =====================================================
// MESSAGE HELPERS
// =====================================================

function unwrapMessage(message) {
    let current = message || {};

    for (let i = 0; i < 5; i++) {
        if (current.ephemeralMessage?.message) {
            current = current.ephemeralMessage.message;
        } else if (current.viewOnceMessage?.message) {
            current = current.viewOnceMessage.message;
        } else if (current.viewOnceMessageV2?.message) {
            current = current.viewOnceMessageV2.message;
        } else if (current.viewOnceMessageV2Extension?.message) {
            current = current.viewOnceMessageV2Extension.message;
        } else if (current.documentWithCaptionMessage?.message) {
            current = current.documentWithCaptionMessage.message;
        } else {
            break;
        }
    }

    return current || {};
}

function getMessageText(message) {
    const content = unwrapMessage(message);

    return (
        content.conversation ||
        content.extendedTextMessage?.text ||
        content.imageMessage?.caption ||
        content.videoMessage?.caption ||
        content.documentMessage?.caption ||
        content.buttonsResponseMessage?.selectedDisplayText ||
        content.listResponseMessage?.title ||
        content.templateButtonReplyMessage?.selectedDisplayText ||
        content.interactiveResponseMessage?.body?.text ||
        ""
    );
}

function isRevokedMessage(message) {
    const protocol = message?.message?.protocolMessage;

    if (!protocol) return false;

    return (
        protocol.type === 0 ||
        protocol.type === proto.Message.ProtocolMessage.Type.REVOKE
    );
}

function getPhoneFromJid(jid) {
    if (typeof jid !== "string" || !jid) return null;

    if (jid.endsWith("@s.whatsapp.net")) {
        return jid
            .split("@")[0]
            .split(":")[0]
            .replace(/\D/g, "") || null;
    }

    return null;
}

function normalizeJid(jid) {
    if (!jid || typeof jid !== "string") return null;

    try {
        return jidNormalizedUser(jid);
    } catch {
        return jid;
    }
}

function getSavedMessage(chatId, messageId) {
    if (!chatId || !messageId) return null;

    const row = findMessageStatement.get(chatId, messageId);

    if (!row) return null;

    try {
        return {
            ...row,
            message: JSON.parse(
                row.message_json,
                BufferJSON.reviver
            )
        };
    } catch (error) {
        console.error("Could not decode saved message:", error.message);
        return null;
    }
}

function saveIncomingMessage(message) {
    const key = message?.key;

    if (!key?.id || !key?.remoteJid || !message.message) {
        return;
    }

    if (isRevokedMessage(message)) return;

    const timestamp = Number(
        message.messageTimestamp || Math.floor(Date.now() / 1000)
    );

    saveMessageStatement.run({
        chat_id: key.remoteJid,
        message_id: key.id,
        sender_jid: key.participant || key.remoteJid,
        timestamp,
        message_json: JSON.stringify(
            message,
            BufferJSON.replacer
        )
    });

    pruneMessagesStatement.run(MAX_STORED_MESSAGES);
}

// =====================================================
// PHONE NUMBER / LID RESOLUTION
// =====================================================

async function resolvePhoneNumber(jid, socket = sock) {
    if (!jid || typeof jid !== "string") return null;

    const directPhone = getPhoneFromJid(jid);

    if (directPhone) return directPhone;

    if (!jid.endsWith("@lid") || !socket) return null;

    try {
        const mapping = socket.signalRepository?.lidMapping;

        if (mapping && typeof mapping.getPNForLID === "function") {
            const phoneJid = await mapping.getPNForLID(jid);

            return getPhoneFromJid(phoneJid);
        }
    } catch (error) {
        console.log("LID lookup unavailable:", error.message);
    }

    return null;
}

async function resolveParticipant(participant, socket = sock) {
    const jid =
        participant?.phoneNumber ||
        participant?.phoneNumberJid ||
        participant?.jid ||
        participant?.id ||
        participant?.lid ||
        (typeof participant === "string" ? participant : null);

    return {
        jid: jid || null,
        phone: await resolvePhoneNumber(jid, socket),
        name:
            participant?.notify ||
            participant?.name ||
            participant?.verifiedName ||
            null
    };
}

// =====================================================
// GROUP HELPERS
// =====================================================

async function getGroupMetadata(groupId) {
    if (!sock || !isConnected) {
        throw new Error("WhatsApp is not connected.");
    }

    return sock.groupMetadata(groupId);
}

async function isGroupAdmin(groupId, senderJid) {
    const metadata = await getGroupMetadata(groupId);

    const sender = normalizeJid(senderJid);
    const me = normalizeJid(sock.user?.id);

    const matches = (participant, jid) => {
        const ids = [
            participant.id,
            participant.jid,
            participant.lid,
            participant.phoneNumber,
            participant.phoneNumberJid
        ].filter(Boolean).map(normalizeJid);

        return ids.includes(jid);
    };

    const senderParticipant =
        metadata.participants.find(p => matches(p, sender));

    const botParticipant =
        metadata.participants.find(p => matches(p, me));

    return {
        senderIsAdmin:
            senderParticipant?.admin === "admin" ||
            senderParticipant?.admin === "superadmin",

        botIsAdmin:
            botParticipant?.admin === "admin" ||
            botParticipant?.admin === "superadmin"
    };
}

async function getGroups() {
    if (!sock || !isConnected) {
        throw new Error("WhatsApp is not connected.");
    }

    const groups = await sock.groupFetchAllParticipating();

    lastGroupCount = Object.keys(groups).length;

    return Object.entries(groups).map(([id, group]) => ({
        id,
        subject: group.subject || "",
        owner: group.owner || null,
        size: group.participants?.length || 0,
        creation: group.creation || null,
        desc: group.desc || ""
    }));
}

// =====================================================
// BOT COMMANDS
// =====================================================

async function handleCommand(message) {
    if (!sock || !isConnected) return;

    const key = message.key || {};
    const chatId = key.remoteJid;
    const senderJid = key.participant || key.remoteJid;
    const text = getMessageText(message.message).trim();

    if (!chatId || !text.startsWith("!")) return;

    const [commandRaw, ...args] = text.split(/\s+/);
    const command = commandRaw.toLowerCase();

    const reply = async (body, options = {}) => {
        await sock.sendMessage(
            chatId,
            { text: body, ...options },
            { quoted: message }
        );
    };

    try {
        switch (command) {
            case "!help":
                return reply([
                    "🤖 *WhatsApp Bot Commands*",
                    "",
                    "!help - Show commands",
                    "!status - Connection status",
                    "!chatid - Show chat ID",
                    "!groups - List groups",
                    "!groupinfo - Group information",
                    "!members - List group participants",
                    "!add 2547XXXXXXXX - Add participant",
                    "!remove @mention - Remove participant",
                    "!promote @mention - Promote participant",
                    "!demote @mention - Demote participant"
                ].join("\n"));

            case "!status":
                return reply([
                    "🤖 *Bot Status*",
                    `Connected: ${isConnected ? "Yes" : "No"}`,
                    `Account: ${accountJid || "Unavailable"}`,
                    `Phone: ${accountPhone || "Unavailable"}`,
                    `Groups: ${lastGroupCount}`,
                    `Stored messages: ${db.prepare(
                        "SELECT COUNT(*) AS total FROM messages"
                    ).get().total}`
                ].join("\n"));

            case "!chatid":
                return reply(`Chat ID:\n${chatId}`);

            case "!groups": {
                const groups = await getGroups();

                if (!groups.length) {
                    return reply("No groups found.");
                }

                const lines = groups.slice(0, 50).map((group, i) =>
                    `${i + 1}. ${group.subject}\nID: ${group.id}\nMembers: ${group.size}`
                );

                return reply(
                    `📚 *Groups (${groups.length})*\n\n${lines.join("\n\n")}`
                );
            }

            case "!groupinfo": {
                if (!chatId.endsWith("@g.us")) {
                    return reply("Use this command inside a group.");
                }

                const group = await getGroupMetadata(chatId);

                return reply([
                    `📋 *${group.subject}*`,
                    `Group ID: ${group.id}`,
                    `Members: ${group.participants.length}`,
                    `Owner: ${group.owner || "Unknown"}`,
                    `Created: ${group.creation || "Unknown"}`,
                    `Description: ${group.desc || "None"}`
                ].join("\n"));
            }

            case "!members": {
                if (!chatId.endsWith("@g.us")) {
                    return reply("Use this command inside a group.");
                }

                const group = await getGroupMetadata(chatId);
                const lines = [];

                for (let i = 0; i < group.participants.length; i++) {
                    const participant = group.participants[i];
                    const resolved = await resolveParticipant(participant);

                    const role =
                        participant.admin === "superadmin" ? "Owner" :
                        participant.admin === "admin" ? "Admin" : "Member";

                    lines.push(
                        `${i + 1}. ${resolved.phone || "Phone unavailable"}\n` +
                        `ID: ${resolved.jid || participant.id}\nRole: ${role}`
                    );
                }

                return reply(
                    `👥 *Participants (${lines.length})*\n\n` +
                    lines.slice(0, 80).join("\n\n") +
                    (lines.length > 80
                        ? "\n\nOnly the first 80 are shown."
                        : "")
                );
            }

            case "!add":
            case "!remove":
            case "!promote":
            case "!demote": {
                if (!chatId.endsWith("@g.us")) {
                    return reply("Use this command inside a group.");
                }

                const admin = await isGroupAdmin(chatId, senderJid);

                if (!admin.senderIsAdmin) {
                    return reply("Only group admins can use this command.");
                }

                if (!admin.botIsAdmin) {
                    return reply("Make the bot a group admin first.");
                }

                let targets = [];

                if (command === "!add") {
                    const phone = (args[0] || "").replace(/\D/g, "");

                    if (phone.length < 8) {
                        return reply("Usage: !add 2547XXXXXXXX");
                    }

                    targets = [`${phone}@s.whatsapp.net`];
                } else {
                    targets =
                        message.message?.extendedTextMessage
                            ?.contextInfo?.mentionedJid || [];

                    if (!targets.length && args[0]) {
                        const phone = args[0].replace(/\D/g, "");

                        if (phone.length >= 8) {
                            targets = [`${phone}@s.whatsapp.net`];
                        }
                    }

                    if (!targets.length) {
                        return reply(
                            `Usage: ${command} @mention or provide a phone number.`
                        );
                    }
                }

                const action =
                    command === "!add" ? "add" :
                    command === "!remove" ? "remove" :
                    command === "!promote" ? "promote" : "demote";

                const result = await sock.groupParticipantsUpdate(
                    chatId,
                    targets,
                    action
                );

                return reply(
                    `${action} request processed:\n` +
                    JSON.stringify(result, null, 2)
                );
            }

            default:
                return;
        }
    } catch (error) {
        console.error("Command error:", error);

        try {
            await reply(`Command failed: ${error.message}`);
        } catch {}
    }
}

// =====================================================
// ANTI-DELETE MESSAGE RECOVERY
// =====================================================

async function handleDeletedMessage(message) {
    const originalKey = message?.message?.protocolMessage?.key;

    if (!originalKey?.id) return;

    const chatId = originalKey.remoteJid || message.key?.remoteJid;

    if (!chatId) return;

    const original = getSavedMessage(chatId, originalKey.id);

    console.log("\n========== ANTI-DELETE ==========");
    console.log("Chat ID:", chatId);
    console.log("Original message ID:", originalKey.id);

    if (!original) {
        console.log("Original message not found in the local cache.");
        console.log("================================\n");
        return;
    }

    const originalMessage = original.message;
    const originalText = getMessageText(originalMessage.message);

    const senderJid =
        originalMessage.key?.participant ||
        originalMessage.key?.remoteJid ||
        original.sender_jid ||
        "Unknown";

    console.log("Sender:", senderJid);
    console.log("Text:", originalText || "[No recoverable text]");
    console.log("================================\n");

    if (ANTI_DELETE_NOTICE && originalText && sock && isConnected) {
        try {
            await sock.sendMessage(chatId, {
                text:
                    "🗑️ *Deleted message recovered*\n\n" +
                    `Sender ID: ${senderJid}\n` +
                    `Message: ${originalText}`
            });
        } catch (error) {
            console.error("Anti-delete notice failed:", error.message);
        }
    }
}

// =====================================================
// MESSAGE AND GROUP EVENTS
// =====================================================

function registerMessageEvents(socket) {
    socket.ev.on("messages.upsert", async ({ messages, type }) => {
        if (!Array.isArray(messages)) return;

        for (const message of messages) {
            try {
                if (isRevokedMessage(message)) {
                    await handleDeletedMessage(message);
                    continue;
                }

                saveIncomingMessage(message);

                const key = message.key || {};

                console.log("\n========== MESSAGE ==========");
                console.log("Chat ID:", key.remoteJid || "Unknown");
                console.log("Message ID:", key.id || "Unknown");
                console.log(
                    "Sender ID:",
                    key.participant || key.remoteJid || "Unknown"
                );
                console.log("From bot:", Boolean(key.fromMe));
                console.log("Message type:", type || "unknown");

                const text = getMessageText(message.message);

                if (text) {
                    console.log("Text:", text);
                }

                console.log("=============================\n");

                if (!key.fromMe) {
                    await handleCommand(message);
                }
            } catch (error) {
                console.error("Message event error:", error);
            }
        }
    });

    socket.ev.on("group-participants.update", async update => {
        try {
            console.log(
                "Group participants update:",
                update.id,
                update.action
            );

            if (!update.id || !Array.isArray(update.participants)) return;

            if (update.action === "add") {
                for (const participant of update.participants) {
                    try {
                        const resolved = await resolveParticipant(
                            participant,
                            socket
                        );

                        const display =
                            resolved.phone ||
                            resolved.jid ||
                            "new participant";

                        await socket.sendMessage(update.id, {
                            text: `👋 Welcome ${display}!`
                        });
                    } catch (error) {
                        console.error("Welcome message failed:", error.message);
                    }
                }
            }
        } catch (error) {
            console.error("Group update error:", error);
        }
    });
}

// =====================================================
// RECONNECTION
// =====================================================

function scheduleReconnect() {
    if (reconnectTimer) return;

    reconnectAttempts++;

    const delay = Math.min(
        30000,
        2000 * Math.pow(2, Math.min(reconnectAttempts - 1, 4))
    );

    console.log(
        `Reconnecting in ${Math.round(delay / 1000)} seconds...`
    );

    reconnectTimer = setTimeout(async () => {
        reconnectTimer = null;
        await startBot();
    }, delay);
}

// =====================================================
// START WHATSAPP
// =====================================================

async function startBot() {
    if (starting) return;

    starting = true;

    try {
        console.log("Initializing WhatsApp bot...");
        console.log("SQLite database:", DB_PATH);

        const { state, saveCreds } = useSQLiteAuthState();

        // Fetch the current WhatsApp Web version.
        // If fetching fails, allow Baileys to use its default version.
        let version;

        try {
            const result = await fetchLatestWaWebVersion();

            if (result?.version?.length) {
                version = result.version;

                console.log(
                    "WhatsApp Web version:",
                    version.join(".")
                );
            } else {
                console.log(
                    "Could not fetch the WhatsApp Web version; using library defaults."
                );
            }
        } catch (error) {
            console.error(
                "WhatsApp Web version lookup failed:",
                error.message
            );
        }

        const socketOptions = {
            auth: state,
            logger,
            printQRInTerminal: false,
            markOnlineOnConnect: false,
            syncFullHistory: false,
            shouldSyncHistoryMessage: () => false,
            getMessage: async key => {
                const saved = getSavedMessage(
                    key.remoteJid,
                    key.id
                );

                return saved?.message?.message || undefined;
            }
        };

        if (version) {
            socketOptions.version = version;
        }

        const socket = makeWASocket(socketOptions);

        sock = socket;

        socket.ev.on("creds.update", saveCreds);

        registerMessageEvents(socket);

        socket.ev.on("connection.update", async update => {
            if (sock !== socket) return;

            const { connection, lastDisconnect } = update;

            if (connection === "connecting") {
                console.log("Connecting to WhatsApp...");
            }

            if (connection === "open") {
                isConnected = true;
                reconnectAttempts = 0;

                lastConnectionTime = new Date().toISOString();
                lastDisconnectReason = null;

                accountJid = socket.user?.id || null;
                accountPhone = getPhoneFromJid(accountJid);

                if (!accountPhone && socket.user?.lid) {
                    accountPhone = await resolvePhoneNumber(
                        socket.user.lid,
                        socket
                    );
                }

                console.log("\n==================================");
                console.log("WHATSAPP CONNECTED");
                console.log("Account JID:", accountJid || "Unavailable");
                console.log("Account phone:", accountPhone || "Unavailable");
                console.log("==================================\n");

                // Do not print the access token.
                try {
                    await getGroups();
                    console.log("Groups found:", lastGroupCount);
                } catch (error) {
                    console.log("Could not fetch groups:", error.message);
                }
            }

            if (connection === "close") {
                isConnected = false;

                const statusCode =
                    lastDisconnect?.error?.output?.statusCode ||
                    lastDisconnect?.error?.statusCode ||
                    null;

                lastDisconnectReason =
                    lastDisconnect?.error?.message ||
                    (statusCode
                        ? `Status ${statusCode}`
                        : "Connection closed");

                console.log("WhatsApp connection closed.");
                console.log("Disconnect reason:", lastDisconnectReason);
                console.log("Disconnect code:", statusCode);

                if (sock === socket) {
                    sock = null;
                }

                if (statusCode === DisconnectReason.loggedOut) {
                    console.error(
                        "WhatsApp logged out. Pair the account again if needed."
                    );
                    return;
                }

                scheduleReconnect();
            }
        });

        // Request a pairing code if the account is not registered.
        if (!state.creds.registered && PAIRING_NUMBER && !pairingRequested) {
            pairingRequested = true;

            setTimeout(async () => {
                try {
                    if (sock !== socket || state.creds.registered) {
                        pairingRequested = false;
                        return;
                    }

                    const code = await socket.requestPairingCode(
                        PAIRING_NUMBER
                    );

                    console.log("\n==================================");
                    console.log("WHATSAPP PAIRING CODE:", code);
                    console.log("Open WhatsApp > Linked devices.");
                    console.log("Choose the phone-number pairing option.");
                    console.log("==================================\n");
                } catch (error) {
                    pairingRequested = false;

                    console.error(
                        "Could not request pairing code:",
                        error.message
                    );
                }
            }, 3000);
        } else if (!state.creds.registered && !PAIRING_NUMBER) {
            console.log(
                "Set PAIRING_NUMBER in Render environment variables to request a pairing code."
            );
        }
    } catch (error) {
        console.error("Could not start WhatsApp bot:", error);

        isConnected = false;
        sock = null;

        scheduleReconnect();
    } finally {
        starting = false;
    }
}

// =====================================================
// HTTP API
// =====================================================

app.get("/", (req, res) => {
    res.type("html").send(`<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>WhatsApp Bot Dashboard</title>
<style>
body {
    font-family: Arial, sans-serif;
    max-width: 800px;
    margin: 35px auto;
    padding: 0 16px;
    background: #f4f7f6;
    color: #17211c;
}
.card {
    background: white;
    border-radius: 12px;
    padding: 18px;
    margin: 15px 0;
    box-shadow: 0 2px 8px #0001;
    overflow-wrap: anywhere;
}
h1 { color: #137c50; }
.status { font-weight: bold; }
button {
    padding: 10px 14px;
    border: 0;
    border-radius: 7px;
    background: #137c50;
    color: white;
    cursor: pointer;
}
</style>
</head>
<body>
<h1>WhatsApp Bot Dashboard</h1>

<div class="card">
<h3>Connection</h3>
<p id="status">Loading...</p>
<p id="account">Account: Loading...</p>
<p id="phone">Phone: Loading...</p>
<p id="groups">Groups: Loading...</p>
<p id="messages">Stored messages: Loading...</p>
<p id="connectedAt">Last connected: Loading...</p>
<button onclick="refreshStatus()">Refresh</button>
</div>

<div class="card">
<h3>API endpoints</h3>
<p><code>GET /health</code> - Health status</p>
<p><code>GET /session</code> - Session status</p>
<p><code>GET /groups</code> - List groups (token required)</p>
<p><code>GET /messages</code> - Stored messages (token required)</p>
<p><code>POST /send</code> - Send message (token required)</p>
<p>The access token is not displayed on this page.</p>
</div>

<script>
async function refreshStatus() {
    try {
        const response = await fetch("/session");
        const data = await response.json();

        document.getElementById("status").textContent =
            "Status: " + (data.connected ? "Connected" : "Disconnected");

        document.getElementById("account").textContent =
            "Account: " + (data.accountJid || "Unavailable");

        document.getElementById("phone").textContent =
            "Phone: " + (data.phone || "Unavailable");

        document.getElementById("groups").textContent =
            "Groups: " + (data.groupCount ?? 0);

        document.getElementById("messages").textContent =
            "Stored messages: " + (data.storedMessages ?? 0);

        document.getElementById("connectedAt").textContent =
            "Last connected: " + (data.lastConnectionTime || "Not connected yet");
    } catch {
        document.getElementById("status").textContent =
            "Unable to load status";
    }
}

refreshStatus();
setInterval(refreshStatus, 15000);
</script>
</body>
</html>`);
});

app.get("/health", (req, res) => {
    res.json({
        success: true,
        server: "online",
        whatsappConnected: isConnected,
        database: "sqlite",
        uptimeSeconds: Math.floor(process.uptime())
    });
});

app.get("/session", (req, res) => {
    const storedMessages = db.prepare(
        "SELECT COUNT(*) AS total FROM messages"
    ).get().total;

    res.json({
        success: true,
        connected: isConnected,
        accountJid,
        phone: accountPhone,
        groupCount: lastGroupCount,
        storedMessages,
        lastConnectionTime,
        lastDisconnectReason
    });
});

app.get("/groups", requireToken, async (req, res) => {
    try {
        const groups = await getGroups();

        res.json({
            success: true,
            count: groups.length,
            groups
        });
    } catch (error) {
        res.status(503).json({
            success: false,
            error: error.message
        });
    }
});

app.get("/messages", requireToken, (req, res) => {
    const limit = Math.min(
        200,
        Math.max(1, Number(req.query.limit || 50))
    );

    const rows = db.prepare(`
        SELECT chat_id, message_id, sender_jid, timestamp, message_json
        FROM messages
        ORDER BY timestamp DESC
        LIMIT ?
    `).all(limit);

    const messages = rows.map(row => {
        try {
            const message = JSON.parse(
                row.message_json,
                BufferJSON.reviver
            );

            return {
                chatId: row.chat_id,
                messageId: row.message_id,
                senderJid: row.sender_jid,
                timestamp: row.timestamp,
                text: getMessageText(message.message) || null
            };
        } catch {
            return {
                chatId: row.chat_id,
                messageId: row.message_id,
                senderJid: row.sender_jid,
                timestamp: row.timestamp,
                text: null
            };
        }
    });

    res.json({
        success: true,
        count: messages.length,
        messages
    });
});

app.post("/send", requireToken, async (req, res) => {
    try {
        if (!sock || !isConnected) {
            return res.status(503).json({
                success: false,
                error: "WhatsApp is not connected."
            });
        }

        const { to, message } = req.body || {};

        if (
            typeof to !== "string" ||
            typeof message !== "string" ||
            !to.trim() ||
            !message.trim()
        ) {
            return res.status(400).json({
                success: false,
                error: "Provide 'to' and 'message' as strings."
            });
        }

        const destination = to.includes("@")
            ? to
            : `${to.replace(/\D/g, "")}@s.whatsapp.net`;

        const result = await sock.sendMessage(destination, {
            text: message
        });

        res.json({
            success: true,
            messageId: result?.key?.id || null,
            destination
        });
    } catch (error) {
        res.status(500).json({
            success: false,
            error: error.message
        });
    }
});

// =====================================================
// START SERVER
// =====================================================

const server = app.listen(PORT, "0.0.0.0", () => {
    console.log("==================================");
    console.log("WhatsApp Bot HTTP server started");
    console.log("Port:", PORT);
    console.log("Database:", DB_PATH);
    console.log("==================================");

    startBot().catch(error => {
        console.error("Initial bot startup failed:", error);
    });
});

function shutdown() {
    console.log("Shutting down...");

    if (reconnectTimer) {
        clearTimeout(reconnectTimer);
        reconnectTimer = null;
    }

    try {
        sock?.end(new Error("Server shutting down"));
    } catch {}

    server.close(() => {
        try {
            db.close();
        } catch {}

        process.exit(0);
    });

    setTimeout(() => process.exit(1), 10000).unref();
}

process.on("SIGTERM", shutdown);
process.on("SIGINT", shutdown);

process.on("unhandledRejection", reason => {
    console.error("Unhandled promise rejection:", reason);
});

process.on("uncaughtException", error => {
    console.error("Uncaught exception:", error);
});
