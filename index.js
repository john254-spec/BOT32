"use strict";

const express = require("express");
const pino = require("pino");
const Database = require("better-sqlite3");
const fs = require("fs");
const path = require("path");
const crypto = require("crypto");

const {
    default: makeWASocket,
    DisconnectReason,
    initAuthCreds,
    BufferJSON,
    proto,
    jidNormalizedUser
} = require("@whiskeysockets/baileys");

// =====================================================
// CONFIGURATION
// =====================================================

const PORT = Number(process.env.PORT || 10000);
const PAIRING_NUMBER = String(process.env.PAIRING_NUMBER || "")
    .replace(/\D/g, "");

const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, "data");
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
// SQLITE AUTH STATE FOR BAILEYS
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
                    value = proto.Message.AppStateSyncKeyData.fromObject(
                        value
                    );
                }

                result[id] = value;
            }

            return result;
        },

        set: async (data) => {
            const transaction = db.transaction((items) => {
                for (const category of Object.keys(items)) {
                    const categoryItems = items[category] || {};

                    for (const id of Object.keys(categoryItems)) {
                        const value = categoryItems[id];
                        const key = `${category}-${id}`;

                        if (value) {
                            authWrite.run(
                                key,
                                JSON.stringify(value, BufferJSON.replacer)
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

// Compare token without directly exposing it through the API.
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
    const authHeader = req.headers.authorization || "";

    if (authHeader.toLowerCase().startsWith("bearer ")) {
        return authHeader.slice(7).trim();
    }

    return String(req.headers["x-access-token"] || "");
}

function requireToken(req, res, next) {
    const token = getRequestToken(req);

    if (!safeTokenEqual(token, ACCESS_TOKEN)) {
        return res.status(401).json({
            success: false,
            error: "Unauthorized. Provide your access token."
        });
    }

    next();
}

// =====================================================
// MESSAGE HELPERS
// =====================================================

function unwrapMessage(message) {
    if (!message) return {};

    let current = message;

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
    return Boolean(
        message?.message?.protocolMessage &&
        (
            message.message.protocolMessage.type === 0 ||
            message.message.protocolMessage.type ===
                proto.Message.ProtocolMessage.Type.REVOKE
        )
    );
}

function getPhoneFromJid(jid) {
    if (!jid || typeof jid !== "string") return null;

    if (jid.endsWith("@s.whatsapp.net")) {
        return jid.split("@")[0].split(":")[0].replace(/\D/g, "") || null;
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

    // Do not store the deletion notice as though it were the original.
    if (isRevokedMessage(message)) return;

    const chatId = key.remoteJid;
    const messageId = key.id;

    const timestamp = Number(message.messageTimestamp || Math.floor(Date.now() / 1000));

    saveMessageStatement.run({
        chat_id: chatId,
        message_id: messageId,
        sender_jid: key.participant || key.remoteJid,
        timestamp,
        message_json: JSON.stringify(message, BufferJSON.replacer)
    });

    pruneMessagesStatement.run(MAX_STORED_MESSAGES);
}

function formatMessageForLog(message) {
    const key = message?.key || {};

    return {
        chatId: key.remoteJid || null,
        messageId: key.id || null,
        senderJid: key.participant || key.remoteJid || null,
        fromMe: Boolean(key.fromMe),
        text: getMessageText(message.message) || null
    };
}

// =====================================================
// PHONE / LID RESOLUTION
// =====================================================

async function resolvePhoneNumber(jid, socket = sock) {
    if (!jid) return null;

    const directPhone = getPhoneFromJid(jid);

    if (directPhone) return directPhone;

    if (!jid.endsWith("@lid")) return null;

    if (!socket) return null;

    try {
        const mapping = socket.signalRepository?.lidMapping;

        if (mapping && typeof mapping.getPNForLID === "function") {
            const phoneJid = await mapping.getPNForLID(jid);

            const phone = getPhoneFromJid(phoneJid);

            if (phone) return phone;
        }
    } catch (error) {
        console.log(
            "LID-to-phone lookup unavailable:",
            error.message
        );
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

    const phone = await resolvePhoneNumber(jid, socket);

    return {
        jid: jid || null,
        phone,
        name:
            participant?.notify ||
            participant?.name ||
            participant?.verifiedName ||
            null
    };
}

// =====================================================
// WHATSAPP GROUP HELPERS
// =====================================================

async function getGroupMetadata(groupId) {
    if (!sock) throw new Error("WhatsApp is not initialized.");

    return sock.groupMetadata(groupId);
}

async function isGroupAdmin(groupId, senderJid) {
    if (!sock) return false;

    const metadata = await getGroupMetadata(groupId);
    const normalizedSender = normalizeJid(senderJid);

    const me = normalizeJid(sock.user?.id);

    const participant = metadata.participants.find((p) => {
        const ids = [
            p.id,
            p.jid,
            p.lid,
            p.phoneNumber,
            p.phoneNumberJid
        ].filter(Boolean).map(normalizeJid);

        return ids.includes(normalizedSender);
    });

    const botParticipant = metadata.participants.find((p) => {
        const ids = [
            p.id,
            p.jid,
            p.lid,
            p.phoneNumber,
            p.phoneNumberJid
        ].filter(Boolean).map(normalizeJid);

        return ids.includes(me);
    });

    const senderIsAdmin =
        participant?.admin === "admin" ||
        participant?.admin === "superadmin";

    const botIsAdmin =
        botParticipant?.admin === "admin" ||
        botParticipant?.admin === "superadmin";

    return {
        senderIsAdmin,
        botIsAdmin
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
                return reply(
                    [
                        "🤖 *WhatsApp Bot Commands*",
                        "",
                        "!help - Show commands",
                        "!status - Bot connection status",
                        "!chatid - Show this chat ID",
                        "!groups - List groups",
                        "!groupinfo - Show this group's information",
                        "!members - List this group's participants",
                        "!add 2547XXXXXXXX - Add a participant",
                        "!remove @mention - Remove a participant",
                        "!promote @mention - Promote a participant",
                        "!demote @mention - Demote a participant",
                        "",
                        "Some commands require the bot to be a group admin."
                    ].join("\n")
                );

            case "!status":
                return reply(
                    [
                        "🤖 *Bot Status*",
                        `Connected: ${isConnected ? "Yes" : "No"}`,
                        `Account: ${accountJid || "Not available"}`,
                        `Phone: ${accountPhone || "Not resolved"}`,
                        `Groups cached: ${lastGroupCount}`,
                        `Database: SQLite`,
                        `Messages stored: ${db.prepare("SELECT COUNT(*) AS total FROM messages").get().total}`
                    ].join("\n")
                );

            case "!chatid":
                return reply(`Chat ID:\n${chatId}`);

            case "!groups": {
                const groups = await getGroups();

                if (!groups.length) {
                    return reply("No groups found.");
                }

                const output = groups.slice(0, 50).map((group, index) => {
                    return `${index + 1}. ${group.subject}\nID: ${group.id}\nMembers: ${group.size}`;
                });

                return reply(
                    `📚 *Groups (${groups.length})*\n\n${output.join("\n\n")}` +
                    (groups.length > 50 ? "\n\nOnly the first 50 groups are shown." : "")
                );
            }

            case "!groupinfo": {
                if (!chatId.endsWith("@g.us")) {
                    return reply("Use this command inside a group.");
                }

                const group = await getGroupMetadata(chatId);

                return reply(
                    [
                        `📋 *${group.subject}*`,
                        `Group ID: ${group.id}`,
                        `Members: ${group.participants.length}`,
                        `Owner: ${group.owner || "Unknown"}`,
                        `Created: ${group.creation || "Unknown"}`,
                        `Description: ${group.desc || "No description"}`
                    ].join("\n")
                );
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
                        participant.admin === "superadmin"
                            ? "Owner"
                            : participant.admin === "admin"
                                ? "Admin"
                                : "Member";

                    lines.push(
                        `${i + 1}. ${resolved.phone || "Phone unavailable"}\n` +
                        `ID: ${resolved.jid || participant.id}\n` +
                        `Role: ${role}`
                    );
                }

                return reply(
                    `👥 *Participants (${lines.length})*\n\n` +
                    lines.slice(0, 80).join("\n\n") +
                    (lines.length > 80 ? "\n\nOnly the first 80 participants are shown." : "")
                );
            }

            case "!add": {
                if (!chatId.endsWith("@g.us")) {
                    return reply("Use this command inside a group.");
                }

                const admin = await isGroupAdmin(chatId, senderJid);

                if (!admin.senderIsAdmin) {
                    return reply("Only group admins can use this command.");
                }

                if (!admin.botIsAdmin) {
                    return reply("Please make the bot a group admin first.");
                }

                const phone = (args[0] || "").replace(/\D/g, "");

                if (!phone || phone.length < 8) {
                    return reply("Usage: !add 2547XXXXXXXX");
                }

                const result = await sock.groupParticipantsUpdate(
                    chatId,
                    [`${phone}@s.whatsapp.net`],
                    "add"
                );

                return reply(
                    `Add request processed:\n${JSON.stringify(result, null, 2)}`
                );
            }

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
                    return reply("Please make the bot a group admin first.");
                }

                const mentioned =
                    message.message?.extendedTextMessage?.contextInfo?.mentionedJid || [];

                let targets = mentioned;

                if (!targets.length && args[0]) {
                    const phone = args[0].replace(/\D/g, "");

                    if (phone.length >= 8) {
                        targets = [`${phone}@s.whatsapp.net`];
                    }
                }

                if (!targets.length) {
                    return reply(
                        `Usage: ${command} @mention\n` +
                        "You can also provide a phone number with its country code."
                    );
                }

                const action =
                    command === "!remove"
                        ? "remove"
                        : command === "!promote"
                            ? "promote"
                            : "demote";

                const result = await sock.groupParticipantsUpdate(
                    chatId,
                    targets,
                    action
                );

                return reply(
                    `${action} request processed:\n${JSON.stringify(result, null, 2)}`
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
// ANTI-DELETE
// =====================================================

async function handleDeletedMessage(message) {
    const protocol = message?.message?.protocolMessage;
    const originalKey = protocol?.key;

    if (!originalKey?.id) return;

    const chatId = originalKey.remoteJid || message.key?.remoteJid;

    if (!chatId) {
        console.log("Deleted message detected, but its chat ID was unavailable.");
        return;
    }

    const original = getSavedMessage(chatId, originalKey.id);

    console.log("\n========== ANTI-DELETE ==========");
    console.log("A message deletion was detected.");
    console.log("Chat ID:", chatId);
    console.log("Original message ID:", originalKey.id);

    if (!original) {
        console.log("Original message was not found in the SQLite message cache.");
        console.log("It may have been deleted before the bot stored it.");
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

    console.log("Original sender:", senderJid);
    console.log("Original text:", originalText || "[No recoverable text]");
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
            console.error(
                "Could not send anti-delete notice:",
                error.message
            );
        }
    }
}

// =====================================================
// MESSAGE EVENTS
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

                // Save incoming messages to SQLite for later recovery.
                saveIncomingMessage(message);

                const details = formatMessageForLog(message);

                console.log("\n========== MESSAGE ==========");
                console.log("Chat ID:", details.chatId);
                console.log("Message ID:", details.messageId);
                console.log("Sender ID:", details.senderJid);
                console.log("From bot:", details.fromMe);
                console.log("Message type:", type || "unknown");

                if (details.text) {
                    console.log("Text:", details.text);
                }

                console.log("=============================\n");

                // Do not execute the bot's own messages as commands.
                if (!message.key?.fromMe) {
                    await handleCommand(message);
                }
            } catch (error) {
                console.error("Message event error:", error);
            }
        }
    });

    socket.ev.on("group-participants.update", async (update) => {
        try {
            console.log("\n========== GROUP UPDATE ==========");
            console.log("Group ID:", update.id);
            console.log("Action:", update.action);
            console.log("Participants:", JSON.stringify(update.participants));
            console.log("==================================\n");

            if (!update.id || !Array.isArray(update.participants)) return;

            if (update.action === "add") {
                for (const participant of update.participants) {
                    try {
                        const resolved = await resolveParticipant(participant, socket);
                        const display = resolved.phone || resolved.jid || participant;

                        await socket.sendMessage(update.id, {
                            text: `👋 Welcome @${String(display).split("@")[0]}!`,
                            mentions: [participant]
                        });
                    } catch (error) {
                        console.error("Welcome message error:", error.message);
                    }
                }
            }

            if (update.action === "remove") {
                for (const participant of update.participants) {
                    try {
                        await socket.sendMessage(update.id, {
                            text: `👋 A participant has left or been removed: ${participant}`
                        });
                    } catch (error) {
                        console.error("Goodbye message error:", error.message);
                    }
                }
            }
        } catch (error) {
            console.error("Group participant update error:", error);
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

    console.log(`Reconnecting in ${Math.round(delay / 1000)} seconds...`);

    reconnectTimer = setTimeout(async () => {
        reconnectTimer = null;
        await startBot();
    }, delay);
}

// =====================================================
// START WHATSAPP BOT
// =====================================================

async function startBot() {
    if (starting) return;

    starting = true;

    try {
        console.log("Initializing WhatsApp bot...");
        console.log("SQLite database:", DB_PATH);

        const { state, saveCreds } = useSQLiteAuthState();

        const socket = makeWASocket({
            auth: state,
            logger,
            printQRInTerminal: false,
            markOnlineOnConnect: false,
            syncFullHistory: false,
            shouldSyncHistoryMessage: () => false,
            generateHighQualityLinkPreview: false,
            getMessage: async (key) => {
                const chatId = key.remoteJid;
                const saved = getSavedMessage(chatId, key.id);
                return saved?.message?.message || undefined;
            }
        });

        sock = socket;

        socket.ev.on("creds.update", saveCreds);

        registerMessageEvents(socket);

        socket.ev.on("connection.update", async (update) => {
            // Ignore events from an obsolete socket.
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

                // The token is printed in the server logs only.
                // It is not returned by any HTTP endpoint.
                console.log("ACCESS TOKEN:", ACCESS_TOKEN);

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
                    (statusCode ? `Status ${statusCode}` : "Connection closed");

                console.log("WhatsApp connection closed.");
                console.log("Disconnect reason:", lastDisconnectReason);
                console.log("Disconnect code:", statusCode);

                sock = null;

                const loggedOut =
                    statusCode === DisconnectReason.loggedOut;

                if (loggedOut) {
                    console.error(
                        "WhatsApp logged out. Remove the old session only if you intend to pair again."
                    );
                    return;
                }

                scheduleReconnect();
            }
        });

        // Request a pairing code only when there is no registered session.
        if (!state.creds.registered && PAIRING_NUMBER && !pairingRequested) {
            pairingRequested = true;

            setTimeout(async () => {
                try {
                    if (sock !== socket || state.creds.registered) return;

                    const code = await socket.requestPairingCode(PAIRING_NUMBER);

                    console.log("\n==================================");
                    console.log("WHATSAPP PAIRING CODE:", code);
                    console.log("Open WhatsApp > Linked devices > Link a device.");
                    console.log("Choose the phone-number pairing option and enter the code.");
                    console.log("==================================\n");
                } catch (error) {
                    pairingRequested = false;
                    console.error("Could not request pairing code:", error.message);
                }
            }, 3000);
        } else if (!state.creds.registered && !PAIRING_NUMBER) {
            console.log(
                "No saved WhatsApp session. Set PAIRING_NUMBER in Render environment variables."
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
small { color: #52615a; }
</style>
</head>
<body>
<h1>WhatsApp Bot Dashboard</h1>
<p>Bot connection and database status.</p>

<div class="card">
    <h3>Connection</h3>
    <p id="status" class="status">Loading...</p>
    <p id="account">Account: Loading...</p>
    <p id="phone">Phone: Loading...</p>
    <p id="groups">Groups: Loading...</p>
    <p id="messages">Stored messages: Loading...</p>
    <p id="connectedAt">Last connected: Loading...</p>
    <button onclick="refreshStatus()">Refresh</button>
</div>

<div class="card">
    <h3>API endpoints</h3>
    <p><code>GET /health</code> — health status</p>
    <p><code>GET /session</code> — basic session status</p>
    <p><code>GET /groups</code> — list groups (token required)</p>
    <p><code>POST /send</code> — send a message (token required)</p>
    <small>The access token is deliberately not displayed on this public page.</small>
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
    } catch (error) {
        document.getElementById("status").textContent = "Unable to load status";
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

// Never return the access token from this endpoint.
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

    const messages = rows.map((row) => {
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
                error: "Provide both 'to' and 'message' as strings."
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
    console.log("Access token:", ACCESS_TOKEN);
    console.log("==================================");

    startBot().catch((error) => {
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
        sock?.end(undefined);
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

process.on("unhandledRejection", (reason) => {
    console.error("Unhandled promise rejection:", reason);
});

process.on("uncaughtException", (error) => {
    console.error("Uncaught exception:", error);
});
