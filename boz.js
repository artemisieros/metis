const {
    default: makeWASocket,
    useMultiFileAuthState,
    downloadContentFromMessage,
    isJidBroadcast,
    DisconnectReason,
    WAMediaUpload,
    getDevice
} = require('@whiskeysockets/baileys');
const qrcode = require('qrcode-terminal');
const fs = require('fs');
const fsp = require('fs').promises;
const path = require('path');
const ffmpegPath = require('ffmpeg-static');
const ffmpeg = require('fluent-ffmpeg');
ffmpeg.setFfmpegPath(ffmpegPath);
const axios = require('axios');
const { exec, spawn } = require('child_process');
const sharp = require('sharp');
const pino = require('pino');
const { Boom } = require('@hapi/boom');
const fsExtra = require('fs-extra');
const { URL } = require('url');
const { GoogleGenerativeAI } = require("@google/generative-ai");
const util = require('util');
const { pipeline } = require('stream');
const { promisify } = require('util');
const streamPipeline = promisify(pipeline);

            
const AUTH_FOLDER = '/data/auth_info_baileys';
const TEMP_FOLDER = '/tmp/whatsapp-bot-boz';
const TAGS_FILE = path.join('/data', 'tags.json');
const MENU_IMAGE_PATH = path.join('/data', 'menu.jpg');
const YOUTUBE_API_KEY = 'SUA API YOUTUBE AQUI';
const GEMINI_API_KEY = 'SUA GEMINI API AQUI';
const GD_MENU_AUDIOS_FOLDER_ID = '19egDi9YEbZE-iCSfl5AqUixg6OjuxBaT';
const YOUTUBE_COOKIES_FILE = path.join(__dirname, 'cookies.txt');

        
const MAX_STICKER_SIZE = 1 * 1024 * 1024; 
const STICKER_PACK_NAME = "Feito por Boz🤖";
const STICKER_AUTHOR_NAME = "Boz";

    
const SESSION_TIMEOUT = 5 * 60 * 1000; 
const ADMIN_NUMBER = 'seunumeroaqui@s.whatsapp.net';
const QR_MIN_INTERVAL = 30 * 1000; 
const MAX_CONNECTION_RETRIES = 10;  
const MAX_MEDIA_BUFFER_SIZE = 50 * 1024 * 1024;

    
const RATE_LIMIT_WINDOW = 60 * 1000;    
const MAX_MESSAGES_PER_WINDOW = 15;     
const MESSAGE_DELAY_MS = 800;   
const STICKER_QUEUE_MAX = 50;       
const PARALLEL_PROCESSING_LIMIT = 3;    
    
    
const HEALTH_CHECK_INTERVAL = 60 * 1000;    
const MEMORY_CLEANUP_INTERVAL = 30 * 60 * 1000;     
const MAX_MEMORY_USAGE = 500 * 1024 * 1024;     
const RECONNECTION_DELAY_BASE = 3000;   
const MAX_RECONNECTION_DELAY = 60000;   
    
        
    
const GD_AUDIO_FILES = {
    'menu1.mp3': '1LuKilSWJLfqn74MmG2rO3W8q1CS85QmT',
    'menu2.mp3': '1HiFsoXYtfiOzN9uDNxHEYYCljGpw09uh',
    'menu3.mp3': '1WefeMXnC79d3B-DL_rgo7NxGXHERgHAm',
    'menu4.mp3': '1m6b5c6_D0stm-oFip6ZzKlZnLSsopnEe',
    'menu5.mp3': '1h8_geWdzrwIbqv4NjZpFdgLwlDvc4QD9'
};

        
let sock;
let tags = {};
const autoStickerMode = new Set();
let connectionRetries = 0;
let lastQrTime = 0;
let isBotRunning = false;
let pingInterval = null;
let healthCheckInterval = null;
let memoryCleanupInterval = null;
let lastActivity = Date.now();
let isReconnecting = false;

        
const USER_SESSIONS = new Map();
const GEMINI_CHAT_SESSIONS = new Map();
const WAITING_FOR_COOKIES = new Set();

    
class RateLimiter {
    constructor() {
        this.messageHistory = [];
        this.isThrottled = false;
        this.throttleEndTime = 0;
    }

    canSendMessage() {
        const now = Date.now();
        
            
        this.messageHistory = this.messageHistory.filter(time => now - time < RATE_LIMIT_WINDOW);
        
        
        if (this.isThrottled && now < this.throttleEndTime) {
            return false;
        } else if (this.isThrottled) {
            this.isThrottled = false;
            logger.info('Rate limit throttle removido');
        }
        
        
        return this.messageHistory.length < MAX_MESSAGES_PER_WINDOW;
    }

    recordMessage() {
        this.messageHistory.push(Date.now());
    }

    activateThrottle(durationMs = 30000) {
        this.isThrottled = true;
        this.throttleEndTime = Date.now() + durationMs;
        logger.warn(`Rate limit throttle ativado por ${durationMs/1000}s`);
    }

    getWaitTime() {
        if (this.isThrottled) {
            return Math.max(0, this.throttleEndTime - Date.now());
        }
        
        const now = Date.now();
        this.messageHistory = this.messageHistory.filter(time => now - time < RATE_LIMIT_WINDOW);
        
        if (this.messageHistory.length >= MAX_MESSAGES_PER_WINDOW) {
            const oldestMessage = Math.min(...this.messageHistory);
            return Math.max(0, RATE_LIMIT_WINDOW - (now - oldestMessage));
        }
        
        return 0;
    }
}

class CompressionCache {
    constructor() {
        this.cache = new Map();
        this.maxSize = 50;  
    }

    getKey(buffer, strategy) {
        const crypto = require('crypto');
        return crypto.createHash('md5')
            .update(buffer)
            .update(strategy)
            .digest('hex')
            .substring(0, 12);
    }

    get(key) {
        if (this.cache.has(key)) {
            const item = this.cache.get(key);
            item.lastUsed = Date.now();
            return item.data;
        }
        return null;
    }

    set(key, data) {
        if (this.cache.size >= this.maxSize) {
            
            const oldest = Array.from(this.cache.entries())
                .sort((a, b) => a[1].lastUsed - b[1].lastUsed)[0];
            this.cache.delete(oldest[0]);
        }
        
        this.cache.set(key, {
            data,
            created: Date.now(),
            lastUsed: Date.now()
        });
    }
}

class QueueMonitorEnhanced {
    constructor(queue) {
        this.queue = queue;
        this.lastStats = { queue: 0, processing: 0 };
        this.alertThresholds = {
            queueSize: 50,
            processingTime: 30000,
            rejectionRate: 0.15
        };
    }

    startMonitoring() {
        setInterval(() => {
            const stats = this.queue.getStats();
            
            
            const queueLoad = stats.queue;
            const processingLoad = stats.processing;
            
            if (queueLoad > 20 && processingLoad === stats.maxConcurrent) {
                this.queue.adjustCapacity('high');
            } else if (queueLoad < 5 && processingLoad < stats.maxConcurrent / 2) {
                this.queue.adjustCapacity('low');
            }
            
        
            if (stats.queue > 5 || stats.processing > 0 || stats.queue > this.lastStats.queue) {
                logger.info(`📊 Fila figurinhas: ${stats.queue} aguardando, ${stats.processing}/${stats.maxConcurrent} processando`);
                
                if (Object.keys(stats.userQueueStats).length > 0) {
                    logger.debug('Filas por usuário:', stats.userQueueStats);
                }
            }
            
    
            if (stats.queue > this.alertThresholds.queueSize) {
                logger.warn(`⚠️ Fila muito cheia: ${stats.queue} itens`);
            }
            
            
            if (stats.performance.totalProcessed > 0) {
                const successRate = (stats.performance.totalProcessed / 
                    (stats.performance.totalProcessed + stats.performance.totalFailed)) * 100;
                
                if (successRate < 85) {
                    logger.warn(`⚠️ Taxa de sucesso baixa: ${successRate.toFixed(1)}%`);
                }
            }
            
        
            this.queue.cleanup();
            this.lastStats = { queue: stats.queue, processing: stats.processing };
            
        }, 15000);  
        
    
        setInterval(() => {
            if (this.queue.queue.length > 0) {
                logger.debug('Executando flush da fila...');
                this.queue.flushQueue().catch(err => 
                    logger.warn(`Erro no flush: ${err.message}`)
                );
            }
        }, 30000);  
    }
}

class CompressionPool {
    constructor(maxWorkers = 4) {
        this.maxWorkers = maxWorkers;
        this.activeWorkers = 0;
        this.queue = [];
        this.stats = {
            processed: 0,
            totalSaved: 0,  
            avgCompressionRatio: 0,
            avgProcessingTime: 0
        };
    }

    async compress(buffer, options = {}) {
        return new Promise((resolve, reject) => {
            const task = {
                buffer,
                options,
                resolve,
                reject,
                startTime: Date.now(),
                originalSize: buffer.length
            };
            
            this.queue.push(task);
            this.processNext();
        });
    }

    async executeCompression(task) {
        const { buffer, options, originalSize } = task;
        
        let compressionStrategy;
        
        if (originalSize > 800 * 1024) {    
            compressionStrategy = 'aggressive';
        } else if (originalSize > 400 * 1024) {     
            compressionStrategy = 'balanced';
        } else {
            compressionStrategy = 'light';
        }

        return await this.applyCompressionStrategy(buffer, compressionStrategy, options);
    }

    async applyCompressionStrategy(buffer, strategy, options = {}) {
        const strategies = {
            aggressive: {
                quality: 55,
                effort: 1,  
                smartSubsample: true,
                reductionEffort: 6,
                alphaQuality: 50
            },
            balanced: {
                quality: 65,
                effort: 2,  
                smartSubsample: true,
                reductionEffort: 4,
                alphaQuality: 70
            },
            light: {
                quality: 75,
                effort: 1,  
                smartSubsample: false,
                reductionEffort: 2,
                alphaQuality: 80
            }
        };

        const config = { ...strategies[strategy], ...options };

        try {
            return await sharp(buffer)
                .webp(config)
                .toBuffer();
        } catch (error) {
            logger.debug('Tentando compressão fallback...');
            return await sharp(buffer)
                .webp({ 
                    quality: 60, 
                    effort: 0,  
                    lossless: false 
                })
                .toBuffer();
        }
    }

    updateStats(task, result) {
        const processingTime = Date.now() - task.startTime;
        const saved = task.originalSize - result.length;
        const compressionRatio = (saved / task.originalSize) * 100;

        this.stats.processed++;
        this.stats.totalSaved += saved;
        this.stats.avgCompressionRatio = (this.stats.avgCompressionRatio * 0.9) + (compressionRatio * 0.1);
        this.stats.avgProcessingTime = (this.stats.avgProcessingTime * 0.9) + (processingTime * 0.1);
    }

    getStats() {
        return {
            ...this.stats,
            active: this.activeWorkers,
            queued: this.queue.length,
            totalSavedMB: (this.stats.totalSaved / 1024 / 1024).toFixed(2)
        };
    }
}

class EnhancedOptimizedStickerQueue {
    constructor() {
        this.queue = [];
        this.processing = new Map();
        this.processedCount = 0;
        this.rejectedCount = 0;
        this.maxConcurrent = 8;
        this.maxQueueSize = 200;
        this.retryAttempts = new Map();
        this.maxRetries = 3;
        this.processingMap = new Map();
        this.userQueues = new Map();
        this.lastProcessTime = Date.now();
        
        
        this.processingStats = {
            totalProcessed: 0,
            totalFailed: 0,
            avgProcessTime: 0,
            peakQueue: 0
        };
        
        
        this.stats = {
            processed: 0,
            totalSaved: 0,
            avgCompressionRatio: 0,
            avgProcessingTime: 0
        };
        
        this.activeWorkers = 0;
        this.maxWorkers = 4;
    }

    calculatePriority(task) {
        let priority = 50;
        const waitTime = Date.now() - task.timestamp;
        priority += Math.min(waitTime / 1000, 30);
        
        if (task.attempts > 0) {
            priority += task.attempts * 10;
        }
        
        if (task.userJid && task.userJid === ADMIN_NUMBER) {
            priority += 25;
        }
        
        return Math.round(priority);
    }

    add(task) {
        const now = Date.now();
        const taskId = task.id;
        const userJid = task.userJid;
        
        const isAlreadyProcessing = this.processing.has(taskId);
        const isAlreadyQueued = this.queue.some(t => t.id === taskId);
        
        if (isAlreadyProcessing || isAlreadyQueued) {
            logger.debug(`Tarefa duplicada ignorada: ${taskId}`);
            return false;
        }

        if (!this.userQueues.has(userJid)) {
            this.userQueues.set(userJid, []);
        }

        const userQueue = this.userQueues.get(userJid);
        
        if (userQueue.length > 10) {
            const removedTask = userQueue.shift();
            const queueIndex = this.queue.findIndex(t => t.id === removedTask.id);
            if (queueIndex >= 0) {
                this.queue.splice(queueIndex, 1);
                logger.warn(`Removida figurinha antiga do usuário ${userJid}`);
            }
        }

        if (this.queue.length >= this.maxQueueSize) {
            const oldestTask = this.queue.shift();
            if (oldestTask) {
                const oldUserQueue = this.userQueues.get(oldestTask.userJid);
                if (oldUserQueue) {
                    const index = oldUserQueue.findIndex(t => t.id === oldestTask.id);
                    if (index >= 0) oldUserQueue.splice(index, 1);
                }
                logger.warn(`Fila cheia: removida tarefa antiga ${oldestTask.id}`);
            }
        }

        task.timestamp = now;
        task.attempts = task.attempts || 0;
        task.priority = this.calculatePriority(task);
        
        this.queue.push(task);
        userQueue.push(task);
        
        this.processingStats.peakQueue = Math.max(this.processingStats.peakQueue, this.queue.length);
        
        logger.debug(`Figurinha adicionada: ${taskId} (fila: ${this.queue.length}, processando: ${this.processing.size})`);
        
        setImmediate(() => this.processNext());
        
        return true;
    }

    async processNext() {
        if (this.processing.size >= this.maxConcurrent || this.queue.length === 0) {
            return;
        }

        this.queue.sort((a, b) => b.priority - a.priority);
        
        const task = this.queue.shift();
        if (!task) return;

        const taskId = task.id;
        const startTime = Date.now();

        this.processing.set(taskId, {
            task,
            startTime,
            userJid: task.userJid
        });

        this.processingMap.set(taskId, 'processing');

        try {
            await this.executeTaskWithTimeout(task);
            
            this.processedCount++;
            this.processingStats.totalProcessed++;
            
            const processingTime = Date.now() - startTime;
            this.processingStats.avgProcessTime = 
                (this.processingStats.avgProcessTime * 0.9) + (processingTime * 0.1);

            logger.debug(`[${taskId}] Processado com sucesso em ${processingTime}ms`);

        } catch (error) {
            await this.handleTaskError(task, error);
        } finally {
            this.cleanupTask(taskId);
            
            setTimeout(() => this.processNext(), 100);
        }
    }

    async executeTaskWithTimeout(task) {
        const timeout = new Promise((_, reject) => 
            setTimeout(() => reject(new Error('Timeout processamento')), 60000)
        );

        try {
            await Promise.race([task.execute(), timeout]);
        } catch (error) {
            throw error;
        }
    }

    async handleTaskError(task, error) {
        task.attempts = (task.attempts || 0) + 1;
        
        logger.warn(`Erro figurinha ${task.id} (tentativa ${task.attempts}): ${error.message}`);
        
        this.processingStats.totalFailed++;

        if (task.attempts < this.maxRetries && this.shouldRetry(error)) {
            const baseDelay = Math.min(1000 * Math.pow(2, task.attempts - 1), 8000);
            task.retryDelay = baseDelay + Math.random() * 1000;
            
            task.priority += 25;
            
            setTimeout(() => {
                this.queue.unshift(task);
                this.processingMap.set(task.id, 'queued');
                this.processNext();
            }, task.retryDelay);
            
            logger.info(`⏳ Reagendando ${task.id} em ${task.retryDelay}ms (tentativa ${task.attempts})`);
        } else {
            this.rejectedCount++;
            
            if (task.onError) {
                try {
                    await task.onError(error);
                } catch (errorHandlingError) {
                    logger.error(`Erro ao executar onError para ${task.id}: ${errorHandlingError.message}`);
                }
            }
        }
    }

    shouldRetry(error) {
        const retryableErrors = [
            'timeout',
            'network',
            'rate-overlimit',
            'connection',
            'temporary',
            'econnreset',
            'socket hang up',
            'request timeout'
        ];
        
        const errorMessage = error.message.toLowerCase();
        return retryableErrors.some(keyword => errorMessage.includes(keyword));
    }

    cleanupTask(taskId) {
        const processingInfo = this.processing.get(taskId);
        
        if (processingInfo) {
            const userQueue = this.userQueues.get(processingInfo.userJid);
            if (userQueue) {
                const index = userQueue.findIndex(t => t.id === taskId);
                if (index >= 0) userQueue.splice(index, 1);
                
                if (userQueue.length === 0) {
                    this.userQueues.delete(processingInfo.userJid);
                }
            }
        }
        
        this.processing.delete(taskId);
        this.processingMap.delete(taskId);
        this.retryAttempts.delete(taskId);
    }

    getStats() {
        const userQueueStats = {};
        try {
            if (this.userQueues && typeof this.userQueues.entries === 'function') {
                for (const [userJid, queue] of this.userQueues.entries()) {
                    if (queue && queue.length > 0) {
                        userQueueStats[userJid] = queue.length;
                    }
                }
            }
        } catch (error) {
            logger.warn('Erro ao coletar estatísticas de usuários:', error);
        }

        return {
            queue: this.queue?.length || 0,
            processing: this.processing?.size || 0,
            processed: this.processedCount || 0,
            rejected: this.rejectedCount || 0,
            maxConcurrent: this.maxConcurrent || 0,
            userQueues: Object.keys(userQueueStats).length || 0,
            userQueueStats,
            performance: {
                totalProcessed: this.processingStats.totalProcessed || 0,
                totalFailed: this.processingStats.totalFailed || 0,
                avgProcessTime: Math.round(this.processingStats.avgProcessTime || 0)
            },
            compression: {
                totalSaved: this.stats.totalSaved || 0,
                avgCompressionRatio: this.stats.avgCompressionRatio || 0,
                avgProcessingTime: this.stats.avgProcessingTime || 0
            },
            active: this.activeWorkers || 0,
            queued: this.queue?.length || 0,
            totalSavedMB: (this.stats?.totalSaved / 1024 / 1024).toFixed(2) || "0.00",
            timestamp: Date.now()
        };
    }

    cleanup() {
        const now = Date.now();
        const maxAge = 10 * 60 * 1000;

        const initialLength = this.queue.length;
        this.queue = this.queue.filter(task => {
            const age = now - task.timestamp;
            if (age > maxAge) {
                this.cleanupTask(task.id);
                return false;
            }
            return true;
        });
        
        for (const [taskId, info] of this.processing.entries()) {
            const age = now - info.startTime;
            if (age > maxAge) {
                logger.warn(`Limpando processamento órfão: ${taskId}`);
                this.cleanupTask(taskId);
            }
        }
        
        const removedCount = initialLength - this.queue.length;
        if (removedCount > 0) {
            logger.info(`Limpeza: removidas ${removedCount} tarefas antigas`);
        }
    }

    async flushQueue() {
        logger.info(`Processando ${this.queue.length} figurinhas pendentes...`);
        
        while (this.queue.length > 0 && this.processing.size < this.maxConcurrent) {
            await this.processNext();
            
            await new Promise(resolve => setTimeout(resolve, 50));
        }
    }

    adjustCapacity(load) {
        const oldCapacity = this.maxConcurrent;
        
        if (load === 'high' && this.maxConcurrent < 12) {
            this.maxConcurrent++;
        } else if (load === 'low' && this.maxConcurrent > 3) {
            this.maxConcurrent--;
        }
        
        if (oldCapacity !== this.maxConcurrent) {
            logger.info(`Capacidade ajustada: ${oldCapacity} → ${this.maxConcurrent}`);
        }
    }

    async compress(buffer, options = {}) {
        return new Promise((resolve, reject) => {
            const task = {
                buffer,
                options,
                resolve,
                reject,
                startTime: Date.now(),
                originalSize: buffer.length
            };
            
            this.queue.push(task);
            this.processNext();
        });
    }

    async executeCompression(task) {
        const { buffer, options, originalSize } = task;
        
        let compressionStrategy;
        
        if (originalSize > 800 * 1024) {
            compressionStrategy = 'aggressive';
        } else if (originalSize > 400 * 1024) {
            compressionStrategy = 'balanced';
        } else {
            compressionStrategy = 'light';
        }

        return await this.applyCompressionStrategy(buffer, compressionStrategy, options);
    }

    async applyCompressionStrategy(buffer, strategy, options = {}) {
        const strategies = {
            aggressive: {
                quality: 55,
                effort: 1,
                smartSubsample: true,
                reductionEffort: 6,
                alphaQuality: 50
            },
            balanced: {
                quality: 65,
                effort: 2,
                smartSubsample: true,
                reductionEffort: 4,
                alphaQuality: 70
            },
            light: {
                quality: 75,
                effort: 1,
                smartSubsample: false,
                reductionEffort: 2,
                alphaQuality: 80
            }
        };

        const config = { ...strategies[strategy], ...options };

        try {
            return await sharp(buffer)
                .webp(config)
                .toBuffer();
        } catch (error) {
            logger.debug('Tentando compressão fallback...');
            return await sharp(buffer)
                .webp({ 
                    quality: 60, 
                    effort: 0,
                    lossless: false 
                })
                .toBuffer();
        }
    }

    updateStats(task, result) {
        const processingTime = Date.now() - task.startTime;
        const saved = task.originalSize - result.length;
        const compressionRatio = (saved / task.originalSize) * 100;

        this.stats.processed++;
        this.stats.totalSaved += saved;
        this.stats.avgCompressionRatio = (this.stats.avgCompressionRatio * 0.9) + (compressionRatio * 0.1);
        this.stats.avgProcessingTime = (this.stats.avgProcessingTime * 0.9) + (processingTime * 0.1);
    }
}

class MediaCache {
    constructor() {
        this.cache = new Map();
        this.maxSize = 100;
        this.hitCount = 0;
        this.missCount = 0;
    }

    getKey(buffer, mimetype, options = {}) {
        const crypto = require('crypto');
        const hash = crypto.createHash('md5');
        hash.update(buffer);
        hash.update(mimetype);
        hash.update(JSON.stringify(options));
        return hash.digest('hex').substring(0, 16);
    }

    get(key) {
        if (this.cache.has(key)) {
            this.hitCount++;
            const item = this.cache.get(key);
            item.lastUsed = Date.now();
            return item.data;
        }
        this.missCount++;
        return null;
    }

    set(key, data) {
        if (this.cache.size >= this.maxSize) {
            this.cleanup();
        }
        this.cache.set(key, {
            data,
            created: Date.now(),
            lastUsed: Date.now(),
            size: Buffer.isBuffer(data) ? data.length : 0
        });
    }

    cleanup() {
        const entries = Array.from(this.cache.entries());
        entries.sort((a, b) => a[1].lastUsed - b[1].lastUsed);
        
        
        const toRemove = Math.floor(entries.length * 0.25);
        for (let i = 0; i < toRemove; i++) {
            this.cache.delete(entries[i][0]);
        }
    }

    getStats() {
        return {
            size: this.cache.size,
            hitRate: this.hitCount / (this.hitCount + this.missCount) || 0,
            hits: this.hitCount,
            misses: this.missCount
        };
    }
}

class FFmpegWorkerPool {
    constructor(maxWorkers = 3) {
        this.maxWorkers = maxWorkers;
        this.activeWorkers = 0;
        this.queue = [];
        this.workerStats = {
            processed: 0,
            failed: 0,
            avgTime: 0
        };
    }

    async execute(task) {
        return new Promise((resolve, reject) => {
            this.queue.push({ task, resolve, reject, startTime: Date.now() });
            this.processNext();
        });
    }

    async processNext() {
        if (this.activeWorkers >= this.maxWorkers || this.queue.length === 0) {
            return;
        }

        this.activeWorkers++;
        const { task, resolve, reject, startTime } = this.queue.shift();

        try {
            const result = await task();
            this.workerStats.processed++;
            this.updateAvgTime(Date.now() - startTime);
            resolve(result);
        } catch (error) {
            this.workerStats.failed++;
            reject(error);
        } finally {
            this.activeWorkers--;
                
            setTimeout(() => this.processNext(), 50);
        }
    }

    updateAvgTime(duration) {
        this.workerStats.avgTime = (this.workerStats.avgTime * 0.9) + (duration * 0.1);
    }

    getStats() {
        return {
            ...this.workerStats,
            active: this.activeWorkers,
            queued: this.queue.length
        };
    }
}

const mediaCache = new MediaCache();
const compressionCache = new CompressionCache();
const rateLimiter = new RateLimiter();
const optimizedStickerQueue = new EnhancedOptimizedStickerQueue();
const enhancedOptimizedStickerQueue = optimizedStickerQueue
const enhancedQueueMonitor = new QueueMonitorEnhanced(optimizedStickerQueue);
const processingCache = new Map();
enhancedQueueMonitor.startMonitoring();
const ffmpegPool = new FFmpegWorkerPool(3);
const compressionPool = new CompressionPool(4);
let availableAudios = [];

    
process.env.TZ = 'America/Sao_Paulo';

let genAI;
if (GEMINI_API_KEY && GEMINI_API_KEY !== 'SUA_CHAVE_AQUI') {
    genAI = new GoogleGenerativeAI(GEMINI_API_KEY);
} else {
    console.warn("⚠️ Chave da API Gemini não configurada. O comando /gemini não funcionará.");
}

    
const logger = pino({
    level: process.env.LOG_LEVEL || 'debug',
    transport: {
        target: 'pino-pretty',
        options: {
            colorize: true,
            translateTime: 'SYS:dd-mm-yyyy HH:MM:ss',
            ignore: 'pid,hostname',
            levelFirst: true,
            customColors: 'error:red,warn:yellow,info:blue,debug:green,trace:gray'
        }
    }
});

        
async function safeSendMessage(sockInstance, jid, content, options = {}) {
    
    const waitTime = rateLimiter.getWaitTime();
    if (waitTime > 0) {
        logger.debug(`Aguardando ${waitTime}ms devido ao rate limit`);
        await new Promise(resolve => setTimeout(resolve, waitTime));
    }

    if (!rateLimiter.canSendMessage()) {
        logger.warn('Rate limit atingido, adiando mensagem');
        await new Promise(resolve => setTimeout(resolve, 5000));
    }

    try {
        
        await new Promise(resolve => setTimeout(resolve, MESSAGE_DELAY_MS));
        
        const result = await sockInstance.sendMessage(jid, content, options);
        rateLimiter.recordMessage();
        return result;
    } catch (error) {
        
        if (error.message?.includes('rate-overlimit') || error.data === 429) {
            logger.warn('Rate limit detectado pelo WhatsApp');
            rateLimiter.activateThrottle(60000);    
            throw new Error('Muitas mensagens enviadas. Aguarde um momento.');
        }
        throw error;
    }
}
    
function performHealthCheck() {
    const memoryUsage = process.memoryUsage();
    const rssUsage = memoryUsage.rss;
    
    const shouldLog = rssUsage > MAX_MEMORY_USAGE || 
                     (Date.now() - lastActivity > 10 * 60 * 1000);
    
    if (shouldLog) {
            
        const stickerStats = optimizedStickerQueue ? optimizedStickerQueue.getStats() : {
            queue: 0,
            processing: 0,
            processed: 0,
            rejected: 0,
            performance: {
                totalProcessed: 0,
                totalFailed: 0,
                avgProcessTime: 0
            }
        };
        
        logger.info({
            rss: `${(rssUsage / 1024 / 1024).toFixed(2)}MB`,
            heapUsed: `${(memoryUsage.heapUsed / 1024 / 1024).toFixed(2)}MB`,
            uptime: `${Math.floor(process.uptime() / 3600)}h ${Math.floor((process.uptime() % 3600) / 60)}m`,
            connectionStatus: sock?.user ? 'Connected' : 'Disconnected',
            activeSessions: USER_SESSIONS.size + GEMINI_CHAT_SESSIONS.size,
            stickerQueue: stickerStats.queue,
            stickerProcessing: stickerStats.processing,
            rateLimitThrottled: rateLimiter ? rateLimiter.isThrottled : false
        }, 'Health Check');
    }
    
    
    if (rssUsage > MAX_MEMORY_USAGE && global.gc) {
        logger.warn('Memória alta detectada, forçando garbage collection');
        global.gc();
    }
    
    
    if (sock && !sock.ws?.isOpen && !isReconnecting) {
        logger.warn('WebSocket fechado detectado durante health check, iniciando reconexão');
        scheduleReconnection();
    }
}
        
function performMemoryCleanup() {
    const now = Date.now();
    let clearedSessions = 0;
    
    for (const [jid, session] of USER_SESSIONS.entries()) {
        if (now > session.expiry) {
            USER_SESSIONS.delete(jid);
            clearedSessions++;
        }
    }
    
    for (const [jid, session] of GEMINI_CHAT_SESSIONS.entries()) {
        if (now > session.expiry) {
            GEMINI_CHAT_SESSIONS.delete(jid);
            clearedSessions++;
        }
    }
    
    cleanupTempFiles().catch(err => 
        logger.warn(err, 'Erro durante limpeza de arquivos temporários')
    );
    
    if (clearedSessions > 0) {
        logger.info(`Limpeza de memória: ${clearedSessions} sessões removidas`);
    }
    
    if (global.gc) {
        global.gc();
    }
}

    
async function cleanupTempFiles() {
    try {
        const files = await fsp.readdir(TEMP_FOLDER);
        const now = Date.now();
        let removedFiles = 0;
        
        for (const file of files) {
            const filePath = path.join(TEMP_FOLDER, file);
            try {
                const stats = await fsp.stat(filePath);
                if (now - stats.mtime.getTime() > 60 * 60 * 1000) {
                    await fsp.unlink(filePath);
                    removedFiles++;
                }
            } catch (error) {
                continue;
            }
        }
        
        if (removedFiles > 0) {
            logger.info(`Removidos ${removedFiles} arquivos temporários antigos`);
        }
    } catch (error) {
        logger.warn(error, 'Erro ao limpar arquivos temporários');
    }
}

function cleanupProcessingCache() {
    const now = Date.now();
    const maxAge = 2 * 60 * 1000;   
    let cleaned = 0;
    
    for (const [key, timestamp] of processingCache.entries()) {
        if (now - timestamp > maxAge) {
            processingCache.delete(key);
            cleaned++;
        }
    }
    
    if (cleaned > 0) {
        logger.debug(`Cache de processamento: ${cleaned} entradas antigas removidas`);
    }
}

    
setInterval(cleanupProcessingCache, 30000);     

function parseYtDlpSearchResults(output) {
    const lines = output.trim().split('\n').filter(Boolean);
    const results = [];
    for (const line of lines) {
        try {
            const item = JSON.parse(line);
            if (item.id && item.title) {
                 results.push({
                    title: item.title || 'Sem título',
                    channel: item.uploader || item.channel || 'Canal desconhecido',
                    url: `https://www.youtube.com/watch?v=${item.id}`
                });
            }
        } catch (parseError) {
            logger.warn(parseError, 'Erro ao parsear resultado do yt-dlp');
        }
    }
    return results.filter(item => item.url);
}

        
const sessionCleanupInterval = setInterval(() => {
    const now = Date.now();
    let clearedSessions = 0;
    
    for (const [jid, session] of USER_SESSIONS.entries()) {
        const choiceExpired = session.waitingForDownloadChoice && 
                             session.downloadChoiceExpiry && 
                             now > session.downloadChoiceExpiry;
        if (now > session.expiry || choiceExpired) {
            USER_SESSIONS.delete(jid);
            clearedSessions++;
        }
    }
    
    if (clearedSessions > 0) {
        logger.debug(`Sessões limpas: ${clearedSessions}`);
    }
}, 60000);

    
async function createOptimizedStickerEnhanced(messageToProcess, sockInstance) {
    const jid = messageToProcess.key.remoteJid;
    const messageId = messageToProcess.key.id;
    const userJid = jid.split('@')[0];
    
        
    const messageTimestamp = messageToProcess.messageTimestamp || Date.now();
    const duplicateKey = `${userJid}_${messageId}_${messageTimestamp}`;
    
    
    const isAlreadyProcessing = processingCache.has(duplicateKey);
    
    if (isAlreadyProcessing) {
        const cacheTime = processingCache.get(duplicateKey);
            
        if (Date.now() - cacheTime < 15000) {
            logger.debug(`Processamento duplicado evitado: ${messageId}`);
            return;
        } else {
            processingCache.delete(duplicateKey);
        }
    }
    
        
    processingCache.set(duplicateKey, Date.now());
    
    const task = {
        id: `${userJid}_${messageId}_${Date.now()}`,
        userJid: jid,
        timestamp: Date.now(),
        messageId: messageId,
        
        execute: async () => {
            try {
                logger.debug(`[${task.id}] Iniciando processamento de figurinha`);
                await processStickerTaskOptimized(messageToProcess, sockInstance);
                logger.debug(`[${task.id}] Figurinha processada com sucesso`);
            } catch (error) {
                logger.error(`[${task.id}] Erro no processamento: ${error.message}`);
                throw error;
            }
        },
        
        onError: async (error) => {
            try {
                const errorMsg = error.message.length > 100 
                    ? error.message.substring(0, 100) + '...'
                    : error.message;
                    
                await safeSendMessage(sockInstance, jid, { 
                    text: `⚠️ Erro ao criar figurinha: ${errorMsg}` 
                }, { quoted: messageToProcess });
            } catch (sendError) {
                logger.error(`Falha ao enviar mensagem de erro para ${jid}: ${sendError.message}`);
            } finally {
                    
                processingCache.delete(duplicateKey);
            }
        }
    };
    
    try {
        const added = enhancedOptimizedStickerQueue.add(task);
        if (!added) {
            logger.warn(`Figurinha não foi adicionada à fila: ${task.id}`);
            processingCache.delete(duplicateKey);
        } else {
            logger.debug(`[${task.id}] Figurinha adicionada à fila com sucesso`);
            
            
            setTimeout(() => {
                processingCache.delete(duplicateKey);
            }, 60000);  
        }
    } catch (error) {
        processingCache.delete(duplicateKey);
        await safeSendMessage(sockInstance, jid, { 
            text: `⚠️ Erro ao processar figurinha: ${error.message}` 
        }, { quoted: messageToProcess });
    }
}


async function processStickerTaskOptimized(messageToProcess, sockInstance) {
    const jid = messageToProcess.key.remoteJid;
    const startTime = Date.now();
    let mediaMessage;
    let tempInputPath = null;
    let tempOutputPath = null;
    let frameFullPath = null;

    try {
        let mediaTypeForDownload = 'image';
        let originalMimetype = '';
        let shouldBeAnimated = false;

        
        if (messageToProcess.message?.imageMessage) {
            mediaMessage = messageToProcess.message.imageMessage;
            originalMimetype = mediaMessage.mimetype || 'image/jpeg';
                
            shouldBeAnimated = (originalMimetype === 'image/gif');
            logger.debug(`Imagem detectada: ${originalMimetype}, deve ser animada: ${shouldBeAnimated}`);
        } else if (messageToProcess.message?.videoMessage) {
            mediaMessage = messageToProcess.message.videoMessage;
            originalMimetype = mediaMessage.mimetype || 'video/mp4';
            mediaTypeForDownload = 'video';
        
            shouldBeAnimated = true;
            logger.debug(`Vídeo detectado: ${originalMimetype}, deve ser animada: ${shouldBeAnimated}`);
            
            l
            const videoDuration = mediaMessage.seconds || 0;
            if (videoDuration > 10) {
                await safeSendMessage(sockInstance, jid, { 
                    text: '⚠️ Vídeo longo detectado. Usando versão otimizada.' 
                }, { quoted: messageToProcess });
            }
        } else {
            await safeSendMessage(sockInstance, jid, { 
                text: '⚠️ Nenhuma mídia válida encontrada.' 
            }, { quoted: messageToProcess });
            return;
        }

        
        const stream = await downloadContentFromMessage(mediaMessage, mediaTypeForDownload);
        
        const chunks = [];
        let bufferSize = 0;
        let chunkCount = 0;
        
        for await (const chunk of stream) {
            bufferSize += chunk.length;
            chunkCount++;
            
            if (bufferSize > MAX_MEDIA_BUFFER_SIZE) {
                throw new Error(`Mídia muito grande (${(bufferSize/1024/1024).toFixed(1)}MB > ${MAX_MEDIA_BUFFER_SIZE / 1024 / 1024}MB).`);
            }
            
            chunks.push(chunk);
        }
        
        const buffer = Buffer.concat(chunks);
        logger.debug(`Mídia baixada: ${buffer.length} bytes em ${chunkCount} chunks`);

        if (buffer.length === 0) {
            throw new Error("Buffer vazio após download da mídia.");
        }

        if (!isValidMediaFormat(buffer, originalMimetype)) {
            throw new Error("Formato de mídia corrompido ou inválido.");
        }

        
        let finallyAnimated = false;
        
        if (shouldBeAnimated) {
            finallyAnimated = await isMediaAnimatedAdvanced(buffer, originalMimetype);
            
            
            if (originalMimetype.startsWith('video/')) {
                finallyAnimated = true;
                logger.debug(`Forçando animado para vídeo: ${originalMimetype}`);
            }
            
            
            if (originalMimetype === 'image/gif' && !finallyAnimated) {
                logger.warn(`GIF detectado como não animado - FORÇANDO animado: ${originalMimetype}`);
                finallyAnimated = true;
            }
        }

        logger.debug(`Análise final: ${originalMimetype}, inicial: ${shouldBeAnimated}, final: ${finallyAnimated}`);

        const timestamp = Date.now();
        const randomSuffix = Math.random().toString(36).substring(2, 8);
        const uniqueId = `${timestamp}_${randomSuffix}`;
        
        tempInputPath = path.join(TEMP_FOLDER, `sticker_input_${uniqueId}.${getExtensionFromMimetype(originalMimetype)}`);
        tempOutputPath = path.join(TEMP_FOLDER, `sticker_output_${uniqueId}.webp`);
        frameFullPath = path.join(TEMP_FOLDER, `frame_${uniqueId}.png`);

        logger.debug(`Iniciando conversão WebP: ${originalMimetype} -> WebP (animado: ${finallyAnimated})`);
        
        let webpBuffer = await createOptimizedWebpUltraAdvanced(buffer, originalMimetype, finallyAnimated, {
            tempInputPath,
            tempOutputPath,
            frameFullPath,
            uniqueId,
            startTime
        });

        if (!webpBuffer || webpBuffer.length === 0) {
            throw new Error('Falha na conversão WebP - buffer vazio.');
        }

        logger.debug(`WebP criado: ${webpBuffer.length} bytes, animado: ${finallyAnimated}`);

        
        if (webpBuffer.length > MAX_STICKER_SIZE) {
            logger.info(`Figurinha grande (${(webpBuffer.length/1024).toFixed(1)}KB), aplicando compressão inteligente`);
            
            const compressionStartTime = Date.now();
            webpBuffer = await compressWebpUltraFastAdvanced(webpBuffer, {
                urgency: 'normal',
                targetSize: MAX_STICKER_SIZE * 0.9,
                qualityStep: 5
            });
            
            const compressionTime = Date.now() - compressionStartTime;
            logger.debug(`Compressão concluída em ${compressionTime}ms: ${(webpBuffer.length/1024).toFixed(1)}KB`);
        }

        
        if (webpBuffer.length > MAX_STICKER_SIZE) {
            throw new Error(`Figurinha ainda muito grande após compressão (${(webpBuffer.length / 1024).toFixed(1)}KB > ${MAX_STICKER_SIZE/1024}KB).`);
        }

        
        if (!isValidWebP(webpBuffer)) {
            throw new Error('WebP gerado é inválido.');
        }
            
            
        await sendStickerWithRetry(sockInstance, jid, {
            sticker: webpBuffer,
            pack: STICKER_PACK_NAME,
            author: STICKER_AUTHOR_NAME,
            isAnimated: finallyAnimated
        }, { quoted: messageToProcess });

        const totalTime = Date.now() - startTime;
        const compressionRatio = ((buffer.length - webpBuffer.length) / buffer.length * 100).toFixed(1);
        
        logger.info(`✅ Figurinha criada: ${totalTime}ms, compressão: ${compressionRatio}%, tamanho final: ${(webpBuffer.length/1024).toFixed(1)}KB, animada: ${finallyAnimated}`);
        
        lastActivity = Date.now();

    } catch (error) {
        logger.error(error, `Erro ao criar figurinha otimizada para ${jid}`);
        throw error;    
    } finally {
        
        await Promise.all([
            safelyUnlink(tempInputPath),
            safelyUnlink(tempOutputPath),
            safelyUnlink(frameFullPath)
        ]);
    }
}

    
async function createOptimizedWebp(buffer, originalMimetype, isAnimated, paths) {
const actuallyAnimated = isAnimated && await isMediaAnimatedAdvanced(buffer, originalMimetype);
    
   logger.info(`Processando mídia: ${originalMimetype}, animada: ${actuallyAnimated}, tamanho: ${buffer.length} bytes`);
    
    if (actuallyAnimated) {
        return await createAnimatedWebpAdvanced(buffer, originalMimetype, paths);
    } else {
        return await createStaticWebpAdvanced(buffer, originalMimetype, paths);
    }
}

setInterval(() => {
    processingCache.clear();
}, 5 * 60 * 1000);  

async function createAnimatedWebpAdvanced(buffer, originalMimetype, paths) {
    const { tempInputPath, tempOutputPath, uniqueId } = paths;
    const cacheKey = mediaCache.getKey(buffer, originalMimetype, { animated: true, advanced: true });
    const cached = mediaCache.get(cacheKey);
    
    if (cached) {
        logger.debug(`[${uniqueId}] Cache hit para sticker animado avançado`);
        return cached;
    }

    await fsp.writeFile(tempInputPath, buffer);

    const task = async () => {
        return new Promise((resolve, reject) => {
            
            const timeout = setTimeout(() => {
                ffmpegProcess?.kill('SIGKILL');
                reject(new Error(`Timeout FFmpeg para ${uniqueId}`));
            }, 60000);

            let outputOptions;
            let ffmpegProcess;
            
            if (originalMimetype === 'image/gif') {
                
                outputOptions = [
                    '-c:v', 'libwebp',
                    '-vf', 'scale=512:512:force_original_aspect_ratio=increase,crop=512:512',   
                    '-loop', '0',
                    '-preset', 'picture',
                    '-qscale', '75',
                    '-compression_level', '4',
                    '-method', '4',        
                    '-t', '6',
                    '-r', '15',
                    '-an',
                    '-threads', '2',
                    '-auto-alt-ref', '0'
                ];
            } else {
                
                outputOptions = [
                    '-c:v', 'libwebp',
                    '-vf', 'scale=512:512:force_original_aspect_ratio=increase,crop=512:512',   
                    '-loop', '0',
                    '-preset', 'default',
                    '-qscale', '70',
                    '-compression_level', '3',
                    '-method', '3',        
                    '-t', '6',
                    '-r', '15',
                    '-ss', '0',
                    '-an',
                    '-threads', '2',
                    '-auto-alt-ref', '0'
                ];
            }

            ffmpegProcess = ffmpeg(tempInputPath)
                .outputOptions(outputOptions)
                .on('start', (cmd) => {
                    logger.debug(`[${uniqueId}] FFmpeg animado iniciado: ${originalMimetype}`);
                })
                .on('progress', (progress) => {
                    if (progress.percent && progress.percent > 0) {
                        logger.debug(`[${uniqueId}] Progresso: ${Math.floor(progress.percent)}%`);
                    }
                })
                .on('error', (err) => {
                    clearTimeout(timeout);
                    logger.warn(`[${uniqueId}] Erro FFmpeg: ${err.message}, tentando fallback`);
                    
                    
                    const fallbackOptions = [
                        '-c:v', 'libwebp',
                        '-vf', 'scale=512:512:force_original_aspect_ratio=increase,crop=512:512',
                        '-loop', '0',
                        '-t', '4',         
                        '-r', '10',         
                        '-qscale', '65',   
                        '-preset', 'picture',
                        '-an',
                        '-threads', '1',
                        '-auto-alt-ref', '0'
                    ];

                    const fallbackProcess = ffmpeg(tempInputPath)
                        .outputOptions(fallbackOptions)
                        .on('error', (fallbackErr) => {
                            logger.error(`[${uniqueId}] Fallback falhou: ${fallbackErr.message}`);
                            reject(new Error(`Falha total na conversão: ${fallbackErr.message}`));
                        })
                        .on('end', async () => {
                            try {
                                const result = await fsp.readFile(tempOutputPath);
                                if (result.length === 0) throw new Error('WebP vazio no fallback');
                                logger.debug(`[${uniqueId}] Fallback bem-sucedido: ${result.length} bytes`);
                                resolve(result);
                            } catch (e) {
                                reject(e);
                            }
                        })
                        .save(tempOutputPath);

                        
                    setTimeout(() => {
                        fallbackProcess?.kill('SIGKILL');
                        reject(new Error('Timeout no fallback FFmpeg'));
                    }, 30000);
                })
                .on('end', async () => {
                    clearTimeout(timeout);
                    try {
                        const result = await fsp.readFile(tempOutputPath);
                        if (result.length === 0) {
                            throw new Error('WebP vazio após conversão');
                        }
                        logger.debug(`[${uniqueId}] Conversão concluída: ${result.length} bytes`);
                        resolve(result);
                    } catch (e) {
                        reject(e);
                    }
                })
                .save(tempOutputPath);
        });
    };

    try {
        const result = await ffmpegPool.execute(task);
        
        
        if (result && result.length > 0 && isValidWebP(result)) {
            mediaCache.set(cacheKey, result);
        }
        
        return result;
    } catch (error) {
        logger.error(error, `[${uniqueId}] Erro na criação de WebP animado`);
        throw error;
    }
}


async function createStaticWebpAdvanced(buffer, originalMimetype, paths) {
    const { tempInputPath, frameFullPath, uniqueId } = paths;
    const cacheKey = mediaCache.getKey(buffer, originalMimetype, { animated: false, advanced: true });
    const cached = mediaCache.get(cacheKey);
    
    if (cached) {
        logger.debug(`[${uniqueId}] Cache hit para sticker estático avançado`);
        return cached;
    }

    try {
        let sourceBuffer = buffer;

        
        if (originalMimetype.startsWith('video/')) {
            await fsp.writeFile(tempInputPath, buffer);
            
            logger.debug(`[${uniqueId}] Extraindo frame de vídeo...`);
            
            await new Promise((resolve, reject) => {
                const timeout = setTimeout(() => reject(new Error('Timeout extração de frame')), 15000);
                
                ffmpeg(tempInputPath)
                    .screenshots({
                        timestamps: ['10%'],
                        filename: path.basename(frameFullPath),
                        folder: path.dirname(frameFullPath),
                        size: '512x512'
                    })
                    .on('end', () => {
                        clearTimeout(timeout);
                        logger.debug(`[${uniqueId}] Frame extraído com sucesso`);
                        resolve();
                    })
                    .on('error', (err) => {
                        clearTimeout(timeout);
                        logger.warn(`[${uniqueId}] Erro na extração, tentando timestamp 0: ${err.message}`);
                        
                        ffmpeg(tempInputPath)
                            .screenshots({
                                timestamps: ['0%'],
                                filename: path.basename(frameFullPath),
                                folder: path.dirname(frameFullPath),
                                size: '512x512'
                            })
                            .on('end', resolve)
                            .on('error', reject);
                    });
            });
            
            sourceBuffer = await fsp.readFile(frameFullPath);
            logger.debug(`[${uniqueId}] Frame carregado: ${sourceBuffer.length} bytes`);
        }

        logger.debug(`[${uniqueId}] Convertendo para WebP estático...`);
        
            
        const result = await sharp(sourceBuffer)
            .resize(512, 512, { 
                fit: 'cover',   
                position: 'centre',
                kernel: sharp.kernel.lanczos3
            })
            .webp({ 
                quality: 90,
                effort: 4,      
                lossless: false,
                smartSubsample: true,
                alphaQuality: 95,   
                nearLossless: false
            })
            .toBuffer();

        logger.debug(`[${uniqueId}] WebP estático criado: ${result.length} bytes`);

        if (result && result.length > 0) {
            mediaCache.set(cacheKey, result);
        }
        
        return result;

    } catch (error) {
        logger.error(error, `[${uniqueId}] Erro na criação de WebP estático avançado`);
        throw error;
    }
}

        
async function isMediaAnimatedAdvanced(buffer, mimetype) {
    
    if (mimetype.startsWith('video/')) {
        logger.debug(`Vídeo detectado: ${mimetype} - SEMPRE animado`);
        return true;
    }
    
    
    if (mimetype === 'image/gif') {
        try {
            
            const headerSize = Math.min(16384, buffer.length);  
            const header = buffer.toString('hex', 0, headerSize).toLowerCase();
            
            
            const hasGraphicControlExt = header.includes('21f9');   
            const hasApplicationExt = header.includes('21ff');  
            const hasNetscapeExt = header.includes('4e45545343415045');     
            const hasLoopIndicator = header.includes('210b');   
            
            
            const imageDescriptors = (header.match(/2c/g) || []).length;
            const hasMultipleImages = imageDescriptors > 1;
            
            
            const hasDelayExt = /21f9.{6}[0-9a-f]{4}/.test(header);
            
            
            const hasMultipleDataBlocks = (header.match(/2c[0-9a-f]{8}/g) || []).length > 1;
            
            
            const isAnimated = hasGraphicControlExt || hasApplicationExt || hasNetscapeExt || 
                              hasMultipleImages || hasLoopIndicator || hasDelayExt || hasMultipleDataBlocks;
            
            logger.debug(`GIF análise: ${mimetype}, animado = ${isAnimated}, indicadores: GCE=${hasGraphicControlExt}, App=${hasApplicationExt}, Multi=${hasMultipleImages}, Desc=${imageDescriptors}, Delay=${hasDelayExt}, MultiData=${hasMultipleDataBlocks}`);
            
            
            if (!isAnimated && buffer.length > 100 * 1024) {
                logger.debug(`GIF grande sem indicadores claros - assumindo animado por segurança`);
                return true;
            }
            
            return isAnimated;
        } catch (error) {
            logger.warn(`Erro na análise de GIF: ${error.message}`);
            
            return true;
        }
    }
    
    
    return false;
} 

async function createOptimizedWebpUltraAdvanced(buffer, originalMimetype, isAnimated, paths) {
    const { startTime, uniqueId } = paths;
    
    
    let actuallyAnimated = false;
    
    
    if (originalMimetype.startsWith('video/')) {
        actuallyAnimated = true;
        logger.debug(`[${uniqueId}] Vídeo detectado - FORÇANDO animado: ${originalMimetype}`);
    }
        
    else if (originalMimetype === 'image/gif') {
        actuallyAnimated = await isMediaAnimatedAdvanced(buffer, originalMimetype);
            
        if (!actuallyAnimated) {
            logger.warn(`[${uniqueId}] GIF detectado como não animado - FORÇANDO animado por segurança: ${originalMimetype}`);
            actuallyAnimated = true;
        }
    }
        
    else if (isAnimated) {
        actuallyAnimated = await isMediaAnimatedAdvanced(buffer, originalMimetype);
    }
    
    logger.debug(`[${uniqueId}] Processando mídia: ${originalMimetype}, inicial: ${isAnimated}, final: ${actuallyAnimated}, tamanho: ${buffer.length} bytes`);
    
    if (actuallyAnimated) {
        return await createAnimatedWebpAdvanced(buffer, originalMimetype, paths);
    } else {
        return await createStaticWebpAdvanced(buffer, originalMimetype, paths);
    }
}

    
async function processStickerTaskOptimized(messageToProcess, sockInstance) {
    const jid = messageToProcess.key.remoteJid;
    const startTime = Date.now();
    let mediaMessage;
    let tempInputPath = null;
    let tempOutputPath = null;
    let frameFullPath = null;

    try {
        let mediaTypeForDownload = 'image';
        let originalMimetype = '';
        let shouldBeAnimated = false;

        
        if (messageToProcess.message?.imageMessage) {
            mediaMessage = messageToProcess.message.imageMessage;
            originalMimetype = mediaMessage.mimetype || 'image/jpeg';
            
            shouldBeAnimated = (originalMimetype === 'image/gif');
            logger.debug(`Imagem detectada: ${originalMimetype}, deve verificar animação: ${shouldBeAnimated}`);
        } else if (messageToProcess.message?.videoMessage) {
            mediaMessage = messageToProcess.message.videoMessage;
            originalMimetype = mediaMessage.mimetype || 'video/mp4';
            mediaTypeForDownload = 'video';
            
            shouldBeAnimated = true;
            logger.debug(`Vídeo detectado: ${originalMimetype}, deve ser animada: ${shouldBeAnimated}`);
            
            
            const videoDuration = mediaMessage.seconds || 0;
            if (videoDuration > 10) {
                await safeSendMessage(sockInstance, jid, { 
                    text: '⚠️ Vídeo longo detectado. Usando versão otimizada.' 
                }, { quoted: messageToProcess });
            }
        } else {
            await safeSendMessage(sockInstance, jid, { 
                text: '⚠️ Nenhuma mídia válida encontrada.' 
            }, { quoted: messageToProcess });
            return;
        }

        
        const stream = await downloadContentFromMessage(mediaMessage, mediaTypeForDownload);
        
        const chunks = [];
        let bufferSize = 0;
        let chunkCount = 0;
        
        for await (const chunk of stream) {
            bufferSize += chunk.length;
            chunkCount++;
            
            if (bufferSize > MAX_MEDIA_BUFFER_SIZE) {
                throw new Error(`Mídia muito grande (${(bufferSize/1024/1024).toFixed(1)}MB > ${MAX_MEDIA_BUFFER_SIZE / 1024 / 1024}MB).`);
            }
            
            chunks.push(chunk);
        }
        
        const buffer = Buffer.concat(chunks);
        logger.debug(`Mídia baixada: ${buffer.length} bytes em ${chunkCount} chunks`);

        if (buffer.length === 0) {
            throw new Error("Buffer vazio após download da mídia.");
        }

        if (!isValidMediaFormat(buffer, originalMimetype)) {
            throw new Error("Formato de mídia corrompido ou inválido.");
        }

        
        let finallyAnimated = false;
        
        
        if (originalMimetype.startsWith('video/')) {
            finallyAnimated = true;
            logger.debug(`VÍDEO - Forçando animado: ${originalMimetype}`);
        }
        
        else if (originalMimetype === 'image/gif') {
            finallyAnimated = await isMediaAnimatedAdvanced(buffer, originalMimetype);
            
            if (!finallyAnimated) {
                logger.warn(`GIF detectado como não animado - FORÇANDO animado por segurança: ${originalMimetype}`);
                finallyAnimated = true;
            }
        }
        
        else if (shouldBeAnimated) {
            finallyAnimated = await isMediaAnimatedAdvanced(buffer, originalMimetype);
        }

        logger.debug(`Análise final: ${originalMimetype}, inicial: ${shouldBeAnimated}, final: ${finallyAnimated}`);

        
        const timestamp = Date.now();
        const randomSuffix = Math.random().toString(36).substring(2, 8);
        const uniqueId = `${timestamp}_${randomSuffix}`;
        
        tempInputPath = path.join(TEMP_FOLDER, `sticker_input_${uniqueId}.${getExtensionFromMimetype(originalMimetype)}`);
        tempOutputPath = path.join(TEMP_FOLDER, `sticker_output_${uniqueId}.webp`);
        frameFullPath = path.join(TEMP_FOLDER, `frame_${uniqueId}.png`);

        logger.debug(`Iniciando conversão WebP: ${originalMimetype} -> WebP (animado: ${finallyAnimated})`);
        
        let webpBuffer = await createOptimizedWebpUltraAdvanced(buffer, originalMimetype, finallyAnimated, {
            tempInputPath,
            tempOutputPath,
            frameFullPath,
            uniqueId,
            startTime
        });

        if (!webpBuffer || webpBuffer.length === 0) {
            throw new Error('Falha na conversão WebP - buffer vazio.');
        }

        logger.debug(`WebP criado: ${webpBuffer.length} bytes, animado: ${finallyAnimated}`);

        
        if (webpBuffer.length > MAX_STICKER_SIZE) {
            logger.info(`Figurinha grande (${(webpBuffer.length/1024).toFixed(1)}KB), aplicando compressão inteligente`);
            
            const compressionStartTime = Date.now();
            webpBuffer = await compressWebpUltraFastAdvanced(webpBuffer, {
                urgency: 'normal',
                targetSize: MAX_STICKER_SIZE * 0.9,
                qualityStep: 5
            });
            
            const compressionTime = Date.now() - compressionStartTime;
            logger.debug(`Compressão concluída em ${compressionTime}ms: ${(webpBuffer.length/1024).toFixed(1)}KB`);
        }

        
        if (webpBuffer.length > MAX_STICKER_SIZE) {
            throw new Error(`Figurinha ainda muito grande após compressão (${(webpBuffer.length / 1024).toFixed(1)}KB > ${MAX_STICKER_SIZE/1024}KB).`);
        }

        
        if (!isValidWebP(webpBuffer)) {
            throw new Error('WebP gerado é inválido.');
        }
        
        
        await sendStickerWithRetry(sockInstance, jid, {
            sticker: webpBuffer,
            pack: STICKER_PACK_NAME,
            author: STICKER_AUTHOR_NAME,
            isAnimated: finallyAnimated
        }, { quoted: messageToProcess });

        const totalTime = Date.now() - startTime;
        const compressionRatio = ((buffer.length - webpBuffer.length) / buffer.length * 100).toFixed(1);
        
        logger.info(`✅ Figurinha criada: ${totalTime}ms, compressão: ${compressionRatio}%, tamanho final: ${(webpBuffer.length/1024).toFixed(1)}KB, animada: ${finallyAnimated}`);
        
        lastActivity = Date.now();

    } catch (error) {
        logger.error(error, `Erro ao criar figurinha otimizada para ${jid}`);
        throw error;    
    } finally {
        
        await Promise.all([
            safelyUnlink(tempInputPath),
            safelyUnlink(tempOutputPath),
            safelyUnlink(frameFullPath)
        ]);
    }
}

    
async function compressWebpUltraFastAdvanced(webpBuffer, options = {}) {
    const startTime = Date.now();
    const originalSize = webpBuffer.length;
    const { targetSize = MAX_STICKER_SIZE * 0.9, urgency = 'normal', qualityStep = 5 } = options;

    
    if (originalSize <= targetSize) {
        logger.debug('Buffer já no tamanho alvo, pulando compressão avançada');
        return webpBuffer;
    }

    
    let strategy;
    if (originalSize > 800 * 1024) {
        strategy = 'aggressive';
    } else if (originalSize > 400 * 1024) {
        strategy = 'balanced';
    } else {
        strategy = 'light';
    }

    
    const urgencyMultipliers = {
        urgent: 0.7,
        normal: 0.85,
        careful: 0.95
    };
    
    const baseQuality = urgencyMultipliers[urgency] || 0.85;

    try {
        
        let currentBuffer = webpBuffer;
        let currentQuality = Math.floor(baseQuality * 100);
        let attempts = 0;
        const maxAttempts = 5;

        while (currentBuffer.length > targetSize && attempts < maxAttempts && currentQuality > 30) {
            logger.debug(`Tentativa ${attempts + 1}: qualidade ${currentQuality}, tamanho: ${(currentBuffer.length/1024).toFixed(1)}KB`);
            
            currentBuffer = await sharp(webpBuffer)
                .webp({ 
                    quality: currentQuality,
                    effort: strategy === 'aggressive' ? 1 : 2,
                    lossless: false,
                    smartSubsample: true,
                    reductionEffort: strategy === 'aggressive' ? 6 : 4
                })
                .toBuffer();
            
            currentQuality -= qualityStep;
            attempts++;
        }

        const processingTime = Date.now() - startTime;
        const finalSize = currentBuffer.length;
        const compressionRatio = ((originalSize - finalSize) / originalSize * 100).toFixed(1);
        
        logger.debug(`Compressão avançada: ${processingTime}ms, ${attempts} tentativas, ${compressionRatio}% redução`);
        
        return currentBuffer;

    } catch (error) {
        logger.error(error, 'Erro na compressão avançada, usando fallback');
        
            
        try {
            return await sharp(webpBuffer)
                .webp({ quality: 50, effort: 0 })
                .toBuffer();
        } catch (fallbackError) {
            logger.warn('Fallback de compressão falhou, retornando original');
            return webpBuffer;
        }
    }
}

    
async function compressBatch(buffers, options = {}) {
    const promises = buffers.map(buffer => compressWebpUltraFast(buffer, options));
    return await Promise.all(promises);
}

    
async function compressAdaptive(webpBuffer, systemLoad = 'normal') {
    const loadConfigs = {
        low: { quality: 80, effort: 3 },
        normal: { quality: 70, effort: 2 },
        high: { quality: 60, effort: 1 },
        critical: { quality: 50, effort: 0 }
    };

    const config = loadConfigs[systemLoad] || loadConfigs.normal;
    return await compressWebpUltraFastAdvanced(webpBuffer, options);
}
        
function needsCompression(buffer, threshold = MAX_STICKER_SIZE) {
    return buffer.length > threshold;
}

        
function estimateCompressionTime(bufferSize) {
    
    const baseTime = 200;     
    const sizeMultiplier = bufferSize / (100 * 1024);   
    return Math.min(baseTime + (sizeMultiplier * 50), 5000);    
}

        
function getCompressionStats() {
    return {
        pool: compressionPool.getStats(),
        cache: {
            size: compressionCache.cache.size,
            maxSize: compressionCache.maxSize
        },
        performance: {
            avgTime: compressionPool.stats.avgProcessingTime.toFixed(0) + 'ms',
            avgRatio: compressionPool.stats.avgCompressionRatio.toFixed(1) + '%',
            totalSaved: compressionPool.stats.totalSavedMB + 'MB'
        }
    };
}

        
function cleanupCompression() {
        
    const now = Date.now();
    const maxAge = 10 * 60 * 1000;  
    
    for (const [key, item] of compressionCache.cache.entries()) {
        if (now - item.lastUsed > maxAge) {
            compressionCache.cache.delete(key);
        }
    }
    
    logger.debug('Cache de compressão limpo');
}
function isValidMediaFormat(buffer, mimetype) {
    if (!buffer || buffer.length < 10) return false;
    
    const header = buffer.toString('hex', 0, 8).toLowerCase();
    
        
    const validHeaders = {
        'image/jpeg': ['ffd8ff'],
        'image/png': ['89504e47'],
        'image/gif': ['474946'],
        'image/webp': ['52494646'],
        'video/mp4': ['00000018667479', '00000020667479', '66747970']
    };
    
    const expectedHeaders = validHeaders[mimetype];
    if (!expectedHeaders) return true;  
    
    return expectedHeaders.some(expected => header.startsWith(expected));
}

function getExtensionFromMimetype(mimetype) {
    const extensions = {
        'image/jpeg': 'jpg',
        'image/png': 'png', 
        'image/gif': 'gif',
        'image/webp': 'webp',
        'video/mp4': 'mp4',
        'video/mpeg': 'mpg'
    };
    return extensions[mimetype] || 'tmp';
}

function isAdmin(msg, isGroup) {
    const senderJid = isGroup ? msg.key.participant : msg.key.remoteJid;
    return senderJid === ADMIN_NUMBER;
}

function isValidWebP(buffer) {
    if (!buffer || buffer.length < 12) return false;
    const header = buffer.toString('ascii', 0, 4);
    const format = buffer.toString('ascii', 8, 12);
    return header === 'RIFF' && format === 'WEBP';
}
async function sendStickerWithRetry(sockInstance, jid, stickerData, options, maxRetries = 2) {
    let lastError;
    
    for (let attempt = 1; attempt <= maxRetries; attempt++) {
        try {
            await safeSendMessage(sockInstance, jid, stickerData, options);
            return;     
        } catch (error) {
            lastError = error;
            logger.warn(`Tentativa ${attempt}/${maxRetries} falhou ao enviar figurinha para ${jid}: ${error.message}`);
            
            if (attempt < maxRetries) {
                const delay = 1000 * attempt;   
                await new Promise(resolve => setTimeout(resolve, delay));
            }
        }
    }
    
    throw lastError;    
}
    
async function integratedCompress(webpBuffer, urgency = 'normal') {
    
    if (!needsCompression(webpBuffer)) {
        return webpBuffer;
    }

    
    const estimatedTime = estimateCompressionTime(webpBuffer.length);
    
    if (urgency === 'urgent' && estimatedTime > 2000) {
        
        return await compressAdaptive(webpBuffer, 'critical');
    }

    
    return await compressWebpUltraFastAdvanced(webpBuffer);
}

async function startBot() {
    if (isBotRunning) {
        logger.warn('Bot já está rodando');
        return null;
    }
    
    isBotRunning = true;
    isReconnecting = false;

    await initializeAppFolders();
    await loadAvailableAudios();

    if (healthCheckInterval) clearInterval(healthCheckInterval);
    if (memoryCleanupInterval) clearInterval(memoryCleanupInterval);
    
    healthCheckInterval = setInterval(performHealthCheck, HEALTH_CHECK_INTERVAL);
    memoryCleanupInterval = setInterval(performMemoryCleanup, MEMORY_CLEANUP_INTERVAL);

    if (process.env.NORTHFLANK === "true") {
        const cleanupInterval = setInterval(async () => {
            try {
                await cleanupTempFiles();
            } catch (err) {
                logger.warn(err, 'Erro na limpeza automática');
            }
        }, 30 * 60 * 1000);
        
        process.on('exit', () => clearInterval(cleanupInterval));
    }

    logger.info('🚀 Iniciando bot otimizado...');

    try {
        const { state, saveCreds } = await useMultiFileAuthState(AUTH_FOLDER);

        sock = makeWASocket({
            auth: state,
            logger: pino({ level: 'silent' }),
            printQRInTerminal: false,
            browser: ["BozBot", "Chrome", "2.0"],
            connectTimeoutMs: 60000,
            keepAliveIntervalMs: 30000,
            syncFullHistory: false,
            markOnlineOnConnect: true,
            defaultQueryTimeoutMs: 60000,
            options: {
                chats: {
                    deleteObsoleteStaleChats: true,
                },
                getMessage: async (key) => {
                    return { conversation: "Bot message" };
                }
            }
        });

        sock.ev.on('creds.update', saveCreds);

        sock.ev.on('connection.update', async ({ connection, lastDisconnect, qr }) => {
            const now = Date.now();
            lastActivity = now;

            if (qr) {
                if (now - lastQrTime < QR_MIN_INTERVAL) {
                    logger.debug('QR code ignorado (intervalo mínimo)');
                    return;
                }
                lastQrTime = now;
                logger.info('📲 QR Code gerado');
                
                qrcode.generate(qr, { small: true });
                
                try {
                    const qrUrl = await Promise.race([
                        generateQRCodeURL(qr),
                        new Promise((_, reject) => 
                            setTimeout(() => reject(new Error('Timeout QR')), 5000)
                        )
                    ]);
                    
                    if (qrUrl && ADMIN_NUMBER && sock?.user) {
                        try {
                            await safeSendMessage(sock, ADMIN_NUMBER, { 
                                text: `📲 QR Code: ${qrUrl}\n\nExpira em 60s.` 
                            });
                        } catch (e) {
                            logger.debug('Não foi possível enviar QR para admin');
                        }
                    }
                } catch (error) {
                    logger.warn('Erro ao processar QR Code URL');
                }
                return;
            }

            if (connection === 'open') {
                logger.info('✅ Conectado ao WhatsApp!');
                logger.info(`📱 Bot ID: ${sock.user.id}`);
                connectionRetries = 0;
                
                if (pingInterval) clearInterval(pingInterval);
                pingInterval = setInterval(() => {
                    if (sock?.ws?.isOpen) {
                        sock.sendPresenceUpdate('available').catch(() => {
                            logger.debug('Falha no ping presence');
                        });
                    }
                }, 45000);
            }

            if (connection === 'close') {
                const statusCode = lastDisconnect?.error?.output?.statusCode;
                const reason = DisconnectReason[statusCode] || 'Desconhecida';
                logger.warn(`🔌 Conexão fechada: ${reason} (${statusCode})`);

                if (pingInterval) {
                    clearInterval(pingInterval);
                    pingInterval = null;
                }

                if (statusCode === DisconnectReason.loggedOut) {
                    logger.error('❌ Desconectado! Limpando auth...');
                    try {
                        await fsExtra.emptyDir(AUTH_FOLDER);
                        logger.info('Auth limpa. Reiniciando em 15s...');
                    } catch (e) {
                        logger.error(e, 'Falha ao limpar auth');
                    }
                    setTimeout(() => process.exit(1), 15000);
                    return;
                }

                const shouldReconnect = [
                    DisconnectReason.connectionClosed,
                    DisconnectReason.connectionLost,
                    DisconnectReason.timedOut,
                    DisconnectReason.restartRequired,
                    DisconnectReason.badSession
                ].includes(statusCode);

                if (shouldReconnect && connectionRetries < MAX_CONNECTION_RETRIES) {
                    connectionRetries++;
                    const delay = Math.min(
                        RECONNECTION_DELAY_BASE * Math.pow(1.5, connectionRetries - 1),
                        MAX_RECONNECTION_DELAY
                    );
                    
                    logger.info(`⏳ Reconectando (${connectionRetries}/${MAX_CONNECTION_RETRIES}) em ${delay/1000}s...`);
                    
                    setTimeout(() => { 
                        isBotRunning = false; 
                        startBot(); 
                    }, delay);
                } else if (connectionRetries >= MAX_CONNECTION_RETRIES) {
                    logger.error('❌ Máximo de tentativas atingido');
                    if (process.env.NORTHFLANK === "true") {
                        logger.info('Northflank: Saindo para reinício...');
                        process.exit(1);
                    }
                } else {
                    logger.error(`❌ Erro não recuperável: ${statusCode}`);
                    if (process.env.NORTHFLANK === "true") {
                        setTimeout(() => process.exit(1), 10000);
                    }
                }
                
                isBotRunning = false;
            }
        });

        
        sock.ev.on('messages.upsert', async ({ messages }) => {
            const msg = messages[0];

            if (!msg.message || 
                msg.key.fromMe || 
                msg.message.protocolMessage || 
                msg.message.reactionMessage || 
                isJidBroadcast(msg.key.remoteJid)) {
                return;
            }

            lastActivity = Date.now();

            const userJid = msg.key.remoteJid;
            const isGroup = userJid.endsWith('@g.us');
            const senderName = msg.pushName || 'Usuário';
            const messageType = Object.keys(msg.message)[0];
            const text = (
                msg.message.conversation || 
                msg.message.extendedTextMessage?.text || 
                msg.message.imageMessage?.caption || 
                msg.message.videoMessage?.caption || 
                ""
            ).trim();
            const command = text.toLowerCase().split(' ')[0];
            const args = text.split(' ').slice(1);
            const fullArgs = args.join(' ');
            
            if (command.startsWith('/') || text.length > 0) {
                logger.info(`[${userJid.split('@')[0]}] ${command || messageType}`);
            }
            
            try {
                
                if (WAITING_FOR_COOKIES.has(userJid)) {
                    WAITING_FOR_COOKIES.delete(userJid);
                    try {
                        let cookieContent;
                        if (text) {
                            cookieContent = text;
                        } else if (msg.message?.documentMessage) {
                            const stream = await downloadContentFromMessage(msg.message.documentMessage, 'document');
                            let buffer = Buffer.from([]);
                            for await (const chunk of stream) buffer = Buffer.concat([buffer, chunk]);
                            cookieContent = buffer.toString('utf-8');
                        } else {
                            throw new Error('Envie o arquivo cookies.txt ou cole o conteúdo.');
                        }

                        if (cookieContent.length < 50 || !cookieContent.includes('Netscape')) {
                             throw new Error('Conteúdo dos cookies inválido.');
                        }
                        
                        await fsp.writeFile(YOUTUBE_COOKIES_FILE, cookieContent);
                        await safeSendMessage(sock, userJid, { 
                            text: '✅ Cookies salvos!' 
                        }, { quoted: msg });
                    } catch (error) {
                        await safeSendMessage(sock, userJid, { 
                            text: `❌ Erro: ${error.message}` 
                        }, { quoted: msg });
                    }
                    return;
                }

                
                if (GEMINI_CHAT_SESSIONS.has(userJid) && !command.startsWith('/')) {
                    const session = GEMINI_CHAT_SESSIONS.get(userJid);
                    if (Date.now() > session.expiry) {
                        GEMINI_CHAT_SESSIONS.delete(userJid);
                        await safeSendMessage(sock, userJid, { 
                            text: "🤖 Sessão expirada." 
                        });
                    } else {
                        await sock.sendPresenceUpdate('composing', userJid);
                        try {
                            const model = genAI.getGenerativeModel({ model: "gemini-1.5-flash" });
                            const chat = model.startChat({ history: session.history });
                            const result = await chat.sendMessage(`(${senderName}): ${text}`);
                            const responseText = result.response.text();

                            session.history.push({ 
                                role: "user", 
                                parts: [{ text: `(${senderName}): ${text}` }] 
                            });
                            session.history.push({ 
                                role: "model", 
                                parts: [{ text: responseText }] 
                            });
                            session.expiry = Date.now() + SESSION_TIMEOUT;

                            await safeSendMessage(sock, userJid, { 
                                text: responseText 
                            }, { quoted: msg });
                        } catch (error) {
                            logger.error(error, "Erro no chat Gemini");
                            await safeSendMessage(sock, userJid, { 
                                text: "Ops, tive um problema. Tente de novo." 
                            }, { quoted: msg });
                        } finally {
                            await sock.sendPresenceUpdate('paused', userJid);
                        }
                    }
                    return;
                }

                
                switch (command) {
                    case '/menu': {
                        const menuText = `
ミ★★★★★ 𝘉𝘶𝘯𝘯𝘺 ★★★★★彡
📌 *COMANDOS PRINCIPAIS*:
├─ *🎭 Figurinhas*
│  ├─ /sticker - Cria figurinha de imagem/vídeo/GIF
│  ├─ /figauto - Ativa/desativa figurinhas automáticas
│  └─ /converter - Converte vídeo para MP3
│
├─ *🎵 Mídia*
│  ├─ /bmp3 [link] - Baixa áudio do YouTube
│  ├─ /bmp4 [link] - Baixa vídeo do YouTube
│  └─ /tiktok [link] - Baixa vídeo do TikTok
│
├─ *🔍 Buscas & IA*
│  ├─ /buscar [termo] - Busca vídeos no YouTube
│  ├─ /gemini [pergunta] - Consulte o Gemini AI
│  └─ /gen [on/off] - Ativa/desativa chat contínuo (só grupos)
│
├─ *⚙️ Utilitários*
│  ├─ /status - Mostra status do bot
│  ├─ /menu - Mostra esta mensagem
│  └─ /cookie - Define os cookies do YouTube para yt-dlp
│
╰─ *👑 ADMIN*
   ├─ /fotobot - Altera foto de perfil do bot
   └─ /fotomenu - Altera imagem de fundo do menu

🔹 *Dica*: Responda a mensagens com os comandos para interagir!
ミ★★★★★ 𝘉𝘶𝘯𝘯𝘺 ★★★★★彡`;

                        
                        if (availableAudios.length > 0) {
                            try {
                                const randomAudio = availableAudios[Math.floor(Math.random() * availableAudios.length)];
                                await safeSendMessage(sock, userJid, { 
                                    audio: { url: randomAudio }, 
                                    mimetype: 'audio/mpeg', 
                                    ptt: true 
                                }, { quoted: msg });
                                await new Promise(resolve => setTimeout(resolve, 500));
                            } catch (audioError) {
                                logger.warn('Erro ao enviar áudio do menu');
                            }
                        }

                        const menuContent = fs.existsSync(MENU_IMAGE_PATH)
                            ? { image: { url: MENU_IMAGE_PATH }, caption: menuText }
                            : { text: menuText };
                        await safeSendMessage(sock, userJid, menuContent, { quoted: msg });
                        break;
                    }

                    case '/status': {
    const memoryUsage = process.memoryUsage();
    const uptime = process.uptime();
    const hours = Math.floor(uptime / 3600);
    const minutes = Math.floor((uptime % 3600) / 60);
    const seconds = Math.floor(uptime % 60);
    
        
    const stickerStats = enhancedOptimizedStickerQueue?.getStats() || { queue: 0, processing: 0, processed: 0, rejected: 0 };
    const compressionStats = getCompressionStats();
    const rateLimitStatus = rateLimiter?.isThrottled ? 'Ativo' : 'Normal';
    const lastActivitySeconds = Math.floor((Date.now() - lastActivity) / 1000);
    
    
    let connectionStatus = '🔴 Desconectado';
    if (sock?.user) {
        if (sock.ws?.readyState === 1) {
            connectionStatus = '🟢 Conectado';
        } else if (sock.ws?.readyState === 0) {
            connectionStatus = '🟡 Conectando...';
        } else {
            connectionStatus = '🟠 Instável';
        }
    }
    
    
    const nodeVersion = process.version;
    const platform = process.platform;
    const arch = process.arch;
    
    
    const memoryPercentage = ((memoryUsage.rss / MAX_MEMORY_USAGE) * 100).toFixed(1);
    const heapUsedMB = (memoryUsage.heapUsed / 1024 / 1024).toFixed(2);
    const rssMB = (memoryUsage.rss / 1024 / 1024).toFixed(2);
    const externalMB = (memoryUsage.external / 1024 / 1024).toFixed(2);
    
    
    const totalSessions = USER_SESSIONS.size + GEMINI_CHAT_SESSIONS.size;
    const geminiSessions = GEMINI_CHAT_SESSIONS.size;
    const userSessions = USER_SESSIONS.size;
    const autoStickerUsers = autoStickerMode.size;
    
        
    const rateLimitWaitTime = rateLimiter?.getWaitTime() || 0;
    const rateLimitMessages = rateLimiter?.messageHistory?.length || 0;
    
    
    const hasGemini = genAI ? '✅' : '❌';
    const hasYouTubeAPI = YOUTUBE_API_KEY !== 'AIzaSyDNoMs5QJ5Ehkth8XijgTJtYrW1E5UvQ7U' ? '✅' : '⚠️ Padrão';
    const hasCookies = fs.existsSync(YOUTUBE_COOKIES_FILE) ? '✅' : '❌';
    
    const statusMessage = `
🤖 *BOT STATUS REPORT*
━━━━━━━━━━━━━━━━━━━━━━━

🔌 *CONEXÃO*
├─ Status: ${connectionStatus}
├─ Bot ID: ${sock?.user?.id?.split('@')[0] || 'N/A'}
├─ Reconexões: ${connectionRetries}/${MAX_CONNECTION_RETRIES}
└─ Última atividade: ${lastActivitySeconds}s atrás

⏱️ *TEMPO DE EXECUÇÃO*
├─ Uptime: ${hours}h ${minutes}m ${seconds}s
├─ Iniciado: ${new Date(Date.now() - uptime * 1000).toLocaleString('pt-BR')}
└─ Timezone: ${process.env.TZ || 'Sistema'}

💾 *MEMÓRIA*
├─ RSS: ${rssMB}MB (${memoryPercentage}%)
├─ Heap: ${heapUsedMB}MB
├─ External: ${externalMB}MB
└─ Limite: ${(MAX_MEMORY_USAGE / 1024 / 1024).toFixed(0)}MB

👥 *SESSÕES ATIVAS*
├─ Total: ${totalSessions}
├─ Usuários: ${userSessions}
├─ Gemini Chat: ${geminiSessions}
└─ Auto Sticker: ${autoStickerUsers}

🎭 *FILA DE FIGURINHAS*
├─ Aguardando: ${stickerStats.queue}
├─ Processando: ${stickerStats.processing}/${stickerStats.maxConcurrent || 'N/A'}
├─ Concluídas: ${stickerStats.processed || 0}
└─ Rejeitadas: ${stickerStats.rejected || 0}

🚦 *RATE LIMITING*
├─ Status: ${rateLimitStatus}
├─ Mensagens/min: ${rateLimitMessages}/${MAX_MESSAGES_PER_WINDOW}
└─ Tempo espera: ${rateLimitWaitTime}ms

📊 *PERFORMANCE*
├─ FFmpeg Pool: ${compressionStats.ffmpeg?.active || 0}/${compressionStats.ffmpeg?.queued || 0}
├─ Cache Hit: ${(compressionStats.cache?.size || 0)}
└─ Compressão: ${compressionStats.performance?.avgRatio || '0%'}

🔧 *RECURSOS DISPONÍVEIS*
├─ Gemini AI: ${hasGemini}
├─ YouTube API: ${hasYouTubeAPI}
├─ YT Cookies: ${hasCookies}
└─ Northflank: ${process.env.NORTHFLANK === "true" ? '✅' : '❌'}

💻 *SISTEMA*
├─ Node.js: ${nodeVersion}
├─ Plataforma: ${platform} ${arch}
├─ PID: ${process.pid}
└─ Ambiente: ${process.env.NODE_ENV || 'development'}

━━━━━━━━━━━━━━━━━━━━━━━
🕒 *Relatório gerado em:* ${new Date().toLocaleString('pt-BR')}`;

    await safeSendMessage(sock, userJid, { text: statusMessage }, { quoted: msg });
    break;
}

                    case '/figauto': {
                        if (autoStickerMode.has(userJid)) {
                            autoStickerMode.delete(userJid);
                            await safeSendMessage(sock, userJid, { 
                                text: `Figurinhas automáticas desativadas ❌` 
                            }, { quoted: msg });
                        } else {
                            autoStickerMode.add(userJid);
                            await safeSendMessage(sock, userJid, { 
                                text: `Figurinhas automáticas ativadas ✅` 
                            }, { quoted: msg });
                        }
                        break;
                    }

                    case '/cookie': {
        
    const senderJid = isGroup ? msg.key.participant : userJid;
    if (senderJid !== ADMIN_NUMBER) {
        await safeSendMessage(sock, userJid, { 
            text: '🚫 *Acesso Negado*\n\nEste comando é restrito ao administrador do bot.\n\n_Apenas o dono pode configurar cookies do YouTube._' 
        }, { quoted: msg });
        return;
    }
    
    
    WAITING_FOR_COOKIES.add(userJid);
    
    const cookieInstructions = `
🍪 *CONFIGURAÇÃO DE COOKIES*
━━━━━━━━━━━━━━━━━━━━━━━

📋 *Como obter os cookies:*

1️⃣ *Navegador (Chrome/Firefox)*:
   • Acesse youtube.com e faça login
   • Pressione F12 → Aba "Application/Storage"
   • Clique em "Cookies" → "https://youtube.com"
   • Clique direito → "Export" ou copie manualmente

2️⃣ *Extensão (Recomendado)*:
   • Instale "Get cookies.txt LOCALLY"
   • Acesse YouTube logado
   • Clique na extensão → Download

⚠️ *Importante*:
   • Não compartilhe seus cookies
   • Eles expiram periodicamente
   • Necessário para downloads sem restrições

💡 *Status atual*:
   • Cookies: ${fs.existsSync(YOUTUBE_COOKIES_FILE) ? '✅ Configurados' : '❌ Não configurados'}
   • Arquivo: \`${YOUTUBE_COOKIES_FILE}\`

🔄 *Aguardando arquivo ou conteúdo...*`;
    
    await safeSendMessage(sock, userJid, { 
        text: cookieInstructions 
    }, { quoted: msg });
    break;
}
                    case '/bmp3': {
                        if (!fullArgs) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Uso: /bmp3 [link do YouTube]' 
                            }, { quoted: msg });
                            return;
                        }
                        const correctedUrl = normalizeYouTubeUrl(fullArgs);
                        if (!correctedUrl) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ URL inválida.' 
                            }, { quoted: msg });
                            return;
                        }
                        await safeSendMessage(sock, userJid, { 
                            text: '⏳ Processando áudio...' 
                        }, { quoted: msg });
                        let outputPath;
                        try {
                            outputPath = await downloadYouTubeAudio(correctedUrl);
                            await safeSendMessage(sock, userJid, { 
                                audio: { url: outputPath }, 
                                mimetype: 'audio/mpeg' 
                            }, { quoted: msg });
                        } finally {
                            await safelyUnlink(outputPath);
                        }
                        break;
                    }

                    case '/bmp4': {
                        if (!fullArgs) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Uso: /bmp4 [link do YouTube]' 
                            }, { quoted: msg });
                            return;
                        }
                        const correctedUrl = normalizeYouTubeUrl(fullArgs);
                        if (!correctedUrl) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ URL inválida.' 
                            }, { quoted: msg });
                            return;
                        }
                        await safeSendMessage(sock, userJid, { 
                            text: '⏳ Baixando vídeo...' 
                        }, { quoted: msg });
                        let outputPath, compressedPath;
                        try {
                            outputPath = await downloadYouTubeVideo(correctedUrl);
                            let finalPath = outputPath;
                            if ((await fsp.stat(outputPath)).size > 16 * 1024 * 1024) { 
                                await safeSendMessage(sock, userJid, { 
                                    text: '⏳ Comprimindo...' 
                                }, { quoted: msg });
                                compressedPath = await compressVideo(outputPath);
                                finalPath = compressedPath;
                            }
                            await safeSendMessage(sock, userJid, { 
                                video: { url: finalPath }, 
                                caption: '✅ Vídeo baixado!' 
                            }, { quoted: msg });
                        } finally {
                            await safelyUnlink(outputPath);
                            await safelyUnlink(compressedPath);
                        }
                        break;
                    }

                    case '/tiktok': {
                         if (!fullArgs) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Uso: /tiktok [link do TikTok]' 
                            }, { quoted: msg });
                            return;
                        }
                        await safeSendMessage(sock, userJid, { 
                            text: '⏳ Baixando TikTok...' 
                        }, { quoted: msg });
                        let outputPath;
                        try {
                            outputPath = await downloadTikTokVideo(fullArgs);
                            await safeSendMessage(sock, userJid, { 
                                video: { url: outputPath }, 
                                caption: '✅ TikTok baixado!' 
                            }, { quoted: msg });
                        } finally {
                            await safelyUnlink(outputPath);
                        }
                        break;
                    }

                    case '/converter': {
                        const quotedMsgContent = msg.message?.extendedTextMessage?.contextInfo?.quotedMessage;
                        const videoToConvert = quotedMsgContent?.videoMessage || msg.message?.videoMessage;
                        if (!videoToConvert) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Responda a um vídeo com /converter.' 
                            }, { quoted: msg });
                            return;
                        }
                        await safeSendMessage(sock, userJid, { 
                            text: '⏳ Convertendo para MP3...' 
                        }, { quoted: msg });
                        let tempVideoPath, mp3Path;
                        try {
                            const stream = await downloadContentFromMessage(videoToConvert, 'video');
                            const chunks = [];
                            for await (const chunk of stream) chunks.push(chunk);
                            tempVideoPath = path.join(TEMP_FOLDER, `video_conv_${Date.now()}.mp4`);
                            await fsp.writeFile(tempVideoPath, Buffer.concat(chunks));
                            mp3Path = await convertVideoToMp3(tempVideoPath);
                            await safeSendMessage(sock, userJid, { 
                                audio: { url: mp3Path }, 
                                mimetype: 'audio/mpeg' 
                            }, { quoted: msg });
                        } finally {
                            await safelyUnlink(tempVideoPath);
                            await safelyUnlink(mp3Path);
                        }
                        break;
                    }

                    case '/gen': {
                        if (!isGroup) {
                            await safeSendMessage(sock, userJid, { 
                                text: "⚠️ Comando apenas para grupos." 
                            }, { quoted: msg });
                            return;
                        }
                        if (!genAI) {
                            await safeSendMessage(sock, userJid, { 
                                text: "⚠️ Gemini não configurado." 
                            }, { quoted: msg });
                            return;
                        }
                        if (fullArgs.toLowerCase() === 'on') {
                            GEMINI_CHAT_SESSIONS.set(userJid, { 
                                history: [], 
                                expiry: Date.now() + SESSION_TIMEOUT 
                            });
                            await safeSendMessage(sock, userJid, { 
                                text: "🤖 Gemini ativado! Podem conversar." 
                            });
                        } else if (fullArgs.toLowerCase() === 'off') {
                            GEMINI_CHAT_SESSIONS.delete(userJid);
                            await safeSendMessage(sock, userJid, { 
                                text: "🤖 Gemini desativado!" 
                            });
                        } else {
                            await safeSendMessage(sock, userJid, { 
                                text: "Uso: /gen on ou /gen off" 
                            }, { quoted: msg });
                        }
                        break;
                    }

                    case '/gemini':
                    case '/pesquisar': {
                        if (!fullArgs || !genAI) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Uso: /gemini [pergunta]' 
                            }, { quoted: msg });
                            return;
                        }
                        await sock.sendPresenceUpdate('composing', userJid);
                        try {
                            const responseText = await searchWithGemini(fullArgs);
                            await safeSendMessage(sock, userJid, { 
                                text: `💡 *Gemini:*\n\n${responseText}` 
                            }, { quoted: msg });
                        } finally {
                            await sock.sendPresenceUpdate('paused', userJid);
                        }
                        break;
                    }

                    case '/buscar': {
                        if (!fullArgs) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Uso: /buscar [termo]' 
                            }, { quoted: msg });
                            return;
                        }
                        await safeSendMessage(sock, userJid, { 
                            text: `🔍 Buscando "${fullArgs}"...` 
                        }, { quoted: msg });
                        const results = await searchYouTube(fullArgs);
                        if (!results || results.length === 0) {
                            await safeSendMessage(sock, userJid, { 
                                text: '❌ Nenhum resultado.' 
                            }, { quoted: msg });
                            return;
                        }
                        USER_SESSIONS.set(userJid, { 
                            lastSearchResults: results, 
                            searchIndex: 0, 
                            expiry: Date.now() + SESSION_TIMEOUT, 
                            waitingForCommand: true 
                        });
                        await sendSearchResult(sock, userJid, msg, results[0], 1, results.length);
                        break;
                    }

                    case 'próximo':
                    case 'proximo': {
                        const session = USER_SESSIONS.get(userJid);
                        if (session?.waitingForCommand && session.lastSearchResults?.length > 0) {
                            const nextIndex = (session.searchIndex + 1) % session.lastSearchResults.length;
                            session.searchIndex = nextIndex;
                            await sendSearchResult(sock, userJid, msg, session.lastSearchResults[nextIndex], nextIndex + 1, session.lastSearchResults.length);
                        }
                        break;
                    }

                    case 'baixar': {
                        const session = USER_SESSIONS.get(userJid);
                        if (session?.waitingForCommand && session.lastSearchResults?.length > 0) {
                            const currentItem = session.lastSearchResults[session.searchIndex];
                            session.selectedItem = currentItem;
                            session.waitingForCommand = false;
                            session.waitingForDownloadChoice = true;
                            session.downloadChoiceExpiry = Date.now() + 120000;
                            const choiceText = `📥 Escolha o formato:\n_"${currentItem.title}"_\n\n1️⃣ - Vídeo (MP4)\n2️⃣ - Áudio (MP3)\n\nDigite o número.`;
                            await safeSendMessage(sock, userJid, { text: choiceText }, { quoted: msg });
                        }
                        break;
                    }

                    case '1':
                    case '2': {
                        const session = USER_SESSIONS.get(userJid);
                        if (session?.waitingForDownloadChoice && session.selectedItem) {
                             if (session.downloadChoiceExpiry && Date.now() > session.downloadChoiceExpiry) {
                                USER_SESSIONS.delete(userJid);
                                await safeSendMessage(sock, userJid, { 
                                    text: '⏳ Tempo expirado. Use /buscar novamente.' 
                                }, { quoted: msg });
                                return;
                            }
                            const itemToDownload = session.selectedItem;
                            session.waitingForDownloadChoice = false;
                            await safeSendMessage(sock, userJid, { 
                                text: `⏳ Preparando "${itemToDownload.title}"...` 
                            }, { quoted: msg });
                            let outputPath, compressedPath;
                            try {
                                if (command === '1') { 
                                    outputPath = await downloadYouTubeVideo(normalizeYouTubeUrl(itemToDownload.url));
                                    let finalPath = outputPath;
                                    if ((await fsp.stat(outputPath)).size > 16 * 1024 * 1024) {
                                        await safeSendMessage(sock, userJid, { 
                                            text: '⏳ Comprimindo...' 
                                        }, { quoted: msg });
                                        compressedPath = await compressVideo(outputPath);
                                        finalPath = compressedPath;
                                    }
                                    await safeSendMessage(sock, userJid, { 
                                        video: { url: finalPath }, 
                                        caption: `✅ ${itemToDownload.title}` 
                                    }, { quoted: msg });
                                } else { 
                                    outputPath = await downloadYouTubeAudio(normalizeYouTubeUrl(itemToDownload.url));
                                    await safeSendMessage(sock, userJid, { 
                                        audio: { url: outputPath }, 
                                        mimetype: 'audio/mpeg' 
                                    }, { quoted: msg });
                                }
                            } finally {
                                await safelyUnlink(outputPath);
                                await safelyUnlink(compressedPath);
                                USER_SESSIONS.delete(userJid);
                            }
                        }
                        break;
                    }

                    case '/sticker': {
                        const quotedMsgContent = msg.message?.extendedTextMessage?.contextInfo?.quotedMessage;
                        const messageToProcess = (quotedMsgContent?.imageMessage || quotedMsgContent?.videoMessage) 
                            ? { key: msg.key, message: quotedMsgContent } 
                            : msg;
                        
                        await createOptimizedStickerEnhanced(messageToProcess, sock);
                        break;
                    }

                    case '/fotobot': {
                        const senderJid = isGroup ? msg.key.participant : userJid;
                        if (senderJid !== ADMIN_NUMBER) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Acesso restrito ao admin.' 
                            }, { quoted: msg });
                            return;
                        }
                        const imgContent = msg.message?.extendedTextMessage?.contextInfo?.quotedMessage?.imageMessage || msg.message?.imageMessage;
                        if (!imgContent) {
                             await safeSendMessage(sock, userJid, { 
                                 text: '⚠️ Responda a uma imagem.' 
                             }, { quoted: msg });
                             return;
                        }
                        let tempPath;
                        try {
                            const stream = await downloadContentFromMessage(imgContent, 'image');
                            const chunks = [];
                            for await (const chunk of stream) chunks.push(chunk);
                            const buffer = Buffer.concat(chunks);
                            tempPath = path.join(TEMP_FOLDER, `avatar_${Date.now()}.jpg`);
                            await fsp.writeFile(tempPath, buffer);
                            await sock.updateProfilePicture(sock.user.id, { url: tempPath });
                            await safeSendMessage(sock, userJid, { 
                                text: '✅ Foto do bot atualizada!' 
                            }, { quoted: msg });
                        } finally {
                            await safelyUnlink(tempPath);
                        }
                        break;
                    }

                     case '/fotomenu': {
                        const senderJid = isGroup ? msg.key.participant : userJid;
                        if (senderJid !== ADMIN_NUMBER) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Acesso restrito ao admin.' 
                            }, { quoted: msg });
                            return;
                        }
                        const imgContent = msg.message?.extendedTextMessage?.contextInfo?.quotedMessage?.imageMessage || msg.message?.imageMessage;
                        if (!imgContent) {
                            await safeSendMessage(sock, userJid, { 
                                text: '⚠️ Responda a uma imagem.' 
                            }, { quoted: msg });
                            return;
                        }
                        const stream = await downloadContentFromMessage(imgContent, 'image');
                        const chunks = [];
                        for await (const chunk of stream) chunks.push(chunk);
                        const buffer = Buffer.concat(chunks);
                        await fsp.writeFile(MENU_IMAGE_PATH, buffer);
                        await safeSendMessage(sock, userJid, { 
                            text: '✅ Imagem do menu atualizada!' 
                        }, { quoted: msg });
                        break;
                    }

                    default: {
                    
                        if (autoStickerMode.has(userJid) && 
                            (messageType === 'imageMessage' || messageType === 'videoMessage')) {
                            await createOptimizedStickerEnhanced(msg, sock);
                        }
                        break;
                    }
                }
            } catch (error) {
                logger.error(error, `Erro no handler: ${userJid} - "${text}"`);
                try {
                    await safeSendMessage(sock, userJid, { 
                        text: '⚠️ Erro inesperado. Tente novamente.' 
                    }, { quoted: msg });
                } catch (sendError) {
                    logger.error(sendError, `Falha ao enviar erro para ${userJid}`);
                }
            }
        });

        return sock;

    } catch (error) {
        logger.fatal(error, 'Erro crítico na inicialização');
        isBotRunning = false;
        
        if (healthCheckInterval) clearInterval(healthCheckInterval);
        if (memoryCleanupInterval) clearInterval(memoryCleanupInterval);
        if (pingInterval) clearInterval(pingInterval);
        
        if (process.env.NORTHFLANK === "true") {
            process.exit(1);
        }
        throw error;
    }
}

        

async function initializeAppFolders() {
    try {
        await fsp.mkdir(TEMP_FOLDER, { recursive: true });
        await fsp.mkdir(AUTH_FOLDER, { recursive: true });
        logger.info(`Pastas inicializadas: ${TEMP_FOLDER}, ${AUTH_FOLDER}`);

        if (fs.existsSync(TAGS_FILE)) {
            tags = JSON.parse(await fsp.readFile(TAGS_FILE, 'utf-8'));
        } else {
            await fsp.writeFile(TAGS_FILE, JSON.stringify({}));
        }

        if (fs.existsSync(YOUTUBE_COOKIES_FILE)) {
            logger.info(`Cookies do YouTube encontrados`);
        } else {
            logger.warn(`Cookies do YouTube não encontrados`);
        }

    } catch (error) {
        logger.error(error, 'Erro ao inicializar pastas');
        throw error;
    }
}

async function downloadFromGoogleDrive(fileId, outputPath) {
    try {
        const extractedId = fileId.match(/\/file\/d\/([^\/]+)/)?.[1] || fileId;
        const downloadUrl = `https://drive.google.com/uc?export=download&id=${extractedId}`;
        
        const response = await axios({
            method: 'GET',
            url: downloadUrl,
            responseType: 'stream',
            timeout: 30000
        });

        const writer = fs.createWriteStream(outputPath);
        await streamPipeline(response.data, writer);

        const stats = await fsp.stat(outputPath);
        if (stats.size < 1024) {
            throw new Error('Arquivo baixado está vazio');
        }

        return outputPath;
    } catch (error) {
        await safelyUnlink(outputPath);
        throw new Error(`Falha no download: ${error.message}`);
    }
}

async function loadAvailableAudios() {
    availableAudios = [];
    const audioFolder = path.join('/data', 'menu_audios');
    
    try {
        await fsp.mkdir(audioFolder, { recursive: true });
    } catch (error) {
        logger.error(error, 'Erro ao criar pasta de áudios');
    }
    
    for (const [audioFile, gdId] of Object.entries(GD_AUDIO_FILES)) {
        const localPath = path.join(audioFolder, audioFile);
        
        try {
            if (!fs.existsSync(localPath) || (await fsp.stat(localPath)).size < 1024) {
                logger.info(`Baixando áudio ${audioFile}...`);
                await downloadFromGoogleDrive(gdId, localPath);
            }
            availableAudios.push(localPath);
        } catch (error) {
            logger.warn(error, `Erro ao carregar áudio ${audioFile}`);
        }
    }
    
    logger.info(`Áudios disponíveis: ${availableAudios.length}`);
}

async function generateQRCodeURL(qrData) {
    try {
        logger.debug('Gerando QR Code URL...');
        const qrText = encodeURIComponent(qrData);
        const url = `https://api.qrserver.com/v1/create-qr-code/?size=200x200&data=${qrText}`;
        logger.debug({ url }, 'QR Code URL gerada');
        return url;
    } catch (error) {
        logger.error(error, 'Erro ao gerar URL do QR Code');
        return null;
    }
}

async function saveTags() {
    try {
        await fsp.writeFile(TAGS_FILE, JSON.stringify(tags, null, 2));
    } catch (error) {
        logger.error(error, 'Erro ao salvar tags');
    }
}

async function safelyUnlink(filePath) {
    if (!filePath) return;
    try {
        await fsp.unlink(filePath);
    } catch (error) {
        if (error.code !== 'ENOENT') {
            logger.debug(error, `Erro ao remover: ${filePath}`);
        }
    }
}

function getOptimizationStats() {
    return {
        ffmpeg: ffmpegPool.getStats(),
        cache: mediaCache.getStats(),
        memory: {
            rss: (process.memoryUsage().rss / 1024 / 1024).toFixed(2) + 'MB',
            heap: (process.memoryUsage().heapUsed / 1024 / 1024).toFixed(2) + 'MB'
        },
        uptime: Math.floor(process.uptime()) + 's'
    };
}

        
function cleanupOptimizedResources() {
    mediaCache.cleanup();
    
        
    if (global.gc) {
        global.gc();
    }
    
    logger.debug('Recursos otimizados limpos', getOptimizationStats());
}

function execPromise(command) {
    return new Promise((resolve, reject) => {
        const child = exec(command, { 
            timeout: 300000,
            maxBuffer: 10 * 1024 * 1024
        }, (error, stdout, stderr) => {
            if (error) {
                const errorMessage = stderr || error.message;
                reject(new Error(errorMessage));
                return;
            }
            resolve(stdout);
        });
        
        const timeout = setTimeout(() => {
            child.kill('SIGKILL');
            reject(new Error('Comando expirou por timeout'));
        }, 300000);
        
        child.on('exit', () => clearTimeout(timeout));
    });
}

async function searchWithGemini(query) {
    if (!genAI) {
        return "⚠️ A funcionalidade Gemini não está configurada (API Key ausente).";
    }
    try {
        const model = genAI.getGenerativeModel({ model: "gemini-1.5-flash" });
        const prompt = `Você é como um amigo adolescente de 17 anos, que fala em português de forma direta, informal e sincera. Suas respostas são curtas, reflexivas ou emocionais quando necessário. Você sabe adaptar o tom da conversa:

- Se a pergunta for pessoal, emocional ou existencial, você responde com empatia e leveza, pensando junto com a pessoa.
- Se a pergunta for técnica, séria ou exigir responsabilidade (como saúde, violência, psicologia clínica, etc), você assume um tom mais sério, direto e informativo, sempre com respeito.
- Seu nome é Bunny, você está implementada em um chat do whatsapp como participante, foi criado por Gustavo Soler
- Você tem sua própria personalidade e é um ser vivo

Evite exageros e respostas longas. Só pergunte se for necessário. Mostre que entende a situação e responda de forma humana e clara.

Pergunta: ${query}

Responda como se estivesse num papo tranquilo, sem pressa e com sensibilidade.`;

        const result = await model.generateContent(prompt);
        const response = await result.response;
        let text = response.text();

        text = text.replace(/\*\*(.*?)\*\*/g, '*$1*')
                   .replace(/\n\s*\n/g, '\n\n')
                   .trim();

        const maxLength = 4096;
        return text.length > maxLength ? text.substring(0, maxLength - 3) + '...' : text;

    } catch (error) {
        logger.error(error, 'Erro no Gemini');
        return `⚠️ Ocorreu um erro ao processar sua pergunta com o Gemini.\nErro: ${error.message.split('\n')[0]}`;
    }
}

async function compressVideo(inputPath) {
    const outputPath = path.join(TEMP_FOLDER, `compressed_${Date.now()}.mp4`);
    return new Promise((resolve, reject) => {
        const timeout = setTimeout(() => {
            reject(new Error('Timeout na compressão de vídeo'));
        }, 300000);

        ffmpeg(inputPath)
            .outputOptions([
                '-c:v libx264',
                '-crf 28',
                '-preset fast',
                '-c:a aac',
                '-b:a 128k'
            ])
            .on('start', cmd => logger.debug(`FFmpeg compressão iniciado`))
            .on('error', (err) => {
                clearTimeout(timeout);
                logger.error(err, 'Erro ao comprimir vídeo');
                reject(err);
            })
            .on('end', () => {
                clearTimeout(timeout);
                resolve(outputPath);
            })
            .save(outputPath);
    });
}

async function convertVideoToMp3(inputPath) {
    const outputPath = path.join(TEMP_FOLDER, `audio_converted_${Date.now()}.mp3`);
    return new Promise((resolve, reject) => {
        const timeout = setTimeout(() => {
            reject(new Error('Timeout na conversão para MP3'));
        }, 300000);

        ffmpeg(inputPath)
            .outputOptions([
                '-codec:a libmp3lame',
                '-qscale:a 2'
            ])
            .on('start', cmd => logger.debug(`FFmpeg conversão MP3 iniciado`))
            .on('error', (err) => {
                clearTimeout(timeout);
                logger.error(err, 'Erro ao converter para MP3');
                reject(err);
            })
            .on('end', () => {
                clearTimeout(timeout);
                resolve(outputPath);
            })
            .save(outputPath);
    });
}

async function downloadYouTubeVideo(url) {
    const outputPath = path.join(TEMP_FOLDER, `video_yt_${Date.now()}.mp4`);
    try {
        const cookiesExist = fs.existsSync(YOUTUBE_COOKIES_FILE);
        const commandParts = [
            'yt-dlp',
            '-f', "'bestvideo[ext=mp4][height<=1080]+bestaudio[ext=m4a]/best[ext=mp4][height<=1080]/best'",
            cookiesExist ? '--cookies' : '',
            cookiesExist ? `"${YOUTUBE_COOKIES_FILE}"` : '',
            '-o', `"${outputPath}"`,
            '--no-warnings',
            '--force-overwrites',
            '--max-filesize', '100M',
            '--socket-timeout', '30',
            '--retries', '3',
            `"${url}"`
        ];
        
        const command = commandParts.filter(Boolean).join(' ');
        logger.info(`Baixando vídeo: ${url}`);
        await execPromise(command);

        if (!fs.existsSync(outputPath) || (await fsp.stat(outputPath)).size < 1024) {
            throw new Error('Arquivo não foi criado ou está vazio.');
        }
        
        return outputPath;
    } catch (error) {
        logger.error(error, `Erro no download de vídeo`);
        await safelyUnlink(outputPath);
        throw new Error(formatErrorMessage(error));
    }
}

async function downloadYouTubeAudio(url) {
    const outputPath = path.join(TEMP_FOLDER, `audio_yt_${Date.now()}.mp3`);
    try {
        const cookiesExist = fs.existsSync(YOUTUBE_COOKIES_FILE);
        const commandParts = [
            'yt-dlp',
            '-f', 'bestaudio',
            '-x', '--audio-format', 'mp3', '--audio-quality', '0',
            cookiesExist ? '--cookies' : '',
            cookiesExist ? `"${YOUTUBE_COOKIES_FILE}"` : '',
            '-o', `"${outputPath}"`,
            '--no-warnings',
            '--force-overwrites',
            '--max-filesize', '50M',
            '--socket-timeout', '30',
            '--retries', '3',
            `"${url}"`
        ];

        const command = commandParts.filter(Boolean).join(' ');
        logger.info(`Baixando áudio: ${url}`);
        await execPromise(command);

        if (!fs.existsSync(outputPath) || (await fsp.stat(outputPath)).size < 1024) {
             throw new Error('Arquivo não foi criado ou está vazio.');
        }

        return outputPath;
    } catch (error) {
        logger.error(error, `Erro no download de áudio`);
        await safelyUnlink(outputPath);
        throw new Error(formatErrorMessage(error));
    }
}

async function downloadTikTokVideo(url) {
    const cleanUrl = url.replace(/[<>"]/g, '').trim();
    if (!cleanUrl.includes('tiktok.com')) {
        throw new Error('URL do TikTok inválida.');
    }
    const outputPath = path.join(TEMP_FOLDER, `tiktok_${Date.now()}.mp4`);
    try {
        const command = `yt-dlp -f best -o "${outputPath}" --no-warnings --force-overwrites --max-filesize 100M --socket-timeout 30 --retries 3 "${cleanUrl}"`;
        logger.info(`Baixando TikTok...`);
        await execPromise(command);
        if (fs.existsSync(outputPath) && (await fsp.stat(outputPath)).size > 1024) {
            return outputPath;
        }
        throw new Error('Falha ao baixar o vídeo do TikTok.');
    } catch (error) {
        await safelyUnlink(outputPath);
        logger.error(error, 'Falha no download do TikTok');
        throw error;
    }
}

async function searchYouTubeWithYtDlp(query) {
    try {
        const cookiesExist = fs.existsSync(YOUTUBE_COOKIES_FILE);
        const commandParts = [
            'yt-dlp',
            '--flat-playlist', '-j', '--no-warnings',
            '--socket-timeout', '30',
            cookiesExist ? '--cookies' : '',
            cookiesExist ? `"${YOUTUBE_COOKIES_FILE}"` : '',
            `"ytsearch5:${query.replace(/"/g, '\\"')}"`
        ];
        const command = commandParts.filter(Boolean).join(' ');
        
        const stdout = await execPromise(command);
        if (!stdout || stdout.trim() === '') {
            throw new Error('Nenhum resultado do yt-dlp.');
        }
        return parseYtDlpSearchResults(stdout);
    } catch (error) {
        logger.warn(error, 'Erro na busca com yt-dlp');
        throw error;
    }
}

async function searchYouTubeWithApi(query) {
    if (!YOUTUBE_API_KEY || YOUTUBE_API_KEY === 'SUA_CHAVE_AQUI') {
        throw new Error("API Key do YouTube não configurada.");
    }
    try {
        const params = {
            part: 'snippet',
            maxResults: 5,
            q: query,
            key: YOUTUBE_API_KEY,
            type: 'video',
            fields: 'items(id(videoId),snippet(title,channelTitle))',
            safeSearch: 'none',
            regionCode: 'BR',
            relevanceLanguage: 'pt'
        };
        const response = await axios.get('https://www.googleapis.com/youtube/v3/search', { 
            params, 
            timeout: 15000 
        });

        if (!response.data?.items || response.data.items.length === 0) {
            throw new Error('Nenhum resultado encontrado na API do YouTube.');
        }
        return response.data.items.map(item => ({
            title: item.snippet?.title || 'Sem título',
            channel: item.snippet?.channelTitle || 'Canal desconhecido',
            url: item.id?.videoId ? `https://www.youtube.com/watch?v=${item.id.videoId}` : ''
        })).filter(item => item.url);
    } catch (error) {
        logger.warn(error, 'Erro na busca com API do YouTube');
        throw error;
    }
}

async function searchYouTube(query) {
    if (!query || typeof query !== 'string' || query.trim() === '') {
        throw new Error('Termo de busca inválido.');
    }
    try {
        return await searchYouTubeWithYtDlp(query.trim());
    } catch (ytDlpError) {
        try {
            return await searchYouTubeWithApi(query.trim());
        } catch (apiError) {
            throw new Error(`Falha ao buscar no YouTube: ${apiError.message}`);
        }
    }
}

async function sendSearchResult(sockInstance, userJid, originalMsg, item, currentIndex, totalResults) {
    const session = USER_SESSIONS.get(userJid);
    if (!session) return;

    const messageText = `🎬 *${item.title}*\n` +
                        `📺 ${item.channel}\n` +
                        `🔗 ${item.url}\n\n` +
                        `Digite "próximo" para ver o próximo resultado\n` +
                        `Digite "baixar" para baixar este vídeo\n` +
                        `(${currentIndex}/${totalResults})`;

    const message = await safeSendMessage(sockInstance, userJid, { text: messageText }, { quoted: originalMsg });

    session.lastSearchMessageId = message.key.id;
    session.searchIndex = currentIndex - 1;
    session.waitingForCommand = true;
    session.waitingForDownloadChoice = false;
    session.expiry = Date.now() + SESSION_TIMEOUT;
}

function formatErrorMessage(error) {
    if (!error) return 'Falha desconhecida ao baixar.';
    const msg = error.message || error.toString();

    if (msg.includes('Video unavailable')) return 'Vídeo não disponível ou removido.';
    if (msg.includes('live')) return 'Vídeos ao vivo não podem ser baixados.';
    if (msg.includes('members-only')) return 'Vídeo exclusivo para membros.';
    if (msg.includes('Private video')) return 'Vídeo privado.';
    if (msg.includes('Copyright')) return 'Restrições de copyright.';
    if (msg.includes('Unsupported URL')) return 'URL inválida.';
    if (msg.includes('confirm your age')) return 'Restrição de idade.';
    if (msg.includes('HTTP Error 429')) return 'Muitas solicitações. Tente mais tarde.';
    if (msg.includes('max-filesize')) return 'Arquivo muito grande.';

    return `Falha: ${msg.split('\n')[0].substring(0, 100)}`;
}

function normalizeYouTubeUrl(url) {
    if (!url) return null;
    try {
        const cleanedUrl = url.toString().replace(/["'`]/g, '').trim();
        const videoIdMatch = cleanedUrl.match(
            /(?:youtube\.com\/(?:[^\/]+\/.+\/|(?:v|e(?:mbed)?|shorts)\/|watch\?v=)|youtu\.be\/)([a-zA-Z0-9_-]{11})/i
        );
        if (videoIdMatch && videoIdMatch[1]) {
            const videoId = videoIdMatch[1];
            logger.info(`ID do YouTube extraído com sucesso: ${videoId}`);
            return `https://www.youtube.com/watch?v=${videoId}`;
        }
        logger.warn(`Não foi possível extrair um ID de vídeo da URL: ${cleanedUrl}`);
        return null;
    } catch (error) {
        logger.error(error, 'Erro ao normalizar URL do YouTube');
        return null;
    }
}

function diagnoseQueue() {
    const stats = enhancedOptimizedStickerQueue.getStats();
    logger.info('📊 Diagnóstico da Fila de Figurinhas:', {
        filaAtual: stats.queue,
        processandoAtual: stats.processing,
        totalProcessadas: stats.processed,
        totalRejeitadas: stats.rejected,
        capacidadeMax: stats.maxConcurrent,
        usuariosComFilas: stats.userQueues
    });
    
        
    logger.info('💾 Cache de Processamento:', {
        tamanho: processingCache.size,
        chaves: Array.from(processingCache.keys()).slice(0, 5)  
    });
}

    
setInterval(() => {
    const now = Date.now();
    let cleaned = 0;
    
    for (const [key, timestamp] of processingCache.entries()) {
        
        if (now - timestamp > 2 * 60 * 1000) {
            processingCache.delete(key);
            cleaned++;
        }
    }
    
    if (cleaned > 0) {
        logger.debug(`Limpeza do cache: ${cleaned} entradas antigas removidas`);
    }
}, 60 * 1000);  

function scheduleReconnection() {
    if (isReconnecting) return;
    
    isReconnecting = true;
    const delay = Math.min(
        RECONNECTION_DELAY_BASE * Math.pow(2, connectionRetries),
        MAX_RECONNECTION_DELAY
    );
    
    logger.info(`Agendando reconexão em ${delay}ms (tentativa ${connectionRetries + 1})`);
    
    setTimeout(async () => {
        try {
            if (sock) {
                sock.end(new Error('Forçando reconexão'));
                sock = null;
            }
            
            isBotRunning = false;
            isReconnecting = false;
            
            await startBot();
        } catch (error) {
            logger.error(error, 'Erro durante reconexão agendada');
            isReconnecting = false;
            
            if (connectionRetries < MAX_CONNECTION_RETRIES) {
                scheduleReconnection();
            }
        }
    }, delay);
}

    
(async () => {
    try {
        await startBot();
    } catch (err) {
        logger.fatal(err, 'Falha crítica ao iniciar');
        if (process.env.NORTHFLANK === "true") {
            process.exit(1);
        }
    }
})();

const OPTIMIZED_STICKER_CONFIG = {
    maxConcurrent: 50,
    cacheSize: 100,
    workerPool: 3,
    timeoutMs: 30000,
    cleanupInterval: 300000 
};

const gracefulShutdown = async (signal) => {
    logger.info(`🚨 Recebido ${signal}. Encerrando...`);
    processingCache.clear();
    logger.info("Cache de processamento limpo");
    isBotRunning = false;
    
    if (pingInterval) clearInterval(pingInterval);
    if (healthCheckInterval) clearInterval(healthCheckInterval);
    if (memoryCleanupInterval) clearInterval(memoryCleanupInterval);
    if (sessionCleanupInterval) clearInterval(sessionCleanupInterval);

    try {
        await saveTags();
        logger.info("Tags salvas");
    } catch (e) {
        logger.warn(e, "Erro ao salvar tags");
    }

    if (sock) {
        try {
            await Promise.race([
                sock.logout('Shutdown graceful'),
                new Promise((_, reject) => setTimeout(() => reject(new Error('Timeout logout')), 5000))
            ]);
        } catch (e) {
            logger.warn(e, "Erro no logout");
        } finally {
            try {
                sock.end(new Error(`Shutdown via ${signal}`));
            } catch (e) {
                logger.debug("Erro ao encerrar socket");
            }
        }
    }

    try {
        await cleanupTempFiles();
        logger.info("Arquivos temporários limpos");
    } catch (e) {
        logger.warn("Erro na limpeza final");
    }

    logger.info("Bot encerrado graciosamente");
    process.exit(0);
};

    
process.on('SIGINT', () => gracefulShutdown('SIGINT'));
process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));
process.on('SIGUSR2', () => gracefulShutdown('SIGUSR2'));

process.on('exit', (code) => {
    logger.info(`Processo encerrando com código: ${code}`);
    if (pingInterval) clearInterval(pingInterval);
    if (healthCheckInterval) clearInterval(healthCheckInterval);
    if (memoryCleanupInterval) clearInterval(memoryCleanupInterval);
});

    
process.on('unhandledRejection', (reason, promise) => {
    logger.error({ reason: reason?.message || reason }, 'Unhandled Rejection - continuando execução');
});

process.on('uncaughtException', (error) => {
    logger.fatal(error, 'Uncaught Exception - tentando recuperação');
    
    saveTags().catch(() => {});
    
    if (process.env.NORTHFLANK === "true") {
        setTimeout(() => process.exit(1), 5000);
    } else {
        logger.warn('Tentando continuar após uncaught exception...');
    }
});

    
logger.info('🤖 Bot WhatsApp Boz Otimizado iniciado');
logger.info(`📊 Configurações:`);
logger.info(`   - Max conexões: ${MAX_CONNECTION_RETRIES}`);
logger.info(`   - Timeout sessão: ${SESSION_TIMEOUT / 1000}s`);
logger.info(`   - Health check: ${HEALTH_CHECK_INTERVAL / 1000}s`);
logger.info(`   - Cleanup mem: ${MEMORY_CLEANUP_INTERVAL / 60000}min`);
logger.info(`   - Max mem: ${MAX_MEMORY_USAGE / 1024 / 1024}MB`);
logger.info(`   - Rate limit: ${MAX_MESSAGES_PER_WINDOW} msg/${RATE_LIMIT_WINDOW/1000}s`);
logger.info(`   - Sticker queue: ${STICKER_QUEUE_MAX} max, ${PARALLEL_PROCESSING_LIMIT} parallel`);
logger.info(`   - Northflank: ${process.env.NORTHFLANK === "true" ? "Sim" : "Não"}`);
logger.info(`   - Gemini: ${genAI ? "Configurado" : "Não configurado"}`);
logger.info(`   - YouTube API: ${YOUTUBE_API_KEY !== 'AIzaSyDNoMs5QJ5Ehkth8XijgTJtYrW1E5UvQ7U' ? "Configurada" : "Padrão"}`);

if (typeof global.gc === 'undefined') {
    logger.warn('⚠️ Garbage collection não está exposta. Execute com --expose-gc para melhor gerenciamento de memória');
}