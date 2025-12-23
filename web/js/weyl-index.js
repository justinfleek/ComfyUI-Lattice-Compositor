import { c as createLogger } from './weyl-main.js';

const logger = createLogger("RenderQueue");
const DB_VERSION = 1;
const JOBS_STORE = "renderJobs";
const FRAMES_STORE = "renderedFrames";
class RenderQueueDB {
  db = null;
  dbName;
  constructor(dbName) {
    this.dbName = dbName;
  }
  async open() {
    return new Promise((resolve, reject) => {
      const request = indexedDB.open(this.dbName, DB_VERSION);
      request.onerror = () => {
        reject(new Error(`Failed to open database: ${request.error}`));
      };
      request.onsuccess = () => {
        this.db = request.result;
        resolve();
      };
      request.onupgradeneeded = (event) => {
        const db = event.target.result;
        if (!db.objectStoreNames.contains(JOBS_STORE)) {
          const jobsStore = db.createObjectStore(JOBS_STORE, { keyPath: "id" });
          jobsStore.createIndex("status", "status", { unique: false });
          jobsStore.createIndex("priority", "priority", { unique: false });
          jobsStore.createIndex("createdAt", "createdAt", { unique: false });
        }
        if (!db.objectStoreNames.contains(FRAMES_STORE)) {
          const framesStore = db.createObjectStore(FRAMES_STORE, { keyPath: ["jobId", "frameNumber"] });
          framesStore.createIndex("jobId", "jobId", { unique: false });
        }
      };
    });
  }
  async saveJob(job) {
    if (!this.db) throw new Error("Database not open");
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([JOBS_STORE], "readwrite");
      const store = transaction.objectStore(JOBS_STORE);
      const request = store.put(job);
      request.onsuccess = () => resolve();
      request.onerror = () => reject(request.error);
    });
  }
  async getJob(jobId) {
    if (!this.db) throw new Error("Database not open");
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([JOBS_STORE], "readonly");
      const store = transaction.objectStore(JOBS_STORE);
      const request = store.get(jobId);
      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
  }
  async getAllJobs() {
    if (!this.db) throw new Error("Database not open");
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([JOBS_STORE], "readonly");
      const store = transaction.objectStore(JOBS_STORE);
      const request = store.getAll();
      request.onsuccess = () => resolve(request.result || []);
      request.onerror = () => reject(request.error);
    });
  }
  async deleteJob(jobId) {
    if (!this.db) throw new Error("Database not open");
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([JOBS_STORE, FRAMES_STORE], "readwrite");
      const jobsStore = transaction.objectStore(JOBS_STORE);
      jobsStore.delete(jobId);
      const framesStore = transaction.objectStore(FRAMES_STORE);
      const index = framesStore.index("jobId");
      const cursorRequest = index.openCursor(IDBKeyRange.only(jobId));
      cursorRequest.onsuccess = () => {
        const cursor = cursorRequest.result;
        if (cursor) {
          cursor.delete();
          cursor.continue();
        }
      };
      transaction.oncomplete = () => resolve();
      transaction.onerror = () => reject(transaction.error);
    });
  }
  async saveFrame(jobId, frame) {
    if (!this.db) throw new Error("Database not open");
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([FRAMES_STORE], "readwrite");
      const store = transaction.objectStore(FRAMES_STORE);
      const request = store.put({ jobId, ...frame });
      request.onsuccess = () => resolve();
      request.onerror = () => reject(request.error);
    });
  }
  async getFrames(jobId) {
    if (!this.db) throw new Error("Database not open");
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([FRAMES_STORE], "readonly");
      const store = transaction.objectStore(FRAMES_STORE);
      const index = store.index("jobId");
      const request = index.getAll(IDBKeyRange.only(jobId));
      request.onsuccess = () => resolve(request.result || []);
      request.onerror = () => reject(request.error);
    });
  }
  async clearCompletedFrames(jobId) {
    if (!this.db) throw new Error("Database not open");
    return new Promise((resolve, reject) => {
      const transaction = this.db.transaction([FRAMES_STORE], "readwrite");
      const store = transaction.objectStore(FRAMES_STORE);
      const index = store.index("jobId");
      const cursorRequest = index.openCursor(IDBKeyRange.only(jobId));
      cursorRequest.onsuccess = () => {
        const cursor = cursorRequest.result;
        if (cursor) {
          cursor.delete();
          cursor.continue();
        }
      };
      transaction.oncomplete = () => resolve();
      transaction.onerror = () => reject(transaction.error);
    });
  }
  close() {
    if (this.db) {
      this.db.close();
      this.db = null;
    }
  }
}
class RenderQueueManager {
  config;
  db;
  jobs = /* @__PURE__ */ new Map();
  activeJobId = null;
  isRunning = false;
  isPaused = false;
  autoSaveTimer = null;
  startTime = 0;
  framesRenderedThisSession = 0;
  // Callbacks
  onProgressCallback;
  onJobCompleteCallback;
  onJobErrorCallback;
  onQueueEmptyCallback;
  // Frame renderer callback (provided by compositor)
  frameRenderer;
  constructor(config = {}) {
    this.config = {
      maxConcurrentJobs: config.maxConcurrentJobs ?? 1,
      workerPoolSize: config.workerPoolSize ?? 4,
      batchSize: config.batchSize ?? 10,
      autoSaveInterval: config.autoSaveInterval ?? 5e3,
      dbName: config.dbName ?? "weyl-render-queue"
    };
    this.db = new RenderQueueDB(this.config.dbName);
  }
  // ============================================================================
  // INITIALIZATION
  // ============================================================================
  async initialize() {
    await this.db.open();
    const savedJobs = await this.db.getAllJobs();
    for (const job of savedJobs) {
      this.jobs.set(job.id, job);
      if (job.progress.status === "rendering") {
        job.progress.status = "pending";
        await this.db.saveJob(job);
      }
    }
    logger.debug(`RenderQueueManager initialized with ${this.jobs.size} jobs`);
  }
  /**
   * Set the frame renderer callback
   * This function is called to render each frame
   */
  setFrameRenderer(renderer) {
    this.frameRenderer = renderer;
  }
  // ============================================================================
  // JOB MANAGEMENT
  // ============================================================================
  /**
   * Add a new render job to the queue
   */
  async addJob(config) {
    const jobId = `render-${Date.now()}-${Math.random().toString(36).substr(2, 9)}`;
    const job = {
      ...config,
      id: jobId,
      priority: config.priority ?? this.jobs.size,
      progress: {
        status: "pending",
        currentFrame: config.startFrame,
        totalFrames: config.endFrame - config.startFrame + 1,
        percentage: 0,
        framesPerSecond: 0,
        estimatedTimeRemaining: 0,
        elapsedTime: 0
      },
      createdAt: Date.now()
    };
    this.jobs.set(jobId, job);
    await this.db.saveJob(job);
    logger.debug(`Added render job: ${jobId} (${job.progress.totalFrames} frames)`);
    if (!this.isRunning && !this.isPaused) {
      this.start();
    }
    return jobId;
  }
  /**
   * Remove a job from the queue
   */
  async removeJob(jobId) {
    const job = this.jobs.get(jobId);
    if (!job) return;
    if (this.activeJobId === jobId) {
      this.cancelCurrentJob();
    }
    this.jobs.delete(jobId);
    await this.db.deleteJob(jobId);
    logger.debug(`Removed render job: ${jobId}`);
  }
  /**
   * Get a job by ID
   */
  getJob(jobId) {
    return this.jobs.get(jobId);
  }
  /**
   * Get all jobs
   */
  getAllJobs() {
    return Array.from(this.jobs.values()).sort((a, b) => a.priority - b.priority);
  }
  /**
   * Update job priority
   */
  async updatePriority(jobId, priority) {
    const job = this.jobs.get(jobId);
    if (!job) return;
    job.priority = priority;
    await this.db.saveJob(job);
  }
  // ============================================================================
  // QUEUE CONTROL
  // ============================================================================
  /**
   * Start processing the queue
   */
  start() {
    if (this.isRunning) return;
    this.isRunning = true;
    this.isPaused = false;
    this.startAutoSave();
    this.processNextJob();
    logger.debug("Render queue started");
  }
  /**
   * Pause the queue (current frame will complete)
   */
  pause() {
    this.isPaused = true;
    if (this.activeJobId) {
      const job = this.jobs.get(this.activeJobId);
      if (job) {
        job.progress.status = "paused";
        this.notifyProgress(this.activeJobId, job.progress);
      }
    }
    logger.debug("Render queue paused");
  }
  /**
   * Resume the queue
   */
  resume() {
    if (!this.isPaused) return;
    this.isPaused = false;
    if (this.activeJobId) {
      const job = this.jobs.get(this.activeJobId);
      if (job) {
        job.progress.status = "rendering";
        this.notifyProgress(this.activeJobId, job.progress);
      }
    }
    this.processNextJob();
    logger.debug("Render queue resumed");
  }
  /**
   * Stop the queue entirely
   */
  stop() {
    this.isRunning = false;
    this.isPaused = false;
    this.stopAutoSave();
    if (this.activeJobId) {
      const job = this.jobs.get(this.activeJobId);
      if (job && job.progress.status === "rendering") {
        job.progress.status = "pending";
      }
      this.activeJobId = null;
    }
    logger.debug("Render queue stopped");
  }
  /**
   * Cancel the currently rendering job
   */
  cancelCurrentJob() {
    if (!this.activeJobId) return;
    const job = this.jobs.get(this.activeJobId);
    if (job) {
      job.progress.status = "cancelled";
      job.completedAt = Date.now();
      this.notifyProgress(this.activeJobId, job.progress);
    }
    this.activeJobId = null;
  }
  // ============================================================================
  // RENDERING
  // ============================================================================
  /**
   * Process the next job in the queue
   */
  async processNextJob() {
    if (!this.isRunning || this.isPaused || this.activeJobId) return;
    const pendingJobs = this.getAllJobs().filter((j) => j.progress.status === "pending" || j.progress.status === "paused");
    if (pendingJobs.length === 0) {
      this.isRunning = false;
      this.stopAutoSave();
      this.onQueueEmptyCallback?.();
      logger.debug("Render queue empty");
      return;
    }
    const job = pendingJobs[0];
    await this.startJob(job);
  }
  /**
   * Start rendering a job
   */
  async startJob(job) {
    if (!this.frameRenderer) {
      logger.warn("No frame renderer configured");
      return;
    }
    this.activeJobId = job.id;
    job.progress.status = "rendering";
    job.startedAt = job.startedAt ?? Date.now();
    this.startTime = Date.now();
    this.framesRenderedThisSession = 0;
    logger.debug(`Starting render job: ${job.id}`);
    try {
      const existingFrames = await this.db.getFrames(job.id);
      const renderedFrameNumbers = new Set(existingFrames.map((f) => f.frameNumber));
      let startFrame = job.startFrame;
      if (job.checkpointFrame !== void 0) {
        startFrame = job.checkpointFrame + 1;
      }
      const allFrames = [...existingFrames];
      for (let frame = startFrame; frame <= job.endFrame; frame++) {
        if (this.isPaused || !this.isRunning) {
          job.checkpointFrame = frame - 1;
          await this.db.saveJob(job);
          this.activeJobId = null;
          return;
        }
        if (renderedFrameNumbers.has(frame)) {
          continue;
        }
        const frameData = await this.frameRenderer(
          job.compositionId,
          frame,
          job.width,
          job.height
        );
        const renderedFrame = {
          frameNumber: frame,
          data: frameData,
          timestamp: Date.now()
        };
        allFrames.push(renderedFrame);
        this.framesRenderedThisSession++;
        await this.db.saveFrame(job.id, renderedFrame);
        this.updateJobProgress(job, frame);
      }
      job.progress.status = "completed";
      job.progress.percentage = 100;
      job.completedAt = Date.now();
      await this.db.saveJob(job);
      this.notifyProgress(job.id, job.progress);
      this.onJobCompleteCallback?.(job.id, allFrames);
      await this.db.clearCompletedFrames(job.id);
      logger.debug(`Render job completed: ${job.id}`);
    } catch (error) {
      job.progress.status = "failed";
      job.progress.error = error instanceof Error ? error.message : "Unknown error";
      job.completedAt = Date.now();
      await this.db.saveJob(job);
      this.notifyProgress(job.id, job.progress);
      this.onJobErrorCallback?.(job.id, job.progress.error);
      logger.warn(`Render job failed: ${job.id}`, error);
    }
    this.activeJobId = null;
    this.processNextJob();
  }
  /**
   * Update job progress
   */
  updateJobProgress(job, currentFrame) {
    const framesRendered = currentFrame - job.startFrame + 1;
    const totalFrames = job.progress.totalFrames;
    const elapsedMs = Date.now() - this.startTime;
    const elapsedSec = elapsedMs / 1e3;
    job.progress.currentFrame = currentFrame;
    job.progress.percentage = Math.round(framesRendered / totalFrames * 100);
    job.progress.elapsedTime = elapsedSec;
    job.progress.framesPerSecond = this.framesRenderedThisSession / Math.max(elapsedSec, 0.1);
    const framesRemaining = totalFrames - framesRendered;
    job.progress.estimatedTimeRemaining = framesRemaining / Math.max(job.progress.framesPerSecond, 0.1);
    this.notifyProgress(job.id, job.progress);
  }
  // ============================================================================
  // AUTO-SAVE
  // ============================================================================
  startAutoSave() {
    if (this.autoSaveTimer !== null) return;
    this.autoSaveTimer = window.setInterval(() => {
      if (this.activeJobId) {
        const job = this.jobs.get(this.activeJobId);
        if (job) {
          job.checkpointFrame = job.progress.currentFrame;
          this.db.saveJob(job);
        }
      }
    }, this.config.autoSaveInterval);
  }
  stopAutoSave() {
    if (this.autoSaveTimer !== null) {
      clearInterval(this.autoSaveTimer);
      this.autoSaveTimer = null;
    }
  }
  // ============================================================================
  // CALLBACKS
  // ============================================================================
  onProgress(callback) {
    this.onProgressCallback = callback;
  }
  onJobComplete(callback) {
    this.onJobCompleteCallback = callback;
  }
  onJobError(callback) {
    this.onJobErrorCallback = callback;
  }
  onQueueEmpty(callback) {
    this.onQueueEmptyCallback = callback;
  }
  notifyProgress(jobId, progress) {
    this.onProgressCallback?.(jobId, progress);
  }
  // ============================================================================
  // STATS
  // ============================================================================
  getStats() {
    const jobs = Array.from(this.jobs.values());
    return {
      totalJobs: jobs.length,
      activeJobs: jobs.filter((j) => j.progress.status === "rendering").length,
      pendingJobs: jobs.filter((j) => j.progress.status === "pending").length,
      completedJobs: jobs.filter((j) => j.progress.status === "completed").length,
      failedJobs: jobs.filter((j) => j.progress.status === "failed").length,
      totalFramesRendered: jobs.reduce((sum, j) => {
        if (j.progress.status === "completed") {
          return sum + j.progress.totalFrames;
        }
        return sum + (j.progress.currentFrame - j.startFrame);
      }, 0),
      averageFps: this.activeJobId ? this.jobs.get(this.activeJobId)?.progress.framesPerSecond ?? 0 : 0
    };
  }
  // ============================================================================
  // CLEANUP
  // ============================================================================
  dispose() {
    this.stop();
    this.db.close();
  }
}

export { RenderQueueManager };
