/**
 * RenderQueueManager - Browser-Based Background Render Queue
 *
 * Phase 5: Render Queue Implementation
 *
 * Features:
 * - Background frame rendering with worker pool
 * - Queue persistence via IndexedDB
 * - Resume interrupted exports
 * - Progress tracking and time estimation
 * - Pause/resume/cancel controls
 */

import { createLogger } from "@/utils/logger";
import { isFiniteNumber } from "@/utils/typeGuards";

const logger = createLogger("RenderQueue");

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

export type RenderJobStatus =
  | "pending"
  | "rendering"
  | "paused"
  | "completed"
  | "failed"
  | "cancelled";

export interface RenderJobConfig {
  /** Unique job identifier */
  id: string;
  /** Human-readable job name */
  name: string;
  /** Composition ID to render */
  compositionId: string;
  /** Start frame (inclusive) */
  startFrame: number;
  /** End frame (inclusive) */
  endFrame: number;
  /** Output width */
  width: number;
  /** Output height */
  height: number;
  /** Frames per second */
  fps: number;
  /** Output format */
  format: "png-sequence" | "webm" | "mp4";
  /** Quality (0-100) */
  quality: number;
  /** Priority (lower = higher priority) */
  priority: number;
}

export interface RenderJobProgress {
  /** Current job status */
  status: RenderJobStatus;
  /** Current frame being rendered */
  currentFrame: number;
  /** Total frames to render */
  totalFrames: number;
  /** Percentage complete (0-100) */
  percentage: number;
  /** Frames rendered per second */
  framesPerSecond: number;
  /** Estimated time remaining in seconds */
  estimatedTimeRemaining: number;
  /** Time elapsed in seconds */
  elapsedTime: number;
  /** Error message if failed */
  error?: string;
}

export interface RenderJob extends RenderJobConfig {
  /** Current progress */
  progress: RenderJobProgress;
  /** Created timestamp */
  createdAt: number;
  /** Started timestamp */
  startedAt?: number;
  /** Completed timestamp */
  completedAt?: number;
  /** Last checkpoint frame (for resume) */
  checkpointFrame?: number;
}

export interface RenderedFrame {
  /** Frame number */
  frameNumber: number;
  /** Frame data as Blob */
  data: Blob;
  /** Timestamp when rendered */
  timestamp: number;
}

export interface RenderQueueStats {
  /** Total jobs in queue */
  totalJobs: number;
  /** Jobs currently rendering */
  activeJobs: number;
  /** Jobs waiting */
  pendingJobs: number;
  /** Jobs completed */
  completedJobs: number;
  /** Jobs failed */
  failedJobs: number;
  /** Total frames rendered across all jobs */
  totalFramesRendered: number;
  /** Average frames per second */
  averageFps: number;
}

export interface RenderQueueConfig {
  /** Maximum concurrent render jobs */
  maxConcurrentJobs: number;
  /** Worker pool size */
  workerPoolSize: number;
  /** Frames per batch */
  batchSize: number;
  /** Auto-save progress interval (ms) */
  autoSaveInterval: number;
  /** IndexedDB database name */
  dbName: string;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                  // indexeddb // persistence
// ════════════════════════════════════════════════════════════════════════════

const DB_VERSION = 1;
const JOBS_STORE = "renderJobs";
const FRAMES_STORE = "renderedFrames";

class RenderQueueDB {
  private db: IDBDatabase | null = null;
  private dbName: string;

  constructor(dbName: string) {
    this.dbName = dbName;
  }

  async open(): Promise<void> {
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
        const db = (event.target as IDBOpenDBRequest).result;

        // Jobs store
        if (!db.objectStoreNames.contains(JOBS_STORE)) {
          const jobsStore = db.createObjectStore(JOBS_STORE, { keyPath: "id" });
          jobsStore.createIndex("status", "status", { unique: false });
          jobsStore.createIndex("priority", "priority", { unique: false });
          jobsStore.createIndex("createdAt", "createdAt", { unique: false });
        }

        // Frames store (for incomplete renders)
        if (!db.objectStoreNames.contains(FRAMES_STORE)) {
          const framesStore = db.createObjectStore(FRAMES_STORE, {
            keyPath: ["jobId", "frameNumber"],
          });
          framesStore.createIndex("jobId", "jobId", { unique: false });
        }
      };
    });
  }

  async saveJob(job: RenderJob): Promise<void> {
    if (!this.db) throw new Error("Database not open");
    const db = this.db;

    return new Promise((resolve, reject) => {
      const transaction = db.transaction([JOBS_STORE], "readwrite");
      const store = transaction.objectStore(JOBS_STORE);
      const request = store.put(job);

      request.onsuccess = () => resolve();
      request.onerror = () => reject(request.error);
    });
  }

  async getJob(jobId: string): Promise<RenderJob | undefined> {
    if (!this.db) throw new Error("Database not open");
    const db = this.db;

    return new Promise((resolve, reject) => {
      const transaction = db.transaction([JOBS_STORE], "readonly");
      const store = transaction.objectStore(JOBS_STORE);
      const request = store.get(jobId);

      request.onsuccess = () => resolve(request.result);
      request.onerror = () => reject(request.error);
    });
  }

  async getAllJobs(): Promise<RenderJob[]> {
    if (!this.db) throw new Error("Database not open");
    const db = this.db;

    return new Promise((resolve, reject) => {
      const transaction = db.transaction([JOBS_STORE], "readonly");
      const store = transaction.objectStore(JOBS_STORE);
      const request = store.getAll();

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      request.onsuccess = () => {
        const result = request.result;
        const resultArray = (result !== null && result !== undefined && Array.isArray(result)) ? result : [];
        resolve(resultArray);
      };
      request.onerror = () => reject(request.error);
    });
  }

  async deleteJob(jobId: string): Promise<void> {
    if (!this.db) throw new Error("Database not open");
    const db = this.db;

    return new Promise((resolve, reject) => {
      const transaction = db.transaction(
        [JOBS_STORE, FRAMES_STORE],
        "readwrite",
      );

      // Delete job
      const jobsStore = transaction.objectStore(JOBS_STORE);
      jobsStore.delete(jobId);

      // Delete associated frames
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

  async saveFrame(jobId: string, frame: RenderedFrame): Promise<void> {
    if (!this.db) throw new Error("Database not open");
    const db = this.db;

    return new Promise((resolve, reject) => {
      const transaction = db.transaction([FRAMES_STORE], "readwrite");
      const store = transaction.objectStore(FRAMES_STORE);
      const request = store.put({ jobId, ...frame });

      request.onsuccess = () => resolve();
      request.onerror = () => reject(request.error);
    });
  }

  async getFrames(jobId: string): Promise<RenderedFrame[]> {
    if (!this.db) throw new Error("Database not open");
    const db = this.db;

    return new Promise((resolve, reject) => {
      const transaction = db.transaction([FRAMES_STORE], "readonly");
      const store = transaction.objectStore(FRAMES_STORE);
      const index = store.index("jobId");
      const request = index.getAll(IDBKeyRange.only(jobId));

      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy || []
      request.onsuccess = () => {
        const result = request.result;
        const resultArray = (result !== null && result !== undefined && Array.isArray(result)) ? result : [];
        resolve(resultArray);
      };
      request.onerror = () => reject(request.error);
    });
  }

  async clearCompletedFrames(jobId: string): Promise<void> {
    if (!this.db) throw new Error("Database not open");
    const db = this.db;

    return new Promise((resolve, reject) => {
      const transaction = db.transaction([FRAMES_STORE], "readwrite");
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

  close(): void {
    if (this.db) {
      this.db.close();
      this.db = null;
    }
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                // render // queue // manager
// ════════════════════════════════════════════════════════════════════════════

export class RenderQueueManager {
  private config: RenderQueueConfig;
  private db: RenderQueueDB;
  private jobs: Map<string, RenderJob> = new Map();
  private activeJobId: string | null = null;
  private isRunning: boolean = false;
  private isPaused: boolean = false;
  private autoSaveTimer: number | null = null;
  private startTime: number = 0;
  private framesRenderedThisSession: number = 0;

  // Callbacks
  private onProgressCallback?: (
    jobId: string,
    progress: RenderJobProgress,
  ) => void;
  private onJobCompleteCallback?: (
    jobId: string,
    frames: RenderedFrame[],
  ) => void;
  private onJobErrorCallback?: (jobId: string, error: string) => void;
  private onQueueEmptyCallback?: () => void;

  // Frame renderer callback (provided by compositor)
  private frameRenderer?: (
    compositionId: string,
    frame: number,
    width: number,
    height: number,
  ) => Promise<Blob>;

  constructor(config: Partial<RenderQueueConfig> = {}) {
    // Type proof: maxConcurrentJobs ∈ number | undefined → number
    const maxConcurrentJobs = isFiniteNumber(config.maxConcurrentJobs) &&
      config.maxConcurrentJobs > 0
      ? Math.floor(config.maxConcurrentJobs)
      : 1;
    // Type proof: workerPoolSize ∈ number | undefined → number
    const workerPoolSize = isFiniteNumber(config.workerPoolSize) &&
      config.workerPoolSize > 0
      ? Math.floor(config.workerPoolSize)
      : 4;
    // Type proof: batchSize ∈ number | undefined → number
    const batchSize = isFiniteNumber(config.batchSize) && config.batchSize > 0
      ? Math.floor(config.batchSize)
      : 10;
    // Type proof: autoSaveInterval ∈ number | undefined → number
    const autoSaveInterval = isFiniteNumber(config.autoSaveInterval) &&
      config.autoSaveInterval > 0
      ? Math.floor(config.autoSaveInterval)
      : 5000;
    // Type proof: dbName ∈ string | undefined → string
    const dbName =
      typeof config.dbName === "string" && config.dbName.length > 0
        ? config.dbName
        : "lattice-render-queue";

    this.config = {
      maxConcurrentJobs,
      workerPoolSize,
      batchSize,
      autoSaveInterval,
      dbName,
    };

    this.db = new RenderQueueDB(this.config.dbName);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                            // initialization
  // ════════════════════════════════════════════════════════════════════════════

  async initialize(): Promise<void> {
    await this.db.open();

    // Load existing jobs
    const savedJobs = await this.db.getAllJobs();
    for (const job of savedJobs) {
      this.jobs.set(job.id, job);

      // Reset in-progress jobs to pending (they were interrupted)
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
  setFrameRenderer(
    renderer: (
      compositionId: string,
      frame: number,
      width: number,
      height: number,
    ) => Promise<Blob>,
  ): void {
    this.frameRenderer = renderer;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // job // management
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Add a new render job to the queue
   */
  async addJob(config: Omit<RenderJobConfig, "id">): Promise<string> {
    const jobId = `render-${Date.now()}-${Math.random().toString(36).slice(2, 11)}`;

    // Type proof: priority ∈ number | undefined → number
    const priority = isFiniteNumber(config.priority)
      ? config.priority
      : this.jobs.size;

    const job: RenderJob = {
      ...config,
      id: jobId,
      priority,
      progress: {
        status: "pending",
        currentFrame: config.startFrame,
        totalFrames: config.endFrame - config.startFrame + 1,
        percentage: 0,
        framesPerSecond: 0,
        estimatedTimeRemaining: 0,
        elapsedTime: 0,
      },
      createdAt: Date.now(),
    };

    this.jobs.set(jobId, job);
    await this.db.saveJob(job);

    logger.debug(
      `Added render job: ${jobId} (${job.progress.totalFrames} frames)`,
    );

    // Auto-start if not running
    if (!this.isRunning && !this.isPaused) {
      this.start();
    }

    return jobId;
  }

  /**
   * Remove a job from the queue
   */
  async removeJob(jobId: string): Promise<void> {
    const job = this.jobs.get(jobId);
    if (!job) return;

    // Cancel if currently rendering
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
  getJob(jobId: string): RenderJob | undefined {
    return this.jobs.get(jobId);
  }

  /**
   * Get all jobs
   */
  getAllJobs(): RenderJob[] {
    return Array.from(this.jobs.values()).sort(
      (a, b) => a.priority - b.priority,
    );
  }

  /**
   * Update job priority
   */
  async updatePriority(jobId: string, priority: number): Promise<void> {
    const job = this.jobs.get(jobId);
    if (!job) return;

    job.priority = priority;
    await this.db.saveJob(job);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                          // queue // control
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Start processing the queue
   */
  start(): void {
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
  pause(): void {
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
  resume(): void {
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
  stop(): void {
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
  cancelCurrentJob(): void {
    if (!this.activeJobId) return;

    const job = this.jobs.get(this.activeJobId);
    if (job) {
      job.progress.status = "cancelled";
      job.completedAt = Date.now();
      this.notifyProgress(this.activeJobId, job.progress);
    }

    this.activeJobId = null;
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // rendering
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Process the next job in the queue
   */
  private async processNextJob(): Promise<void> {
    if (!this.isRunning || this.isPaused || this.activeJobId) return;

    // Find next pending job by priority
    const pendingJobs = this.getAllJobs().filter(
      (j) => j.progress.status === "pending" || j.progress.status === "paused",
    );

    if (pendingJobs.length === 0) {
      this.isRunning = false;
      this.stopAutoSave();
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const onQueueEmptyCallback = this.onQueueEmptyCallback;
      if (onQueueEmptyCallback != null && typeof onQueueEmptyCallback === "function") {
        onQueueEmptyCallback();
      }
      logger.debug("Render queue empty");
      return;
    }

    const job = pendingJobs[0];
    await this.startJob(job);
  }

  /**
   * Start rendering a job
   */
  private async startJob(job: RenderJob): Promise<void> {
    if (!this.frameRenderer) {
      logger.warn("No frame renderer configured");
      return;
    }

    this.activeJobId = job.id;
    job.progress.status = "rendering";
    // Type proof: startedAt ∈ number | undefined → number
    job.startedAt = isFiniteNumber(job.startedAt) ? job.startedAt : Date.now();
    this.startTime = Date.now();
    this.framesRenderedThisSession = 0;

    logger.debug(`Starting render job: ${job.id}`);

    try {
      // Load any previously rendered frames
      const existingFrames = await this.db.getFrames(job.id);
      const renderedFrameNumbers = new Set(
        existingFrames.map((f) => f.frameNumber),
      );

      // Find resume point
      let startFrame = job.startFrame;
      if (job.checkpointFrame !== undefined) {
        startFrame = job.checkpointFrame + 1;
      }

      // Render remaining frames
      const allFrames: RenderedFrame[] = [...existingFrames];

      for (let frame = startFrame; frame <= job.endFrame; frame++) {
        // Check for pause/stop
        if (this.isPaused || !this.isRunning) {
          job.checkpointFrame = frame - 1;
          await this.db.saveJob(job);
          this.activeJobId = null;
          return;
        }

        // Skip already rendered frames
        if (renderedFrameNumbers.has(frame)) {
          continue;
        }

        // Render frame
        const frameData = await this.frameRenderer(
          job.compositionId,
          frame,
          job.width,
          job.height,
        );

        const renderedFrame: RenderedFrame = {
          frameNumber: frame,
          data: frameData,
          timestamp: Date.now(),
        };

        allFrames.push(renderedFrame);
        this.framesRenderedThisSession++;

        // Save to IndexedDB (for resume capability)
        await this.db.saveFrame(job.id, renderedFrame);

        // Update progress
        this.updateJobProgress(job, frame);
      }

      // Job complete
      job.progress.status = "completed";
      job.progress.percentage = 100;
      job.completedAt = Date.now();
      await this.db.saveJob(job);

      this.notifyProgress(job.id, job.progress);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const onJobCompleteCallback = this.onJobCompleteCallback;
      if (onJobCompleteCallback != null && typeof onJobCompleteCallback === "function") {
        onJobCompleteCallback(job.id, allFrames);
      }

      // Clear temporary frames from IndexedDB
      await this.db.clearCompletedFrames(job.id);

      logger.debug(`Render job completed: ${job.id}`);
    } catch (error) {
      job.progress.status = "failed";
      job.progress.error =
        error instanceof Error ? error.message : "Unknown error";
      job.completedAt = Date.now();
      await this.db.saveJob(job);

      this.notifyProgress(job.id, job.progress);
      // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
      const onJobErrorCallback = this.onJobErrorCallback;
      if (onJobErrorCallback != null && typeof onJobErrorCallback === "function") {
        onJobErrorCallback(job.id, job.progress.error);
      }

      logger.warn(`Render job failed: ${job.id}`, error);
    }

    this.activeJobId = null;

    // Process next job
    this.processNextJob();
  }

  /**
   * Update job progress
   */
  private updateJobProgress(job: RenderJob, currentFrame: number): void {
    const framesRendered = currentFrame - job.startFrame + 1;
    const totalFrames = job.progress.totalFrames;
    const elapsedMs = Date.now() - this.startTime;
    const elapsedSec = elapsedMs / 1000;

    job.progress.currentFrame = currentFrame;
    job.progress.percentage = Math.round((framesRendered / totalFrames) * 100);
    job.progress.elapsedTime = elapsedSec;
    job.progress.framesPerSecond =
      this.framesRenderedThisSession / Math.max(elapsedSec, 0.1);

    const framesRemaining = totalFrames - framesRendered;
    job.progress.estimatedTimeRemaining =
      framesRemaining / Math.max(job.progress.framesPerSecond, 0.1);

    this.notifyProgress(job.id, job.progress);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                      // auto
  // ════════════════════════════════════════════════════════════════════════════

  private startAutoSave(): void {
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

  private stopAutoSave(): void {
    if (this.autoSaveTimer !== null) {
      clearInterval(this.autoSaveTimer);
      this.autoSaveTimer = null;
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                 // callbacks
  // ════════════════════════════════════════════════════════════════════════════

  onProgress(
    callback: (jobId: string, progress: RenderJobProgress) => void,
  ): void {
    this.onProgressCallback = callback;
  }

  onJobComplete(
    callback: (jobId: string, frames: RenderedFrame[]) => void,
  ): void {
    this.onJobCompleteCallback = callback;
  }

  onJobError(callback: (jobId: string, error: string) => void): void {
    this.onJobErrorCallback = callback;
  }

  onQueueEmpty(callback: () => void): void {
    this.onQueueEmptyCallback = callback;
  }

  private notifyProgress(jobId: string, progress: RenderJobProgress): void {
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
    const onProgressCallback = this.onProgressCallback;
    if (onProgressCallback != null && typeof onProgressCallback === "function") {
      onProgressCallback(jobId, progress);
    }
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                           // frame // access
  // ════════════════════════════════════════════════════════════════════════════

  /**
   * Get all rendered frames for a job
   */
  async getFrames(jobId: string): Promise<RenderedFrame[]> {
    return this.db.getFrames(jobId);
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                     // stats
  // ════════════════════════════════════════════════════════════════════════════

  getStats(): RenderQueueStats {
    const jobs = Array.from(this.jobs.values());

    return {
      totalJobs: jobs.length,
      activeJobs: jobs.filter((j) => j.progress.status === "rendering").length,
      pendingJobs: jobs.filter((j) => j.progress.status === "pending").length,
      completedJobs: jobs.filter((j) => j.progress.status === "completed")
        .length,
      failedJobs: jobs.filter((j) => j.progress.status === "failed").length,
      totalFramesRendered: jobs.reduce((sum, j) => {
        if (j.progress.status === "completed") {
          return sum + j.progress.totalFrames;
        }
        return sum + (j.progress.currentFrame - j.startFrame);
      }, 0),
      // Type proof: averageFps ∈ number | undefined → number
      averageFps: (() => {
        if (!this.activeJobId) return 0;
        const activeJob = this.jobs.get(this.activeJobId);
        // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ?.
        const activeJobProgress = (activeJob != null && typeof activeJob === "object" && "progress" in activeJob && activeJob.progress != null && typeof activeJob.progress === "object") ? activeJob.progress : undefined;
        const framesPerSecond = (activeJobProgress != null && typeof activeJobProgress === "object" && "framesPerSecond" in activeJobProgress && typeof activeJobProgress.framesPerSecond === "number") ? activeJobProgress.framesPerSecond : undefined;
        return isFiniteNumber(framesPerSecond) ? framesPerSecond : 0;
      })(),
    };
  }

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                   // cleanup
  // ════════════════════════════════════════════════════════════════════════════

  dispose(): void {
    this.stop();
    this.db.close();
  }
}

// ════════════════════════════════════════════════════════════════════════════
//                                                     // singleton // instance
// ════════════════════════════════════════════════════════════════════════════

let queueInstance: RenderQueueManager | null = null;

export function getRenderQueueManager(): RenderQueueManager {
  if (!queueInstance) {
    queueInstance = new RenderQueueManager();
  }
  return queueInstance;
}

export async function initializeRenderQueue(): Promise<RenderQueueManager> {
  const manager = getRenderQueueManager();
  await manager.initialize();
  return manager;
}
