/**
 * Worker Pool Service
 *
 * Manages a pool of WebWorkers for parallel computation.
 * Features:
 * - Automatic worker spawning based on hardware concurrency
 * - Task queuing and load balancing
 * - Promise-based API for async operations
 * - Automatic cleanup and error handling
 */

import type {
  WorkerMessage,
  WorkerMessageType,
  WorkerResponse,
  ParticleStepPayload,
  ParticleStepResult,
} from '@/workers/computeWorker';

// ============================================================================
// TYPES
// ============================================================================

interface PendingTask {
  id: string;
  resolve: (result: unknown) => void;
  reject: (error: Error) => void;
  timestamp: number;
}

interface WorkerState {
  worker: Worker;
  busy: boolean;
  taskCount: number;
}

export interface WorkerPoolConfig {
  /** Number of workers to spawn (default: navigator.hardwareConcurrency) */
  workerCount?: number;
  /** Task timeout in milliseconds (default: 30000) */
  taskTimeout?: number;
  /** Enable worker recycling after N tasks (default: 1000) */
  recycleAfterTasks?: number;
}

// ============================================================================
// WORKER POOL CLASS
// ============================================================================

export class WorkerPool {
  private workers: WorkerState[] = [];
  private pendingTasks: Map<string, PendingTask> = new Map();
  private taskQueue: Array<{ message: WorkerMessage; resolve: (r: unknown) => void; reject: (e: Error) => void }> = [];
  private nextTaskId = 0;
  private config: Required<WorkerPoolConfig>;
  private isDisposed = false;

  constructor(config: WorkerPoolConfig = {}) {
    this.config = {
      workerCount: config.workerCount ?? Math.max(2, navigator.hardwareConcurrency - 1),
      taskTimeout: config.taskTimeout ?? 30000,
      recycleAfterTasks: config.recycleAfterTasks ?? 1000,
    };

    this.spawnWorkers();
  }

  /**
   * Spawn initial workers
   */
  private spawnWorkers(): void {
    for (let i = 0; i < this.config.workerCount; i++) {
      this.spawnWorker();
    }
  }

  /**
   * Spawn a single worker
   */
  private spawnWorker(): void {
    const worker = new Worker(
      new URL('@/workers/computeWorker.ts', import.meta.url),
      { type: 'module' }
    );

    const state: WorkerState = {
      worker,
      busy: false,
      taskCount: 0,
    };

    worker.onmessage = (event: MessageEvent<WorkerResponse>) => {
      this.handleWorkerMessage(state, event.data);
    };

    worker.onerror = (error) => {
      console.error('Worker error:', error);
      this.handleWorkerError(state, error);
    };

    this.workers.push(state);
  }

  /**
   * Handle worker message
   */
  private handleWorkerMessage(state: WorkerState, response: WorkerResponse): void {
    state.busy = false;
    state.taskCount++;

    // Recycle worker if needed
    if (state.taskCount >= this.config.recycleAfterTasks) {
      this.recycleWorker(state);
    }

    const pending = this.pendingTasks.get(response.id);
    if (pending) {
      this.pendingTasks.delete(response.id);

      if (response.success) {
        pending.resolve(response.result);
      } else {
        pending.reject(new Error(response.error || 'Unknown worker error'));
      }
    }

    // Process next task in queue
    this.processQueue();
  }

  /**
   * Handle worker error
   */
  private handleWorkerError(state: WorkerState, error: ErrorEvent): void {
    state.busy = false;

    // Reject all pending tasks for this worker
    // (in practice, we don't track which worker has which task, so we just log)
    console.error('Worker crashed:', error.message);

    // Recycle the crashed worker
    this.recycleWorker(state);
    this.processQueue();
  }

  /**
   * Recycle a worker (terminate and spawn new)
   */
  private recycleWorker(state: WorkerState): void {
    const index = this.workers.indexOf(state);
    if (index > -1) {
      state.worker.terminate();
      this.workers.splice(index, 1);

      if (!this.isDisposed) {
        this.spawnWorker();
      }
    }
  }

  /**
   * Find an available worker
   */
  private getAvailableWorker(): WorkerState | null {
    // Find least busy worker
    let best: WorkerState | null = null;
    let bestTaskCount = Infinity;

    for (const state of this.workers) {
      if (!state.busy && state.taskCount < bestTaskCount) {
        best = state;
        bestTaskCount = state.taskCount;
      }
    }

    return best;
  }

  /**
   * Process the task queue
   */
  private processQueue(): void {
    while (this.taskQueue.length > 0) {
      const worker = this.getAvailableWorker();
      if (!worker) break;

      const task = this.taskQueue.shift()!;
      this.dispatchToWorker(worker, task.message, task.resolve, task.reject);
    }
  }

  /**
   * Dispatch task to worker
   */
  private dispatchToWorker(
    state: WorkerState,
    message: WorkerMessage,
    resolve: (r: unknown) => void,
    reject: (e: Error) => void
  ): void {
    state.busy = true;

    const pending: PendingTask = {
      id: message.id,
      resolve,
      reject,
      timestamp: Date.now(),
    };

    this.pendingTasks.set(message.id, pending);

    // Set timeout
    setTimeout(() => {
      const task = this.pendingTasks.get(message.id);
      if (task) {
        this.pendingTasks.delete(message.id);
        task.reject(new Error(`Task ${message.type} timed out after ${this.config.taskTimeout}ms`));
        state.busy = false;
        this.processQueue();
      }
    }, this.config.taskTimeout);

    state.worker.postMessage(message);
  }

  /**
   * Execute a task on a worker
   */
  private execute<T>(type: WorkerMessageType, payload: unknown): Promise<T> {
    return new Promise((resolve, reject) => {
      if (this.isDisposed) {
        reject(new Error('WorkerPool has been disposed'));
        return;
      }

      const message: WorkerMessage = {
        type,
        id: `task_${this.nextTaskId++}`,
        payload,
      };

      const worker = this.getAvailableWorker();
      if (worker) {
        this.dispatchToWorker(worker, message, resolve as (r: unknown) => void, reject);
      } else {
        // Queue the task
        this.taskQueue.push({ message, resolve: resolve as (r: unknown) => void, reject });
      }
    });
  }

  // ============================================================================
  // PUBLIC API
  // ============================================================================

  /**
   * Step particle simulation
   */
  async stepParticles(payload: ParticleStepPayload): Promise<ParticleStepResult> {
    return this.execute<ParticleStepResult>('PARTICLE_STEP', payload);
  }

  /**
   * Evaluate a bezier curve at parameter t
   */
  async evaluateBezier(points: Array<{ x: number; y: number }>, t: number): Promise<{ x: number; y: number }> {
    return this.execute('BEZIER_EVALUATE', { points, t });
  }

  /**
   * Compute arc length table for a bezier curve
   */
  async computeArcLengthTable(points: Array<{ x: number; y: number }>, samples: number): Promise<number[]> {
    return this.execute('BEZIER_ARC_LENGTH', { points, samples });
  }

  /**
   * Apply box blur to image data
   */
  async blurImage(imageData: ImageData, radius: number): Promise<ImageData> {
    return this.execute('IMAGE_BLUR', { imageData, radius });
  }

  /**
   * Apply threshold to image data
   */
  async thresholdImage(imageData: ImageData, threshold: number): Promise<ImageData> {
    return this.execute('IMAGE_THRESHOLD', { imageData, threshold });
  }

  /**
   * Compute SHA-256 hash
   */
  async computeHash(data: string | ArrayBuffer): Promise<string> {
    return this.execute('COMPUTE_HASH', { data });
  }

  /**
   * Get pool statistics
   */
  getStats(): {
    workerCount: number;
    busyWorkers: number;
    pendingTasks: number;
    queuedTasks: number;
  } {
    return {
      workerCount: this.workers.length,
      busyWorkers: this.workers.filter(w => w.busy).length,
      pendingTasks: this.pendingTasks.size,
      queuedTasks: this.taskQueue.length,
    };
  }

  /**
   * Dispose all workers
   */
  dispose(): void {
    this.isDisposed = true;

    // Reject all pending tasks
    for (const [id, task] of this.pendingTasks) {
      task.reject(new Error('WorkerPool disposed'));
    }
    this.pendingTasks.clear();

    // Clear queue
    for (const task of this.taskQueue) {
      task.reject(new Error('WorkerPool disposed'));
    }
    this.taskQueue = [];

    // Terminate all workers
    for (const state of this.workers) {
      state.worker.terminate();
    }
    this.workers = [];
  }
}

// ============================================================================
// SINGLETON INSTANCE
// ============================================================================

let globalWorkerPool: WorkerPool | null = null;

/**
 * Get the global worker pool instance
 */
export function getWorkerPool(): WorkerPool {
  if (!globalWorkerPool) {
    globalWorkerPool = new WorkerPool();
  }
  return globalWorkerPool;
}

/**
 * Dispose the global worker pool
 */
export function disposeWorkerPool(): void {
  if (globalWorkerPool) {
    globalWorkerPool.dispose();
    globalWorkerPool = null;
  }
}

export default WorkerPool;
