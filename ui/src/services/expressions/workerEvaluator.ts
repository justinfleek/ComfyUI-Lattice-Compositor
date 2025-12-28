/**
 * Worker-based Expression Evaluator with Timeout Protection
 *
 * This module provides DoS protection by evaluating expressions in a Web Worker
 * with a strict timeout. If an expression hangs (infinite loop), the worker is
 * terminated and recreated.
 *
 * SECURITY: This is the ACTUAL fix for expression DoS attacks.
 * - 100ms timeout per evaluation
 * - Worker terminated on timeout (kills infinite loops)
 * - Worker recreated automatically for next evaluation
 * - Main thread NEVER blocks
 */

const EVAL_TIMEOUT_MS = 100;
const MAX_PENDING = 100; // Prevent memory leak from abandoned requests

interface PendingRequest {
  resolve: (result: number) => void;
  reject: (error: Error) => void;
  timer: ReturnType<typeof setTimeout>;
}

let worker: Worker | null = null;
let workerReady = false;
let requestId = 0;
const pending = new Map<number, PendingRequest>();

/**
 * Create or recreate the expression worker
 */
function createWorker(): Worker {
  // Terminate existing worker if any
  if (worker) {
    worker.terminate();
    worker = null;
    workerReady = false;
  }

  // Clear any pending requests (they'll timeout anyway)
  for (const [id, req] of pending) {
    clearTimeout(req.timer);
    req.reject(new Error('Worker recreated'));
  }
  pending.clear();

  // Create new worker
  const w = new Worker(
    new URL('../../workers/expressionWorker.ts', import.meta.url),
    { type: 'module' }
  );

  w.onmessage = (e) => {
    const data = e.data;

    // Handle ready signal
    if (data.type === 'ready') {
      workerReady = true;
      return;
    }

    // Handle evaluation response
    const req = pending.get(data.id);
    if (req) {
      clearTimeout(req.timer);
      pending.delete(data.id);

      if (data.success) {
        req.resolve(data.result ?? 0);
      } else {
        req.reject(new Error(data.error || 'Evaluation failed'));
      }
    }
  };

  w.onerror = (e) => {
    console.error('[WorkerEvaluator] Worker error:', e.message);
    // Recreate worker on error
    worker = createWorker();
  };

  worker = w;
  return w;
}

/**
 * Evaluate an expression in the worker with timeout protection
 *
 * @param code - The expression code to evaluate
 * @param context - Variables available to the expression
 * @param fallback - Value to return on timeout/error (default: 0)
 * @returns The evaluation result, or fallback on timeout/error
 */
export async function evaluateWithTimeout(
  code: string,
  context: Record<string, unknown>,
  fallback: number = 0
): Promise<number> {
  // Input validation
  if (typeof code !== 'string' || code.length === 0) {
    return fallback;
  }

  if (code.length > 10240) {
    console.warn('[WorkerEvaluator] Expression too long, returning fallback');
    return fallback;
  }

  // Ensure worker exists
  if (!worker) {
    worker = createWorker();
  }

  // Prevent memory leak
  if (pending.size >= MAX_PENDING) {
    console.warn('[WorkerEvaluator] Too many pending requests, clearing oldest');
    const oldest = pending.keys().next().value;
    if (oldest !== undefined) {
      const req = pending.get(oldest);
      if (req) {
        clearTimeout(req.timer);
        req.reject(new Error('Evicted'));
        pending.delete(oldest);
      }
    }
  }

  const id = ++requestId;

  return new Promise((resolve) => {
    const timer = setTimeout(() => {
      // TIMEOUT: Expression took too long (probably infinite loop)
      pending.delete(id);
      console.warn('[WorkerEvaluator] Expression timeout - terminating worker');

      // Terminate and recreate worker
      worker = createWorker();

      // Return fallback value
      resolve(fallback);
    }, EVAL_TIMEOUT_MS);

    pending.set(id, {
      resolve: (result) => resolve(result),
      reject: () => resolve(fallback), // On error, return fallback
      timer
    });

    // Send to worker
    worker!.postMessage({ id, code, context });
  });
}

/**
 * Check if worker evaluation is available
 */
export function isWorkerAvailable(): boolean {
  return typeof Worker !== 'undefined';
}

/**
 * Terminate the worker (cleanup)
 */
export function terminateWorker(): void {
  if (worker) {
    worker.terminate();
    worker = null;
    workerReady = false;
  }
  for (const [, req] of pending) {
    clearTimeout(req.timer);
  }
  pending.clear();
}
