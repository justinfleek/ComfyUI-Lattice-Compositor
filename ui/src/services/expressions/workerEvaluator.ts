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
  resolve: (result: EvalResult) => void;
  timer: ReturnType<typeof setTimeout>;
}

export interface EvalResult {
  value: number;
  timedOut: boolean;
  error?: string;
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
  for (const [, req] of pending) {
    clearTimeout(req.timer);
    req.resolve({ value: 0, timedOut: true, error: 'Worker recreated' });
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
        req.resolve({ value: data.result ?? 0, timedOut: false });
      } else {
        req.resolve({ value: 0, timedOut: false, error: data.error });
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
 * @returns EvalResult with value, timedOut flag, and optional error
 */
export async function evaluateWithTimeout(
  code: string,
  context: Record<string, unknown>
): Promise<EvalResult> {
  // Input validation
  if (typeof code !== 'string' || code.length === 0) {
    return { value: 0, timedOut: false, error: 'Empty code' };
  }

  if (code.length > 10240) {
    return { value: 0, timedOut: false, error: 'Expression too long' };
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
        req.resolve({ value: 0, timedOut: true, error: 'Evicted' });
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

      // Return with timedOut flag
      resolve({ value: 0, timedOut: true });
    }, EVAL_TIMEOUT_MS);

    pending.set(id, { resolve, timer });

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
