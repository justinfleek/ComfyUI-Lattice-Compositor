/**
 * Expression Evaluation Worker
 *
 * Evaluates expressions in an isolated Worker thread with timeout protection.
 * If an expression contains an infinite loop, the worker can be terminated
 * without hanging the main thread.
 *
 * SECURITY: This is the DoS protection layer. The main thread sets a timeout
 * and terminates this worker if it doesn't respond in time.
 */

// Worker-side SES initialization
let sesReady = false;
let Compartment: any = null;
let harden: any = null;

async function initSES(): Promise<boolean> {
  if (sesReady) return true;

  try {
    await import('ses');
    const g = globalThis as any;

    if (!g.lockdown) {
      return false;
    }

    g.lockdown({
      consoleTaming: 'unsafe',
      errorTaming: 'unsafe',
      stackFiltering: 'verbose',
      overrideTaming: 'severe',
      localeTaming: 'unsafe',
      domainTaming: 'unsafe',
    });

    Compartment = g.Compartment;
    harden = g.harden;
    sesReady = true;
    return true;
  } catch (e) {
    console.error('[ExpressionWorker] SES init failed:', e);
    return false;
  }
}

// Safe math functions (no random - use seeded version)
const safeMath = {
  abs: Math.abs,
  acos: Math.acos,
  asin: Math.asin,
  atan: Math.atan,
  atan2: Math.atan2,
  ceil: Math.ceil,
  cos: Math.cos,
  exp: Math.exp,
  floor: Math.floor,
  log: Math.log,
  max: Math.max,
  min: Math.min,
  pow: Math.pow,
  round: Math.round,
  sin: Math.sin,
  sqrt: Math.sqrt,
  tan: Math.tan,
  PI: Math.PI,
  E: Math.E,
};

interface EvalRequest {
  id: number;
  code: string;
  context: Record<string, unknown>;
}

interface EvalResponse {
  id: number;
  success: boolean;
  result?: number;
  error?: string;
}

function createSeededRandom(frame: number) {
  return (seed?: number): number => {
    const s = seed !== undefined ? seed : frame;
    const x = Math.sin(s * 12.9898) * 43758.5453;
    return x - Math.floor(x);
  };
}

async function evaluate(req: EvalRequest): Promise<EvalResponse> {
  if (!sesReady) {
    const ok = await initSES();
    if (!ok) {
      return { id: req.id, success: false, error: 'SES not available' };
    }
  }

  try {
    const frame = typeof req.context.frame === 'number' ? req.context.frame : 0;
    const seededRandom = harden(createSeededRandom(frame));

    // Build compartment globals from context
    const globals: Record<string, unknown> = {
      ...safeMath,
      random: seededRandom,
    };

    // Add context values (only primitives)
    for (const [key, value] of Object.entries(req.context)) {
      if (typeof value === 'number' || typeof value === 'string' || typeof value === 'boolean') {
        globals[key] = value;
      }
    }

    const compartment = new Compartment(harden(globals));
    const result = compartment.evaluate(req.code);

    // Validate result is a number
    if (typeof result !== 'number' || !Number.isFinite(result)) {
      return { id: req.id, success: true, result: 0 };
    }

    return { id: req.id, success: true, result };
  } catch (e) {
    return {
      id: req.id,
      success: false,
      error: e instanceof Error ? e.message : String(e)
    };
  }
}

// Message handler
self.onmessage = async (e: MessageEvent<EvalRequest>) => {
  const response = await evaluate(e.data);
  self.postMessage(response);
};

// Signal ready
self.postMessage({ type: 'ready' });
