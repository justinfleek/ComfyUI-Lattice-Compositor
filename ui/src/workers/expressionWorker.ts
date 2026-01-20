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
// SES types are declared in types/ses-ambient.d.ts
import type { SESCompartmentConstructor, HardenFunction } from "@/types/ses-ambient";

let sesReady = false;
let Compartment: SESCompartmentConstructor | null = null;
let harden: HardenFunction | null = null;

async function initSES(): Promise<boolean> {
  if (sesReady) return true;

  try {
    await import("ses");
    
    // Type-safe access - SES injects these on globalThis after import
    // Types are declared in types/ses-ambient.d.ts
    if (!globalThis.lockdown) {
      return false;
    }

    globalThis.lockdown({
      consoleTaming: "unsafe",
      errorTaming: "unsafe",
      stackFiltering: "verbose",
      overrideTaming: "severe",
      localeTaming: "unsafe",
      domainTaming: "unsafe",
    });

    // Type-safe assignment - these are available after lockdown()
    Compartment = globalThis.Compartment ?? null;
    harden = globalThis.harden ?? null;
    
    if (!Compartment || !harden) {
      return false;
    }
    
    sesReady = true;
    return true;
  } catch (e) {
    console.error("[ExpressionWorker] SES init failed:", e);
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

import type { ExpressionContext } from "../services/expressions/types";

interface EvalRequest {
  id: number;
  code: string;
  context: ExpressionContext;
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
      return { id: req.id, success: false, error: "SES not available" };
    }
  }

  try {
    const frame = typeof req.context.frame === "number" ? req.context.frame : 0;
    const seededRandom = harden(createSeededRandom(frame));

    // Build compartment globals from context
    // Type for SES compartment globals (primitives only for security)
    interface SESGlobals {
      [key: string]: number | string | boolean | (() => number) | typeof Math | undefined;
    }

    const globals: SESGlobals = {
      ...safeMath,
      random: seededRandom,

      // SECURITY: Explicitly block dangerous intrinsics
      // Even though SES sandboxes these, we block them for defense-in-depth
      Function: undefined,
      eval: undefined,
      globalThis: undefined,
      window: undefined,
      document: undefined,
      setTimeout: undefined,
      setInterval: undefined,
      setImmediate: undefined,
      fetch: undefined,
      XMLHttpRequest: undefined,
      WebSocket: undefined,
      Worker: undefined,
      importScripts: undefined,
      require: undefined,
      process: undefined,
      Deno: undefined,
      Bun: undefined,
    };

    // Add context values (only primitives)
    for (const [key, value] of Object.entries(req.context)) {
      if (
        typeof value === "number" ||
        typeof value === "string" ||
        typeof value === "boolean"
      ) {
        globals[key] = value;
      }
    }

    const compartment = new Compartment(harden(globals));
    const result = compartment.evaluate(req.code);

    // Validate result is a number
    if (typeof result !== "number" || !Number.isFinite(result)) {
      return { id: req.id, success: true, result: 0 };
    }

    return { id: req.id, success: true, result };
  } catch (e) {
    return {
      id: req.id,
      success: false,
      error: e instanceof Error ? e.message : String(e),
    };
  }
}

// Message handler
self.onmessage = async (e: MessageEvent<EvalRequest>) => {
  const response = await evaluate(e.data);
  self.postMessage(response);
};

// Signal ready
self.postMessage({ type: "ready" });

// Export empty object to make this a module (fixes TypeScript scope issues)
export {};
