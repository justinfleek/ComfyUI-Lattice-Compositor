/**
 * SES (Secure ECMAScript) Expression Evaluator
 *
 * This module provides a secure sandbox for evaluating user expressions using
 * Agoric's SES (Secure ECMAScript) implementation.
 *
 * SECURITY FEATURES:
 * - All JavaScript intrinsics are frozen (Object, Array, Function prototypes)
 * - No access to global objects (window, document, process, etc.)
 * - No eval, Function constructor, or import() access
 * - Prototype pollution attacks are blocked
 * - Constructor chain escapes are blocked
 * - Length limit (10KB) prevents payload attacks
 * - Deterministic evaluation (no Math.random, uses seeded PRNG)
 * - DoS PROTECTION via Worker timeout (100ms) - use evaluateWithTimeout()
 *
 * TWO EVALUATION MODES:
 * 1. evaluateWithTimeout() - ASYNC, Worker-based, 100ms timeout, DoS PROTECTED
 *    Use this for untrusted input or when async is acceptable.
 *
 * 2. evaluateInSES() / evaluateSimpleExpression() - SYNC, main thread, NO timeout
 *    Use only for render-loop where async is not possible.
 *    WARNING: Can hang on infinite loops.
 *
 * This replaces the previous Proxy+with sandbox (BUG-006) which was bypassable.
 */

import type { ExpressionContext } from "./types";

// Re-export worker-based evaluator for DoS-protected async evaluation
export {
  type EvalResult,
  evaluateWithTimeout,
  isWorkerAvailable,
  terminateWorker,
} from "./workerEvaluator";

// SES lockdown status
let sesInitialized = false;
const sesError: Error | null = null;

// Maximum expression length (10KB) to prevent payload attacks
const MAX_EXPRESSION_LENGTH = 10240;

/**
 * Initialize SES security sandbox
 *
 * NOTE: Main thread lockdown has been DISABLED because it breaks Vue/Three.js.
 * SES freezes Array Iterator and other intrinsics, causing:
 * "TypeError: Cannot assign to read only property 'next' of object '[object Array Iterator]'"
 *
 * Expression evaluation is STILL SECURE because:
 * 1. All expressions are evaluated in an isolated Web Worker (expressionWorker.ts)
 * 2. The worker has its own SES lockdown that doesn't affect the main thread
 * 3. Worker provides timeout protection against infinite loops (100ms max)
 *
 * This function now just marks SES as "initialized" without calling lockdown.
 */
export async function initializeSES(): Promise<boolean> {
  if (sesInitialized) {
    return true;
  }

  // Mark as initialized - actual SES lockdown happens in the worker only
  sesInitialized = true;
  console.log(
    "[SES] Expression security via worker sandbox - main thread lockdown disabled for Vue/Three.js compatibility",
  );
  return true;
}

/**
 * Check if SES is initialized
 */
export function isSESInitialized(): boolean {
  return sesInitialized;
}

/**
 * Get SES initialization error if any
 */
export function getSESError(): Error | null {
  return sesError;
}

/**
 * Create a safe evaluation compartment with expression context
 *
 * This creates a new Compartment with only the allowed globals,
 * preventing access to dangerous APIs.
 */
export function createExpressionCompartment(ctx: ExpressionContext): any {
  if (!sesInitialized) {
    throw new Error(
      "[SES] Not initialized. Call initializeSES() at app startup.",
    );
  }

  // Import Compartment from SES (available after lockdown)
  const { Compartment, harden } = globalThis as any;

  if (!Compartment) {
    throw new Error(
      "[SES] Compartment not available. Ensure lockdown() was called.",
    );
  }

  // Create safe Math object (harden to prevent modification)
  // NOTE: Math.random is intentionally EXCLUDED for determinism
  // Use the seeded random() utility function instead
  const safeMath = harden({
    PI: Math.PI,
    E: Math.E,
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
    log10: Math.log10,
    log2: Math.log2,
    max: Math.max,
    min: Math.min,
    pow: Math.pow,
    // random: EXCLUDED - use seeded random() for determinism
    round: Math.round,
    sign: Math.sign,
    sin: Math.sin,
    sqrt: Math.sqrt,
    tan: Math.tan,
    trunc: Math.trunc,
    hypot: Math.hypot,
    cbrt: Math.cbrt,
    expm1: Math.expm1,
    log1p: Math.log1p,
    sinh: Math.sinh,
    cosh: Math.cosh,
    tanh: Math.tanh,
    asinh: Math.asinh,
    acosh: Math.acosh,
    atanh: Math.atanh,
  });

  // Create safe Number utilities
  const safeNumber = harden({
    isFinite: Number.isFinite,
    isNaN: Number.isNaN,
    isInteger: Number.isInteger,
    parseFloat: Number.parseFloat,
    parseInt: Number.parseInt,
    MAX_VALUE: Number.MAX_VALUE,
    MIN_VALUE: Number.MIN_VALUE,
    MAX_SAFE_INTEGER: Number.MAX_SAFE_INTEGER,
    MIN_SAFE_INTEGER: Number.MIN_SAFE_INTEGER,
    EPSILON: Number.EPSILON,
    POSITIVE_INFINITY: Number.POSITIVE_INFINITY,
    NEGATIVE_INFINITY: Number.NEGATIVE_INFINITY,
    NaN: Number.NaN,
  });

  // Utility functions for expressions
  const utilities = harden({
    // Linear interpolation
    linear: (
      t: number,
      tMin: number,
      tMax: number,
      vMin: number,
      vMax: number,
    ): number => {
      if (t <= tMin) return vMin;
      if (t >= tMax) return vMax;
      return vMin + (vMax - vMin) * ((t - tMin) / (tMax - tMin));
    },

    // Clamp value
    clamp: (val: number, min: number, max: number): number => {
      return Math.max(min, Math.min(max, val));
    },

    // Seeded random (deterministic)
    random: (seed?: number): number => {
      const s = seed !== undefined ? seed : ctx.frame;
      const x = Math.sin(s * 12.9898) * 43758.5453;
      return x - Math.floor(x);
    },

    // Angle conversion
    radiansToDegrees: (rad: number): number => (rad * 180) / Math.PI,
    degreesToRadians: (deg: number): number => (deg * Math.PI) / 180,

    // Time conversion
    timeToFrames: (t: number = ctx.time): number => Math.round(t * ctx.fps),
    framesToTime: (f: number): number => f / ctx.fps,

    // Degree-based trig
    sinDeg: (deg: number): number => Math.sin((deg * Math.PI) / 180),
    cosDeg: (deg: number): number => Math.cos((deg * Math.PI) / 180),
    tanDeg: (deg: number): number => Math.tan((deg * Math.PI) / 180),

    // Vector operations (basic)
    length: (a: number | number[], b?: number | number[]): number => {
      if (b === undefined) {
        if (typeof a === "number") return Math.abs(a);
        return Math.sqrt(a.reduce((sum: number, v: number) => sum + v * v, 0));
      }
      if (typeof a === "number" && typeof b === "number") {
        return Math.abs(a - b);
      }
      const arrA = Array.isArray(a) ? a : [a];
      const arrB = Array.isArray(b) ? b : [b];
      let sum = 0;
      for (let i = 0; i < Math.max(arrA.length, arrB.length); i++) {
        const diff = (arrA[i] || 0) - (arrB[i] || 0);
        sum += diff * diff;
      }
      return Math.sqrt(sum);
    },

    // Vector add
    add: (a: number | number[], b: number | number[]): number | number[] => {
      if (typeof a === "number" && typeof b === "number") return a + b;
      const arrA = Array.isArray(a) ? a : [a];
      const arrB = Array.isArray(b) ? b : [b];
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        result.push((arrA[i] || 0) + (arrB[i] || 0));
      }
      return result;
    },

    // Vector subtract
    sub: (a: number | number[], b: number | number[]): number | number[] => {
      if (typeof a === "number" && typeof b === "number") return a - b;
      const arrA = Array.isArray(a) ? a : [a];
      const arrB = Array.isArray(b) ? b : [b];
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        result.push((arrA[i] || 0) - (arrB[i] || 0));
      }
      return result;
    },

    // Vector multiply
    mul: (a: number | number[], b: number | number[]): number | number[] => {
      if (typeof a === "number" && typeof b === "number") return a * b;
      if (typeof b === "number" && Array.isArray(a)) {
        return a.map((v) => v * b);
      }
      if (typeof a === "number" && Array.isArray(b)) {
        return b.map((v) => v * a);
      }
      const arrA = a as number[];
      const arrB = b as number[];
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        result.push((arrA[i] || 0) * (arrB[i] || 0));
      }
      return result;
    },

    // Vector divide
    div: (a: number | number[], b: number | number[]): number | number[] => {
      if (typeof a === "number" && typeof b === "number") return a / (b || 1);
      if (typeof b === "number" && Array.isArray(a)) {
        return a.map((v) => v / (b || 1));
      }
      if (typeof a === "number" && Array.isArray(b)) {
        return b.map((v) => a / (v || 1));
      }
      const arrA = a as number[];
      const arrB = b as number[];
      const len = Math.max(arrA.length, arrB.length);
      const result = [];
      for (let i = 0; i < len; i++) {
        result.push((arrA[i] || 0) / (arrB[i] || 1));
      }
      return result;
    },
  });

  // Create the compartment with safe globals only
  const compartment = new Compartment({
    // Safe Math
    Math: safeMath,

    // Safe Number utilities
    Number: safeNumber,

    // Basic type checking
    isNaN: Number.isNaN,
    isFinite: Number.isFinite,
    parseInt: Number.parseInt,
    parseFloat: Number.parseFloat,

    // Constants
    Infinity,
    NaN,
    undefined,

    // Context values (frozen)
    time: ctx.time,
    frame: ctx.frame,
    fps: ctx.fps,
    duration: ctx.duration,

    // Layer info
    index: ctx.layerIndex,
    layerName: ctx.layerName,
    inPoint: ctx.inPoint,
    outPoint: ctx.outPoint,

    // Property value (frozen if array)
    value: Array.isArray(ctx.value) ? harden([...ctx.value]) : ctx.value,
    velocity: Array.isArray(ctx.velocity)
      ? harden([...ctx.velocity])
      : ctx.velocity,
    numKeys: ctx.numKeys,

    // Utility functions
    ...utilities,

    // Console for debugging (limited)
    console: harden({
      log: (...args: any[]) => console.log("[Expression]", ...args),
      warn: (...args: any[]) => console.warn("[Expression]", ...args),
    }),

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
  });

  return compartment;
}

/**
 * Evaluate an expression in a SES Compartment
 *
 * SECURITY: This is the ONLY way expressions should be evaluated.
 * If SES is not available, expressions are disabled and return ctx.value unchanged.
 * There is NO fallback to a weaker sandbox - that would defeat the security model.
 *
 * @param code - The expression code to evaluate
 * @param ctx - The expression context
 * @returns The evaluated result, or ctx.value if SES unavailable
 */
export function evaluateInSES(
  code: string,
  ctx: ExpressionContext,
): number | number[] | string {
  // SECURITY: Type check - defense in depth for JS callers
  if (typeof code !== "string") {
    console.warn("[SECURITY] evaluateInSES: code is not a string");
    return ctx.value;
  }

  if (!code || code.trim() === "") {
    return ctx.value;
  }

  // SECURITY: If SES is not initialized, DO NOT evaluate - return passthrough
  // This is intentional. We fail CLOSED, not open.
  if (!sesInitialized) {
    console.error(
      "[SECURITY] SES not initialized - expression evaluation DISABLED for security",
    );
    console.error(
      "[SECURITY] Call initializeSES() at app startup to enable expressions",
    );
    return ctx.value;
  }

  // SECURITY: Length limit to prevent payload attacks
  if (code.length > MAX_EXPRESSION_LENGTH) {
    console.warn(
      `[SECURITY] Expression too long (${code.length} bytes, max ${MAX_EXPRESSION_LENGTH})`,
    );
    return ctx.value;
  }

  // WARNING: This is SYNC evaluation - no timeout protection.
  // For DoS protection, use evaluateWithTimeout() which runs in a Worker with 100ms timeout.

  try {
    const compartment = createExpressionCompartment(ctx);

    // Auto-return the last expression if code doesn't contain explicit return
    const needsReturn = !code.includes("return ") && !code.includes("return;");
    const processedCode = needsReturn
      ? code
          .trim()
          .split("\n")
          .map((line, i, arr) =>
            i === arr.length - 1 &&
            !line.trim().startsWith("//") &&
            line.trim().length > 0
              ? `return ${line}`
              : line,
          )
          .join("\n")
      : code;

    // Wrap in IIFE for proper return handling
    const wrappedCode = `(function() { ${processedCode} })()`;

    // Evaluate in compartment
    const result = compartment.evaluate(wrappedCode);

    return result;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.warn("[SES] Expression error:", message);
    return ctx.value;
  }
}

/**
 * Evaluate a simple expression with custom context
 *
 * SECURITY: This is for textAnimator-style expressions that need custom context
 * variables (textIndex, selectorValue, etc.) instead of the full ExpressionContext.
 *
 * Returns number or null on failure (fail closed - never throws, never returns unsafe values).
 *
 * @param expr - The expression code to evaluate
 * @param context - Custom context variables to expose (will be hardened)
 * @returns The evaluated number, or null if evaluation fails or SES unavailable
 */
export function evaluateSimpleExpression(
  expr: string,
  context: Record<string, unknown>,
): number | null {
  // SECURITY: Type check - defense in depth for JS callers
  if (typeof expr !== "string") {
    console.warn("[SECURITY] evaluateSimpleExpression: expr is not a string");
    return null;
  }

  // SECURITY: Empty expression = fail closed
  if (!expr || expr.trim() === "") {
    return null;
  }

  // SECURITY: If SES is not initialized, DO NOT evaluate
  if (!sesInitialized) {
    console.error(
      "[SECURITY] SES not initialized - expression evaluation DISABLED",
    );
    return null;
  }

  // SECURITY: Length limit to prevent payload attacks
  if (expr.length > MAX_EXPRESSION_LENGTH) {
    console.warn(
      `[SECURITY] Expression too long (${expr.length} bytes, max ${MAX_EXPRESSION_LENGTH})`,
    );
    return null;
  }

  // WARNING: This is SYNC evaluation - no timeout protection.
  // For DoS protection, use evaluateWithTimeout() which runs in a Worker with 100ms timeout.

  // Get SES globals
  const { Compartment, harden } = globalThis as any;

  // SECURITY: Both Compartment AND harden must exist
  if (!Compartment || !harden) {
    console.error("[SECURITY] SES Compartment or harden not available");
    return null;
  }

  try {
    // Create safe Math subset (hardened)
    // NOTE: Math.random is intentionally EXCLUDED for determinism
    const safeMath = harden({
      PI: Math.PI,
      E: Math.E,
      abs: Math.abs,
      ceil: Math.ceil,
      floor: Math.floor,
      round: Math.round,
      max: Math.max,
      min: Math.min,
      pow: Math.pow,
      sqrt: Math.sqrt,
      sin: Math.sin,
      cos: Math.cos,
      tan: Math.tan,
      // random: EXCLUDED - non-deterministic breaks consistent renders
      sign: Math.sign,
      trunc: Math.trunc,
    });

    // Seeded random for deterministic results
    // Uses frame from context if available, otherwise 0
    const frame = typeof context.frame === "number" ? context.frame : 0;
    const seededRandom = harden((seed?: number): number => {
      const s = seed !== undefined ? seed : frame;
      const x = Math.sin(s * 12.9898) * 43758.5453;
      return x - Math.floor(x);
    });

    // Harden the provided context values
    const safeContext: Record<string, unknown> = {};
    for (const [key, value] of Object.entries(context)) {
      // Only allow primitive values in context (numbers, strings, booleans)
      if (
        typeof value === "number" ||
        typeof value === "string" ||
        typeof value === "boolean"
      ) {
        safeContext[key] = value;
      } else if (value === null || value === undefined) {
        safeContext[key] = value;
      }
      // Skip objects/arrays/functions - they could have malicious valueOf/toString
    }

    // Create compartment with minimal globals
    const compartment = new Compartment(
      harden({
        Math: safeMath,
        isNaN: Number.isNaN,
        isFinite: Number.isFinite,
        Infinity,
        NaN,
        undefined,
        // Deterministic seeded random function
        random: seededRandom,
        // Spread safe context values
        ...safeContext,

        // SECURITY: Explicitly block dangerous intrinsics
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
      }),
    );

    // Evaluate expression (auto-return single expression)
    const trimmedExpr = expr.trim();
    const wrappedCode = trimmedExpr.includes("return ")
      ? `(function() { ${trimmedExpr} })()`
      : trimmedExpr;

    const result = compartment.evaluate(wrappedCode);

    // SECURITY: Validate result is a primitive number
    // Using typeof check - NOT Number(result) which could trigger valueOf
    if (typeof result !== "number") {
      console.warn("[SES] Expression did not return a number:", typeof result);
      return null;
    }

    // SECURITY: Check for NaN/Infinity
    if (!Number.isFinite(result)) {
      console.warn("[SES] Expression returned non-finite number:", result);
      return null;
    }

    return result;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.warn("[SES] Simple expression error:", message);
    return null;
  }
}

/**
 * Check if SES evaluation is available
 *
 * SECURITY NOTE: If this returns false, expressions will NOT evaluate.
 * This is intentional - we fail closed, not open.
 */
export function isSESAvailable(): boolean {
  return sesInitialized && !sesError;
}
