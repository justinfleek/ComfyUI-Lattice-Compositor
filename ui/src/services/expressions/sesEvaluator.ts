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
 *
 * This replaces the previous Proxy+with sandbox (BUG-006) which was bypassable.
 *
 * @see AUDIT/SECURITY_ARCHITECTURE.md for full security analysis
 */

import type { ExpressionContext } from './types';

// SES lockdown status
let sesInitialized = false;
let sesError: Error | null = null;

/**
 * Initialize SES lockdown
 *
 * CRITICAL: This must be called ONCE at application startup, before any other code.
 * It freezes all JavaScript intrinsics to prevent prototype pollution.
 *
 * Call this in your main.ts or App.vue before mounting the app.
 */
export async function initializeSES(): Promise<boolean> {
  if (sesInitialized) {
    return true;
  }

  try {
    // Dynamically import SES (side effects add lockdown to globalThis)
    await import('ses');

    // Get lockdown from globalThis (SES adds it via side effects)
    const { lockdown } = globalThis as any;

    if (!lockdown) {
      throw new Error('SES lockdown function not found on globalThis');
    }

    // Lockdown configuration
    // See: https://github.com/endojs/endo/blob/master/packages/ses/docs/lockdown.md
    lockdown({
      // Allow console for debugging (set to 'safe' in production for security)
      consoleTaming: 'unsafe',

      // Preserve error stacks for debugging (set to 'safe' in production)
      errorTaming: 'unsafe',

      // Show full stack traces
      stackFiltering: 'verbose',

      // Maximum prototype protection
      overrideTaming: 'severe',

      // Don't tame locale methods (needed for number formatting)
      localeTaming: 'unsafe',

      // Tame Math.random for determinism (optional - disable if random needed)
      // mathTaming: 'unsafe',

      // Tame Date.now for determinism (optional - disable if real time needed)
      // dateTaming: 'unsafe',
    });

    sesInitialized = true;
    console.log('[SES] Lockdown complete - JavaScript intrinsics are now frozen');
    return true;
  } catch (error) {
    sesError = error instanceof Error ? error : new Error(String(error));
    console.error('[SES] Failed to initialize:', sesError);
    return false;
  }
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
    throw new Error('[SES] Not initialized. Call initializeSES() at app startup.');
  }

  // Import Compartment from SES (available after lockdown)
  const { Compartment, harden } = (globalThis as any);

  if (!Compartment) {
    throw new Error('[SES] Compartment not available. Ensure lockdown() was called.');
  }

  // Create safe Math object (harden to prevent modification)
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
    random: Math.random,
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
    linear: (t: number, tMin: number, tMax: number, vMin: number, vMax: number): number => {
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
    radiansToDegrees: (rad: number): number => rad * 180 / Math.PI,
    degreesToRadians: (deg: number): number => deg * Math.PI / 180,

    // Time conversion
    timeToFrames: (t: number = ctx.time): number => Math.round(t * ctx.fps),
    framesToTime: (f: number): number => f / ctx.fps,

    // Degree-based trig
    sinDeg: (deg: number): number => Math.sin(deg * Math.PI / 180),
    cosDeg: (deg: number): number => Math.cos(deg * Math.PI / 180),
    tanDeg: (deg: number): number => Math.tan(deg * Math.PI / 180),

    // Vector operations (basic)
    length: (a: number | number[], b?: number | number[]): number => {
      if (b === undefined) {
        if (typeof a === 'number') return Math.abs(a);
        return Math.sqrt(a.reduce((sum: number, v: number) => sum + v * v, 0));
      }
      if (typeof a === 'number' && typeof b === 'number') {
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
      if (typeof a === 'number' && typeof b === 'number') return a + b;
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
      if (typeof a === 'number' && typeof b === 'number') return a - b;
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
      if (typeof a === 'number' && typeof b === 'number') return a * b;
      if (typeof b === 'number' && Array.isArray(a)) {
        return a.map(v => v * b);
      }
      if (typeof a === 'number' && Array.isArray(b)) {
        return b.map(v => v * a);
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
      if (typeof a === 'number' && typeof b === 'number') return a / (b || 1);
      if (typeof b === 'number' && Array.isArray(a)) {
        return a.map(v => v / (b || 1));
      }
      if (typeof a === 'number' && Array.isArray(b)) {
        return b.map(v => a / (v || 1));
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
    velocity: Array.isArray(ctx.velocity) ? harden([...ctx.velocity]) : ctx.velocity,
    numKeys: ctx.numKeys,

    // Utility functions
    ...utilities,

    // Console for debugging (limited)
    console: harden({
      log: (...args: any[]) => console.log('[Expression]', ...args),
      warn: (...args: any[]) => console.warn('[Expression]', ...args),
    }),
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
export function evaluateInSES(code: string, ctx: ExpressionContext): number | number[] | string {
  if (!code || code.trim() === '') {
    return ctx.value;
  }

  // SECURITY: If SES is not initialized, DO NOT evaluate - return passthrough
  // This is intentional. We fail CLOSED, not open.
  if (!sesInitialized) {
    console.error('[SECURITY] SES not initialized - expression evaluation DISABLED for security');
    console.error('[SECURITY] Call initializeSES() at app startup to enable expressions');
    return ctx.value;
  }

  try {
    const compartment = createExpressionCompartment(ctx);

    // Auto-return the last expression if code doesn't contain explicit return
    const needsReturn = !code.includes('return ') && !code.includes('return;');
    const processedCode = needsReturn
      ? code.trim().split('\n').map((line, i, arr) =>
          i === arr.length - 1 && !line.trim().startsWith('//') && line.trim().length > 0
            ? `return ${line}`
            : line
        ).join('\n')
      : code;

    // Wrap in IIFE for proper return handling
    const wrappedCode = `(function() { ${processedCode} })()`;

    // Evaluate in compartment
    const result = compartment.evaluate(wrappedCode);

    return result;
  } catch (error) {
    const message = error instanceof Error ? error.message : String(error);
    console.warn('[SES] Expression error:', message);
    return ctx.value;
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
