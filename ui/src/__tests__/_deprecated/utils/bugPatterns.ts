/**
 * Shared Utilities for Common Bug Patterns
 * 
 * These utilities address recurring issues found during the audit:
 * - Float comparison for frame numbers
 * - JSON serialization of special values (-0, NaN, Infinity)
 * - Seed hash functions for RNG
 * - Determinism verification
 * 
 * Use these instead of reimplementing in each file.
 */

// ==============================================================================
// FLOAT COMPARISON (BUG-046, BUG-061)
// ==============================================================================

/**
 * Compare frame numbers with epsilon tolerance.
 * Fixes: Float comparison for frame equality fails due to precision.
 * 
 * @param a First frame number
 * @param b Second frame number
 * @param epsilon Tolerance (default: 0.0001)
 */
export function framesEqual(a: number, b: number, epsilon = 0.0001): boolean {
  return Math.abs(a - b) < epsilon;
}

/**
 * Find keyframe at exact frame with tolerance.
 * Returns undefined if no keyframe at that frame.
 */
export function findKeyframeAtFrame<T extends { frame: number }>(
  keyframes: T[],
  frame: number,
  epsilon = 0.0001
): T | undefined {
  return keyframes.find(k => framesEqual(k.frame, frame, epsilon));
}

// ==============================================================================
// LINEAR INTERPOLATION (BUG-047, BUG-062)
// ==============================================================================

/**
 * Numerically stable linear interpolation.
 * Uses the form a + (b - a) * t which has better precision than (1-t)*a + t*b.
 */
export function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

/**
 * Check if lerp result is exactly the midpoint.
 * Uses tolerance for floating point comparison.
 */
export function isLerpMidpoint(a: number, b: number, result: number, tolerance = 1e-10): boolean {
  const expectedMidpoint = (a + b) / 2;
  return Math.abs(result - expectedMidpoint) < tolerance;
}

// ==============================================================================
// SEED HASHING (BUG-059, BUG-065)
// ==============================================================================

/**
 * MurmurHash3-inspired hash function for seeds.
 * Prevents hash collisions that cause different seeds to produce same output.
 */
export function hashSeed(seed: number): number {
  let h = seed | 0; // Force to 32-bit integer
  
  // Handle seed 0 specially (BUG-026)
  if (h === 0) h = 0x5bd1e995;
  
  h ^= h >>> 16;
  h = Math.imul(h, 0x85ebca6b);
  h ^= h >>> 13;
  h = Math.imul(h, 0xc2b2ae35);
  h ^= h >>> 16;
  
  // Ensure positive result
  return h >>> 0;
}

/**
 * Verify two different seeds produce different hashes.
 * Returns true if hashes are different (good), false if collision (bad).
 */
export function checkSeedCollision(seed1: number, seed2: number): boolean {
  if (seed1 === seed2) return true; // Same seed, same hash is expected
  return hashSeed(seed1) !== hashSeed(seed2);
}

// ==============================================================================
// JSON SERIALIZATION (BUG-035 through BUG-040)
// ==============================================================================

/**
 * JSON serializer that preserves special values.
 * - -0 is preserved (normally becomes 0)
 * - undefined becomes null (normally removed)
 * - NaN/Infinity throw (they become null in standard JSON)
 * - Typed arrays are preserved with metadata
 */
export function serializeWithSpecialValues(value: unknown): string {
  return JSON.stringify(value, (key, val) => {
    // Preserve -0
    if (Object.is(val, -0)) {
      return { __type: 'negativeZero' };
    }
    
    // Convert undefined to explicit null marker
    if (val === undefined) {
      return { __type: 'undefined' };
    }
    
    // Reject NaN and Infinity (they corrupt data)
    if (typeof val === 'number') {
      if (Number.isNaN(val)) {
        throw new Error(`Cannot serialize NaN at key "${key}"`);
      }
      if (!Number.isFinite(val)) {
        throw new Error(`Cannot serialize ${val} at key "${key}"`);
      }
    }
    
    // Preserve typed arrays
    if (val instanceof Float32Array) {
      return { __type: 'Float32Array', data: Array.from(val) };
    }
    if (val instanceof Float64Array) {
      return { __type: 'Float64Array', data: Array.from(val) };
    }
    if (val instanceof Uint8Array) {
      return { __type: 'Uint8Array', data: Array.from(val) };
    }
    if (val instanceof Uint16Array) {
      return { __type: 'Uint16Array', data: Array.from(val) };
    }
    if (val instanceof Int32Array) {
      return { __type: 'Int32Array', data: Array.from(val) };
    }
    
    return val;
  });
}

/**
 * Deserializer that restores special values.
 */
export function deserializeWithSpecialValues(json: string): unknown {
  return JSON.parse(json, (_key, val) => {
    if (val && typeof val === 'object' && '__type' in val) {
      switch (val.__type) {
        case 'negativeZero':
          return -0;
        case 'undefined':
          return undefined;
        case 'Float32Array':
          return new Float32Array(val.data);
        case 'Float64Array':
          return new Float64Array(val.data);
        case 'Uint8Array':
          return new Uint8Array(val.data);
        case 'Uint16Array':
          return new Uint16Array(val.data);
        case 'Int32Array':
          return new Int32Array(val.data);
      }
    }
    return val;
  });
}

/**
 * Verify roundtrip serialization preserves value exactly.
 */
export function verifyRoundtrip<T>(value: T, compareFn?: (a: T, b: T) => boolean): boolean {
  try {
    const serialized = serializeWithSpecialValues(value);
    const restored = deserializeWithSpecialValues(serialized) as T;
    
    if (compareFn) {
      return compareFn(value, restored);
    }
    
    // Deep equality check
    return JSON.stringify(value) === JSON.stringify(restored);
  } catch {
    return false;
  }
}

// ==============================================================================
// DETERMINISM VERIFICATION
// ==============================================================================

/**
 * Run a function multiple times and verify all results are identical.
 * For testing deterministic behavior.
 */
export function verifyDeterminism<T>(
  fn: () => T,
  runs: number = 100,
  compareFn?: (a: T, b: T) => boolean
): { deterministic: boolean; results: T[] } {
  const results: T[] = [];
  
  for (let i = 0; i < runs; i++) {
    results.push(fn());
  }
  
  const reference = results[0];
  const compare = compareFn || ((a, b) => JSON.stringify(a) === JSON.stringify(b));
  
  const deterministic = results.every(r => compare(reference, r));
  
  return { deterministic, results };
}

/**
 * Compare ImageData for exact pixel equality.
 */
export function imageDataEqual(a: ImageData, b: ImageData): boolean {
  if (a.width !== b.width || a.height !== b.height) return false;
  
  for (let i = 0; i < a.data.length; i++) {
    if (a.data[i] !== b.data[i]) return false;
  }
  
  return true;
}

// ==============================================================================
// VALUE CLAMPING AND VALIDATION
// ==============================================================================

/**
 * Clamp value to range and handle NaN/Infinity.
 * Returns fallback for invalid values.
 */
export function safeClamp(value: number, min: number, max: number, fallback: number): number {
  if (!Number.isFinite(value)) return fallback;
  return Math.max(min, Math.min(max, value));
}

/**
 * Validate depth range (BUG-001, BUG-002).
 * Ensures near < far and both are positive finite values.
 */
export function validateDepthRange(
  near: number,
  far: number
): { valid: boolean; near: number; far: number; error?: string } {
  if (!Number.isFinite(near) || near <= 0) {
    return { valid: false, near: 0.1, far, error: 'nearClip must be positive finite' };
  }
  if (!Number.isFinite(far) || far <= 0) {
    return { valid: false, near, far: 1000, error: 'farClip must be positive finite' };
  }
  if (near >= far) {
    return { valid: false, near, far, error: 'nearClip must be less than farClip' };
  }
  return { valid: true, near, far };
}

/**
 * Ensure alpha channel is always 255 (BUG-009).
 */
export function ensureOpaqueAlpha(imageData: ImageData): void {
  for (let i = 3; i < imageData.data.length; i += 4) {
    imageData.data[i] = 255;
  }
}

/**
 * Enforce binary mask values (BUG-018).
 */
export function enforceBinaryMask(imageData: ImageData, threshold = 127): void {
  for (let i = 0; i < imageData.data.length; i += 4) {
    const value = imageData.data[i] > threshold ? 255 : 0;
    imageData.data[i] = value;
    imageData.data[i + 1] = value;
    imageData.data[i + 2] = value;
    imageData.data[i + 3] = 255;
  }
}

// ==============================================================================
// TEST HELPERS
// ==============================================================================

/**
 * Create test counterexample from bug report.
 * Use this to ensure regression tests use exact values.
 */
export function createCounterexample<T extends Record<string, unknown>>(
  bugId: string,
  values: T
): T & { __bugId: string } {
  return { ...values, __bugId: bugId };
}

/**
 * Seeds that have caused bugs (from COMPREHENSIVE_BUG_REPORT.md).
 * Use these for regression testing.
 */
export const KNOWN_BAD_SEEDS = {
  'BUG-001': -1249449431,
  'BUG-002': -1642374030,
  'BUG-018': 122771531,
  'BUG-019': -1113950213,
  'BUG-020': 411036484,
  'BUG-026': 0, // Seed 0 catastrophic failure
  'BUG-027': 1062795911,
  'BUG-028': 730057176,
  'BUG-029': 244871912,
  'BUG-034': 1715486422,
  'BUG-041': 2076192896,
  'BUG-042': 778967537,
  'BUG-043': 1884774886,
  'BUG-044': -491268369,
  'BUG-045': -1232366547,
  'BUG-046': -790379486,
  'BUG-047': -1617449551,
  'BUG-048': -644889241,
  'BUG-049': -1836635708,
  'BUG-050': 1770533153,
  'BUG-059': -1743549297,
  'BUG-060': -335209887,
  'BUG-061': 1228890611,
  'BUG-062': -1230355288,
  'BUG-063': -435931602,
  'BUG-064': -266685938,
  'BUG-065': -1945269044,
} as const;
