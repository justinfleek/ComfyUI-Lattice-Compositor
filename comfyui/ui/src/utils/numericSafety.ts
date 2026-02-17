// ============================================================================
// NUMERIC SAFETY UTILITIES
// ============================================================================
// Guards against NaN, Infinity, division by zero, and other numeric edge cases.
// Use these in hot paths: interpolation, transforms, physics, particles.
// ============================================================================

// ============================================================================
// BASIC SAFETY
// ============================================================================

/**
 * Ensure a value is a finite number, returning fallback if not.
 * Use this for any value that might be NaN, Infinity, or non-numeric.
 */
export function ensureFinite(value: unknown, fallback: number): number {
  if (typeof value !== "number") return fallback;
  if (!Number.isFinite(value)) return fallback;
  return value;
}

/**
 * Require a value to be a finite number, throwing if not.
 * Use at boundaries where invalid data should crash.
 */
export function requireFinite(value: unknown, name: string): number {
  if (typeof value !== "number") {
    throw new TypeError(`${name} must be a number, got ${typeof value}`);
  }
  if (Number.isNaN(value)) {
    throw new TypeError(`${name} must not be NaN`);
  }
  if (!Number.isFinite(value)) {
    throw new TypeError(`${name} must be finite, got ${value}`);
  }
  return value;
}

// ============================================================================
// SAFE ARITHMETIC
// ============================================================================

/**
 * Safe division - returns fallback instead of Infinity or NaN.
 */
export function safeDivide(
  numerator: number,
  denominator: number,
  fallback: number,
): number {
  if (denominator === 0) return fallback;
  const result = numerator / denominator;
  if (!Number.isFinite(result)) return fallback;
  return result;
}

/**
 * Safe modulo - always returns positive result, handles zero divisor.
 * Unlike JS %, this always returns a positive value.
 */
export function safeMod(value: number, divisor: number): number {
  if (divisor === 0) return 0;
  const result = ((value % divisor) + divisor) % divisor;
  if (!Number.isFinite(result)) return 0;
  return result;
}

/**
 * Safe square root - returns 0 for negative numbers instead of NaN.
 */
export function safeSqrt(value: number): number {
  if (value < 0) return 0;
  if (!Number.isFinite(value)) return 0;
  return Math.sqrt(value);
}

/**
 * Safe power - handles edge cases.
 */
export function safePow(base: number, exponent: number, fallback = 0): number {
  const result = Math.pow(base, exponent);
  if (!Number.isFinite(result)) return fallback;
  return result;
}

/**
 * Safe log - handles zero and negative numbers.
 */
export function safeLog(value: number, fallback = 0): number {
  if (value <= 0) return fallback;
  const result = Math.log(value);
  if (!Number.isFinite(result)) return fallback;
  return result;
}

// ============================================================================
// CLAMPING
// ============================================================================

/**
 * Clamp a value between min and max.
 * Handles NaN by returning min.
 */
export function clamp(value: number, min: number, max: number): number {
  if (Number.isNaN(value)) return min;
  if (value < min) return min;
  if (value > max) return max;
  return value;
}

/**
 * Clamp a value to [0, 1] range.
 */
export function clamp01(value: number): number {
  return clamp(value, 0, 1);
}

/**
 * Clamp a value to [0, 100] range (for percentages).
 */
export function clamp0100(value: number): number {
  return clamp(value, 0, 100);
}

/**
 * Clamp a value to [0, 255] range (for color channels).
 */
export function clamp0255(value: number): number {
  return clamp(value, 0, 255);
}

/**
 * Clamp a value to [-1, 1] range.
 */
export function clampNeg1To1(value: number): number {
  return clamp(value, -1, 1);
}

// ============================================================================
// INTERPOLATION
// ============================================================================

/**
 * Safe linear interpolation - clamps t to [0, 1] and ensures finite result.
 */
export function safeLerp(a: number, b: number, t: number): number {
  const safeA = ensureFinite(a, 0);
  const safeB = ensureFinite(b, 0);
  const safeT = clamp01(ensureFinite(t, 0));

  // Check for overflow in (b - a)
  const diff = safeB - safeA;
  if (!Number.isFinite(diff)) {
    // Fallback: use the mathematically equivalent but more stable formula
    // lerp(a, b, t) = a*(1-t) + b*t
    const result = safeA * (1 - safeT) + safeB * safeT;
    return ensureFinite(result, safeA);
  }

  return safeA + diff * safeT;
}

/**
 * Unclamped lerp - allows t outside [0, 1] but still ensures finite result.
 */
export function safeLerpUnclamped(a: number, b: number, t: number): number {
  const safeA = ensureFinite(a, 0);
  const safeB = ensureFinite(b, 0);
  const safeT = ensureFinite(t, 0);

  // Check for overflow in (b - a)
  const diff = safeB - safeA;
  if (!Number.isFinite(diff)) {
    // Fallback: use the mathematically equivalent but more stable formula
    const result = safeA * (1 - safeT) + safeB * safeT;
    return ensureFinite(result, safeA);
  }

  const result = safeA + diff * safeT;
  return ensureFinite(result, safeA);
}

/**
 * Safe inverse lerp - returns where value falls between a and b as [0, 1].
 * Returns 0 if a === b (zero range).
 */
export function safeInverseLerp(a: number, b: number, value: number): number {
  const safeA = ensureFinite(a, 0);
  const safeB = ensureFinite(b, 0);
  const safeValue = ensureFinite(value, 0);

  const range = safeB - safeA;
  if (range === 0) return 0;

  return clamp01((safeValue - safeA) / range);
}

/**
 * Safe remap - remaps value from [inMin, inMax] to [outMin, outMax].
 */
export function safeRemap(
  value: number,
  inMin: number,
  inMax: number,
  outMin: number,
  outMax: number,
): number {
  const t = safeInverseLerp(inMin, inMax, value);
  return safeLerp(outMin, outMax, t);
}

/**
 * Smooth step interpolation - smooth Hermite interpolation.
 */
export function smoothStep(a: number, b: number, t: number): number {
  const safeT = clamp01(ensureFinite(t, 0));
  const smooth = safeT * safeT * (3 - 2 * safeT);
  return safeLerp(a, b, smooth);
}

/**
 * Smoother step - Ken Perlin's improved smooth step.
 */
export function smootherStep(a: number, b: number, t: number): number {
  const safeT = clamp01(ensureFinite(t, 0));
  const smooth = safeT * safeT * safeT * (safeT * (safeT * 6 - 15) + 10);
  return safeLerp(a, b, smooth);
}

// ============================================================================
// 2D VECTOR SAFETY
// ============================================================================

/**
 * Safe 2D vector normalization - returns zero vector for zero-length input.
 */
export function safeNormalize2D(
  x: number,
  y: number,
): { x: number; y: number } {
  const safeX = ensureFinite(x, 0);
  const safeY = ensureFinite(y, 0);

  const lengthSq = safeX * safeX + safeY * safeY;
  if (lengthSq === 0) return { x: 0, y: 0 };

  const length = Math.sqrt(lengthSq);
  if (length === 0) return { x: 0, y: 0 };

  return {
    x: safeX / length,
    y: safeY / length,
  };
}

/**
 * Safe 2D distance calculation.
 */
export function safeDistance2D(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
): number {
  const dx = ensureFinite(x2, 0) - ensureFinite(x1, 0);
  const dy = ensureFinite(y2, 0) - ensureFinite(y1, 0);
  return safeSqrt(dx * dx + dy * dy);
}

/**
 * Safe 2D length calculation.
 */
export function safeLength2D(x: number, y: number): number {
  const safeX = ensureFinite(x, 0);
  const safeY = ensureFinite(y, 0);
  return safeSqrt(safeX * safeX + safeY * safeY);
}

/**
 * Safe 2D dot product.
 */
export function safeDot2D(
  x1: number,
  y1: number,
  x2: number,
  y2: number,
): number {
  const result =
    ensureFinite(x1, 0) * ensureFinite(x2, 0) +
    ensureFinite(y1, 0) * ensureFinite(y2, 0);
  return ensureFinite(result, 0);
}

// ============================================================================
// 3D VECTOR SAFETY
// ============================================================================

/**
 * Safe 3D vector normalization.
 */
export function safeNormalize3D(
  x: number,
  y: number,
  z: number,
): { x: number; y: number; z: number } {
  const safeX = ensureFinite(x, 0);
  const safeY = ensureFinite(y, 0);
  const safeZ = ensureFinite(z, 0);

  const lengthSq = safeX * safeX + safeY * safeY + safeZ * safeZ;
  if (lengthSq === 0) return { x: 0, y: 0, z: 0 };

  const length = Math.sqrt(lengthSq);
  if (length === 0) return { x: 0, y: 0, z: 0 };

  return {
    x: safeX / length,
    y: safeY / length,
    z: safeZ / length,
  };
}

/**
 * Safe 3D distance calculation.
 */
export function safeDistance3D(
  x1: number,
  y1: number,
  z1: number,
  x2: number,
  y2: number,
  z2: number,
): number {
  const dx = ensureFinite(x2, 0) - ensureFinite(x1, 0);
  const dy = ensureFinite(y2, 0) - ensureFinite(y1, 0);
  const dz = ensureFinite(z2, 0) - ensureFinite(z1, 0);
  return safeSqrt(dx * dx + dy * dy + dz * dz);
}

/**
 * Safe 3D length calculation.
 */
export function safeLength3D(x: number, y: number, z: number): number {
  const safeX = ensureFinite(x, 0);
  const safeY = ensureFinite(y, 0);
  const safeZ = ensureFinite(z, 0);
  return safeSqrt(safeX * safeX + safeY * safeY + safeZ * safeZ);
}

// ============================================================================
// ANGLE SAFETY
// ============================================================================

/**
 * Normalize angle to [0, 360) degrees.
 */
export function normalizeAngleDegrees(angle: number): number {
  const safe = ensureFinite(angle, 0);
  return safeMod(safe, 360);
}

/**
 * Normalize angle to [0, 2*PI) radians.
 */
export function normalizeAngleRadians(angle: number): number {
  const safe = ensureFinite(angle, 0);
  return safeMod(safe, Math.PI * 2);
}

/**
 * Normalize angle to [-180, 180) degrees.
 */
export function normalizeAngleDegreesSymmetric(angle: number): number {
  const normalized = normalizeAngleDegrees(angle);
  return normalized > 180 ? normalized - 360 : normalized;
}

/**
 * Normalize angle to [-PI, PI) radians.
 */
export function normalizeAngleRadiansSymmetric(angle: number): number {
  const normalized = normalizeAngleRadians(angle);
  return normalized > Math.PI ? normalized - Math.PI * 2 : normalized;
}

/**
 * Convert degrees to radians safely.
 */
export function degreesToRadians(degrees: number): number {
  return ensureFinite(degrees, 0) * (Math.PI / 180);
}

/**
 * Convert radians to degrees safely.
 */
export function radiansToDegrees(radians: number): number {
  return ensureFinite(radians, 0) * (180 / Math.PI);
}

/**
 * Shortest angular distance between two angles in degrees.
 */
export function shortestAngleDifferenceDegrees(from: number, to: number): number {
  const diff = normalizeAngleDegreesSymmetric(to - from);
  return diff;
}

/**
 * Lerp between angles using shortest path (degrees).
 */
export function lerpAngleDegrees(from: number, to: number, t: number): number {
  const diff = shortestAngleDifferenceDegrees(from, to);
  return normalizeAngleDegrees(from + diff * clamp01(ensureFinite(t, 0)));
}

// ============================================================================
// COMPARISON
// ============================================================================

/**
 * Check if two numbers are approximately equal.
 * Uses relative epsilon for large numbers, absolute for small.
 */
export function approximately(
  a: number,
  b: number,
  epsilon = 1e-6,
): boolean {
  const safeA = ensureFinite(a, 0);
  const safeB = ensureFinite(b, 0);
  const diff = Math.abs(safeA - safeB);

  // For values near zero, use absolute comparison
  if (Math.abs(safeA) < 1 && Math.abs(safeB) < 1) {
    return diff < epsilon;
  }

  // For larger values, use relative comparison
  const maxAbs = Math.max(Math.abs(safeA), Math.abs(safeB));
  return diff < epsilon * maxAbs;
}

/**
 * Check if a value is approximately zero.
 */
export function isApproximatelyZero(value: number, epsilon = 1e-6): boolean {
  return Math.abs(ensureFinite(value, 0)) < epsilon;
}

// ============================================================================
// ROUNDING
// ============================================================================

/**
 * Round to specified decimal places.
 * Handles NaN by returning 0.
 */
export function roundTo(value: number, decimals: number): number {
  const safe = ensureFinite(value, 0);
  const factor = Math.pow(10, Math.max(0, Math.floor(decimals)));
  return Math.round(safe * factor) / factor;
}

/**
 * Floor to specified decimal places.
 */
export function floorTo(value: number, decimals: number): number {
  const safe = ensureFinite(value, 0);
  const factor = Math.pow(10, Math.max(0, Math.floor(decimals)));
  return Math.floor(safe * factor) / factor;
}

/**
 * Ceil to specified decimal places.
 */
export function ceilTo(value: number, decimals: number): number {
  const safe = ensureFinite(value, 0);
  const factor = Math.pow(10, Math.max(0, Math.floor(decimals)));
  return Math.ceil(safe * factor) / factor;
}

/**
 * Snap value to nearest multiple of step.
 */
export function snapTo(value: number, step: number): number {
  if (step === 0) return ensureFinite(value, 0);
  const safe = ensureFinite(value, 0);
  const safeStep = ensureFinite(step, 1);
  return Math.round(safe / safeStep) * safeStep;
}

// ============================================================================
// RANGE UTILITIES
// ============================================================================

/**
 * Check if value is in range [min, max] inclusive.
 */
export function inRange(
  value: number,
  min: number,
  max: number,
): boolean {
  const safe = ensureFinite(value, min - 1); // Default outside range
  return safe >= min && safe <= max;
}

/**
 * Wrap value to range [min, max).
 */
export function wrapToRange(value: number, min: number, max: number): number {
  const safe = ensureFinite(value, min);
  const range = max - min;
  if (range === 0) return min;
  return min + safeMod(safe - min, range);
}

/**
 * Ping-pong value between min and max.
 */
export function pingPong(value: number, min: number, max: number): number {
  const safe = ensureFinite(value, min);
  const range = max - min;
  if (range === 0) return min;

  const wrapped = safeMod(safe - min, range * 2);
  if (wrapped < range) {
    return min + wrapped;
  }
  return max - (wrapped - range);
}
