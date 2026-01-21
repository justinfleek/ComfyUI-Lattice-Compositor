/**
 * Array Utility Functions
 *
 * Common array operations used throughout the codebase.
 * Centralized to reduce duplication and ensure consistent behavior.
 */

/**
 * Normalize an array of numbers to the range [0, 1]
 * @param values - Array of numbers to normalize
 * @param maxValue - Optional max value (defaults to array max)
 * @returns Normalized array with values in [0, 1] range
 */
export function normalize(
  values: number[],
  maxValue: number = Math.max(...values),
): number[] {
  // Type proof: maxValue ∈ number | NaN → number (> 0, must be positive for division)
  const safeMax = Number.isFinite(maxValue) && maxValue > 0 ? maxValue : 0.0001;
  return values.map((v) => v / safeMax);
}

/**
 * Clamp a value to a range
 * @param value - Value to clamp
 * @param min - Minimum value
 * @param max - Maximum value
 */
export function clamp(value: number, min: number, max: number): number {
  return Math.max(min, Math.min(max, value));
}

/**
 * Linear interpolation between two values
 * @param a - Start value
 * @param b - End value
 * @param t - Interpolation factor (0-1)
 */
export function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}

/**
 * Map a value from one range to another
 * @param value - Value to map
 * @param inMin - Input range minimum
 * @param inMax - Input range maximum
 * @param outMin - Output range minimum
 * @param outMax - Output range maximum
 */
export function mapRange(
  value: number,
  inMin: number,
  inMax: number,
  outMin: number,
  outMax: number,
): number {
  const normalized = (value - inMin) / (inMax - inMin);
  return outMin + normalized * (outMax - outMin);
}

/**
 * Calculate the mean of an array
 * @param values - Array of numbers
 */
export function mean(values: number[]): number {
  if (values.length === 0) return 0;
  return values.reduce((sum, v) => sum + v, 0) / values.length;
}
