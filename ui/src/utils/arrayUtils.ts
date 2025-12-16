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
  maxValue: number = Math.max(...values)
): number[] {
  const safeMax = maxValue || 0.0001; // Prevent division by zero
  return values.map(v => v / safeMax);
}

/**
 * Normalize array in place (mutates original array)
 * More efficient for large arrays when you don't need the original
 * @param values - Array to normalize in place
 * @param maxValue - Optional max value (defaults to array max)
 */
export function normalizeInPlace(
  values: number[],
  maxValue: number = Math.max(...values)
): void {
  const safeMax = maxValue || 0.0001;
  for (let i = 0; i < values.length; i++) {
    values[i] = values[i] / safeMax;
  }
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
  outMax: number
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

/**
 * Calculate the standard deviation of an array
 * @param values - Array of numbers
 */
export function standardDeviation(values: number[]): number {
  if (values.length === 0) return 0;
  const avg = mean(values);
  const squareDiffs = values.map(v => Math.pow(v - avg, 2));
  return Math.sqrt(mean(squareDiffs));
}

/**
 * Smooth an array using a simple moving average
 * @param values - Array of numbers
 * @param windowSize - Size of the smoothing window
 */
export function smoothMovingAverage(
  values: number[],
  windowSize: number
): number[] {
  if (windowSize <= 1) return [...values];

  const result: number[] = [];
  const halfWindow = Math.floor(windowSize / 2);

  for (let i = 0; i < values.length; i++) {
    const start = Math.max(0, i - halfWindow);
    const end = Math.min(values.length, i + halfWindow + 1);
    let sum = 0;
    for (let j = start; j < end; j++) {
      sum += values[j];
    }
    result.push(sum / (end - start));
  }

  return result;
}

/**
 * Find local maxima (peaks) in an array
 * @param values - Array of numbers
 * @param threshold - Minimum value to be considered a peak
 */
export function findPeaks(values: number[], threshold: number = 0): number[] {
  const peaks: number[] = [];

  for (let i = 1; i < values.length - 1; i++) {
    if (
      values[i] > threshold &&
      values[i] > values[i - 1] &&
      values[i] > values[i + 1]
    ) {
      peaks.push(i);
    }
  }

  return peaks;
}

/**
 * Downsample an array by averaging groups of samples
 * @param values - Array to downsample
 * @param factor - Downsampling factor
 */
export function downsample(values: number[], factor: number): number[] {
  if (factor <= 1) return [...values];

  const result: number[] = [];
  for (let i = 0; i < values.length; i += factor) {
    const end = Math.min(i + factor, values.length);
    let sum = 0;
    for (let j = i; j < end; j++) {
      sum += values[j];
    }
    result.push(sum / (end - i));
  }

  return result;
}
