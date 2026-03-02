/**
 * Jitter Expressions Module
 *
 * Expression functions for adding noise/randomness:
 * - jitter: Simple noise based on sine waves
 * - temporalJitter: Smooth noise with Catmull-Rom interpolation
 */

import { isFiniteNumber } from "@/utils/typeGuards";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/**
 * Minimal expression context for jitter expressions
 */
export interface JitterExpressionContext {
  time: number;
  value: number | number[];
}

// ════════════════════════════════════════════════════════════════════════════
//                                                     // jitter // expressions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Jitter expression
 * Adds random noise to value
 */
export function jitter(
  ctx: JitterExpressionContext,
  frequency: number = 5,
  amplitude: number = 50,
  octaves: number = 1,
  amplitudeMultiplier: number = 0.5,
  time?: number,
): number | number[] {
  // Type proof: number | undefined → number
  const t = isFiniteNumber(time) ? time : ctx.time;
  const { value } = ctx;

  // Guard against invalid octaves (prevents infinite loop)
  if (!Number.isFinite(octaves) || octaves < 1) {
    octaves = 1;
  } else if (octaves > 10) {
    octaves = 10; // Cap at 10 - more octaves add negligible detail
  }
  octaves = Math.floor(octaves);

  // Simple noise implementation
  const noise = (seed: number, t: number): number => {
    // Combine multiple sine waves for pseudo-noise
    let result = 0;
    let amp = 1;
    let freq = 1;

    for (let i = 0; i < octaves; i++) {
      result +=
        amp * Math.sin(t * frequency * freq * Math.PI * 2 + seed * 1000);
      result +=
        amp *
        0.5 *
        Math.sin(t * frequency * freq * Math.PI * 2 * 1.5 + seed * 500);
      amp *= amplitudeMultiplier;
      freq *= 2;
    }

    // Guard against division by zero
    const denominator = 1 + (octaves - 1) * amplitudeMultiplier;
    if (!Number.isFinite(denominator) || denominator === 0) {
      return result; // Return unnormalized if normalization factor is invalid
    }
    return result / denominator;
  };

  if (typeof value === "number") {
    return value + noise(0, t) * amplitude;
  }

  // For arrays, use different seeds for each component
  return (value as number[]).map((v, i) => v + noise(i, t) * amplitude);
}

/**
 * Smooth jitter with temporal correlation
 */
export function temporalJitter(
  ctx: JitterExpressionContext,
  frequency: number = 5,
  amplitude: number = 50,
  octaves: number = 1,
  time?: number,
): number | number[] {
  // Type proof: number | undefined → number
  const t = isFiniteNumber(time) ? time : ctx.time;

  // Guard against invalid frequency (prevents division by zero)
  if (!Number.isFinite(frequency) || frequency <= 0) {
    frequency = 5; // Use default frequency
  }

  // Guard against invalid octaves (prevents infinite loop)
  if (!Number.isFinite(octaves) || octaves < 1) {
    octaves = 1;
  } else if (octaves > 10) {
    octaves = 10; // Cap at 10 - more octaves add negligible detail
  }
  octaves = Math.floor(octaves);

  // Use interpolated noise for smoother results
  const smoothNoise = (seed: number, t: number): number => {
    const period = 1 / frequency;
    const index = Math.floor(t / period);
    const frac = t / period - index;

    // Generate deterministic random values
    const rand = (n: number) => {
      const x = Math.sin(n * 12.9898 + seed * 78.233) * 43758.5453;
      return x - Math.floor(x);
    };

    // Cubic interpolation between random values
    const v0 = rand(index - 1) * 2 - 1;
    const v1 = rand(index) * 2 - 1;
    const v2 = rand(index + 1) * 2 - 1;
    const v3 = rand(index + 2) * 2 - 1;

    // Catmull-Rom interpolation
    const t2 = frac * frac;
    const t3 = t2 * frac;

    return (
      0.5 *
      (2 * v1 +
        (-v0 + v2) * frac +
        (2 * v0 - 5 * v1 + 4 * v2 - v3) * t2 +
        (-v0 + 3 * v1 - 3 * v2 + v3) * t3)
    );
  };

  const { value } = ctx;

  if (typeof value === "number") {
    let result = 0;
    let amp = amplitude;
    let freq = frequency;
    for (let i = 0; i < octaves; i++) {
      result += smoothNoise(i * 100, (t * freq) / frequency) * amp;
      amp *= 0.5;
      freq *= 2;
    }
    return value + result;
  }

  return (value as number[]).map((v, idx) => {
    let result = 0;
    let amp = amplitude;
    let freq = frequency;
    for (let i = 0; i < octaves; i++) {
      result += smoothNoise(idx * 100 + i * 1000, (t * freq) / frequency) * amp;
      amp *= 0.5;
      freq *= 2;
    }
    return v + result;
  });
}
