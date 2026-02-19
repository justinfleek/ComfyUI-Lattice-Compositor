/**
 * Motion Expressions Module
 *
 * Expression functions for momentum-based animations:
 * - inertia: Momentum after keyframes with decay
 * - bounce: Bouncing settle physics
 * - elastic: Spring-like elastic motion
 */

import type { Keyframe } from "@/types/project";
import { isFiniteNumber } from "@/utils/typeGuards";

/**
 * Minimal expression context for motion expressions
 * (Avoids circular dependency with main expressions.ts)
 */
export interface MotionExpressionContext {
  time: number;
  fps: number;
  keyframes: Keyframe<number | number[]>[];
  value: number | number[];
  velocity: number | number[];
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                   // helpers
// ════════════════════════════════════════════════════════════════════════════

/**
 * Convert value to array format for consistent processing.
 * Handles both array [x, y, z] and object {x, y, z} formats.
 * Prevents crashes with object-style vectors by normalizing to arrays.
 */
function toArray(value: number | number[] | { x: number; y: number; z?: number }): number[] {
  if (typeof value === 'number') {
    return [value];
  }
  if (Array.isArray(value)) {
    return value;
  }
  // Object format {x, y} or {x, y, z}
  if (typeof value === 'object' && value !== null && 'x' in value && 'y' in value) {
    const arr = [value.x, value.y];
    if ('z' in value && value.z !== undefined) {
      arr.push(value.z);
    }
    return arr;
  }
  // Fallback: return as single-element array or empty
  return [0];
}

/**
 * Convert array back to original format based on original value structure
 */
function fromArray(
  arr: number[],
  originalValue: number | number[] | { x: number; y: number; z?: number }
): number | number[] | { x: number; y: number; z?: number } {
  if (typeof originalValue === 'number') {
    // Type proof: arr[0] ∈ number | undefined → number
    return isFiniteNumber(arr[0]) ? arr[0] : 0;
  }
  if (Array.isArray(originalValue)) {
    return arr;
  }
  // Object format
  if (typeof originalValue === 'object' && originalValue !== null && 'x' in originalValue) {
    // Type proof: arr[0] ∈ number | undefined → number
    const x = isFiniteNumber(arr[0]) ? arr[0] : 0;
    // Type proof: arr[1] ∈ number | undefined → number
    const y = isFiniteNumber(arr[1]) ? arr[1] : 0;
    const result: { x: number; y: number; z?: number } = {
      x,
      y,
    };
    if ('z' in originalValue && originalValue.z !== undefined) {
      // Type proof: arr[2] ∈ number | undefined → number
      result.z = isFiniteNumber(arr[2]) ? arr[2] : 0;
    }
    return result;
  }
  return arr;
}

// ════════════════════════════════════════════════════════════════════════════
//                                                     // motion // expressions
// ════════════════════════════════════════════════════════════════════════════

/**
 * Inertia/Overshoot expression
 * Creates momentum-based animation after keyframes
 */
export function inertia(
  ctx: MotionExpressionContext,
  amplitude: number = 0.1,
  frequency: number = 2.0,
  decay: number = 2.0,
): number | number[] {
  const { time, keyframes, value, velocity } = ctx;

  // Validate parameters
  const safeAmplitude = Number.isFinite(amplitude) ? amplitude : 0.1;
  const safeFrequency = Number.isFinite(frequency) ? frequency : 2.0;
  const safeDecay = Number.isFinite(decay) ? Math.max(0.001, decay) : 2.0;

  if (keyframes.length === 0) return value;

  // Find nearest keyframe before current time
  // Type proof: fps ∈ number | undefined → number
  const fps = isFiniteNumber(ctx.fps) && ctx.fps > 0
    ? ctx.fps
    : 16;
  const currentFrame = time * fps;

  let nearestKey: Keyframe<number | number[]> | null = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      nearestKey = keyframes[i];
      break;
    }
  }

  if (!nearestKey) return value;

  const keyTime = nearestKey.frame / fps;
  const t = time - keyTime;

  if (t <= 0) return value;

  // Convert to arrays for consistent processing
  const valueArr = toArray(value);
  const velocityArr = toArray(velocity);

  // Apply oscillation to each component
  const resultArr = valueArr.map((v, i) => {
    // Type proof: componentVel ∈ number | undefined → number
    const componentVel = isFiniteNumber(velocityArr[i]) ? velocityArr[i] : 0;
    const oscillation =
      (componentVel * safeAmplitude * Math.sin(safeFrequency * t * 2 * Math.PI)) /
      Math.exp(safeDecay * t);
    return v + oscillation;
  });

  // Convert back to original format
  return fromArray(resultArr, value) as number | number[];
}

/**
 * Bounce expression
 * Creates bouncing settle after keyframes
 */
export function bounce(
  ctx: MotionExpressionContext,
  elasticity: number = 0.7,
  gravity: number = 4000,
): number | number[] {
  const { time, keyframes, value } = ctx;

  // Validate parameters
  const safeElasticity = Number.isFinite(elasticity)
    ? Math.max(0, Math.min(1, elasticity))
    : 0.7;
  const safeGravity = Number.isFinite(gravity) && gravity > 0 ? gravity : 4000;

  if (keyframes.length === 0) return value;

  // Type proof: fps ∈ number | undefined → number
  const fps = isFiniteNumber(ctx.fps) && ctx.fps > 0
    ? ctx.fps
    : 16;
  const currentFrame = time * fps;

  // Find last keyframe
  let lastKey: Keyframe<number | number[]> | null = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      lastKey = keyframes[i];
      break;
    }
  }

  if (!lastKey) return value;

  const keyTime = lastKey.frame / fps;
  const t = time - keyTime;

  if (t <= 0) return value;

  // Bounce physics
  let bounceTime = t;
  let bounceHeight = 1;
  let totalBounces = 0;
  const maxBounces = 10;

  // Calculate which bounce we're in
  while (bounceTime > 0 && totalBounces < maxBounces) {
    const bounceDuration = Math.sqrt((2 * bounceHeight) / safeGravity);
    if (bounceTime < bounceDuration * 2) {
      break;
    }
    bounceTime -= bounceDuration * 2;
    bounceHeight *= safeElasticity * safeElasticity;
    totalBounces++;
  }

  // Position within current bounce
  const bounceDuration = Math.sqrt((2 * bounceHeight) / safeGravity);
  const bounceT = bounceTime / (bounceDuration * 2);
  const bounceOffset = bounceHeight * 4 * bounceT * (1 - bounceT);

  // Convert to arrays for consistent processing
  const valueArr = toArray(value);
  const resultArr = valueArr.map((v) => v - bounceOffset * (1 - safeElasticity));
  
  return fromArray(resultArr, value) as number | number[];
}

/**
 * Elastic expression
 * Creates elastic spring-like motion
 */
export function elastic(
  ctx: MotionExpressionContext,
  amplitude: number = 1,
  period: number = 0.3,
): number | number[] {
  const { time, keyframes, value } = ctx;

  // Validate parameters
  const safeAmplitude = Number.isFinite(amplitude) ? amplitude : 1;
  const safePeriod = Number.isFinite(period) && period > 0 ? period : 0.3;

  if (keyframes.length === 0) return value;

  // Type proof: fps ∈ number | undefined → number
  const fps = isFiniteNumber(ctx.fps) && ctx.fps > 0
    ? ctx.fps
    : 16;
  const currentFrame = time * fps;

  let lastKey: Keyframe<number | number[]> | null = null;
  for (let i = keyframes.length - 1; i >= 0; i--) {
    if (keyframes[i].frame <= currentFrame) {
      lastKey = keyframes[i];
      break;
    }
  }

  if (!lastKey) return value;

  const keyTime = lastKey.frame / fps;
  const t = time - keyTime;

  if (t <= 0) return value;

  const s = safePeriod / 4;
  const decay = 2 ** (-10 * t);
  const oscillation = decay * Math.sin(((t - s) * (2 * Math.PI)) / safePeriod);

  // Convert to arrays for consistent processing
  const valueArr = toArray(value);
  const resultArr = valueArr.map((v) => v + safeAmplitude * oscillation);
  
  return fromArray(resultArr, value) as number | number[];
}
