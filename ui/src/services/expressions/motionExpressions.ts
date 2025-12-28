/**
 * Motion Expressions Module
 *
 * Expression functions for momentum-based animations:
 * - inertia: Momentum after keyframes with decay
 * - bounce: Bouncing settle physics
 * - elastic: Spring-like elastic motion
 */

import type { Keyframe } from '@/types/project';

/**
 * Minimal expression context for motion expressions
 * (Avoids circular dependency with main expressions.ts)
 */
export interface MotionExpressionContext {
  time: number;
  fps: number;
  keyframes: Keyframe<any>[];
  value: number | number[];
  velocity: number | number[];
}

// ============================================================================
// MOTION EXPRESSIONS
// ============================================================================

/**
 * Inertia/Overshoot expression
 * Creates momentum-based animation after keyframes
 */
export function inertia(
  ctx: MotionExpressionContext,
  amplitude: number = 0.1,
  frequency: number = 2.0,
  decay: number = 2.0
): number | number[] {
  const { time, keyframes, value, velocity } = ctx;

  // Validate parameters
  const safeAmplitude = Number.isFinite(amplitude) ? amplitude : 0.1;
  const safeFrequency = Number.isFinite(frequency) ? frequency : 2.0;
  const safeDecay = Number.isFinite(decay) ? Math.max(0.001, decay) : 2.0;

  if (keyframes.length === 0) return value;

  // Find nearest keyframe before current time
  const fps = ctx.fps || 16;
  const currentFrame = time * fps;

  let nearestKey: Keyframe<any> | null = null;
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

  // Calculate velocity at keyframe
  const vel = typeof velocity === 'number' ? velocity : velocity[0];
  const val = typeof value === 'number' ? value : value[0];

  const oscillation = vel * safeAmplitude * Math.sin(safeFrequency * t * 2 * Math.PI) / Math.exp(safeDecay * t);

  if (typeof value === 'number') {
    return val + oscillation;
  }
  // For arrays, apply to all components
  return (value as number[]).map((v, i) => {
    const componentVel = (velocity as number[])[i] || 0;
    return v + componentVel * safeAmplitude * Math.sin(safeFrequency * t * 2 * Math.PI) / Math.exp(safeDecay * t);
  });
}

/**
 * Bounce expression
 * Creates bouncing settle after keyframes
 */
export function bounce(
  ctx: MotionExpressionContext,
  elasticity: number = 0.7,
  gravity: number = 4000
): number | number[] {
  const { time, keyframes, value } = ctx;

  // Validate parameters
  const safeElasticity = Number.isFinite(elasticity) ? Math.max(0, Math.min(1, elasticity)) : 0.7;
  const safeGravity = (Number.isFinite(gravity) && gravity > 0) ? gravity : 4000;

  if (keyframes.length === 0) return value;

  const fps = ctx.fps || 16;
  const currentFrame = time * fps;

  // Find last keyframe
  let lastKey: Keyframe<any> | null = null;
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
    const bounceDuration = Math.sqrt(2 * bounceHeight / safeGravity);
    if (bounceTime < bounceDuration * 2) {
      break;
    }
    bounceTime -= bounceDuration * 2;
    bounceHeight *= safeElasticity * safeElasticity;
    totalBounces++;
  }

  // Position within current bounce
  const bounceDuration = Math.sqrt(2 * bounceHeight / safeGravity);
  const bounceT = bounceTime / (bounceDuration * 2);
  const bounceOffset = bounceHeight * 4 * bounceT * (1 - bounceT);

  if (typeof value === 'number') {
    return value - bounceOffset * (1 - safeElasticity);
  }

  return (value as number[]).map((v) => v - bounceOffset * (1 - safeElasticity));
}

/**
 * Elastic expression
 * Creates elastic spring-like motion
 */
export function elastic(
  ctx: MotionExpressionContext,
  amplitude: number = 1,
  period: number = 0.3
): number | number[] {
  const { time, keyframes, value } = ctx;

  // Validate parameters
  const safeAmplitude = Number.isFinite(amplitude) ? amplitude : 1;
  const safePeriod = (Number.isFinite(period) && period > 0) ? period : 0.3;

  if (keyframes.length === 0) return value;

  const fps = ctx.fps || 16;
  const currentFrame = time * fps;

  let lastKey: Keyframe<any> | null = null;
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
  const decay = Math.pow(2, -10 * t);
  const oscillation = decay * Math.sin((t - s) * (2 * Math.PI) / safePeriod);

  if (typeof value === 'number') {
    return value + safeAmplitude * oscillation;
  }

  return (value as number[]).map((v) => v + safeAmplitude * oscillation);
}
