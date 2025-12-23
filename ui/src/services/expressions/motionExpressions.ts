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

  if (keyframes.length === 0) return value;

  // Find nearest keyframe before current time
  const fps = ctx.fps || 30;
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

  const oscillation = vel * amplitude * Math.sin(frequency * t * 2 * Math.PI) / Math.exp(decay * t);

  if (typeof value === 'number') {
    return val + oscillation;
  }
  // For arrays, apply to all components
  return (value as number[]).map((v, i) => {
    const componentVel = (velocity as number[])[i] || 0;
    return v + componentVel * amplitude * Math.sin(frequency * t * 2 * Math.PI) / Math.exp(decay * t);
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

  if (keyframes.length === 0) return value;

  const fps = ctx.fps || 30;
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
    const bounceDuration = Math.sqrt(2 * bounceHeight / gravity);
    if (bounceTime < bounceDuration * 2) {
      break;
    }
    bounceTime -= bounceDuration * 2;
    bounceHeight *= elasticity * elasticity;
    totalBounces++;
  }

  // Position within current bounce
  const bounceDuration = Math.sqrt(2 * bounceHeight / gravity);
  const bounceT = bounceTime / (bounceDuration * 2);
  const bounceOffset = bounceHeight * 4 * bounceT * (1 - bounceT);

  if (typeof value === 'number') {
    return value - bounceOffset * (1 - elasticity);
  }

  return (value as number[]).map((v) => v - bounceOffset * (1 - elasticity));
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

  if (keyframes.length === 0) return value;

  const fps = ctx.fps || 30;
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

  const s = period / 4;
  const decay = Math.pow(2, -10 * t);
  const oscillation = decay * Math.sin((t - s) * (2 * Math.PI) / period);

  if (typeof value === 'number') {
    return value + amplitude * oscillation;
  }

  return (value as number[]).map((v) => v + amplitude * oscillation);
}
