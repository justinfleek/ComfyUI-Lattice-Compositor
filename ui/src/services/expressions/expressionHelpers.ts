/**
 * Expression Helpers Module
 *
 * Utility functions used by various expression modules:
 * - Value interpolation at specific times
 * - Value arithmetic (add, subtract, scale)
 * - Easing application
 */

import type { Keyframe, InterpolationType } from '@/types/project';
import { EASING_FUNCTIONS } from './easing';

// ============================================================================
// VALUE OPERATIONS
// ============================================================================

/**
 * Subtract two values (numbers or arrays)
 */
export function subtractValues(a: any, b: any): number | number[] {
  if (typeof a === 'number' && typeof b === 'number') {
    return a - b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v - b[i]);
  }
  return 0;
}

/**
 * Add two values (numbers or arrays)
 */
export function addValues(a: any, b: any): number | number[] {
  if (typeof a === 'number' && typeof b === 'number') {
    return a + b;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + b[i]);
  }
  return a;
}

/**
 * Scale a value by a scalar
 */
export function scaleValue(v: any, s: number): number | number[] {
  if (typeof v === 'number') {
    return v * s;
  }
  if (Array.isArray(v)) {
    return v.map((x) => x * s);
  }
  return 0;
}

/**
 * Linear interpolation between two values
 */
export function lerpValues(a: any, b: any, t: number): number | number[] {
  if (typeof a === 'number' && typeof b === 'number') {
    return a + (b - a) * t;
  }
  if (Array.isArray(a) && Array.isArray(b)) {
    return a.map((v, i) => v + (b[i] - v) * t);
  }
  return a;
}

// ============================================================================
// EASING APPLICATION
// ============================================================================

/**
 * Apply easing function to a t value
 */
export function applyEasing(t: number, interpolation: InterpolationType): number {
  const fn = EASING_FUNCTIONS[interpolation];
  return fn ? fn(t) : t;
}

// ============================================================================
// TIME-BASED INTERPOLATION
// ============================================================================

/**
 * Interpolate keyframes at a specific time
 */
export function interpolateAtTime(keyframes: Keyframe<any>[], time: number, fps: number): number | number[] {
  const frame = time * fps;

  // Find surrounding keyframes
  let before: Keyframe<any> | null = null;
  let after: Keyframe<any> | null = null;

  for (const kf of keyframes) {
    if (kf.frame <= frame) {
      before = kf;
    } else if (!after) {
      after = kf;
      break;
    }
  }

  if (!before) return keyframes.length > 0 ? keyframes[0].value : 0;
  if (!after) return before.value;

  const frameDelta = after.frame - before.frame;
  if (!Number.isFinite(frameDelta) || frameDelta === 0) return before.value;
  const t = (frame - before.frame) / frameDelta;
  const easedT = applyEasing(t, before.interpolation);

  return lerpValues(before.value, after.value, easedT);
}
