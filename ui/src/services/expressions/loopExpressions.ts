/**
 * Loop Expressions Module
 *
 * Expression functions for repeating animations:
 * - repeatAfter: Loop animation after last keyframe
 * - repeatBefore: Loop animation before first keyframe
 */

import type { Keyframe } from '@/types/project';
import { interpolateAtTime, subtractValues, addValues, scaleValue } from './expressionHelpers';

// ============================================================================
// TYPES
// ============================================================================

export type LoopType = 'cycle' | 'pingpong' | 'offset' | 'continue';

/**
 * Minimal expression context for loop expressions
 */
export interface LoopExpressionContext {
  time: number;
  fps: number;
  keyframes: Keyframe<any>[];
  value: number | number[];
  velocity: number | number[];
}

// ============================================================================
// LOOP EXPRESSIONS
// ============================================================================

/**
 * Repeat After expression
 * Repeats animation after last keyframe
 */
export function repeatAfter(
  ctx: LoopExpressionContext,
  type: LoopType = 'cycle',
  numKeyframes: number = 0
): number | number[] {
  const { time, keyframes, fps } = ctx;

  if (keyframes.length < 2) return ctx.value;

  const startIdx = numKeyframes > 0 ? Math.max(0, keyframes.length - numKeyframes) : 0;
  const startKey = keyframes[startIdx];
  const endKey = keyframes[keyframes.length - 1];

  const startTime = startKey.frame / fps;
  const endTime = endKey.frame / fps;
  const duration = endTime - startTime;

  if (duration <= 0 || time <= endTime) return ctx.value;

  const elapsed = time - endTime;

  switch (type) {
    case 'cycle': {
      // Repeat from start
      const cycleTime = startTime + (elapsed % duration);
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'pingpong': {
      // Alternate forward/backward
      const cycles = Math.floor(elapsed / duration);
      const cycleProgress = (elapsed % duration) / duration;
      const isReverse = cycles % 2 === 1;
      const t = isReverse ? 1 - cycleProgress : cycleProgress;
      const cycleTime = startTime + t * duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'offset': {
      // Add cumulative offset each cycle
      const cycles = Math.floor(elapsed / duration);
      const cycleTime = startTime + (elapsed % duration);
      const baseValue = interpolateAtTime(keyframes, cycleTime, fps);
      const delta = subtractValues(endKey.value, startKey.value);
      return addValues(baseValue, scaleValue(delta, cycles + 1));
    }
    case 'continue': {
      // Continue at last velocity
      const velocity = ctx.velocity;
      if (typeof velocity === 'number') {
        return (ctx.value as number) + velocity * elapsed;
      }
      return (ctx.value as number[]).map((v, i) => v + (velocity as number[])[i] * elapsed);
    }
  }
}

/**
 * Repeat Before expression
 * Repeats animation before first keyframe
 */
export function repeatBefore(
  ctx: LoopExpressionContext,
  type: LoopType = 'cycle',
  numKeyframes: number = 0
): number | number[] {
  const { time, keyframes, fps } = ctx;

  if (keyframes.length < 2) return ctx.value;

  const endIdx = numKeyframes > 0 ? Math.min(keyframes.length - 1, numKeyframes - 1) : keyframes.length - 1;
  const startKey = keyframes[0];
  const endKey = keyframes[endIdx];

  const startTime = startKey.frame / fps;
  const endTime = endKey.frame / fps;
  const duration = endTime - startTime;

  if (duration <= 0 || time >= startTime) return ctx.value;

  const elapsed = startTime - time;

  switch (type) {
    case 'cycle': {
      const cycleTime = endTime - (elapsed % duration);
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'pingpong': {
      const cycles = Math.floor(elapsed / duration);
      const cycleProgress = (elapsed % duration) / duration;
      const isReverse = cycles % 2 === 1;
      const t = isReverse ? cycleProgress : 1 - cycleProgress;
      const cycleTime = startTime + t * duration;
      return interpolateAtTime(keyframes, cycleTime, fps);
    }
    case 'offset': {
      const cycles = Math.floor(elapsed / duration);
      const cycleTime = endTime - (elapsed % duration);
      const baseValue = interpolateAtTime(keyframes, cycleTime, fps);
      const delta = subtractValues(startKey.value, endKey.value);
      return addValues(baseValue, scaleValue(delta, cycles + 1));
    }
    case 'continue': {
      const velocity = ctx.velocity;
      if (typeof velocity === 'number') {
        return (ctx.value as number) - velocity * elapsed;
      }
      return (ctx.value as number[]).map((v, i) => v - (velocity as number[])[i] * elapsed);
    }
  }
}
