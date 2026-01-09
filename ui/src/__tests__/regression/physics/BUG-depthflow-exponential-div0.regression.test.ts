/**
 * REGRESSION TEST: BUG - Exponential Division by Zero
 * 
 * @fixed 2026-01-06
 * @file services/depthflow.ts
 * @rootCause Exponential motion calculation divided by startValue without checking if it's zero
 * @fix Added startValue===0 fallback to linear interpolation
 * @counterexample calculateMotion with exponential type and startValue=0 produced NaN
 */

import { describe, test, expect } from 'vitest';
import { calculateMotion } from '@/services/depthflow';
import type { MotionComponent } from '@/services/depthflow';

function createExponentialMotion(
  startValue: number,
  endValue: number,
  startFrame: number = 0,
  endFrame: number = 100,
): MotionComponent {
  return {
    id: 'test-motion',
    type: 'exponential',
    parameter: 'zoom',
    startValue,
    endValue,
    startFrame,
    endFrame,
    easing: 'linear',
    enabled: true,
  };
}

describe('BUG Regression: Exponential Division by Zero', () => {
  /**
   * This test MUST reproduce the exact counterexample from the bug report.
   * Before fix: calculateMotion with exponential type and startValue=0 would divide by zero → NaN
   * After fix: Falls back to linear interpolation when startValue is zero
   */
  test('original counterexample now passes', () => {
    const motion = createExponentialMotion(0, 100, 0, 100);

    // Before fix: Would produce NaN due to division by zero (ratio = endValue / startValue)
    // After fix: Falls back to linear interpolation
    const resultAtStart = calculateMotion(motion, 0);
    const resultAtMid = calculateMotion(motion, 50);
    const resultAtEnd = calculateMotion(motion, 100);

    // All results should be finite numbers
    expect(Number.isFinite(resultAtStart)).toBe(true);
    expect(Number.isFinite(resultAtMid)).toBe(true);
    expect(Number.isFinite(resultAtEnd)).toBe(true);
    expect(Number.isNaN(resultAtStart)).toBe(false);
    expect(Number.isNaN(resultAtMid)).toBe(false);
    expect(Number.isNaN(resultAtEnd)).toBe(false);

    // Should use linear interpolation: startValue + (endValue - startValue) * t
    // At t=0: 0 + (100 - 0) * 0 = 0
    // At t=0.5: 0 + (100 - 0) * 0.5 = 50
    // At t=1: 0 + (100 - 0) * 1 = 100
    expect(resultAtStart).toBe(0);
    expect(resultAtMid).toBe(50);
    expect(resultAtEnd).toBe(100);
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('startValue=0 with negative endValue works', () => {
    const motion = createExponentialMotion(0, -100, 0, 100);

    const resultAtMid = calculateMotion(motion, 50);
    expect(Number.isFinite(resultAtMid)).toBe(true);
    expect(resultAtMid).toBe(-50); // Linear interpolation: 0 + (-100 - 0) * 0.5 = -50
  });

  test('startValue=0 with endValue=0 returns 0', () => {
    const motion = createExponentialMotion(0, 0, 0, 100);

    const resultAtStart = calculateMotion(motion, 0);
    const resultAtMid = calculateMotion(motion, 50);
    const resultAtEnd = calculateMotion(motion, 100);

    expect(resultAtStart).toBe(0);
    expect(resultAtMid).toBe(0);
    expect(resultAtEnd).toBe(0);
  });

  test('non-zero startValue works correctly (exponential interpolation)', () => {
    const motion = createExponentialMotion(1, 100, 0, 100);

    const resultAtStart = calculateMotion(motion, 0);
    const resultAtEnd = calculateMotion(motion, 100);

    // Should use exponential interpolation (not linear fallback)
    expect(resultAtStart).toBe(1);
    expect(resultAtEnd).toBe(100);
    
    // Midpoint should be geometric mean (sqrt(1*100) = 10) for exponential
    const resultAtMid = calculateMotion(motion, 50);
    expect(resultAtMid).toBeCloseTo(10, 1);
  });

  test('works at various easedT values', () => {
    const motion = createExponentialMotion(0, 100, 0, 100);

    const easedTValues = [0, 0.25, 0.5, 0.75, 1];
    for (const easedT of easedTValues) {
      const frame = easedT * 100;
      const result = calculateMotion(motion, frame);
      
      expect(Number.isFinite(result)).toBe(true);
      expect(Number.isNaN(result)).toBe(false);
      // Should be linear interpolation: 0 + (100 - 0) * easedT
      expect(result).toBe(easedT * 100);
    }
  });

  test('works with different frame ranges', () => {
    const motion1 = createExponentialMotion(0, 100, 10, 50);
    const motion2 = createExponentialMotion(0, 200, 0, 200);

    // Test motion1: frames 10-50
    const result1 = calculateMotion(motion1, 30); // Midpoint
    expect(Number.isFinite(result1)).toBe(true);
    expect(result1).toBe(50); // Linear: 0 + (100 - 0) * 0.5 = 50

    // Test motion2: frames 0-200
    const result2 = calculateMotion(motion2, 100); // Midpoint
    expect(Number.isFinite(result2)).toBe(true);
    expect(result2).toBe(100); // Linear: 0 + (200 - 0) * 0.5 = 100
  });
});
