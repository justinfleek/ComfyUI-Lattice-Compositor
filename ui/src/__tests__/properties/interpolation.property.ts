/**
 * INTERPOLATION Property Tests
 * 
 * Mathematical properties that MUST hold for keyframe interpolation.
 * These are invariants, not specific examples.
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { interpolateProperty } from '@/services/interpolation';
import { easings, getEasing, type EasingName } from '@/services/easing';
import { 
  sortedNumericKeyframesArb,
  normalizedArb,
  easingInterpolationArb,
  baseInterpolationArb,
} from './arbitraries';
import type { AnimatableProperty, Keyframe } from '@/types/animation';

describe('INTERPOLATION Properties', () => {

  // =========================================================================
  // BOUNDARY CONDITIONS
  // =========================================================================

  describe('boundary conditions', () => {

    test.prop([sortedNumericKeyframesArb])(
      'interpolation at first keyframe returns first value',
      (keyframes) => {
        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 999,
          animated: true,
          keyframes,
        };

        const result = interpolateProperty(property, keyframes[0].frame);
        expect(result).toBeCloseTo(keyframes[0].value, 10);
      }
    );

    test.prop([sortedNumericKeyframesArb])(
      'interpolation at last keyframe returns last value',
      (keyframes) => {
        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 999,
          animated: true,
          keyframes,
        };

        const lastKf = keyframes[keyframes.length - 1];
        const result = interpolateProperty(property, lastKf.frame);
        expect(result).toBeCloseTo(lastKf.value, 10);
      }
    );

    test.prop([
      sortedNumericKeyframesArb,
      fc.integer({ min: 1, max: 1000 })
    ])(
      'interpolation before first keyframe returns first value',
      (keyframes, offset) => {
        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 999,
          animated: true,
          keyframes,
        };

        const frameBefore = keyframes[0].frame - offset;
        const result = interpolateProperty(property, frameBefore);
        expect(result).toBe(keyframes[0].value);
      }
    );

    test.prop([
      sortedNumericKeyframesArb,
      fc.integer({ min: 1, max: 1000 })
    ])(
      'interpolation after last keyframe returns last value',
      (keyframes, offset) => {
        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 999,
          animated: true,
          keyframes,
        };

        const lastKf = keyframes[keyframes.length - 1];
        const frameAfter = lastKf.frame + offset;
        const result = interpolateProperty(property, frameAfter);
        expect(result).toBe(lastKf.value);
      }
    );

  });

  // =========================================================================
  // LINEAR INTERPOLATION PROPERTIES
  // =========================================================================

  describe('linear interpolation', () => {

    test.prop([
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
      normalizedArb,
    ])(
      'linear: result is bounded between keyframe values (monotonic case)',
      (v1, v2, t) => {
        const keyframes: Keyframe<number>[] = [
          {
            id: 'kf1',
            frame: 0,
            value: v1,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
          {
            id: 'kf2',
            frame: 100,
            value: v2,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
        ];

        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes,
        };

        const frame = t * 100;
        const result = interpolateProperty(property, frame);

        // Result should be between the two values
        const minVal = Math.min(v1, v2);
        const maxVal = Math.max(v1, v2);
        expect(result).toBeGreaterThanOrEqual(minVal - 1e-10);
        expect(result).toBeLessThanOrEqual(maxVal + 1e-10);
      }
    );

    test.prop([
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
    ])(
      'linear: midpoint is exactly average of endpoints',
      (v1, v2) => {
        const keyframes: Keyframe<number>[] = [
          {
            id: 'kf1',
            frame: 0,
            value: v1,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
          {
            id: 'kf2',
            frame: 100,
            value: v2,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
        ];

        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes,
        };

        const result = interpolateProperty(property, 50);
        const expected = (v1 + v2) / 2;

        expect(result).toBeCloseTo(expected, 10);
      }
    );

    test.prop([
      fc.double({ min: 0, max: 100, noNaN: true }),
      fc.double({ min: 101, max: 200, noNaN: true }), // v2 > v1 always
      fc.double({ min: 0.01, max: 0.99, noNaN: true }),
      fc.double({ min: 0.01, max: 0.99, noNaN: true }),
    ])(
      'linear: monotonically increasing for increasing values',
      (v1, v2, t1, t2) => {
        // Ensure t1 < t2
        const [tSmall, tLarge] = t1 < t2 ? [t1, t2] : [t2, t1];
        
        const keyframes: Keyframe<number>[] = [
          {
            id: 'kf1',
            frame: 0,
            value: v1,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
          {
            id: 'kf2',
            frame: 100,
            value: v2, // v2 > v1
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
        ];

        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes,
        };

        const result1 = interpolateProperty(property, tSmall * 100);
        const result2 = interpolateProperty(property, tLarge * 100);

        // For monotonically increasing values with linear interpolation,
        // earlier time = smaller value
        expect(result1).toBeLessThanOrEqual(result2 + 1e-10);
      }
    );

  });

  // =========================================================================
  // EASING FUNCTION PROPERTIES
  // =========================================================================

  describe('easing functions', () => {

    const easingNames = Object.keys(easings) as EasingName[];

    test.prop([fc.constantFrom(...easingNames)])(
      'easing(0) = 0 (start at origin)',
      (easingName) => {
        const fn = getEasing(easingName);
        expect(fn(0)).toBeCloseTo(0, 10);
      }
    );

    test.prop([fc.constantFrom(...easingNames)])(
      'easing(1) = 1 (end at target)',
      (easingName) => {
        const fn = getEasing(easingName);
        expect(fn(1)).toBeCloseTo(1, 10);
      }
    );

    test.prop([
      fc.constantFrom(...easingNames),
      normalizedArb,
    ])(
      'easing output is finite for all valid inputs',
      (easingName, t) => {
        const fn = getEasing(easingName);
        const result = fn(t);
        expect(Number.isFinite(result)).toBe(true);
      }
    );

    // Specific tests for non-overshooting easings
    const boundedEasings: EasingName[] = [
      'linear',
      'easeInSine', 'easeOutSine', 'easeInOutSine',
      'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
      'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
      'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
      'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
      'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
      'easeInCirc', 'easeOutCirc', 'easeInOutCirc',
    ];

    test.prop([
      fc.constantFrom(...boundedEasings),
      normalizedArb,
    ])(
      'bounded easings stay within [0, 1] range',
      (easingName, t) => {
        const fn = getEasing(easingName);
        const result = fn(t);
        expect(result).toBeGreaterThanOrEqual(-1e-10);
        expect(result).toBeLessThanOrEqual(1 + 1e-10);
      }
    );

    // Overshooting easings (back, elastic) can go outside [0, 1]
    const overshootingEasings: EasingName[] = [
      'easeInBack', 'easeOutBack', 'easeInOutBack',
      'easeInElastic', 'easeOutElastic', 'easeInOutElastic',
    ];

    test.prop([
      fc.constantFrom(...overshootingEasings),
      normalizedArb,
    ])(
      'overshooting easings are bounded within reasonable range [-2, 2]',
      (easingName, t) => {
        const fn = getEasing(easingName);
        const result = fn(t);
        // Elastic and back can overshoot significantly, but should stay reasonable
        expect(result).toBeGreaterThanOrEqual(-2);
        expect(result).toBeLessThanOrEqual(2);
      }
    );

  });

  // =========================================================================
  // CONTINUITY PROPERTIES
  // =========================================================================

  describe('continuity', () => {

    test.prop([
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: 0.1, max: 0.9, noNaN: true }),
      fc.double({ min: 1e-6, max: 1e-4, noNaN: true }),
    ])(
      'linear interpolation is continuous (small frame change = small value change)',
      (v1, v2, t, epsilon) => {
        const keyframes: Keyframe<number>[] = [
          {
            id: 'kf1',
            frame: 0,
            value: v1,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
          {
            id: 'kf2',
            frame: 100,
            value: v2,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
        ];

        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes,
        };

        const frame1 = t * 100;
        const frame2 = frame1 + epsilon;

        const result1 = interpolateProperty(property, frame1);
        const result2 = interpolateProperty(property, frame2);

        // Linear interpolation: value change should be proportional to frame change
        const expectedDelta = (epsilon / 100) * Math.abs(v2 - v1);
        const actualDelta = Math.abs(result2 - result1);

        expect(actualDelta).toBeLessThanOrEqual(expectedDelta + 1e-10);
      }
    );

  });

  // =========================================================================
  // HOLD INTERPOLATION PROPERTIES
  // =========================================================================

  describe('hold interpolation', () => {

    test.prop([
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: 0.01, max: 0.99, noNaN: true }),
    ])(
      'hold: always returns first keyframe value until next keyframe',
      (v1, v2, t) => {
        const keyframes: Keyframe<number>[] = [
          {
            id: 'kf1',
            frame: 0,
            value: v1,
            interpolation: 'hold',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
          {
            id: 'kf2',
            frame: 100,
            value: v2,
            interpolation: 'linear',
            inHandle: { frame: -5, value: 0, enabled: true },
            outHandle: { frame: 5, value: 0, enabled: true },
            controlMode: 'smooth',
          },
        ];

        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes,
        };

        const frame = t * 100; // Between 0 and 100, exclusive of endpoints
        const result = interpolateProperty(property, frame);

        // Hold always returns first value
        expect(result).toBe(v1);
      }
    );

  });

  // =========================================================================
  // STATIC PROPERTY PROPERTIES
  // =========================================================================

  describe('static properties', () => {

    test.prop([
      fc.double({ min: -1000, max: 1000, noNaN: true }),
      fc.double({ min: -1000, max: 1000, noNaN: true }),
    ])(
      'static property always returns base value regardless of frame',
      (baseValue, frame) => {
        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: baseValue,
          animated: false,
          keyframes: [],
        };

        const result = interpolateProperty(property, frame);
        expect(result).toBe(baseValue);
      }
    );

    test.prop([
      fc.double({ min: -1000, max: 1000, noNaN: true }),
      sortedNumericKeyframesArb,
      fc.double({ min: -1000, max: 1000, noNaN: true }),
    ])(
      'animated=false ignores keyframes',
      (baseValue, keyframes, frame) => {
        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: baseValue,
          animated: false, // Even with keyframes, this should be ignored
          keyframes,
        };

        const result = interpolateProperty(property, frame);
        expect(result).toBe(baseValue);
      }
    );

  });

});
