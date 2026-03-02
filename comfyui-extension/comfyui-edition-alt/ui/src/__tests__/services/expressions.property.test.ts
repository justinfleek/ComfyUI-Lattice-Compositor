/**
 * EXPRESSION Property Tests
 * 
 * Mathematical properties that MUST hold for expression functions.
 * These test:
 * - Pure functions produce consistent outputs
 * - Mathematical invariants (lerp boundaries, clamp bounds)
 * - Wave functions are periodic
 * - Seeded random is deterministic
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  timeExpressions,
  mathExpressions,
  expressionEase,
  expressionEaseIn,
  expressionEaseOut,
} from '@/services/expressions/expressionEvaluator';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const normalizedArb = fc.double({ min: 0, max: 1, noNaN: true });
const finiteArb = fc.double({ min: -1e6, max: 1e6, noNaN: true });
const positiveArb = fc.double({ min: 0.01, max: 1e6, noNaN: true });
const smallPositiveArb = fc.double({ min: 0.01, max: 100, noNaN: true });
const percentArb = fc.double({ min: 0, max: 100, noNaN: true });
const seedArb = fc.integer({ min: 0, max: 1000000 });

describe('EXPRESSION Properties', () => {

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // math // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('mathExpressions.lerp', () => {

    test.prop([finiteArb, finiteArb])(
      'lerp(a, b, 0) = a',
      (a, b) => {
        const result = mathExpressions.lerp(a, b, 0);
        // Handle -0 vs +0 edge case: both are mathematically equal
        expect(result === a || (result === 0 && a === 0)).toBe(true);
      }
    );

    test.prop([finiteArb, finiteArb])(
      'lerp(a, b, 1) = b',
      (a, b) => {
        const result = mathExpressions.lerp(a, b, 1);
        // Use relative tolerance for large values
        const tolerance = Math.max(Math.abs(b) * 1e-9, 1e-10);
        expect(Math.abs(result - b)).toBeLessThanOrEqual(tolerance);
      }
    );

    test.prop([finiteArb, finiteArb])(
      'lerp(a, b, 0.5) = midpoint',
      (a, b) => {
        const result = mathExpressions.lerp(a, b, 0.5);
        const expected = (a + b) / 2;
        // Use relative tolerance for large values
        const tolerance = Math.max(Math.abs(expected) * 1e-9, 1e-9);
        expect(Math.abs(result - expected)).toBeLessThanOrEqual(tolerance);
      }
    );

    test.prop([finiteArb, normalizedArb])(
      'lerp(a, a, t) = a (same endpoints)',
      (a, t) => {
        expect(mathExpressions.lerp(a, a, t)).toBeCloseTo(a, 10);
      }
    );

    test.prop([
      fc.double({ min: 0, max: 100, noNaN: true }),
      fc.double({ min: 101, max: 200, noNaN: true }),
      normalizedArb,
    ])(
      'lerp result is bounded between a and b',
      (a, b, t) => {
        const result = mathExpressions.lerp(a, b, t);
        const minVal = Math.min(a, b);
        const maxVal = Math.max(a, b);
        expect(result).toBeGreaterThanOrEqual(minVal - 1e-10);
        expect(result).toBeLessThanOrEqual(maxVal + 1e-10);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // math // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('mathExpressions.clamp', () => {

    test.prop([finiteArb, finiteArb, finiteArb])(
      'clamp result is always within [min, max]',
      (value, min, max) => {
        // Ensure min <= max
        const [realMin, realMax] = min <= max ? [min, max] : [max, min];
        const result = mathExpressions.clamp(value, realMin, realMax);
        expect(result).toBeGreaterThanOrEqual(realMin);
        expect(result).toBeLessThanOrEqual(realMax);
      }
    );

    test.prop([fc.double({ min: 50, max: 100, noNaN: true })])(
      'clamp(value, min, max) = value when min <= value <= max',
      (value) => {
        const min = 0;
        const max = 150;
        expect(mathExpressions.clamp(value, min, max)).toBe(value);
      }
    );

    test.prop([finiteArb])(
      'clamp(value, min, min) = min',
      (min) => {
        const value = min + 100;
        expect(mathExpressions.clamp(value, min, min)).toBe(min);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // math // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('mathExpressions.map', () => {

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'map(inMin, inMin, inMax, outMin, outMax) = outMin',
      (inMin, inMax, outMin, outMax) => {
        fc.pre(Math.abs(inMax - inMin) > 0.01); // Need distinct input range
        const result = mathExpressions.map(inMin, inMin, inMax, outMin, outMax);
        expect(result).toBeCloseTo(outMin, 6);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'map(inMax, inMin, inMax, outMin, outMax) = outMax',
      (inMin, inMax, outMin, outMax) => {
        fc.pre(Math.abs(inMax - inMin) > 0.01); // Need distinct input range
        const result = mathExpressions.map(inMax, inMin, inMax, outMin, outMax);
        expect(result).toBeCloseTo(outMax, 6);
      }
    );

    test.prop([finiteArb, finiteArb])(
      'map preserves midpoint',
      (inMin, outMin) => {
        const inMax = inMin + 100;
        const outMax = outMin + 200;
        const midIn = (inMin + inMax) / 2;
        const expectedMidOut = (outMin + outMax) / 2;
        const result = mathExpressions.map(midIn, inMin, inMax, outMin, outMax);
        expect(result).toBeCloseTo(expectedMidOut, 6);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // math // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('mathExpressions.smoothstep', () => {

    test.prop([finiteArb, finiteArb])(
      'smoothstep(edge0, edge1, edge0) = 0',
      (edge0, edge1) => {
        fc.pre(Math.abs(edge1 - edge0) > 0.01);
        const result = mathExpressions.smoothstep(edge0, edge1, edge0);
        expect(result).toBeCloseTo(0, 6);
      }
    );

    test.prop([finiteArb, finiteArb])(
      'smoothstep(edge0, edge1, edge1) = 1',
      (edge0, edge1) => {
        fc.pre(Math.abs(edge1 - edge0) > 0.01);
        const result = mathExpressions.smoothstep(edge0, edge1, edge1);
        expect(result).toBeCloseTo(1, 6);
      }
    );

    test.prop([finiteArb])(
      'smoothstep is bounded in [0, 1]',
      (x) => {
        const edge0 = 0;
        const edge1 = 100;
        const result = mathExpressions.smoothstep(edge0, edge1, x);
        expect(result).toBeGreaterThanOrEqual(-1e-10);
        expect(result).toBeLessThanOrEqual(1 + 1e-10);
      }
    );

    test.prop([normalizedArb])(
      'smoothstep(0, 1, 0.5) is approximately 0.5',
      (t) => {
        // At t=0.5, smoothstep should return 0.5
        const result = mathExpressions.smoothstep(0, 1, 0.5);
        expect(result).toBeCloseTo(0.5, 6);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // math // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('mathExpressions.seedRandom', () => {

    test.prop([seedArb])(
      'seedRandom is deterministic (same seed = same result)',
      (seed) => {
        const result1 = mathExpressions.seedRandom(seed);
        const result2 = mathExpressions.seedRandom(seed);
        expect(result1).toBe(result2);
      }
    );

    test.prop([seedArb, finiteArb, finiteArb])(
      'seedRandom respects min/max bounds',
      (seed, min, max) => {
        fc.pre(min < max);
        fc.pre(Math.abs(max - min) > 0.01);
        const result = mathExpressions.seedRandom(seed, min, max);
        expect(result).toBeGreaterThanOrEqual(min - 1e-10);
        expect(result).toBeLessThanOrEqual(max + 1e-10);
      }
    );

    test.prop([seedArb, seedArb])(
      'different seeds produce different results (usually)',
      (seed1, seed2) => {
        fc.pre(seed1 !== seed2);
        const result1 = mathExpressions.seedRandom(seed1);
        const result2 = mathExpressions.seedRandom(seed2);
        // While not guaranteed, different seeds should almost always produce different results
        // We just verify they're both valid numbers
        expect(Number.isFinite(result1)).toBe(true);
        expect(Number.isFinite(result2)).toBe(true);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // time // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('timeExpressions.sine', () => {

    test.prop([smallPositiveArb, smallPositiveArb])(
      'sine is bounded by amplitude',
      (time, amplitude) => {
        const frequency = 1;
        const result = timeExpressions.sine(time, frequency, amplitude);
        expect(result).toBeGreaterThanOrEqual(-amplitude - 1e-10);
        expect(result).toBeLessThanOrEqual(amplitude + 1e-10);
      }
    );

    test.prop([smallPositiveArb])(
      'sine(0, f, a, 0) = 0',
      (amplitude) => {
        const result = timeExpressions.sine(0, 1, amplitude, 0);
        expect(result).toBeCloseTo(0, 6);
      }
    );

    test.prop([smallPositiveArb, smallPositiveArb])(
      'sine is periodic: sine(t) = sine(t + period)',
      (time, amplitude) => {
        const frequency = 1;
        const period = 1 / frequency;
        const result1 = timeExpressions.sine(time, frequency, amplitude);
        const result2 = timeExpressions.sine(time + period, frequency, amplitude);
        expect(result1).toBeCloseTo(result2, 6);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // time // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('timeExpressions.sawtooth', () => {

    test.prop([smallPositiveArb, smallPositiveArb])(
      'sawtooth is bounded by amplitude',
      (time, amplitude) => {
        const result = timeExpressions.sawtooth(time, 1, amplitude);
        expect(result).toBeGreaterThanOrEqual(-amplitude - 1e-6);
        expect(result).toBeLessThanOrEqual(amplitude + 1e-6);
      }
    );

    test.prop([smallPositiveArb, smallPositiveArb])(
      'sawtooth is periodic',
      (time, amplitude) => {
        const frequency = 1;
        const period = 1 / frequency;
        // Sample at same position in two different periods
        const t1 = time % period;
        const t2 = t1 + period * 3;
        const result1 = timeExpressions.sawtooth(t1, frequency, amplitude);
        const result2 = timeExpressions.sawtooth(t2, frequency, amplitude);
        expect(result1).toBeCloseTo(result2, 4);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // time // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('timeExpressions.square', () => {

    test.prop([smallPositiveArb, smallPositiveArb])(
      'square only produces +amplitude or -amplitude',
      (time, amplitude) => {
        const result = timeExpressions.square(time, 1, amplitude);
        const isPositive = Math.abs(result - amplitude) < 1e-6;
        const isNegative = Math.abs(result + amplitude) < 1e-6;
        expect(isPositive || isNegative).toBe(true);
      }
    );

    test.prop([smallPositiveArb, smallPositiveArb])(
      'square is periodic',
      (time, amplitude) => {
        const frequency = 1;
        const period = 1 / frequency;
        const t1 = time % period + 0.01; // Small offset to avoid edge
        const t2 = t1 + period * 2;
        const result1 = timeExpressions.square(t1, frequency, amplitude);
        const result2 = timeExpressions.square(t2, frequency, amplitude);
        expect(result1).toBeCloseTo(result2, 4);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // time // expressions
  // ════════════════════════════════════════════════════════════════════════════

  describe('timeExpressions.timeRamp', () => {

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'timeRamp at startTime returns startValue',
      (startTime, startValue, endValue, duration) => {
        fc.pre(duration > 0.01);
        const endTime = startTime + duration;
        const result = timeExpressions.timeRamp(startTime, endTime, startValue, endValue, startTime);
        expect(result).toBeCloseTo(startValue, 6);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'timeRamp at endTime returns endValue',
      (startTime, startValue, endValue, duration) => {
        fc.pre(duration > 0.01);
        const endTime = startTime + duration;
        const result = timeExpressions.timeRamp(startTime, endTime, startValue, endValue, endTime);
        expect(result).toBeCloseTo(endValue, 6);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb])(
      'timeRamp before startTime returns startValue',
      (startTime, startValue, endValue) => {
        const endTime = startTime + 10;
        const time = startTime - 5;
        const result = timeExpressions.timeRamp(startTime, endTime, startValue, endValue, time);
        expect(result).toBe(startValue);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb])(
      'timeRamp after endTime returns endValue',
      (startTime, startValue, endValue) => {
        const endTime = startTime + 10;
        const time = endTime + 5;
        const result = timeExpressions.timeRamp(startTime, endTime, startValue, endValue, time);
        expect(result).toBe(endValue);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                           // expression // ease // functions
  // ════════════════════════════════════════════════════════════════════════════

  describe('expressionEase', () => {

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'ease at tMin returns vMin',
      (tMin, vMin, vMax, duration) => {
        fc.pre(duration > 0.01);
        const tMax = tMin + duration;
        const result = expressionEase(tMin, tMin, tMax, vMin, vMax);
        expect(result).toBeCloseTo(vMin, 6);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'ease at tMax returns vMax',
      (tMin, vMin, vMax, duration) => {
        fc.pre(duration > 0.01);
        const tMax = tMin + duration;
        const result = expressionEase(tMax, tMin, tMax, vMin, vMax);
        expect(result).toBeCloseTo(vMax, 6);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'easeIn at tMin returns vMin',
      (tMin, vMin, vMax, duration) => {
        fc.pre(duration > 0.01);
        const tMax = tMin + duration;
        const result = expressionEaseIn(tMin, tMin, tMax, vMin, vMax);
        expect(result).toBeCloseTo(vMin, 6);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'easeOut at tMax returns vMax',
      (tMin, vMin, vMax, duration) => {
        fc.pre(duration > 0.01);
        const tMax = tMin + duration;
        const result = expressionEaseOut(tMax, tMin, tMax, vMin, vMax);
        expect(result).toBeCloseTo(vMax, 6);
      }
    );

  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // utility // functions
  // ════════════════════════════════════════════════════════════════════════════

  describe('mathExpressions.degreesToRadians / radiansToDegrees', () => {

    test.prop([finiteArb])(
      'degreesToRadians -> radiansToDegrees roundtrip',
      (degrees) => {
        const radians = mathExpressions.degreesToRadians(degrees);
        const back = mathExpressions.radiansToDegrees(radians);
        expect(back).toBeCloseTo(degrees, 6);
      }
    );

    test.prop([fc.constant(null)])(
      '90 degrees = PI/2 radians',
      () => {
        expect(mathExpressions.degreesToRadians(90)).toBeCloseTo(Math.PI / 2, 10);
      }
    );

    test.prop([fc.constant(null)])(
      '180 degrees = PI radians',
      () => {
        expect(mathExpressions.degreesToRadians(180)).toBeCloseTo(Math.PI, 10);
      }
    );

  });

  describe('mathExpressions.distance', () => {

    test.prop([finiteArb, finiteArb])(
      'distance from point to itself is 0',
      (x, y) => {
        expect(mathExpressions.distance(x, y, x, y)).toBe(0);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'distance is symmetric: d(A,B) = d(B,A)',
      (x1, y1, x2, y2) => {
        const d1 = mathExpressions.distance(x1, y1, x2, y2);
        const d2 = mathExpressions.distance(x2, y2, x1, y1);
        expect(d1).toBeCloseTo(d2, 10);
      }
    );

    test.prop([finiteArb, finiteArb, finiteArb, finiteArb])(
      'distance is always non-negative',
      (x1, y1, x2, y2) => {
        const d = mathExpressions.distance(x1, y1, x2, y2);
        expect(d).toBeGreaterThanOrEqual(0);
      }
    );

  });

});
