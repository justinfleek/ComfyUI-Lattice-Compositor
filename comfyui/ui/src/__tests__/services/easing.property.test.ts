/**
 * PROPERTY TESTS: ui/src/services/easing.ts
 * 
 * Created: 2026-01-06
 * Methodology: fast-check property-based testing
 * 
 * These tests verify MATHEMATICAL INVARIANTS that all easing functions must satisfy.
 * Easing functions are used everywhere in animation - if they're wrong, animations are wrong.
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  easings,
  easingNames,
  easingGroups,
  getEasing,
  applyEasing,
  interpolateWithEasing,
  type EasingName,
} from '@/services/easing';

// ============================================================================
// ARBITRARIES
// ============================================================================

// Parameter t in [0, 1] for easing functions
const tArb = fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true });

// Parameter t that can go outside [0, 1]
const extendedTArb = fc.double({ min: -2, max: 2, noNaN: true, noDefaultInfinity: true });

// All easing names
const easingNameArb = fc.constantFrom(...easingNames);

// Easing names that DON'T overshoot (stay in [0, 1])
const BOUNDED_EASINGS: EasingName[] = [
  'linear',
  'easeInSine', 'easeOutSine', 'easeInOutSine',
  'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
  'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
  'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
  'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
  'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
  'easeInCirc', 'easeOutCirc', 'easeInOutCirc',
  'easeOutBounce', 'easeInBounce', 'easeInOutBounce',
];

const boundedEasingArb = fc.constantFrom(...BOUNDED_EASINGS);

// Easing names that ARE monotonically increasing
const MONOTONIC_EASINGS: EasingName[] = [
  'linear',
  'easeInSine', 'easeOutSine', 'easeInOutSine',
  'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
  'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
  'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
  'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
  'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
  'easeInCirc', 'easeOutCirc', 'easeInOutCirc',
];

const monotonicEasingArb = fc.constantFrom(...MONOTONIC_EASINGS);

// Power-based easings (Quad, Cubic, Quart, Quint) have nice symmetry properties
const POWER_FAMILIES = ['Quad', 'Cubic', 'Quart', 'Quint'];

// Interpolation values
const startEndArb = fc.record({
  start: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  end: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
});

const EPSILON = 1e-10;

// ============================================================================
// BOUNDARY CONDITIONS (CRITICAL)
// ============================================================================

describe('PROPERTY: Boundary Conditions', () => {
  test.prop([easingNameArb])('f(0) = 0 for ALL easings', (name) => {
    const fn = easings[name];
    expect(fn(0)).toBeCloseTo(0, 10);
  });

  test.prop([easingNameArb])('f(1) = 1 for ALL easings', (name) => {
    const fn = easings[name];
    expect(fn(1)).toBeCloseTo(1, 10);
  });
});

// ============================================================================
// OUTPUT RANGE
// ============================================================================

describe('PROPERTY: Output Range', () => {
  test.prop([boundedEasingArb, tArb])('bounded easings stay in [0, 1]', (name, t) => {
    const fn = easings[name];
    const result = fn(t);
    expect(result).toBeGreaterThanOrEqual(-EPSILON);
    expect(result).toBeLessThanOrEqual(1 + EPSILON);
  });

  test.prop([easingNameArb, tArb])('all easings produce finite output', (name, t) => {
    const fn = easings[name];
    const result = fn(t);
    expect(Number.isFinite(result)).toBe(true);
  });
});

// ============================================================================
// MONOTONICITY
// ============================================================================

describe('PROPERTY: Monotonicity', () => {
  test.prop([monotonicEasingArb, tArb, tArb])('monotonic easings: t1 < t2 → f(t1) ≤ f(t2)', (name, t1, t2) => {
    fc.pre(t1 < t2);
    const fn = easings[name];
    expect(fn(t1)).toBeLessThanOrEqual(fn(t2) + EPSILON);
  });
});

// ============================================================================
// SYMMETRY PROPERTIES
// ============================================================================

describe('PROPERTY: Power Easing Symmetry', () => {
  for (const family of POWER_FAMILIES) {
    const easeIn = `easeIn${family}` as EasingName;
    const easeOut = `easeOut${family}` as EasingName;
    const easeInOut = `easeInOut${family}` as EasingName;

    test.prop([tArb])(`${family}: easeIn(t) + easeOut(1-t) = 1`, (t) => {
      const inFn = easings[easeIn];
      const outFn = easings[easeOut];
      const sum = inFn(t) + outFn(1 - t);
      expect(sum).toBeCloseTo(1, 5);
    });

    test.prop([fc.constant(null)])(`${family}: easeInOut(0.5) = 0.5`, () => {
      const fn = easings[easeInOut];
      expect(fn(0.5)).toBeCloseTo(0.5, 5);
    });
  }
});

// ============================================================================
// DETERMINISM
// ============================================================================

describe('PROPERTY: Determinism', () => {
  test.prop([easingNameArb, tArb])('same input always produces same output', (name, t) => {
    const fn = easings[name];
    const r1 = fn(t);
    const r2 = fn(t);
    expect(r1).toBe(r2);
  });

  test.prop([easingNameArb, fc.integer({ min: 1, max: 100 })])('multiple calls are consistent', (name, n) => {
    const fn = easings[name];
    const t = 0.5;
    const results = Array.from({ length: n }, () => fn(t));
    for (let i = 1; i < results.length; i++) {
      expect(results[i]).toBe(results[0]);
    }
  });
});

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

describe('PROPERTY: getEasing', () => {
  test.prop([easingNameArb])('returns correct function for valid names', (name) => {
    const fn = getEasing(name);
    expect(fn).toBe(easings[name]);
  });

  test.prop([fc.string()])('returns linear for invalid names', (name) => {
    fc.pre(!(name in easings)); // Skip if accidentally valid
    const fn = getEasing(name);
    expect(fn).toBe(easings.linear);
  });
});

describe('PROPERTY: applyEasing', () => {
  test.prop([extendedTArb, easingNameArb])('clamps input to [0, 1]', (t, name) => {
    const result = applyEasing(t, name);
    
    // For bounded easings, output should also be in [0, 1]
    if (BOUNDED_EASINGS.includes(name)) {
      expect(result).toBeGreaterThanOrEqual(-EPSILON);
      expect(result).toBeLessThanOrEqual(1 + EPSILON);
    }
    
    // Output should always be finite
    expect(Number.isFinite(result)).toBe(true);
  });

  test.prop([tArb])('uses linear by default', (t) => {
    const result = applyEasing(t);
    expect(result).toBeCloseTo(t, 10);
  });
});

describe('PROPERTY: interpolateWithEasing', () => {
  test.prop([startEndArb, easingNameArb])('at t=0 returns start', ({ start, end }, name) => {
    const result = interpolateWithEasing(start, end, 0, name);
    expect(result).toBeCloseTo(start, 5);
  });

  test.prop([startEndArb, easingNameArb])('at t=1 returns end', ({ start, end }, name) => {
    const result = interpolateWithEasing(start, end, 1, name);
    expect(result).toBeCloseTo(end, 5);
  });

  test.prop([startEndArb, tArb])('linear interpolation is exact', ({ start, end }, t) => {
    const result = interpolateWithEasing(start, end, t, 'linear');
    const expected = start + (end - start) * t;
    expect(result).toBeCloseTo(expected, 10);
  });

  test.prop([fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }), tArb, easingNameArb])(
    'interpolating same value gives that value',
    (value, t, name) => {
      const result = interpolateWithEasing(value, value, t, name);
      expect(result).toBeCloseTo(value, 5);
    }
  );
});

// ============================================================================
// EASING GROUPS VALIDATION
// ============================================================================

describe('PROPERTY: Easing Groups', () => {
  test.prop([fc.constant(null)])('all grouped names exist in easings', () => {
    for (const group of Object.values(easingGroups)) {
      for (const name of group) {
        expect(name in easings).toBe(true);
      }
    }
  });

  test.prop([fc.constant(null)])('groups cover all easings', () => {
    const allGrouped = Object.values(easingGroups).flat();
    const allEasings = easingNames;
    expect(allGrouped.sort()).toEqual(allEasings.sort());
  });

  test.prop([fc.constant(null)])('no duplicate names across groups', () => {
    const allGrouped = Object.values(easingGroups).flat();
    const unique = new Set(allGrouped);
    expect(unique.size).toBe(allGrouped.length);
  });
});

// ============================================================================
// SPECIFIC EASING FAMILIES
// ============================================================================

describe('PROPERTY: Linear is Identity', () => {
  test.prop([tArb])('linear(t) = t', (t) => {
    expect(easings.linear(t)).toBe(t);
  });
});

describe('PROPERTY: Expo Boundary Handling', () => {
  test.prop([fc.constant(null)])('easeInExpo(0) = 0 exactly', () => {
    expect(easings.easeInExpo(0)).toBe(0);
  });

  test.prop([fc.constant(null)])('easeOutExpo(1) = 1 exactly', () => {
    expect(easings.easeOutExpo(1)).toBe(1);
  });
});

describe('PROPERTY: Elastic Oscillation', () => {
  test.prop([fc.constant(null)])('easeInElastic oscillates below 0', () => {
    // At some points in [0, 1], output should be negative
    const samples = [0.1, 0.2, 0.3, 0.4, 0.5];
    const values = samples.map(t => easings.easeInElastic(t));
    expect(values.some(v => v < 0)).toBe(true);
  });

  test.prop([fc.constant(null)])('easeOutElastic oscillates above 1', () => {
    const samples = [0.5, 0.6, 0.7, 0.8, 0.9];
    const values = samples.map(t => easings.easeOutElastic(t));
    expect(values.some(v => v > 1)).toBe(true);
  });
});

describe('PROPERTY: Back Overshoot', () => {
  test.prop([fc.constant(null)])('easeInBack goes negative', () => {
    const samples = [0.1, 0.2, 0.3];
    const values = samples.map(t => easings.easeInBack(t));
    expect(values.some(v => v < 0)).toBe(true);
  });

  test.prop([fc.constant(null)])('easeOutBack goes above 1', () => {
    const samples = [0.7, 0.8, 0.9];
    const values = samples.map(t => easings.easeOutBack(t));
    expect(values.some(v => v > 1)).toBe(true);
  });
});
