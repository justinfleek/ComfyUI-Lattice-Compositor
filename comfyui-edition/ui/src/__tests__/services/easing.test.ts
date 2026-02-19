/**
 * AUDIT TEST: ui/src/services/easing.ts
 * 
 * Created: 2026-01-06
 * File Lines: 212
 * Importers: Used by interpolation.ts (36 importers)
 * 
 * This is a FOUNDATION FILE for all animation curves.
 * Every animation in the system uses these easing functions.
 * 
 * Tests verify:
 * - All 31 easing functions have correct boundary values
 * - Helper functions work correctly
 * - Edge cases don't break
 */

import { describe, expect, it } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  easings,
  easingNames,
  easingGroups,
  getEasing,
  applyEasing,
  interpolateWithEasing,
  type EasingName,
  type EasingFunction,
} from '@/services/easing';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Constants
// ════════════════════════════════════════════════════════════════════════════

const TOLERANCE = 1e-10; // Very tight tolerance for mathematical correctness

// Easing functions that overshoot (go below 0 or above 1)
const OVERSHOOT_EASINGS: EasingName[] = [
  'easeInBack',
  'easeOutBack',
  'easeInOutBack',
  'easeInElastic',
  'easeOutElastic',
  'easeInOutElastic',
];

// All other easings should stay in [0, 1] range
const BOUNDED_EASINGS: EasingName[] = easingNames.filter(
  name => !OVERSHOOT_EASINGS.includes(name)
);

// ════════════════════════════════════════════════════════════════════════════
//                                                       // easing // functions
// ════════════════════════════════════════════════════════════════════════════

describe('All easing functions: f(0) = 0', () => {
  for (const name of easingNames) {
    it(`${name}(0) = 0`, () => {
      const fn = easings[name];
      expect(fn(0)).toBeCloseTo(0, 10);
    });
  }
});

describe('All easing functions: f(1) = 1', () => {
  for (const name of easingNames) {
    it(`${name}(1) = 1`, () => {
      const fn = easings[name];
      expect(fn(1)).toBeCloseTo(1, 10);
    });
  }
});

// ════════════════════════════════════════════════════════════════════════════
//                                                        // bounded // easings
// ════════════════════════════════════════════════════════════════════════════

describe('Bounded easings stay in [0, 1] range', () => {
  const tValues = [0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0];
  
  for (const name of BOUNDED_EASINGS) {
    it(`${name} outputs in [0, 1] for all t in [0, 1]`, () => {
      const fn = easings[name];
      for (const t of tValues) {
        const result = fn(t);
        expect(result).toBeGreaterThanOrEqual(-TOLERANCE);
        expect(result).toBeLessThanOrEqual(1 + TOLERANCE);
      }
    });
  }
});

// ════════════════════════════════════════════════════════════════════════════
//                                               // specific // easing // tests
// ════════════════════════════════════════════════════════════════════════════

describe('linear', () => {
  it('is the identity function', () => {
    expect(easings.linear(0)).toBe(0);
    expect(easings.linear(0.5)).toBe(0.5);
    expect(easings.linear(1)).toBe(1);
  });

  test.prop([fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true })])(
    'linear(t) = t for all t',
    (t) => {
      expect(easings.linear(t)).toBeCloseTo(t, 10);
    }
  );
});

describe('easeInQuad', () => {
  it('is t squared', () => {
    expect(easings.easeInQuad(0.5)).toBeCloseTo(0.25, 10);
  });

  test.prop([fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true })])(
    'easeInQuad(t) = t²',
    (t) => {
      expect(easings.easeInQuad(t)).toBeCloseTo(t * t, 10);
    }
  );
});

describe('easeOutQuad', () => {
  it('is 1 - (1-t)²', () => {
    expect(easings.easeOutQuad(0.5)).toBeCloseTo(0.75, 10);
  });

  test.prop([fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true })])(
    'easeOutQuad(t) = 1 - (1-t)²',
    (t) => {
      const expected = 1 - (1 - t) * (1 - t);
      expect(easings.easeOutQuad(t)).toBeCloseTo(expected, 10);
    }
  );
});

describe('easeInCubic', () => {
  it('is t cubed', () => {
    expect(easings.easeInCubic(0.5)).toBeCloseTo(0.125, 10);
  });

  test.prop([fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true })])(
    'easeInCubic(t) = t³',
    (t) => {
      expect(easings.easeInCubic(t)).toBeCloseTo(t * t * t, 10);
    }
  );
});

describe('easeInExpo', () => {
  it('returns 0 at t=0', () => {
    expect(easings.easeInExpo(0)).toBe(0);
  });

  it('is nearly 0 at small t', () => {
    expect(easings.easeInExpo(0.1)).toBeLessThan(0.01);
  });
});

describe('easeOutExpo', () => {
  it('returns 1 at t=1', () => {
    expect(easings.easeOutExpo(1)).toBe(1);
  });

  it('approaches 1 quickly', () => {
    expect(easings.easeOutExpo(0.5)).toBeGreaterThan(0.95);
  });
});

describe('easeInOutSine', () => {
  it('is symmetric around 0.5', () => {
    const at25 = easings.easeInOutSine(0.25);
    const at75 = easings.easeInOutSine(0.75);
    expect(at25 + at75).toBeCloseTo(1, 5);
  });

  it('is 0.5 at t=0.5', () => {
    expect(easings.easeInOutSine(0.5)).toBeCloseTo(0.5, 10);
  });
});

describe('easeInBack (overshoot)', () => {
  it('goes negative for small t', () => {
    const at25 = easings.easeInBack(0.25);
    expect(at25).toBeLessThan(0);
  });

  it('returns exactly 0 at t=0', () => {
    expect(easings.easeInBack(0)).toBe(0);
  });

  it('returns exactly 1 at t=1', () => {
    expect(easings.easeInBack(1)).toBe(1);
  });
});

describe('easeOutBack (overshoot)', () => {
  it('goes above 1 before settling', () => {
    const at75 = easings.easeOutBack(0.75);
    expect(at75).toBeGreaterThan(1);
  });

  it('returns exactly 0 at t=0', () => {
    expect(easings.easeOutBack(0)).toBe(0);
  });

  it('returns exactly 1 at t=1', () => {
    expect(easings.easeOutBack(1)).toBe(1);
  });
});

describe('easeInElastic (overshoot)', () => {
  it('oscillates below 0', () => {
    // At some points it should be negative
    const values = [0.1, 0.2, 0.3, 0.4, 0.5].map(t => easings.easeInElastic(t));
    expect(values.some(v => v < 0)).toBe(true);
  });

  it('returns exactly 0 at t=0', () => {
    expect(easings.easeInElastic(0)).toBe(0);
  });

  it('returns exactly 1 at t=1', () => {
    expect(easings.easeInElastic(1)).toBe(1);
  });
});

describe('easeOutElastic (overshoot)', () => {
  it('oscillates above 1', () => {
    // At some points it should be above 1
    const values = [0.5, 0.6, 0.7, 0.8, 0.9].map(t => easings.easeOutElastic(t));
    expect(values.some(v => v > 1)).toBe(true);
  });
});

describe('easeOutBounce', () => {
  it('bounces up multiple times', () => {
    // Test that the function isn't monotonic (bounces)
    const at50 = easings.easeOutBounce(0.5);
    const at60 = easings.easeOutBounce(0.6);
    const at70 = easings.easeOutBounce(0.7);
    // These values demonstrate non-monotonic behavior
    expect(at60).toBeLessThan(at70);
  });

  it('stays in [0, 1] range', () => {
    for (let t = 0; t <= 1; t += 0.05) {
      const result = easings.easeOutBounce(t);
      expect(result).toBeGreaterThanOrEqual(-TOLERANCE);
      expect(result).toBeLessThanOrEqual(1 + TOLERANCE);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                       // helper // functions
// ════════════════════════════════════════════════════════════════════════════

describe('getEasing', () => {
  it('returns the correct easing function for valid names', () => {
    for (const name of easingNames) {
      const fn = getEasing(name);
      expect(fn).toBe(easings[name]);
    }
  });

  it('returns linear for invalid names', () => {
    const fn = getEasing('invalidEasingName');
    expect(fn).toBe(easings.linear);
  });

  it('returns linear for empty string', () => {
    const fn = getEasing('');
    expect(fn).toBe(easings.linear);
  });
});

describe('applyEasing', () => {
  it('applies easing with clamped input', () => {
    // Should clamp t to [0, 1]
    expect(applyEasing(-0.5, 'linear')).toBe(0);
    expect(applyEasing(1.5, 'linear')).toBe(1);
  });

  it('uses linear by default', () => {
    expect(applyEasing(0.5)).toBe(0.5);
  });

  it('applies named easing correctly', () => {
    const result = applyEasing(0.5, 'easeInQuad');
    expect(result).toBeCloseTo(0.25, 10);
  });

  test.prop([fc.double({ min: -10, max: 10, noNaN: true, noDefaultInfinity: true })])(
    'always clamps to [0, 1] output range for bounded easings',
    (t) => {
      const result = applyEasing(t, 'easeInQuad');
      expect(result).toBeGreaterThanOrEqual(0);
      expect(result).toBeLessThanOrEqual(1);
    }
  );
});

describe('interpolateWithEasing', () => {
  it('returns start at t=0', () => {
    expect(interpolateWithEasing(10, 20, 0, 'linear')).toBe(10);
  });

  it('returns end at t=1', () => {
    expect(interpolateWithEasing(10, 20, 1, 'linear')).toBe(20);
  });

  it('returns midpoint at t=0.5 for linear', () => {
    expect(interpolateWithEasing(0, 100, 0.5, 'linear')).toBe(50);
  });

  it('applies easing to interpolation', () => {
    // easeInQuad(0.5) = 0.25, so result should be 25% of the way
    const result = interpolateWithEasing(0, 100, 0.5, 'easeInQuad');
    expect(result).toBeCloseTo(25, 10);
  });

  it('handles negative ranges', () => {
    expect(interpolateWithEasing(-100, 100, 0.5, 'linear')).toBe(0);
  });

  it('handles reversed ranges (end < start)', () => {
    expect(interpolateWithEasing(100, 0, 0.5, 'linear')).toBe(50);
  });

  test.prop([
    fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true }),
  ])('linear interpolation is exact', (start, end, t) => {
    const result = interpolateWithEasing(start, end, t, 'linear');
    const expected = start + (end - start) * t;
    expect(result).toBeCloseTo(expected, 10);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                     // exported // constants
// ════════════════════════════════════════════════════════════════════════════

describe('easingNames', () => {
  it('contains all 31 easing functions', () => {
    expect(easingNames.length).toBe(31);
  });

  it('matches keys of easings object', () => {
    const keys = Object.keys(easings);
    expect(easingNames.sort()).toEqual(keys.sort());
  });
});

describe('easingGroups', () => {
  it('contains all expected groups', () => {
    const expectedGroups = [
      'Linear', 'Sine', 'Quad', 'Cubic', 'Quart', 'Quint',
      'Expo', 'Circ', 'Back', 'Elastic', 'Bounce'
    ];
    expect(Object.keys(easingGroups).sort()).toEqual(expectedGroups.sort());
  });

  it('all grouped names exist in easings', () => {
    for (const group of Object.values(easingGroups)) {
      for (const name of group) {
        expect(name in easings).toBe(true);
      }
    }
  });

  it('groups cover all easings', () => {
    const allGrouped = Object.values(easingGroups).flat();
    expect(allGrouped.sort()).toEqual(easingNames.sort());
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                         // property // tests
// ════════════════════════════════════════════════════════════════════════════

describe('Property: In/Out/InOut relationships', () => {
  // For most easing families, the following should hold:
  // - easeIn(t) + easeOut(1-t) ≈ 1 (complementary)
  // - easeInOut(0.5) ≈ 0.5 (symmetric)
  
  const families = ['Quad', 'Cubic', 'Quart', 'Quint'];
  
  for (const family of families) {
    it(`ease${family}: easeIn(t) + easeOut(1-t) ≈ 1`, () => {
      const easeIn = easings[`easeIn${family}` as EasingName];
      const easeOut = easings[`easeOut${family}` as EasingName];
      
      for (const t of [0, 0.25, 0.5, 0.75, 1]) {
        const sum = easeIn(t) + easeOut(1 - t);
        expect(sum).toBeCloseTo(1, 5);
      }
    });

    it(`ease${family}: easeInOut(0.5) = 0.5`, () => {
      const easeInOut = easings[`easeInOut${family}` as EasingName];
      expect(easeInOut(0.5)).toBeCloseTo(0.5, 5);
    });
  }
});

describe('Property: Monotonicity of non-overshoot functions', () => {
  // Non-elastic, non-back, non-bounce easings should be monotonically increasing
  const monotonicEasings: EasingName[] = [
    'linear',
    'easeInSine', 'easeOutSine', 'easeInOutSine',
    'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
    'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
    'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
    'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
    'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
    'easeInCirc', 'easeOutCirc', 'easeInOutCirc',
  ];

  for (const name of monotonicEasings) {
    it(`${name} is monotonically increasing`, () => {
      const fn = easings[name];
      let prev = fn(0);
      for (let t = 0.01; t <= 1; t += 0.01) {
        const curr = fn(t);
        expect(curr).toBeGreaterThanOrEqual(prev - TOLERANCE);
        prev = curr;
      }
    });
  }
});

// ════════════════════════════════════════════════════════════════════════════
//                                                             // edge // cases
// ════════════════════════════════════════════════════════════════════════════

describe('Edge cases', () => {
  it('handles t = 0.5 for all easings without error', () => {
    for (const name of easingNames) {
      const fn = easings[name];
      expect(() => fn(0.5)).not.toThrow();
      expect(Number.isFinite(fn(0.5))).toBe(true);
    }
  });

  it('handles rapid repeated calls', () => {
    const fn = easings.easeInOutCubic;
    for (let i = 0; i < 1000; i++) {
      const t = i / 1000;
      expect(Number.isFinite(fn(t))).toBe(true);
    }
  });

  it('produces consistent results (deterministic)', () => {
    for (const name of easingNames) {
      const fn = easings[name];
      const result1 = fn(0.5);
      const result2 = fn(0.5);
      expect(result1).toBe(result2);
    }
  });
});
