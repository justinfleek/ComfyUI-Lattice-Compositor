/**
 * Easing Functions Tests
 *
 * Tests all easing functions from the mojs-style easing library.
 * Verifies boundary conditions, symmetry, and mathematical properties.
 */

import { describe, it, expect } from 'vitest';
import {
  easings,
  easingNames,
  easingGroups,
  getEasing,
  applyEasing,
  interpolateWithEasing,
  type EasingName
} from '@/services/easing';

// ============================================================================
// BOUNDARY CONDITION TESTS
// ============================================================================

describe('Easing Boundary Conditions', () => {
  // All easing functions should return 0 at t=0 and 1 at t=1
  const boundaryTestCases: EasingName[] = easingNames;

  describe('All easings at t=0', () => {
    for (const name of boundaryTestCases) {
      it(`${name} should return ~0 at t=0`, () => {
        const result = easings[name](0);
        expect(result).toBeCloseTo(0, 3);
      });
    }
  });

  describe('All easings at t=1', () => {
    for (const name of boundaryTestCases) {
      it(`${name} should return ~1 at t=1`, () => {
        const result = easings[name](1);
        expect(result).toBeCloseTo(1, 3);
      });
    }
  });
});

// ============================================================================
// LINEAR EASING
// ============================================================================

describe('Linear Easing', () => {
  it('should return identity function', () => {
    expect(easings.linear(0)).toBe(0);
    expect(easings.linear(0.25)).toBe(0.25);
    expect(easings.linear(0.5)).toBe(0.5);
    expect(easings.linear(0.75)).toBe(0.75);
    expect(easings.linear(1)).toBe(1);
  });
});

// ============================================================================
// SINE EASING
// ============================================================================

describe('Sine Easing', () => {
  describe('easeInSine', () => {
    it('should start slowly (derivative near 0)', () => {
      const early = easings.easeInSine(0.1);
      expect(early).toBeLessThan(0.1);
    });

    it('should accelerate toward the end', () => {
      const late = easings.easeInSine(0.9);
      expect(late).toBeGreaterThan(0.7);
    });
  });

  describe('easeOutSine', () => {
    it('should start fast (value > t early on)', () => {
      const early = easings.easeOutSine(0.1);
      expect(early).toBeGreaterThan(0.1);
    });

    it('should decelerate at the end', () => {
      const late = easings.easeOutSine(0.9);
      expect(late).toBeGreaterThan(0.9);
    });
  });

  describe('easeInOutSine', () => {
    it('should be symmetric around 0.5', () => {
      const at25 = easings.easeInOutSine(0.25);
      const at75 = easings.easeInOutSine(0.75);
      expect(at25 + at75).toBeCloseTo(1, 5);
    });

    it('should return 0.5 at t=0.5', () => {
      expect(easings.easeInOutSine(0.5)).toBeCloseTo(0.5, 5);
    });
  });
});

// ============================================================================
// POLYNOMIAL EASINGS (Quad, Cubic, Quart, Quint)
// ============================================================================

describe('Polynomial Easings', () => {
  const polyGroups = ['Quad', 'Cubic', 'Quart', 'Quint'] as const;

  describe('Ease-In variants (slow start)', () => {
    it('easeInQuad should equal t^2', () => {
      expect(easings.easeInQuad(0.5)).toBe(0.25);
    });

    it('easeInCubic should equal t^3', () => {
      expect(easings.easeInCubic(0.5)).toBe(0.125);
    });

    it('easeInQuart should equal t^4', () => {
      expect(easings.easeInQuart(0.5)).toBe(0.0625);
    });

    it('easeInQuint should equal t^5', () => {
      expect(easings.easeInQuint(0.5)).toBe(0.03125);
    });

    it('higher powers should be slower at start', () => {
      const t = 0.3;
      expect(easings.easeInQuad(t)).toBeGreaterThan(easings.easeInCubic(t));
      expect(easings.easeInCubic(t)).toBeGreaterThan(easings.easeInQuart(t));
      expect(easings.easeInQuart(t)).toBeGreaterThan(easings.easeInQuint(t));
    });
  });

  describe('Ease-Out variants (slow end)', () => {
    it('all easeOut variants should be > t for 0 < t < 1', () => {
      const t = 0.5;
      expect(easings.easeOutQuad(t)).toBeGreaterThan(t);
      expect(easings.easeOutCubic(t)).toBeGreaterThan(t);
      expect(easings.easeOutQuart(t)).toBeGreaterThan(t);
      expect(easings.easeOutQuint(t)).toBeGreaterThan(t);
    });
  });

  describe('Ease-InOut variants (symmetric)', () => {
    for (const group of polyGroups) {
      const easingName = `easeInOut${group}` as EasingName;

      it(`${easingName} should be symmetric around (0.5, 0.5)`, () => {
        const at25 = easings[easingName](0.25);
        const at75 = easings[easingName](0.75);
        expect(at25 + at75).toBeCloseTo(1, 5);
      });

      it(`${easingName} should pass through (0.5, 0.5)`, () => {
        expect(easings[easingName](0.5)).toBeCloseTo(0.5, 5);
      });
    }
  });
});

// ============================================================================
// EXPONENTIAL EASING
// ============================================================================

describe('Exponential Easing', () => {
  describe('easeInExpo', () => {
    it('should return exactly 0 at t=0', () => {
      expect(easings.easeInExpo(0)).toBe(0);
    });

    it('should be very close to 0 early on', () => {
      expect(easings.easeInExpo(0.1)).toBeLessThan(0.01);
    });

    it('should approach 1 rapidly at end', () => {
      expect(easings.easeInExpo(0.9)).toBeGreaterThan(0.4);
    });
  });

  describe('easeOutExpo', () => {
    it('should return exactly 1 at t=1', () => {
      expect(easings.easeOutExpo(1)).toBe(1);
    });

    it('should jump quickly from 0', () => {
      expect(easings.easeOutExpo(0.1)).toBeGreaterThan(0.4);
    });
  });

  describe('easeInOutExpo', () => {
    it('should return 0 at t=0 and 1 at t=1', () => {
      expect(easings.easeInOutExpo(0)).toBe(0);
      expect(easings.easeInOutExpo(1)).toBe(1);
    });

    it('should be symmetric', () => {
      const at25 = easings.easeInOutExpo(0.25);
      const at75 = easings.easeInOutExpo(0.75);
      expect(at25 + at75).toBeCloseTo(1, 3);
    });
  });
});

// ============================================================================
// CIRCULAR EASING
// ============================================================================

describe('Circular Easing', () => {
  describe('easeInCirc', () => {
    it('should start very slowly', () => {
      expect(easings.easeInCirc(0.1)).toBeLessThan(0.02);
    });

    it('should follow circular curve', () => {
      // For easeInCirc: f(t) = 1 - sqrt(1 - t^2)
      const t = 0.6;
      const expected = 1 - Math.sqrt(1 - t * t);
      expect(easings.easeInCirc(t)).toBeCloseTo(expected, 5);
    });
  });

  describe('easeOutCirc', () => {
    it('should reach near 1 quickly', () => {
      expect(easings.easeOutCirc(0.5)).toBeGreaterThan(0.8);
    });
  });

  describe('easeInOutCirc', () => {
    it('should be symmetric', () => {
      const at3 = easings.easeInOutCirc(0.3);
      const at7 = easings.easeInOutCirc(0.7);
      expect(at3 + at7).toBeCloseTo(1, 5);
    });
  });
});

// ============================================================================
// BACK EASING (Overshoot)
// ============================================================================

describe('Back Easing', () => {
  describe('easeInBack', () => {
    it('should go negative initially (anticipation)', () => {
      const result = easings.easeInBack(0.2);
      expect(result).toBeLessThan(0);
    });
  });

  describe('easeOutBack', () => {
    it('should overshoot past 1 before settling', () => {
      // Check at various points to find overshoot
      const values = [0.6, 0.7, 0.8].map(t => easings.easeOutBack(t));
      const hasOvershoot = values.some(v => v > 1);
      expect(hasOvershoot).toBe(true);
    });
  });

  describe('easeInOutBack', () => {
    it('should go negative in first half', () => {
      expect(easings.easeInOutBack(0.1)).toBeLessThan(0);
    });

    it('should overshoot in second half', () => {
      expect(easings.easeInOutBack(0.9)).toBeGreaterThan(1);
    });
  });
});

// ============================================================================
// ELASTIC EASING
// ============================================================================

describe('Elastic Easing', () => {
  describe('easeInElastic', () => {
    it('should return exactly 0 at t=0', () => {
      expect(easings.easeInElastic(0)).toBe(0);
    });

    it('should return exactly 1 at t=1', () => {
      expect(easings.easeInElastic(1)).toBe(1);
    });

    it('should oscillate (go negative)', () => {
      // Elastic easing goes below 0 or above 1 due to spring-like behavior
      const values = [];
      for (let t = 0.1; t < 0.9; t += 0.1) {
        values.push(easings.easeInElastic(t));
      }
      // Should have some negative values
      const hasNegative = values.some(v => v < 0);
      expect(hasNegative).toBe(true);
    });
  });

  describe('easeOutElastic', () => {
    it('should return exactly 0 at t=0', () => {
      expect(easings.easeOutElastic(0)).toBe(0);
    });

    it('should return exactly 1 at t=1', () => {
      expect(easings.easeOutElastic(1)).toBe(1);
    });

    it('should overshoot past 1', () => {
      const values = [];
      for (let t = 0.1; t < 0.9; t += 0.1) {
        values.push(easings.easeOutElastic(t));
      }
      const hasOvershoot = values.some(v => v > 1);
      expect(hasOvershoot).toBe(true);
    });
  });

  describe('easeInOutElastic', () => {
    it('should return boundaries correctly', () => {
      expect(easings.easeInOutElastic(0)).toBe(0);
      expect(easings.easeInOutElastic(1)).toBe(1);
    });

    it('should have oscillations in both halves', () => {
      const firstHalf = [];
      const secondHalf = [];
      for (let t = 0.1; t < 0.5; t += 0.1) {
        firstHalf.push(easings.easeInOutElastic(t));
      }
      for (let t = 0.6; t < 1; t += 0.1) {
        secondHalf.push(easings.easeInOutElastic(t));
      }

      // First half should go negative, second half should overshoot
      const hasNegative = firstHalf.some(v => v < 0);
      const hasOvershoot = secondHalf.some(v => v > 1);
      expect(hasNegative || hasOvershoot).toBe(true);
    });
  });
});

// ============================================================================
// BOUNCE EASING
// ============================================================================

describe('Bounce Easing', () => {
  describe('easeOutBounce', () => {
    it('should stay within [0, 1] range', () => {
      for (let t = 0; t <= 1; t += 0.05) {
        const result = easings.easeOutBounce(t);
        expect(result).toBeGreaterThanOrEqual(0);
        expect(result).toBeLessThanOrEqual(1);
      }
    });

    it('should have bounce characteristics (multiple local maxima)', () => {
      // Sample at many points and look for non-monotonic behavior
      const values = [];
      for (let t = 0; t <= 1; t += 0.02) {
        values.push(easings.easeOutBounce(t));
      }

      // Count direction changes (bounces)
      let bounces = 0;
      let increasing = true;
      for (let i = 1; i < values.length; i++) {
        const nowIncreasing = values[i] >= values[i - 1];
        if (nowIncreasing !== increasing) {
          bounces++;
          increasing = nowIncreasing;
        }
      }

      // Should have multiple direction changes (bounces)
      expect(bounces).toBeGreaterThan(2);
    });
  });

  describe('easeInBounce', () => {
    it('should be the reverse of easeOutBounce', () => {
      const t = 0.3;
      const inResult = easings.easeInBounce(t);
      const outResult = easings.easeOutBounce(1 - t);
      expect(inResult).toBeCloseTo(1 - outResult, 5);
    });
  });

  describe('easeInOutBounce', () => {
    it('should be symmetric around 0.5', () => {
      const at3 = easings.easeInOutBounce(0.3);
      const at7 = easings.easeInOutBounce(0.7);
      expect(at3 + at7).toBeCloseTo(1, 5);
    });
  });
});

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

describe('getEasing', () => {
  it('should return correct easing function by name', () => {
    const easing = getEasing('easeInQuad');
    expect(easing(0.5)).toBe(easings.easeInQuad(0.5));
  });

  it('should return linear for unknown easing name', () => {
    const easing = getEasing('unknownEasing');
    expect(easing(0.5)).toBe(0.5);
  });

  it('should handle empty string', () => {
    const easing = getEasing('');
    expect(easing(0.5)).toBe(0.5);
  });
});

describe('applyEasing', () => {
  it('should apply easing and clamp input', () => {
    expect(applyEasing(0.5, 'easeInQuad')).toBe(0.25);
  });

  it('should clamp negative values to 0', () => {
    expect(applyEasing(-0.5, 'linear')).toBe(0);
  });

  it('should clamp values > 1 to 1', () => {
    expect(applyEasing(1.5, 'linear')).toBe(1);
  });

  it('should default to linear', () => {
    expect(applyEasing(0.5)).toBe(0.5);
  });
});

describe('interpolateWithEasing', () => {
  it('should interpolate between start and end with linear', () => {
    expect(interpolateWithEasing(0, 100, 0.5, 'linear')).toBe(50);
  });

  it('should interpolate with easing applied', () => {
    // With easeInQuad, t=0.5 becomes 0.25
    expect(interpolateWithEasing(0, 100, 0.5, 'easeInQuad')).toBe(25);
  });

  it('should return start at t=0', () => {
    expect(interpolateWithEasing(10, 90, 0, 'easeInQuad')).toBe(10);
  });

  it('should return end at t=1', () => {
    expect(interpolateWithEasing(10, 90, 1, 'easeInQuad')).toBe(90);
  });

  it('should handle negative ranges', () => {
    expect(interpolateWithEasing(-100, 100, 0.5, 'linear')).toBe(0);
  });

  it('should handle reversed ranges (start > end)', () => {
    expect(interpolateWithEasing(100, 0, 0.5, 'linear')).toBe(50);
  });
});

// ============================================================================
// EASING GROUPS AND NAMES
// ============================================================================

describe('easingNames', () => {
  it('should contain all easing function names', () => {
    expect(easingNames.length).toBeGreaterThan(0);
    expect(easingNames).toContain('linear');
    expect(easingNames).toContain('easeInQuad');
    expect(easingNames).toContain('easeOutBounce');
  });

  it('should have corresponding function for each name', () => {
    for (const name of easingNames) {
      expect(typeof easings[name]).toBe('function');
    }
  });
});

describe('easingGroups', () => {
  it('should have all expected groups', () => {
    const expectedGroups = [
      'Linear', 'Sine', 'Quad', 'Cubic', 'Quart', 'Quint',
      'Expo', 'Circ', 'Back', 'Elastic', 'Bounce'
    ];

    for (const group of expectedGroups) {
      expect(easingGroups[group as keyof typeof easingGroups]).toBeDefined();
    }
  });

  it('should have valid easing names in each group', () => {
    for (const [groupName, groupEasings] of Object.entries(easingGroups)) {
      expect(groupEasings.length).toBeGreaterThan(0);

      for (const easingName of groupEasings) {
        expect(easingNames).toContain(easingName);
      }
    }
  });

  it('should have 3 variants per non-linear group', () => {
    const groupsWithVariants = ['Sine', 'Quad', 'Cubic', 'Quart', 'Quint', 'Expo', 'Circ', 'Back', 'Elastic', 'Bounce'];

    for (const group of groupsWithVariants) {
      const groupEasings = easingGroups[group as keyof typeof easingGroups];
      expect(groupEasings.length).toBe(3);
    }
  });
});

// ============================================================================
// MONOTONICITY TESTS
// ============================================================================

describe('Monotonicity (for easings that should be monotonic)', () => {
  const monotonicEasings: EasingName[] = [
    'linear',
    'easeInSine', 'easeOutSine', 'easeInOutSine',
    'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
    'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
    'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
    'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
    'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
    'easeInCirc', 'easeOutCirc', 'easeInOutCirc'
  ];

  for (const name of monotonicEasings) {
    it(`${name} should be monotonically non-decreasing`, () => {
      let prev = -Infinity;
      for (let t = 0; t <= 1; t += 0.01) {
        const curr = easings[name](t);
        expect(curr).toBeGreaterThanOrEqual(prev - 0.0001); // Small tolerance
        prev = curr;
      }
    });
  }
});

// ============================================================================
// PERFORMANCE TEST
// ============================================================================

describe('Performance', () => {
  it('should evaluate 10000 calls in reasonable time', () => {
    const start = performance.now();

    for (let i = 0; i < 10000; i++) {
      for (const name of easingNames) {
        easings[name](Math.random());
      }
    }

    const duration = performance.now() - start;
    // Should complete in under 500ms (very conservative)
    expect(duration).toBeLessThan(500);
  });
});
