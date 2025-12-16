/**
 * EasingFunctions (Engine) Tests
 *
 * Tests the engine's easing function library used by KeyframeEvaluator.
 */

import { describe, it, expect } from 'vitest';
import {
  easingFunctions,
  getEasing,
  getEasingNames,
  hasEasing
} from '@/engine/animation/EasingFunctions';

// ============================================================================
// BOUNDARY TESTS - All easings should be 0 at t=0 and 1 at t=1
// ============================================================================

describe('Easing Boundary Conditions', () => {
  const easingNames = getEasingNames();

  describe('At t=0', () => {
    for (const name of easingNames) {
      it(`${name} should return ~0`, () => {
        const result = easingFunctions[name](0);
        expect(result).toBeCloseTo(0, 3);
      });
    }
  });

  describe('At t=1', () => {
    for (const name of easingNames) {
      it(`${name} should return ~1`, () => {
        const result = easingFunctions[name](1);
        expect(result).toBeCloseTo(1, 3);
      });
    }
  });
});

// ============================================================================
// LINEAR
// ============================================================================

describe('linear easing', () => {
  it('should return identity', () => {
    expect(easingFunctions.linear(0)).toBe(0);
    expect(easingFunctions.linear(0.25)).toBe(0.25);
    expect(easingFunctions.linear(0.5)).toBe(0.5);
    expect(easingFunctions.linear(0.75)).toBe(0.75);
    expect(easingFunctions.linear(1)).toBe(1);
  });
});

// ============================================================================
// EASING CHARACTERISTICS
// ============================================================================

describe('Ease-in characteristics (slow start)', () => {
  const easeInFunctions = [
    'easeInSine',
    'easeInQuad',
    'easeInCubic',
    'easeInQuart',
    'easeInQuint',
    'easeInExpo',
    'easeInCirc'
  ];

  for (const name of easeInFunctions) {
    it(`${name} at t=0.5 should be < 0.5`, () => {
      const result = easingFunctions[name](0.5);
      expect(result).toBeLessThan(0.5);
    });
  }
});

describe('Ease-out characteristics (fast start)', () => {
  const easeOutFunctions = [
    'easeOutSine',
    'easeOutQuad',
    'easeOutCubic',
    'easeOutQuart',
    'easeOutQuint',
    'easeOutExpo',
    'easeOutCirc'
  ];

  for (const name of easeOutFunctions) {
    it(`${name} at t=0.5 should be > 0.5`, () => {
      const result = easingFunctions[name](0.5);
      expect(result).toBeGreaterThan(0.5);
    });
  }
});

describe('Ease-in-out characteristics (symmetric)', () => {
  const easeInOutFunctions = [
    'easeInOutSine',
    'easeInOutQuad',
    'easeInOutCubic',
    'easeInOutQuart',
    'easeInOutQuint',
    'easeInOutExpo',
    'easeInOutCirc'
  ];

  for (const name of easeInOutFunctions) {
    it(`${name} should be symmetric around (0.5, 0.5)`, () => {
      const at25 = easingFunctions[name](0.25);
      const at75 = easingFunctions[name](0.75);
      expect(at25 + at75).toBeCloseTo(1, 3);
    });

    it(`${name} at t=0.5 should be ~0.5`, () => {
      const result = easingFunctions[name](0.5);
      expect(result).toBeCloseTo(0.5, 3);
    });
  }
});

// ============================================================================
// SPECIAL EASINGS
// ============================================================================

describe('Back easing (overshoot)', () => {
  it('easeInBack should go negative (anticipation)', () => {
    const result = easingFunctions.easeInBack(0.2);
    expect(result).toBeLessThan(0);
  });

  it('easeOutBack should overshoot past 1', () => {
    const result = easingFunctions.easeOutBack(0.8);
    expect(result).toBeGreaterThan(1);
  });
});

describe('Elastic easing', () => {
  it('easeInElastic should have negative values (wind-up)', () => {
    const hasNegative = [0.2, 0.3, 0.4, 0.5, 0.6, 0.7].some(
      t => easingFunctions.easeInElastic(t) < 0
    );
    expect(hasNegative).toBe(true);
  });

  it('easeOutElastic should overshoot past 1', () => {
    const hasOvershoot = [0.2, 0.3, 0.4, 0.5, 0.6, 0.7].some(
      t => easingFunctions.easeOutElastic(t) > 1
    );
    expect(hasOvershoot).toBe(true);
  });
});

describe('Bounce easing', () => {
  it('easeOutBounce should stay within [0, 1]', () => {
    for (let t = 0; t <= 1; t += 0.05) {
      const result = easingFunctions.easeOutBounce(t);
      expect(result).toBeGreaterThanOrEqual(0);
      expect(result).toBeLessThanOrEqual(1);
    }
  });

  it('easeOutBounce should have multiple bounces (direction changes)', () => {
    const values: number[] = [];
    for (let t = 0; t <= 1; t += 0.02) {
      values.push(easingFunctions.easeOutBounce(t));
    }

    let directionChanges = 0;
    let increasing = true;
    for (let i = 1; i < values.length; i++) {
      const nowIncreasing = values[i] >= values[i - 1];
      if (nowIncreasing !== increasing) {
        directionChanges++;
        increasing = nowIncreasing;
      }
    }

    expect(directionChanges).toBeGreaterThan(2);
  });

  it('easeInBounce should be reverse of easeOutBounce', () => {
    const t = 0.3;
    const inResult = easingFunctions.easeInBounce(t);
    const outResult = easingFunctions.easeOutBounce(1 - t);
    expect(inResult).toBeCloseTo(1 - outResult, 5);
  });
});

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

describe('getEasing', () => {
  it('should return correct easing function', () => {
    const fn = getEasing('easeInQuad');
    expect(fn(0.5)).toBe(easingFunctions.easeInQuad(0.5));
  });

  it('should return linear for unknown easing', () => {
    const fn = getEasing('unknownEasing');
    expect(fn(0.5)).toBe(0.5);
  });
});

describe('getEasingNames', () => {
  it('should return all easing names', () => {
    const names = getEasingNames();

    expect(names).toContain('linear');
    expect(names).toContain('easeInQuad');
    expect(names).toContain('easeOutBounce');
    expect(names.length).toBeGreaterThan(25);
  });
});

describe('hasEasing', () => {
  it('should return true for valid easings', () => {
    expect(hasEasing('linear')).toBe(true);
    expect(hasEasing('easeInQuad')).toBe(true);
    expect(hasEasing('easeOutBounce')).toBe(true);
  });

  it('should return false for invalid easings', () => {
    expect(hasEasing('unknownEasing')).toBe(false);
    expect(hasEasing('')).toBe(false);
  });
});

// ============================================================================
// POLYNOMIAL POWER VERIFICATION
// ============================================================================

describe('Polynomial power verification', () => {
  it('easeInQuad should equal t^2', () => {
    expect(easingFunctions.easeInQuad(0.5)).toBeCloseTo(0.25, 5);
    expect(easingFunctions.easeInQuad(0.3)).toBeCloseTo(0.09, 5);
  });

  it('easeInCubic should equal t^3', () => {
    expect(easingFunctions.easeInCubic(0.5)).toBeCloseTo(0.125, 5);
    expect(easingFunctions.easeInCubic(0.4)).toBeCloseTo(0.064, 5);
  });

  it('easeInQuart should equal t^4', () => {
    expect(easingFunctions.easeInQuart(0.5)).toBeCloseTo(0.0625, 5);
  });

  it('easeInQuint should equal t^5', () => {
    expect(easingFunctions.easeInQuint(0.5)).toBeCloseTo(0.03125, 5);
  });
});
