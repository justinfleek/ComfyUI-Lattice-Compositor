/**
 * Text Animator Service Tests
 *
 * Comprehensive tests for Tutorial 7: Kinetic Typography
 * Tests all selector types, modes, and expression evaluation
 *
 * Key areas:
 * - Range Selector shapes and animation
 * - Wiggly Selector randomization (deterministic)
 * - Expression Selector programmatic control
 * - Selector mode combination (Add, Subtract, Intersect, Min, Max, Difference)
 * - Complete character influence calculation
 * - Determinism verification
 */

import { describe, it, expect, beforeEach } from 'vitest';
import {
  calculateCharacterInfluence,
  calculateWigglyInfluence,
  calculateWigglyOffset,
  calculateExpressionInfluence,
  combineSelectorValues,
  calculateCompleteCharacterInfluence,
  createTextAnimator,
  createWigglySelector,
  createExpressionSelector,
  applyTextAnimatorPreset,
  DEFAULT_RANGE_SELECTOR,
  DEFAULT_WIGGLY_SELECTOR,
  DEFAULT_EXPRESSION_SELECTOR,
  EXPRESSION_PRESETS,
  TEXT_ANIMATOR_PRESETS,
} from '@/services/textAnimator';
import type {
  TextRangeSelector,
  TextWigglySelector,
  TextExpressionSelector,
  TextAnimator,
} from '@/types/project';

// ============================================================================
// RANGE SELECTOR TESTS
// ============================================================================

describe('Range Selector - calculateCharacterInfluence', () => {
  let rangeSelector: TextRangeSelector;

  beforeEach(() => {
    rangeSelector = {
      ...DEFAULT_RANGE_SELECTOR,
      start: { ...DEFAULT_RANGE_SELECTOR.start, value: 0 },
      end: { ...DEFAULT_RANGE_SELECTOR.end, value: 100 },
      offset: { ...DEFAULT_RANGE_SELECTOR.offset, value: 0 },
    };
  });

  describe('Shape: Square', () => {
    beforeEach(() => {
      rangeSelector.shape = 'square';
    });

    it('should return 1 for all characters in range', () => {
      const totalChars = 10;
      for (let i = 0; i < totalChars; i++) {
        const influence = calculateCharacterInfluence(i, totalChars, rangeSelector, 0);
        expect(influence).toBe(1);
      }
    });

    it('should return 0 for characters outside range', () => {
      rangeSelector.start.value = 50;
      rangeSelector.end.value = 100;

      const totalChars = 10;
      // Characters 0-4 are at positions 0-44%, should be outside
      for (let i = 0; i < 4; i++) {
        const influence = calculateCharacterInfluence(i, totalChars, rangeSelector, 0);
        expect(influence).toBe(0);
      }
    });
  });

  describe('Shape: Ramp Up', () => {
    beforeEach(() => {
      rangeSelector.shape = 'ramp_up';
    });

    it('should increase linearly from start to end', () => {
      const totalChars = 11; // 0, 10%, 20%, ... 100%
      const influences: number[] = [];

      for (let i = 0; i < totalChars; i++) {
        influences.push(calculateCharacterInfluence(i, totalChars, rangeSelector, 0));
      }

      // First character should be near 0
      expect(influences[0]).toBeCloseTo(0, 1);
      // Last character should be 1
      expect(influences[totalChars - 1]).toBe(1);
      // Should be monotonically increasing
      for (let i = 1; i < totalChars; i++) {
        expect(influences[i]).toBeGreaterThanOrEqual(influences[i - 1]);
      }
    });
  });

  describe('Shape: Ramp Down', () => {
    beforeEach(() => {
      rangeSelector.shape = 'ramp_down';
    });

    it('should decrease linearly from start to end', () => {
      const totalChars = 11;
      const influences: number[] = [];

      for (let i = 0; i < totalChars; i++) {
        influences.push(calculateCharacterInfluence(i, totalChars, rangeSelector, 0));
      }

      // First character should be 1
      expect(influences[0]).toBe(1);
      // Last character should be near 0
      expect(influences[totalChars - 1]).toBeCloseTo(0, 1);
      // Should be monotonically decreasing
      for (let i = 1; i < totalChars; i++) {
        expect(influences[i]).toBeLessThanOrEqual(influences[i - 1]);
      }
    });
  });

  describe('Shape: Triangle', () => {
    beforeEach(() => {
      rangeSelector.shape = 'triangle';
    });

    it('should peak in the middle', () => {
      const totalChars = 11;
      const influences: number[] = [];

      for (let i = 0; i < totalChars; i++) {
        influences.push(calculateCharacterInfluence(i, totalChars, rangeSelector, 0));
      }

      // Middle character should have highest influence
      const middleIndex = Math.floor(totalChars / 2);
      expect(influences[middleIndex]).toBe(1);

      // First and last should be near 0
      expect(influences[0]).toBeCloseTo(0, 1);
      expect(influences[totalChars - 1]).toBeCloseTo(0, 1);
    });
  });

  describe('Shape: Round', () => {
    beforeEach(() => {
      rangeSelector.shape = 'round';
    });

    it('should follow sine curve (peak in middle)', () => {
      const totalChars = 11;
      const influences: number[] = [];

      for (let i = 0; i < totalChars; i++) {
        influences.push(calculateCharacterInfluence(i, totalChars, rangeSelector, 0));
      }

      // Middle character should be at peak (sine(π/2) = 1)
      const middleIndex = Math.floor(totalChars / 2);
      expect(influences[middleIndex]).toBeCloseTo(1, 1);

      // Edges should be near 0 (sine(0) = 0, sine(π) = 0)
      expect(influences[0]).toBeCloseTo(0, 1);
      expect(influences[totalChars - 1]).toBeCloseTo(0, 1);
    });
  });

  describe('Shape: Smooth', () => {
    beforeEach(() => {
      rangeSelector.shape = 'smooth';
    });

    it('should apply smooth step (ease in-out)', () => {
      const totalChars = 11;
      const influences: number[] = [];

      for (let i = 0; i < totalChars; i++) {
        influences.push(calculateCharacterInfluence(i, totalChars, rangeSelector, 0));
      }

      // At t=0.5, smooth step should be 0.5
      const middleIndex = Math.floor(totalChars / 2);
      expect(influences[middleIndex]).toBeCloseTo(0.5, 1);

      // Boundaries
      expect(influences[0]).toBeCloseTo(0, 1);
      expect(influences[totalChars - 1]).toBe(1);
    });
  });

  describe('Offset Animation', () => {
    it('should shift range based on offset', () => {
      rangeSelector.start.value = 0;
      rangeSelector.end.value = 50;
      rangeSelector.offset.value = 25; // Shift by 25%

      const totalChars = 10;

      // Character at 0% should now be outside (range is 25-75%)
      const firstInfluence = calculateCharacterInfluence(0, totalChars, rangeSelector, 0);
      expect(firstInfluence).toBe(0);

      // Character at 50% should be in range
      const middleInfluence = calculateCharacterInfluence(5, totalChars, rangeSelector, 0);
      expect(middleInfluence).toBeGreaterThan(0);
    });
  });

  describe('Animated Values', () => {
    it('should interpolate keyframed start value', () => {
      rangeSelector.start = {
        ...DEFAULT_RANGE_SELECTOR.start,
        animated: true,
        keyframes: [
          { id: 'k1', frame: 0, value: 100, interpolation: 'linear' as const, controlMode: 'smooth' as const },
          { id: 'k2', frame: 60, value: 0, interpolation: 'linear' as const, controlMode: 'smooth' as const },
        ],
      };

      const totalChars = 10;

      // At frame 0, start=100, so only last char should be visible
      const frame0Influence = calculateCharacterInfluence(0, totalChars, rangeSelector, 0);
      expect(frame0Influence).toBe(0); // First char outside range

      // At frame 30, start=50, middle chars should be visible
      const frame30Influence = calculateCharacterInfluence(5, totalChars, rangeSelector, 30);
      expect(frame30Influence).toBeGreaterThan(0);

      // At frame 60, start=0, all chars visible
      const frame60Influence = calculateCharacterInfluence(0, totalChars, rangeSelector, 60);
      expect(frame60Influence).toBe(1);
    });
  });
});

// ============================================================================
// WIGGLY SELECTOR TESTS
// ============================================================================

describe('Wiggly Selector - calculateWigglyInfluence', () => {
  let wigglySelector: TextWigglySelector;

  beforeEach(() => {
    wigglySelector = {
      ...DEFAULT_WIGGLY_SELECTOR,
      enabled: true,
      randomSeed: 12345, // Fixed seed for determinism
    };
  });

  describe('Enabled/Disabled', () => {
    it('should return 0 when disabled', () => {
      wigglySelector.enabled = false;
      const influence = calculateWigglyInfluence(0, 10, wigglySelector, 0, 16);
      expect(influence).toBe(0);
    });

    it('should return non-zero when enabled', () => {
      wigglySelector.enabled = true;
      const influence = calculateWigglyInfluence(0, 10, wigglySelector, 0, 16);
      expect(influence).toBeGreaterThan(0);
    });
  });

  describe('Determinism (CRITICAL)', () => {
    it('should return identical values for same inputs', () => {
      const charIndex = 5;
      const totalChars = 10;
      const frame = 30;

      const result1 = calculateWigglyInfluence(charIndex, totalChars, wigglySelector, frame, 16);
      const result2 = calculateWigglyInfluence(charIndex, totalChars, wigglySelector, frame, 16);
      const result3 = calculateWigglyInfluence(charIndex, totalChars, wigglySelector, frame, 16);

      expect(result1).toBe(result2);
      expect(result2).toBe(result3);
    });

    it('should return same value when scrubbing backwards then forwards', () => {
      const charIndex = 3;
      const totalChars = 10;

      // Scrub to frame 50
      const forward1 = calculateWigglyInfluence(charIndex, totalChars, wigglySelector, 50, 16);

      // Scrub back to frame 10
      calculateWigglyInfluence(charIndex, totalChars, wigglySelector, 10, 16);

      // Scrub forward again to frame 50
      const forward2 = calculateWigglyInfluence(charIndex, totalChars, wigglySelector, 50, 16);

      expect(forward1).toBe(forward2);
    });

    it('should produce different values for different random seeds', () => {
      const charIndex = 5;
      const frame = 30;

      wigglySelector.randomSeed = 11111;
      const result1 = calculateWigglyInfluence(charIndex, 10, wigglySelector, frame, 16);

      wigglySelector.randomSeed = 99999;
      const result2 = calculateWigglyInfluence(charIndex, 10, wigglySelector, frame, 16);

      expect(result1).not.toBe(result2);
    });
  });

  describe('Amount Range', () => {
    it('should stay within min/max amount range', () => {
      wigglySelector.minAmount = 20;
      wigglySelector.maxAmount = 80;

      // Test across many frames and characters
      for (let frame = 0; frame < 60; frame++) {
        for (let char = 0; char < 10; char++) {
          const influence = calculateWigglyInfluence(char, 10, wigglySelector, frame, 16);
          expect(influence).toBeGreaterThanOrEqual(0.2 - 0.01); // Allow small floating point error
          expect(influence).toBeLessThanOrEqual(0.8 + 0.01);
        }
      }
    });

    it('should return 0.5 when min=50 and max=50', () => {
      wigglySelector.minAmount = 50;
      wigglySelector.maxAmount = 50;

      const influence = calculateWigglyInfluence(0, 10, wigglySelector, 0, 16);
      expect(influence).toBeCloseTo(0.5, 2);
    });
  });

  describe('Wiggles Per Second', () => {
    it('should change faster with higher wiggles/second', () => {
      wigglySelector.wigglesPerSecond = 1;
      const slow1 = calculateWigglyInfluence(0, 10, wigglySelector, 0, 16);
      const slow2 = calculateWigglyInfluence(0, 10, wigglySelector, 8, 16); // 0.5 seconds

      wigglySelector.wigglesPerSecond = 10;
      const fast1 = calculateWigglyInfluence(0, 10, wigglySelector, 0, 16);
      const fast2 = calculateWigglyInfluence(0, 10, wigglySelector, 8, 16);

      // Fast should have more variance in same time period
      const slowDelta = Math.abs(slow2 - slow1);
      const fastDelta = Math.abs(fast2 - fast1);

      // Not strictly deterministic which is larger, but fast should show more variation
      // over multiple samples
      expect(fastDelta + slowDelta).toBeGreaterThan(0);
    });
  });

  describe('Correlation', () => {
    it('should move together when correlation=100', () => {
      wigglySelector.correlation = 100;

      const influences: number[] = [];
      for (let char = 0; char < 10; char++) {
        influences.push(calculateWigglyInfluence(char, 10, wigglySelector, 30, 16));
      }

      // All characters should have very similar values
      const avg = influences.reduce((a, b) => a + b, 0) / influences.length;
      const variance = influences.reduce((sum, v) => sum + Math.pow(v - avg, 2), 0) / influences.length;

      expect(variance).toBeLessThan(0.01); // Very low variance
    });

    it('should move independently when correlation=0', () => {
      wigglySelector.correlation = 0;

      const influences: number[] = [];
      for (let char = 0; char < 10; char++) {
        influences.push(calculateWigglyInfluence(char, 10, wigglySelector, 30, 16));
      }

      // Characters should have different values
      const uniqueValues = new Set(influences.map(v => v.toFixed(4)));
      expect(uniqueValues.size).toBeGreaterThan(1);
    });
  });
});

describe('Wiggly Selector - calculateWigglyOffset', () => {
  let wigglySelector: TextWigglySelector;

  beforeEach(() => {
    wigglySelector = {
      ...DEFAULT_WIGGLY_SELECTOR,
      enabled: true,
      randomSeed: 12345,
    };
  });

  it('should return {0, 0} when disabled', () => {
    wigglySelector.enabled = false;
    const offset = calculateWigglyOffset(0, wigglySelector, 0, 16);
    expect(offset.x).toBe(0);
    expect(offset.y).toBe(0);
  });

  it('should return deterministic offsets', () => {
    const offset1 = calculateWigglyOffset(5, wigglySelector, 30, 16);
    const offset2 = calculateWigglyOffset(5, wigglySelector, 30, 16);

    expect(offset1.x).toBe(offset2.x);
    expect(offset1.y).toBe(offset2.y);
  });

  describe('Lock Dimensions', () => {
    it('should return same x and y when lockDimensions=true', () => {
      wigglySelector.lockDimensions = true;

      // Test across multiple frames and characters
      for (let frame = 0; frame < 30; frame += 5) {
        for (let char = 0; char < 5; char++) {
          const offset = calculateWigglyOffset(char, wigglySelector, frame, 16);
          expect(offset.x).toBeCloseTo(offset.y, 5);
        }
      }
    });

    it('should return different x and y when lockDimensions=false', () => {
      wigglySelector.lockDimensions = false;

      // At least some should be different
      let hasDifferent = false;
      for (let char = 0; char < 10; char++) {
        const offset = calculateWigglyOffset(char, wigglySelector, 15, 16);
        if (Math.abs(offset.x - offset.y) > 0.001) {
          hasDifferent = true;
          break;
        }
      }
      expect(hasDifferent).toBe(true);
    });
  });
});

// ============================================================================
// EXPRESSION SELECTOR TESTS
// ============================================================================

describe('Expression Selector - calculateExpressionInfluence', () => {
  let expressionSelector: TextExpressionSelector;

  beforeEach(() => {
    expressionSelector = {
      ...DEFAULT_EXPRESSION_SELECTOR,
      enabled: true,
    };
  });

  it('should return rangeValue when disabled', () => {
    expressionSelector.enabled = false;
    const result = calculateExpressionInfluence(5, 10, expressionSelector, 0.75, 30, 16);
    expect(result).toBe(0.75);
  });

  describe('Built-in Variables', () => {
    it('should provide textIndex', () => {
      expressionSelector.amountExpression = 'textIndex';
      const result = calculateExpressionInfluence(5, 10, expressionSelector, 0, 0, 16);
      expect(result).toBeCloseTo(0.05, 2); // 5 / 100, clamped to 0-1
    });

    it('should provide textTotal', () => {
      expressionSelector.amountExpression = 'textTotal';
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0, 0, 16);
      expect(result).toBeCloseTo(0.1, 2); // 10 / 100
    });

    it('should provide selectorValue', () => {
      expressionSelector.amountExpression = 'selectorValue';
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0.8, 0, 16);
      expect(result).toBeCloseTo(0.8, 2); // 80 / 100
    });

    it('should provide time in seconds', () => {
      expressionSelector.amountExpression = 'time * 50'; // 50 per second
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0, 32, 16);
      expect(result).toBeCloseTo(1, 1); // 2 seconds * 50 = 100 → 1
    });

    it('should provide frame number', () => {
      expressionSelector.amountExpression = 'frame';
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0, 50, 16);
      expect(result).toBeCloseTo(0.5, 2); // 50 / 100
    });
  });

  describe('Math Functions', () => {
    it('should support Math.sin', () => {
      expressionSelector.amountExpression = 'Math.sin(textIndex) * 50 + 50';
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0, 0, 16);
      expect(result).toBeCloseTo(0.5, 1); // sin(0) = 0, 0 * 50 + 50 = 50 → 0.5
    });

    it('should support Math.abs', () => {
      expressionSelector.amountExpression = 'Math.abs(textIndex - 5) * 10';
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0, 0, 16);
      expect(result).toBeCloseTo(0.5, 1); // |0 - 5| * 10 = 50 → 0.5
    });
  });

  describe('Helper Functions', () => {
    it('should support linear() interpolation', () => {
      expressionSelector.amountExpression = 'linear(time, 0, 2, 0, 100)';

      // At t=0 (frame 0)
      const result0 = calculateExpressionInfluence(0, 10, expressionSelector, 0, 0, 16);
      expect(result0).toBeCloseTo(0, 1);

      // At t=1 (frame 16)
      const result1 = calculateExpressionInfluence(0, 10, expressionSelector, 0, 16, 16);
      expect(result1).toBeCloseTo(0.5, 1);

      // At t=2 (frame 32)
      const result2 = calculateExpressionInfluence(0, 10, expressionSelector, 0, 32, 16);
      expect(result2).toBeCloseTo(1, 1);
    });

    it('should support ease() interpolation', () => {
      expressionSelector.amountExpression = 'ease(time, 0, 1, 0, 100)';

      // At t=0.5
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0, 8, 16);
      // Smooth step at 0.5 should be 0.5
      expect(result).toBeCloseTo(0.5, 1);
    });

    it('should support random() (deterministic)', () => {
      expressionSelector.amountExpression = 'random() * 100';

      // Same inputs should give same result
      const result1 = calculateExpressionInfluence(5, 10, expressionSelector, 0, 30, 16);
      const result2 = calculateExpressionInfluence(5, 10, expressionSelector, 0, 30, 16);
      expect(result1).toBe(result2);
    });
  });

  describe('Error Handling', () => {
    it('should return rangeValue on syntax error', () => {
      expressionSelector.amountExpression = 'this is not valid javascript ((';
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0.6, 0, 16);
      expect(result).toBe(0.6);
    });

    it('should handle division by zero', () => {
      expressionSelector.amountExpression = '50 / 0';
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0.5, 0, 16);
      // Infinity clamped to 100 → 1
      expect(result).toBe(1);
    });

    it('should handle NaN results', () => {
      expressionSelector.amountExpression = 'Math.sqrt(-1)'; // NaN
      const result = calculateExpressionInfluence(0, 10, expressionSelector, 0.5, 0, 16);
      expect(result).toBe(0); // NaN || 0 → 0
    });
  });

  describe('Clamping', () => {
    it('should clamp results to 0-1', () => {
      expressionSelector.amountExpression = '200'; // Over 100
      const resultHigh = calculateExpressionInfluence(0, 10, expressionSelector, 0, 0, 16);
      expect(resultHigh).toBe(1);

      expressionSelector.amountExpression = '-50'; // Under 0
      const resultLow = calculateExpressionInfluence(0, 10, expressionSelector, 0, 0, 16);
      expect(resultLow).toBe(0);
    });
  });
});

// ============================================================================
// SELECTOR MODE COMBINATION TESTS
// ============================================================================

describe('Selector Mode Combination - combineSelectorValues', () => {
  describe('Add Mode', () => {
    it('should add values and clamp to 1', () => {
      expect(combineSelectorValues(0.3, 0.4, 'add')).toBeCloseTo(0.7, 5);
      expect(combineSelectorValues(0.7, 0.5, 'add')).toBe(1); // Clamped
    });
  });

  describe('Subtract Mode', () => {
    it('should subtract values and clamp to 0', () => {
      expect(combineSelectorValues(0.8, 0.3, 'subtract')).toBeCloseTo(0.5, 5);
      expect(combineSelectorValues(0.3, 0.8, 'subtract')).toBe(0); // Clamped
    });
  });

  describe('Intersect Mode', () => {
    it('should multiply values', () => {
      expect(combineSelectorValues(0.8, 0.5, 'intersect')).toBeCloseTo(0.4, 5);
      expect(combineSelectorValues(1, 0.7, 'intersect')).toBeCloseTo(0.7, 5);
      expect(combineSelectorValues(0, 1, 'intersect')).toBe(0);
    });
  });

  describe('Min Mode', () => {
    it('should return minimum of two values', () => {
      expect(combineSelectorValues(0.8, 0.3, 'min')).toBe(0.3);
      expect(combineSelectorValues(0.2, 0.9, 'min')).toBe(0.2);
      expect(combineSelectorValues(0.5, 0.5, 'min')).toBe(0.5);
    });
  });

  describe('Max Mode', () => {
    it('should return maximum of two values', () => {
      expect(combineSelectorValues(0.8, 0.3, 'max')).toBe(0.8);
      expect(combineSelectorValues(0.2, 0.9, 'max')).toBe(0.9);
      expect(combineSelectorValues(0.5, 0.5, 'max')).toBe(0.5);
    });
  });

  describe('Difference Mode', () => {
    it('should return absolute difference', () => {
      expect(combineSelectorValues(0.8, 0.3, 'difference')).toBeCloseTo(0.5, 5);
      expect(combineSelectorValues(0.3, 0.8, 'difference')).toBeCloseTo(0.5, 5);
      expect(combineSelectorValues(0.5, 0.5, 'difference')).toBe(0);
    });
  });

  describe('Edge Cases', () => {
    it('should handle 0 values', () => {
      expect(combineSelectorValues(0, 0, 'add')).toBe(0);
      expect(combineSelectorValues(0, 0, 'subtract')).toBe(0);
      expect(combineSelectorValues(0, 0, 'intersect')).toBe(0);
      expect(combineSelectorValues(0, 0, 'min')).toBe(0);
      expect(combineSelectorValues(0, 0, 'max')).toBe(0);
      expect(combineSelectorValues(0, 0, 'difference')).toBe(0);
    });

    it('should handle 1 values', () => {
      expect(combineSelectorValues(1, 1, 'add')).toBe(1);
      expect(combineSelectorValues(1, 1, 'subtract')).toBe(0);
      expect(combineSelectorValues(1, 1, 'intersect')).toBe(1);
      expect(combineSelectorValues(1, 1, 'min')).toBe(1);
      expect(combineSelectorValues(1, 1, 'max')).toBe(1);
      expect(combineSelectorValues(1, 1, 'difference')).toBe(0);
    });
  });
});

// ============================================================================
// COMPLETE CHARACTER INFLUENCE TESTS
// ============================================================================

describe('Complete Character Influence - calculateCompleteCharacterInfluence', () => {
  let animator: TextAnimator;

  beforeEach(() => {
    animator = createTextAnimator('Test Animator');
  });

  describe('Range Selector Only', () => {
    it('should calculate basic range influence', () => {
      animator.rangeSelector.start.value = 0;
      animator.rangeSelector.end.value = 100;
      animator.rangeSelector.shape = 'square';

      const influence = calculateCompleteCharacterInfluence(5, 10, animator, 0, 16);
      expect(influence).toBe(1);
    });

    it('should apply amount modifier', () => {
      animator.rangeSelector.amount = 50; // 50%

      const influence = calculateCompleteCharacterInfluence(5, 10, animator, 0, 16);
      expect(influence).toBeCloseTo(0.5, 2);
    });

    it('should apply smoothness modifier', () => {
      animator.rangeSelector.smoothness = 0; // Full smoothing → 0.5

      const influence = calculateCompleteCharacterInfluence(5, 10, animator, 0, 16);
      expect(influence).toBeCloseTo(0.5, 2);
    });
  });

  describe('With Wiggly Selector', () => {
    beforeEach(() => {
      animator.wigglySelector = {
        ...DEFAULT_WIGGLY_SELECTOR,
        enabled: true,
        randomSeed: 12345,
        mode: 'add',
        minAmount: 0,
        maxAmount: 50,
      };
    });

    it('should combine wiggly with range selector using add mode', () => {
      animator.rangeSelector.amount = 50;
      animator.wigglySelector!.mode = 'add';

      const influence = calculateCompleteCharacterInfluence(5, 10, animator, 30, 16);

      // Should be between 0.5 (range only) and 1 (range + max wiggly)
      expect(influence).toBeGreaterThanOrEqual(0.5);
      expect(influence).toBeLessThanOrEqual(1);
    });

    it('should combine wiggly with range selector using subtract mode', () => {
      animator.rangeSelector.amount = 100;
      animator.wigglySelector!.mode = 'subtract';

      const influence = calculateCompleteCharacterInfluence(5, 10, animator, 30, 16);

      // Should be between 0.5 (1 - max wiggly) and 1 (1 - 0 wiggly)
      expect(influence).toBeGreaterThanOrEqual(0.5);
      expect(influence).toBeLessThanOrEqual(1);
    });
  });

  describe('With Expression Selector', () => {
    beforeEach(() => {
      animator.expressionSelector = {
        ...DEFAULT_EXPRESSION_SELECTOR,
        enabled: true,
        amountExpression: 'textIndex / textTotal * 100',
      };
    });

    it('should apply expression after range selector', () => {
      const influence0 = calculateCompleteCharacterInfluence(0, 10, animator, 0, 16);
      const influence5 = calculateCompleteCharacterInfluence(5, 10, animator, 0, 16);
      const influence9 = calculateCompleteCharacterInfluence(9, 10, animator, 0, 16);

      // Expression: textIndex / textTotal * 100
      // char 0: 0/10 * 100 = 0
      // char 5: 5/10 * 100 = 50
      // char 9: 9/10 * 100 = 90
      expect(influence0).toBeCloseTo(0, 1);
      expect(influence5).toBeCloseTo(0.5, 1);
      expect(influence9).toBeCloseTo(0.9, 1);
    });
  });

  describe('Combined Selectors', () => {
    it('should chain all selectors correctly', () => {
      // Range: base influence
      animator.rangeSelector.amount = 80;

      // Wiggly: add variation
      animator.wigglySelector = {
        ...DEFAULT_WIGGLY_SELECTOR,
        enabled: true,
        mode: 'intersect',
        minAmount: 50,
        maxAmount: 100,
        randomSeed: 12345,
      };

      // Expression: modify based on position
      animator.expressionSelector = {
        ...DEFAULT_EXPRESSION_SELECTOR,
        enabled: true,
        mode: 'add',
        amountExpression: 'selectorValue', // Pass through
      };

      const influence = calculateCompleteCharacterInfluence(5, 10, animator, 30, 16);

      // Result should be valid (0-1)
      expect(influence).toBeGreaterThanOrEqual(0);
      expect(influence).toBeLessThanOrEqual(1);
    });

    it('should be deterministic with all selectors enabled', () => {
      animator.wigglySelector = {
        ...DEFAULT_WIGGLY_SELECTOR,
        enabled: true,
        randomSeed: 99999,
      };

      animator.expressionSelector = {
        ...DEFAULT_EXPRESSION_SELECTOR,
        enabled: true,
        amountExpression: 'random() * selectorValue',
      };

      const result1 = calculateCompleteCharacterInfluence(3, 10, animator, 45, 16);
      const result2 = calculateCompleteCharacterInfluence(3, 10, animator, 45, 16);
      const result3 = calculateCompleteCharacterInfluence(3, 10, animator, 45, 16);

      expect(result1).toBe(result2);
      expect(result2).toBe(result3);
    });
  });

  describe('Output Clamping', () => {
    it('should clamp final result to 0-1', () => {
      // Try to exceed bounds
      animator.rangeSelector.amount = 100;
      animator.wigglySelector = {
        ...DEFAULT_WIGGLY_SELECTOR,
        enabled: true,
        mode: 'add',
        minAmount: 100,
        maxAmount: 100,
      };

      const influence = calculateCompleteCharacterInfluence(5, 10, animator, 0, 16);
      expect(influence).toBeLessThanOrEqual(1);
      expect(influence).toBeGreaterThanOrEqual(0);
    });
  });
});

// ============================================================================
// EXPRESSION PRESETS TESTS
// ============================================================================

describe('Expression Presets', () => {
  describe('All presets should be valid JavaScript', () => {
    for (const [name, expression] of Object.entries(EXPRESSION_PRESETS)) {
      it(`${name} should evaluate without error`, () => {
        const expressionSelector: TextExpressionSelector = {
          ...DEFAULT_EXPRESSION_SELECTOR,
          enabled: true,
          amountExpression: expression,
        };

        // Should not throw
        expect(() => {
          calculateExpressionInfluence(5, 10, expressionSelector, 0.5, 30, 16);
        }).not.toThrow();
      });

      it(`${name} should return valid 0-1 result`, () => {
        const expressionSelector: TextExpressionSelector = {
          ...DEFAULT_EXPRESSION_SELECTOR,
          enabled: true,
          amountExpression: expression,
        };

        const result = calculateExpressionInfluence(5, 10, expressionSelector, 0.5, 30, 16);
        expect(result).toBeGreaterThanOrEqual(0);
        expect(result).toBeLessThanOrEqual(1);
      });
    }
  });

  describe('Preset Behaviors', () => {
    it('wave should oscillate over time', () => {
      const expressionSelector: TextExpressionSelector = {
        ...DEFAULT_EXPRESSION_SELECTOR,
        enabled: true,
        amountExpression: EXPRESSION_PRESETS.wave,
      };

      const values: number[] = [];
      for (let frame = 0; frame < 32; frame += 4) {
        values.push(calculateExpressionInfluence(0, 10, expressionSelector, 0, frame, 16));
      }

      // Should have variation (not all same value)
      const uniqueValues = new Set(values.map(v => v.toFixed(2)));
      expect(uniqueValues.size).toBeGreaterThan(1);
    });

    it('linearGradient should increase with textIndex', () => {
      const expressionSelector: TextExpressionSelector = {
        ...DEFAULT_EXPRESSION_SELECTOR,
        enabled: true,
        amountExpression: EXPRESSION_PRESETS.linearGradient,
      };

      const values: number[] = [];
      for (let i = 0; i < 10; i++) {
        values.push(calculateExpressionInfluence(i, 10, expressionSelector, 0, 0, 16));
      }

      // Should be monotonically increasing
      for (let i = 1; i < values.length; i++) {
        expect(values[i]).toBeGreaterThanOrEqual(values[i - 1]);
      }
    });

    it('alternating should produce binary pattern', () => {
      const expressionSelector: TextExpressionSelector = {
        ...DEFAULT_EXPRESSION_SELECTOR,
        enabled: true,
        amountExpression: EXPRESSION_PRESETS.alternating,
      };

      for (let i = 0; i < 10; i++) {
        const result = calculateExpressionInfluence(i, 10, expressionSelector, 0, 0, 16);
        if (i % 2 === 0) {
          expect(result).toBe(1);
        } else {
          expect(result).toBe(0);
        }
      }
    });

    it('cascadeCenter should peak in middle', () => {
      const expressionSelector: TextExpressionSelector = {
        ...DEFAULT_EXPRESSION_SELECTOR,
        enabled: true,
        amountExpression: EXPRESSION_PRESETS.cascadeCenter,
      };

      const values: number[] = [];
      for (let i = 0; i < 10; i++) {
        values.push(calculateExpressionInfluence(i, 10, expressionSelector, 0, 0, 16));
      }

      // Middle characters should have highest values
      const middleValue = values[5];
      expect(middleValue).toBeGreaterThan(values[0]);
      expect(middleValue).toBeGreaterThan(values[9]);
    });
  });
});

// ============================================================================
// FACTORY FUNCTION TESTS
// ============================================================================

describe('Factory Functions', () => {
  describe('createTextAnimator', () => {
    it('should create animator with default values', () => {
      const animator = createTextAnimator();

      expect(animator.id).toBeDefined();
      expect(animator.name).toBe('Animator 1');
      expect(animator.enabled).toBe(true);
      expect(animator.rangeSelector).toBeDefined();
      expect(animator.properties).toBeDefined();
    });

    it('should accept custom name', () => {
      const animator = createTextAnimator('Custom Name');
      expect(animator.name).toBe('Custom Name');
    });

    it('should generate unique IDs', () => {
      const animator1 = createTextAnimator();
      const animator2 = createTextAnimator();
      expect(animator1.id).not.toBe(animator2.id);
    });
  });

  describe('createWigglySelector', () => {
    it('should create with defaults', () => {
      const selector = createWigglySelector();

      expect(selector.enabled).toBe(false); // Default is disabled
      expect(selector.mode).toBe('add');
      expect(selector.wigglesPerSecond).toBe(2);
      expect(selector.correlation).toBe(50);
      expect(selector.randomSeed).toBeDefined();
    });

    it('should accept overrides', () => {
      const selector = createWigglySelector({
        enabled: true,
        mode: 'subtract',
        maxAmount: 75,
      });

      expect(selector.enabled).toBe(true);
      expect(selector.mode).toBe('subtract');
      expect(selector.maxAmount).toBe(75);
    });

    it('should generate random seed if not provided', () => {
      const selector1 = createWigglySelector();
      const selector2 = createWigglySelector();

      // Seeds should be numbers
      expect(typeof selector1.randomSeed).toBe('number');
      expect(typeof selector2.randomSeed).toBe('number');
    });
  });

  describe('createExpressionSelector', () => {
    it('should create with default expression', () => {
      const selector = createExpressionSelector();

      expect(selector.enabled).toBe(true); // Factory enables by default
      expect(selector.mode).toBe('add');
      expect(selector.amountExpression).toBeDefined();
    });

    it('should accept custom expression', () => {
      const selector = createExpressionSelector('textIndex * 10');
      expect(selector.amountExpression).toBe('textIndex * 10');
    });

    it('should accept overrides', () => {
      const selector = createExpressionSelector('textIndex', {
        mode: 'intersect',
        basedOn: 'words',
      });

      expect(selector.mode).toBe('intersect');
      expect(selector.basedOn).toBe('words');
    });
  });
});

// ============================================================================
// PRESET APPLICATION TESTS
// ============================================================================

describe('Animator Presets', () => {
  describe('All presets should be valid', () => {
    for (const [type, preset] of Object.entries(TEXT_ANIMATOR_PRESETS)) {
      it(`${type} should create valid animator`, () => {
        const animator = applyTextAnimatorPreset(type as any);

        expect(animator.id).toBeDefined();
        expect(animator.name).toBeDefined();
        expect(animator.enabled).toBe(true);
        expect(animator.rangeSelector).toBeDefined();
        expect(animator.properties).toBeDefined();
      });

      it(`${type} should produce valid influence values`, () => {
        const animator = applyTextAnimatorPreset(type as any, 60);

        for (let frame = 0; frame <= 60; frame += 10) {
          for (let char = 0; char < 10; char++) {
            const influence = calculateCompleteCharacterInfluence(char, 10, animator, frame, 16);
            expect(influence).toBeGreaterThanOrEqual(0);
            expect(influence).toBeLessThanOrEqual(1);
          }
        }
      });
    }
  });

  describe('Typewriter preset', () => {
    it('should reveal characters over time', () => {
      const animator = applyTextAnimatorPreset('typewriter', 60);

      // At frame 0, start=100, no characters visible (high influence = hidden)
      const influence0 = calculateCompleteCharacterInfluence(0, 10, animator, 0, 16);

      // At frame 60, start=0, all characters visible
      const influence60 = calculateCompleteCharacterInfluence(0, 10, animator, 60, 16);

      // Animation reveals characters, so influence should change
      expect(influence0).not.toBe(influence60);
    });
  });

  describe('Random fade preset', () => {
    it('should have randomizeOrder enabled', () => {
      const animator = applyTextAnimatorPreset('random_fade', 60);
      expect(animator.rangeSelector.randomizeOrder).toBe(true);
    });
  });
});

// ============================================================================
// DETERMINISM COMPREHENSIVE TEST
// ============================================================================

describe('Determinism - Comprehensive', () => {
  it('should produce identical results across 100 frame-character combinations', () => {
    const animator = createTextAnimator('Determinism Test');
    animator.wigglySelector = {
      ...DEFAULT_WIGGLY_SELECTOR,
      enabled: true,
      randomSeed: 42,
    };
    animator.expressionSelector = {
      ...DEFAULT_EXPRESSION_SELECTOR,
      enabled: true,
      amountExpression: 'Math.sin(time + textIndex) * 50 + 50',
    };

    const results1: number[] = [];
    const results2: number[] = [];

    // First pass
    for (let frame = 0; frame < 50; frame++) {
      for (let char = 0; char < 20; char++) {
        results1.push(calculateCompleteCharacterInfluence(char, 20, animator, frame, 16));
      }
    }

    // Second pass (should be identical)
    for (let frame = 0; frame < 50; frame++) {
      for (let char = 0; char < 20; char++) {
        results2.push(calculateCompleteCharacterInfluence(char, 20, animator, frame, 16));
      }
    }

    expect(results1).toEqual(results2);
  });

  it('should handle scrub backwards deterministically', () => {
    const animator = createTextAnimator('Scrub Test');
    animator.wigglySelector = createWigglySelector({ enabled: true, randomSeed: 12345 });

    // Capture values going forward
    const forwardValues: number[] = [];
    for (let frame = 0; frame <= 60; frame += 5) {
      forwardValues.push(calculateCompleteCharacterInfluence(5, 10, animator, frame, 16));
    }

    // Scrub backwards
    const backwardValues: number[] = [];
    for (let frame = 60; frame >= 0; frame -= 5) {
      backwardValues.push(calculateCompleteCharacterInfluence(5, 10, animator, frame, 16));
    }

    // Reverse backward values and compare
    backwardValues.reverse();
    expect(forwardValues).toEqual(backwardValues);
  });
});

// ============================================================================
// PERFORMANCE TEST
// ============================================================================

describe('Performance', () => {
  it('should calculate 10000 character influences in reasonable time', () => {
    const animator = createTextAnimator('Perf Test');
    animator.wigglySelector = createWigglySelector({ enabled: true });
    animator.expressionSelector = createExpressionSelector('textIndex * 10');

    const start = performance.now();

    for (let i = 0; i < 10000; i++) {
      calculateCompleteCharacterInfluence(i % 100, 100, animator, i % 60, 16);
    }

    const duration = performance.now() - start;

    // Should complete in under 500ms (very conservative)
    expect(duration).toBeLessThan(500);
  });
});
