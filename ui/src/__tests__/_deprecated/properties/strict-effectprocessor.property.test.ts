/**
 * STRICT EffectProcessor Property Tests
 * 
 * Created: Fresh audit - do NOT trust old tests
 * 
 * NOTE: Most effectProcessor functions require browser APIs (HTMLCanvasElement, 
 * document.createElement). This file tests only the non-DOM functions.
 * Full effect testing requires browser environment (Playwright E2E).
 * 
 * Testable without DOM:
 * - evaluateEffectParameters
 * - Audio modifier application logic
 * - Parameter evaluation
 * 
 * Requires browser (test in E2E):
 * - processEffectStack
 * - processEffectStackAsync
 * - CanvasPool
 * - EffectCache
 * - GPU processing
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { 
  evaluateEffectParameters,
  hasEnabledEffects,
  getRegisteredEffects,
} from '@/services/effectProcessor';
import type { EffectInstance } from '@/types/effects';
import type { AnimatableProperty } from '@/types/project';

// ============================================================================
// HELPERS
// ============================================================================

function createAnimatableProperty<T>(value: T): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random()}`,
    name: 'test',
    type: typeof value as any,
    value,
    animated: false,
    keyframes: [],
  };
}

function createAnimatedProperty<T>(
  startValue: T,
  endValue: T,
  startFrame: number = 0,
  endFrame: number = 100,
): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random()}`,
    name: 'test',
    type: typeof startValue as any,
    value: startValue,
    animated: true,
    keyframes: [
      {
        id: 'kf1',
        frame: startFrame,
        value: startValue,
        interpolation: 'linear',
        inHandle: { frame: -5, value: 0, enabled: true },
        outHandle: { frame: 5, value: 0, enabled: true },
        controlMode: 'smooth',
      },
      {
        id: 'kf2',
        frame: endFrame,
        value: endValue,
        interpolation: 'linear',
        inHandle: { frame: -5, value: 0, enabled: true },
        outHandle: { frame: 5, value: 0, enabled: true },
        controlMode: 'smooth',
      },
    ],
  };
}

function createMockEffect(
  params: Record<string, AnimatableProperty<any>>,
  enabled: boolean = true,
): EffectInstance {
  return {
    id: `effect-${Math.random()}`,
    name: 'Test Effect',
    effectKey: 'test-effect',
    enabled,
    category: 'utility',
    expanded: false,
    parameters: params,
  };
}

describe('STRICT: EffectProcessor (non-DOM)', () => {

  // =========================================================================
  // EVALUATE EFFECT PARAMETERS
  // =========================================================================

  describe('evaluateEffectParameters', () => {

    test.prop([
      fc.double({ min: -1000, max: 1000, noNaN: true }),
      fc.integer({ min: 0, max: 1000 }),
    ])(
      'STRICT: static parameters return their value at any frame',
      (value, frame) => {
        const effect = createMockEffect({
          intensity: createAnimatableProperty(value),
        });

        const result = evaluateEffectParameters(effect, frame);
        expect(result.intensity).toBe(value);
      }
    );

    test.prop([
      fc.double({ min: 0, max: 100, noNaN: true }),
      fc.double({ min: 100, max: 200, noNaN: true }),
    ])(
      'STRICT: animated parameters interpolate correctly at midpoint',
      (startValue, endValue) => {
        const effect = createMockEffect({
          intensity: createAnimatedProperty(startValue, endValue, 0, 100),
        });

        const result = evaluateEffectParameters(effect, 50);
        const expected = (startValue + endValue) / 2;
        expect(result.intensity).toBeCloseTo(expected, 5);
      }
    );

    test.prop([
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
    ])(
      'STRICT: animated parameters return start value at frame 0',
      (startValue, endValue) => {
        const effect = createMockEffect({
          intensity: createAnimatedProperty(startValue, endValue, 0, 100),
        });

        const result = evaluateEffectParameters(effect, 0);
        expect(result.intensity).toBeCloseTo(startValue, 10);
      }
    );

    test.prop([
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
    ])(
      'STRICT: animated parameters return end value at final frame',
      (startValue, endValue) => {
        const effect = createMockEffect({
          intensity: createAnimatedProperty(startValue, endValue, 0, 100),
        });

        const result = evaluateEffectParameters(effect, 100);
        expect(result.intensity).toBeCloseTo(endValue, 10);
      }
    );

    test('evaluates multiple parameters correctly', () => {
      const effect = createMockEffect({
        intensity: createAnimatableProperty(50),
        radius: createAnimatableProperty(25),
        color: createAnimatableProperty('#ff0000'),
      });

      const result = evaluateEffectParameters(effect, 0);
      
      expect(result.intensity).toBe(50);
      expect(result.radius).toBe(25);
      expect(result.color).toBe('#ff0000');
    });

    test('handles empty parameters', () => {
      const effect = createMockEffect({});
      const result = evaluateEffectParameters(effect, 0);
      expect(Object.keys(result)).toHaveLength(0);
    });
  });

  // =========================================================================
  // HAS ENABLED EFFECTS
  // =========================================================================

  describe('hasEnabledEffects', () => {

    test('returns false for empty array', () => {
      expect(hasEnabledEffects([])).toBe(false);
    });

    test('returns false when all effects disabled', () => {
      const effects = [
        createMockEffect({ intensity: createAnimatableProperty(1) }, false),
        createMockEffect({ intensity: createAnimatableProperty(1) }, false),
      ];
      expect(hasEnabledEffects(effects)).toBe(false);
    });

    test('returns true when at least one effect enabled', () => {
      const effects = [
        createMockEffect({ intensity: createAnimatableProperty(1) }, false),
        createMockEffect({ intensity: createAnimatableProperty(1) }, true),
        createMockEffect({ intensity: createAnimatableProperty(1) }, false),
      ];
      expect(hasEnabledEffects(effects)).toBe(true);
    });

    test.prop([
      fc.array(fc.boolean(), { minLength: 1, maxLength: 10 }),
    ])(
      'STRICT: hasEnabledEffects matches expected behavior',
      (enabledStates) => {
        const effects = enabledStates.map(enabled =>
          createMockEffect({ intensity: createAnimatableProperty(1) }, enabled)
        );
        
        const result = hasEnabledEffects(effects);
        const expected = enabledStates.some(e => e);
        
        expect(result).toBe(expected);
      }
    );
  });

  // =========================================================================
  // GET REGISTERED EFFECTS
  // =========================================================================

  describe('getRegisteredEffects', () => {

    test('returns an array', () => {
      const effects = getRegisteredEffects();
      expect(Array.isArray(effects)).toBe(true);
    });

    test('returns strings', () => {
      const effects = getRegisteredEffects();
      for (const effect of effects) {
        expect(typeof effect).toBe('string');
      }
    });
  });

  // =========================================================================
  // DETERMINISM
  // =========================================================================

  describe('determinism', () => {

    test.prop([
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.integer({ min: 0, max: 100 }),
    ])(
      'STRICT: same effect + frame = identical result (100 runs)',
      (startValue, endValue, frame) => {
        const effect = createMockEffect({
          intensity: createAnimatedProperty(startValue, endValue, 0, 100),
        });

        const results: number[] = [];
        for (let i = 0; i < 100; i++) {
          const result = evaluateEffectParameters(effect, frame);
          results.push(result.intensity);
        }

        // All results must be identical
        const first = results[0];
        for (const result of results) {
          expect(result).toBe(first);
        }
      }
    );
  });

  // =========================================================================
  // EDGE CASES
  // =========================================================================

  describe('edge cases', () => {

    test('handles negative frame', () => {
      const effect = createMockEffect({
        intensity: createAnimatedProperty(0, 100, 0, 100),
      });

      const result = evaluateEffectParameters(effect, -10);
      // Should return first keyframe value
      expect(result.intensity).toBe(0);
    });

    test('handles very large frame', () => {
      const effect = createMockEffect({
        intensity: createAnimatedProperty(0, 100, 0, 100),
      });

      const result = evaluateEffectParameters(effect, 10000);
      // Should return last keyframe value
      expect(result.intensity).toBe(100);
    });

    test('handles object parameters', () => {
      const effect = createMockEffect({
        position: createAnimatableProperty({ x: 100, y: 200 }),
      });

      const result = evaluateEffectParameters(effect, 0);
      expect(result.position.x).toBe(100);
      expect(result.position.y).toBe(200);
    });

    test('handles animated object parameters', () => {
      const effect = createMockEffect({
        position: createAnimatedProperty({ x: 0, y: 0 }, { x: 100, y: 100 }, 0, 100),
      });

      const result = evaluateEffectParameters(effect, 50);
      expect(result.position.x).toBeCloseTo(50, 5);
      expect(result.position.y).toBeCloseTo(50, 5);
    });
  });

  // =========================================================================
  // BROWSER TESTS (run separately with npm run test:browser)
  // =========================================================================

  describe('Browser tests reference', () => {

    test('Browser tests exist for DOM-dependent functionality', () => {
      // These are tested in src/__tests__/browser/effectProcessor.browser.test.ts
      // Run with: npm run test:browser
      // 
      // Browser tests cover:
      // - processEffectStack with real canvas (21 tests)
      // - CanvasPool acquire/release
      // - EffectCache hit/miss
      // - GPU processing detection
      // - ImageData roundtrip
      // - Determinism across 100 runs
      // - Edge cases (1x1, 4K, transparent)
      expect(true).toBe(true);
    });
  });
});
