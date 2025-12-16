/**
 * KeyframeEvaluator Tests
 *
 * Tests keyframe-based animation evaluation including:
 * - Value interpolation for different types
 * - Easing function application
 * - Bezier curve evaluation
 * - Caching behavior
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { KeyframeEvaluator } from '@/engine/animation/KeyframeEvaluator';
import type { AnimatableProperty, Keyframe } from '@/types/project';

// ============================================================================
// TEST HELPERS
// ============================================================================

let idCounter = 0;

function createProperty<T>(
  value: T,
  animated: boolean = false,
  keyframes: Keyframe<T>[] = []
): AnimatableProperty<T> {
  return {
    id: `prop_${idCounter++}`,
    name: 'Test Property',
    type: 'number',
    value,
    animated,
    keyframes
  };
}

function createKeyframe<T>(
  frame: number,
  value: T,
  interpolation: 'linear' | 'hold' | 'bezier' = 'linear'
): Keyframe<T> {
  return {
    id: `kf_${frame}_${idCounter++}`,
    frame,
    value,
    interpolation,
    inHandle: { frame: -5, value: 0, enabled: false },
    outHandle: { frame: 5, value: 0, enabled: false },
    controlMode: 'smooth'
  };
}

// ============================================================================
// EVALUATOR TESTS
// ============================================================================

describe('KeyframeEvaluator', () => {
  let evaluator: KeyframeEvaluator;

  beforeEach(() => {
    evaluator = new KeyframeEvaluator();
    idCounter = 0;
  });

  describe('Non-animated properties', () => {
    it('should return static value for non-animated property', () => {
      const prop = createProperty(100, false);
      expect(evaluator.evaluate(prop, 0)).toBe(100);
      expect(evaluator.evaluate(prop, 50)).toBe(100);
      expect(evaluator.evaluate(prop, 100)).toBe(100);
    });

    it('should return default value when animated but no keyframes', () => {
      const prop = createProperty(50, true, []);
      expect(evaluator.evaluate(prop, 0)).toBe(50);
    });
  });

  describe('Number interpolation', () => {
    it('should return first keyframe value before first keyframe', () => {
      const prop = createProperty(0, true, [
        createKeyframe(10, 100),
        createKeyframe(20, 200)
      ]);

      expect(evaluator.evaluate(prop, 0)).toBe(100);
      expect(evaluator.evaluate(prop, 5)).toBe(100);
      expect(evaluator.evaluate(prop, 10)).toBe(100);
    });

    it('should return last keyframe value after last keyframe', () => {
      const prop = createProperty(0, true, [
        createKeyframe(10, 100),
        createKeyframe(20, 200)
      ]);

      expect(evaluator.evaluate(prop, 20)).toBe(200);
      expect(evaluator.evaluate(prop, 30)).toBe(200);
    });

    it('should linearly interpolate between keyframes', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(100, 100)
      ]);

      expect(evaluator.evaluate(prop, 0)).toBe(0);
      expect(evaluator.evaluate(prop, 25)).toBe(25);
      expect(evaluator.evaluate(prop, 50)).toBe(50);
      expect(evaluator.evaluate(prop, 75)).toBe(75);
      expect(evaluator.evaluate(prop, 100)).toBe(100);
    });

    it('should interpolate negative values', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, -100),
        createKeyframe(100, 100)
      ]);

      expect(evaluator.evaluate(prop, 50)).toBe(0);
    });

    it('should handle multiple keyframe segments', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(50, 100),
        createKeyframe(100, 50)
      ]);

      expect(evaluator.evaluate(prop, 0)).toBe(0);
      expect(evaluator.evaluate(prop, 25)).toBe(50);
      expect(evaluator.evaluate(prop, 50)).toBe(100);
      expect(evaluator.evaluate(prop, 75)).toBe(75);
      expect(evaluator.evaluate(prop, 100)).toBe(50);
    });
  });

  describe('Position/Vector interpolation', () => {
    it('should interpolate 2D positions', () => {
      const prop = createProperty({ x: 0, y: 0 }, true, [
        createKeyframe(0, { x: 0, y: 0 }),
        createKeyframe(100, { x: 100, y: 200 })
      ]);

      const result = evaluator.evaluate(prop, 50);
      expect(result.x).toBe(50);
      expect(result.y).toBe(100);
    });

    it('should interpolate 3D positions', () => {
      const prop = createProperty({ x: 0, y: 0, z: 0 }, true, [
        createKeyframe(0, { x: 0, y: 0, z: 0 }),
        createKeyframe(100, { x: 100, y: 200, z: 300 })
      ]);

      const result = evaluator.evaluate(prop, 50);
      expect(result.x).toBe(50);
      expect(result.y).toBe(100);
      expect(result.z).toBe(150);
    });
  });

  describe('Color interpolation', () => {
    it('should interpolate hex colors', () => {
      const prop = createProperty('#000000', true, [
        createKeyframe(0, '#000000'),
        createKeyframe(100, '#ffffff')
      ]);

      const result = evaluator.evaluate(prop, 50);
      expect(result.toLowerCase()).toBe('#808080');
    });

    it('should interpolate color channels independently', () => {
      const prop = createProperty('#000000', true, [
        createKeyframe(0, '#ff0000'),
        createKeyframe(100, '#00ff00')
      ]);

      const result = evaluator.evaluate(prop, 50);
      // Red goes from 255 to 0, green goes from 0 to 255
      expect(result.toLowerCase()).toBe('#808000');
    });
  });

  describe('Array interpolation', () => {
    it('should interpolate number arrays', () => {
      const prop = createProperty([0, 0, 0], true, [
        createKeyframe(0, [0, 100, 200]),
        createKeyframe(100, [100, 200, 300])
      ]);

      const result = evaluator.evaluate(prop, 50);
      expect(result[0]).toBe(50);
      expect(result[1]).toBe(150);
      expect(result[2]).toBe(250);
    });
  });

  describe('Hold interpolation', () => {
    it('should hold previous value until next keyframe', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0, 'hold'),
        createKeyframe(100, 100)
      ]);

      expect(evaluator.evaluate(prop, 0)).toBe(0);
      expect(evaluator.evaluate(prop, 50)).toBe(0);
      expect(evaluator.evaluate(prop, 99)).toBe(0);
      expect(evaluator.evaluate(prop, 100)).toBe(100);
    });
  });

  describe('Easing functions', () => {
    it('should apply easeInQuad easing', () => {
      const kf1 = createKeyframe(0, 0);
      kf1.interpolation = 'easeInQuad' as any;
      const prop = createProperty(0, true, [
        kf1,
        createKeyframe(100, 100)
      ]);

      const result = evaluator.evaluate(prop, 50);
      // easeInQuad at t=0.5 should be 0.25 * 100 = 25
      expect(result).toBe(25);
    });

    it('should apply easeOutQuad easing', () => {
      const kf1 = createKeyframe(0, 0);
      kf1.interpolation = 'easeOutQuad' as any;
      const prop = createProperty(0, true, [
        kf1,
        createKeyframe(100, 100)
      ]);

      const result = evaluator.evaluate(prop, 50);
      // easeOutQuad at t=0.5 should be 0.75 * 100 = 75
      expect(result).toBe(75);
    });

    it('should apply easeInOutQuad easing', () => {
      const kf1 = createKeyframe(0, 0);
      kf1.interpolation = 'easeInOutQuad' as any;
      const prop = createProperty(0, true, [
        kf1,
        createKeyframe(100, 100)
      ]);

      const result = evaluator.evaluate(prop, 50);
      // easeInOutQuad at t=0.5 should be 0.5 * 100 = 50
      expect(result).toBe(50);
    });
  });

  describe('Bezier interpolation', () => {
    it('should use linear when handles are disabled', () => {
      const kf1 = createKeyframe(0, 0, 'bezier');
      kf1.outHandle = { frame: 5, value: 0, enabled: false };
      const kf2 = createKeyframe(100, 100);
      kf2.inHandle = { frame: -5, value: 0, enabled: false };

      const prop = createProperty(0, true, [kf1, kf2]);

      const result = evaluator.evaluate(prop, 50);
      expect(result).toBe(50);
    });

    it('should apply bezier easing when handles are enabled', () => {
      const kf1 = createKeyframe(0, 0, 'bezier');
      kf1.outHandle = { frame: 33, value: 0, enabled: true };
      const kf2 = createKeyframe(100, 100);
      kf2.inHandle = { frame: -33, value: 0, enabled: true };

      const prop = createProperty(0, true, [kf1, kf2]);

      const result = evaluator.evaluate(prop, 50);
      // With handles enabled, the curve will be different from linear
      expect(typeof result).toBe('number');
      expect(result).toBeGreaterThanOrEqual(0);
      expect(result).toBeLessThanOrEqual(100);
    });
  });

  describe('Caching', () => {
    it('should cache evaluation results', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(100, 100)
      ]);

      const result1 = evaluator.evaluate(prop, 50);
      const result2 = evaluator.evaluate(prop, 50);

      expect(result1).toBe(result2);
    });

    it('should recalculate for different frames', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(100, 100)
      ]);

      const result1 = evaluator.evaluate(prop, 25);
      const result2 = evaluator.evaluate(prop, 75);

      expect(result1).toBe(25);
      expect(result2).toBe(75);
    });

    it('should clear cache on demand', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(100, 100)
      ]);

      evaluator.evaluate(prop, 50);
      evaluator.clearCache();

      // After clearing, should still work
      const result = evaluator.evaluate(prop, 50);
      expect(result).toBe(50);
    });
  });

  describe('Edge cases', () => {
    it('should handle single keyframe', () => {
      const prop = createProperty(0, true, [
        createKeyframe(50, 100)
      ]);

      expect(evaluator.evaluate(prop, 0)).toBe(100);
      expect(evaluator.evaluate(prop, 50)).toBe(100);
      expect(evaluator.evaluate(prop, 100)).toBe(100);
    });

    it('should handle unsorted keyframes', () => {
      const prop = createProperty(0, true, [
        createKeyframe(100, 100),
        createKeyframe(0, 0),
        createKeyframe(50, 50)
      ]);

      expect(evaluator.evaluate(prop, 25)).toBe(25);
      expect(evaluator.evaluate(prop, 75)).toBe(75);
    });

    it('should handle zero duration between keyframes', () => {
      const prop = createProperty(0, true, [
        createKeyframe(50, 100),
        createKeyframe(50, 200)
      ]);

      const result = evaluator.evaluate(prop, 50);
      expect(typeof result).toBe('number');
    });

    it('should handle negative frame values', () => {
      const prop = createProperty(0, true, [
        createKeyframe(-50, 0),
        createKeyframe(50, 100)
      ]);

      expect(evaluator.evaluate(prop, 0)).toBe(50);
    });

    it('should handle very large frame values', () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(1000000, 100)
      ]);

      expect(evaluator.evaluate(prop, 500000)).toBe(50);
    });
  });
});
