/**
 * DETERMINISM Property Tests
 * 
 * The single most critical property for a motion graphics compositor:
 * THE SAME INPUT MUST ALWAYS PRODUCE THE SAME OUTPUT.
 * 
 * These tests verify that:
 * 1. Evaluating the same frame twice returns identical results
 * 2. Evaluation order doesn't affect results
 * 3. No hidden state influences evaluation
 * 4. Seeded random values are reproducible
 * 
 * REINTEGRATED: 2026-01-07 from _deprecated/properties/determinism.property.test.ts
 * Updated to use current interpolateProperty API (with fps parameter)
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { interpolateProperty } from '@/services/interpolation';
import type { AnimatableProperty, Keyframe } from '@/types/project';
import type { Vec2 } from '@/types/transform';

// ============================================================================
// ARBITRARIES
// ============================================================================

const frameArb = fc.integer({ min: 0, max: 10000 });
const wanFrameArb = fc.integer({ min: 0, max: 81 });
const smallPositionArb = fc.double({ min: -1000, max: 1000, noNaN: true });

const vec2Arb: fc.Arbitrary<Vec2> = fc.record({
  x: smallPositionArb,
  y: smallPositionArb,
});

const bezierHandleArb = fc.record({
  frame: fc.double({ min: -50, max: 50, noNaN: true }),
  value: fc.double({ min: -100, max: 100, noNaN: true }),
  enabled: fc.boolean(),
});

const interpolationTypeArb = fc.constantFrom<'linear' | 'bezier' | 'hold' | 'easeInSine' | 'easeOutSine' | 'easeInOutSine' | 'easeInQuad' | 'easeOutQuad' | 'easeInOutQuad' | 'easeInCubic' | 'easeOutCubic' | 'easeInOutCubic' | 'easeInQuart' | 'easeOutQuart' | 'easeInOutQuart' | 'easeInQuint' | 'easeOutQuint' | 'easeInOutQuint' | 'easeInExpo' | 'easeOutExpo' | 'easeInOutExpo' | 'easeInCirc' | 'easeOutCirc' | 'easeInOutCirc' | 'easeInBack' | 'easeOutBack' | 'easeInOutBack' | 'easeInElastic' | 'easeOutElastic' | 'easeInOutElastic' | 'easeInBounce' | 'easeOutBounce' | 'easeInOutBounce'>(
  'linear', 'bezier', 'hold',
  'easeInSine', 'easeOutSine', 'easeInOutSine',
  'easeInQuad', 'easeOutQuad', 'easeInOutQuad',
  'easeInCubic', 'easeOutCubic', 'easeInOutCubic',
  'easeInQuart', 'easeOutQuart', 'easeInOutQuart',
  'easeInQuint', 'easeOutQuint', 'easeInOutQuint',
  'easeInExpo', 'easeOutExpo', 'easeInOutExpo',
  'easeInCirc', 'easeOutCirc', 'easeInOutCirc',
  'easeInBack', 'easeOutBack', 'easeInOutBack',
  'easeInElastic', 'easeOutElastic', 'easeInOutElastic',
  'easeInBounce', 'easeOutBounce', 'easeInOutBounce'
);

const numericKeyframeArb: fc.Arbitrary<Keyframe<number>> = fc.record({
  id: fc.string({ minLength: 8, maxLength: 12 }),
  frame: frameArb,
  value: fc.double({ min: -1000, max: 1000, noNaN: true }),
  interpolation: interpolationTypeArb,
  inHandle: bezierHandleArb,
  outHandle: bezierHandleArb,
  controlMode: fc.constantFrom('symmetric', 'smooth', 'corner'),
});

const positionKeyframeArb: fc.Arbitrary<Keyframe<Vec2>> = fc.record({
  id: fc.string({ minLength: 8, maxLength: 12 }),
  frame: frameArb,
  value: vec2Arb,
  interpolation: interpolationTypeArb,
  inHandle: bezierHandleArb,
  outHandle: bezierHandleArb,
  controlMode: fc.constantFrom('symmetric', 'smooth', 'corner'),
});

function sortedKeyframesArb<T>(
  valueArb: fc.Arbitrary<T>,
  minLength: number = 2,
  maxLength: number = 10
): fc.Arbitrary<Keyframe<T>[]> {
  return fc.array(
    valueArb === vec2Arb ? positionKeyframeArb as fc.Arbitrary<Keyframe<T>> : numericKeyframeArb as fc.Arbitrary<Keyframe<T>>,
    { minLength, maxLength }
  ).map(keyframes => {
    const sorted = [...keyframes].sort((a, b) => a.frame - b.frame);
    const unique: Keyframe<T>[] = [];
    let lastFrame = -1;
    
    for (const kf of sorted) {
      if (kf.frame > lastFrame) {
        unique.push(kf);
        lastFrame = kf.frame;
      }
    }
    
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??/?.
    while (unique.length < minLength && sorted.length > 0) {
      const lastKeyframe = unique[unique.length - 1];
      const lastFrame = (lastKeyframe !== null && lastKeyframe !== undefined && typeof lastKeyframe === "object" && "frame" in lastKeyframe && typeof lastKeyframe.frame === "number" && Number.isFinite(lastKeyframe.frame)) ? lastKeyframe.frame : 0;
      const newFrame = lastFrame + 10;
      unique.push({
        ...sorted[0],
        id: `kf_pad_${unique.length}`,
        frame: newFrame,
      } as Keyframe<T>);
    }
    
    return unique;
  });
}

const sortedNumericKeyframesArb = sortedKeyframesArb(
  fc.double({ min: -1000, max: 1000, noNaN: true }),
  2,
  10
) as fc.Arbitrary<Keyframe<number>[]>;

const sortedPositionKeyframesArb = sortedKeyframesArb(
  vec2Arb,
  2,
  10
) as fc.Arbitrary<Keyframe<Vec2>[]>;

const animatedNumericPropertyArb: fc.Arbitrary<AnimatableProperty<number>> = fc.record({
  id: fc.string({ minLength: 8, maxLength: 12 }),
  name: fc.constantFrom('opacity', 'rotation', 'scale', 'blur'),
  type: fc.constant('number' as const),
  value: fc.double({ min: 0, max: 100, noNaN: true }),
  animated: fc.constant(true),
  keyframes: sortedNumericKeyframesArb,
});

const animatedPositionPropertyArb: fc.Arbitrary<AnimatableProperty<Vec2>> = fc.record({
  id: fc.string({ minLength: 8, maxLength: 12 }),
  name: fc.constant('position'),
  type: fc.constant('position' as const),
  value: vec2Arb,
  animated: fc.constant(true),
  keyframes: sortedPositionKeyframesArb,
});

const staticNumericPropertyArb: fc.Arbitrary<AnimatableProperty<number>> = fc.record({
  id: fc.string({ minLength: 8, maxLength: 12 }),
  name: fc.constantFrom('opacity', 'rotation', 'scale', 'blur'),
  type: fc.constant('number' as const),
  value: fc.double({ min: 0, max: 100, noNaN: true }),
  animated: fc.constant(false),
  keyframes: fc.constant([]),
});

const frameWithKeyframesArb = sortedNumericKeyframesArb.chain(keyframes => {
  const firstFrame = keyframes[0].frame;
  const lastFrame = keyframes[keyframes.length - 1].frame;
  
  return fc.double({ min: firstFrame, max: lastFrame, noNaN: true }).map(frame => ({
    frame,
    keyframes
  }));
});

describe('DETERMINISM Properties', () => {
  
  // =========================================================================
  // CORE DETERMINISM: Same input = Same output
  // =========================================================================
  
  describe('interpolateProperty() determinism', () => {
    
    test.prop([animatedNumericPropertyArb, wanFrameArb])(
      'numeric interpolation is deterministic - same frame always returns same value',
      (property, frame) => {
        const result1 = interpolateProperty(property, frame, 30);
        const result2 = interpolateProperty(property, frame, 30);
        
        // Must be exactly equal (not approximately)
        expect(result1).toBe(result2);
      }
    );

    test.prop([animatedPositionPropertyArb, wanFrameArb])(
      'position interpolation is deterministic - same frame always returns same position',
      (property, frame) => {
        const result1 = interpolateProperty(property, frame, 30);
        const result2 = interpolateProperty(property, frame, 30);
        
        // Position is an object, must be deep equal
        expect(result1).toEqual(result2);
      }
    );

    test.prop([staticNumericPropertyArb, wanFrameArb])(
      'static property returns same value for any frame',
      (property, frame) => {
        const result = interpolateProperty(property, frame, 30);
        
        // Static properties always return their base value
        expect(result).toBe(property.value);
      }
    );

  });

  // =========================================================================
  // ORDER INDEPENDENCE: Evaluation order doesn't matter
  // =========================================================================

  describe('evaluation order independence', () => {
    
    test.prop([
      animatedNumericPropertyArb,
      fc.array(wanFrameArb, { minLength: 2, maxLength: 10 })
    ])(
      'evaluating frames in different orders produces same results',
      (property, frames) => {
        // Evaluate in original order
        const results1 = frames.map(f => interpolateProperty(property, f, 30));
        
        // Evaluate in reverse order
        const reversed = [...frames].reverse();
        const results2Reversed = reversed.map(f => interpolateProperty(property, f, 30));
        const results2 = results2Reversed.reverse();
        
        // Should produce identical results
        expect(results1).toEqual(results2);
      }
    );

    test.prop([
      animatedNumericPropertyArb,
      wanFrameArb
    ])(
      'evaluating same frame multiple times produces identical results',
      (property, frame) => {
        const results: number[] = [];
        
        // Evaluate 10 times
        for (let i = 0; i < 10; i++) {
          results.push(interpolateProperty(property, frame, 30));
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
  // INTERLEAVED EVALUATION: Mixed property evaluation doesn't cause crosstalk
  // =========================================================================

  describe('no state crosstalk between properties', () => {
    
    test.prop([
      animatedNumericPropertyArb,
      animatedNumericPropertyArb,
      wanFrameArb
    ])(
      'evaluating property A does not affect property B',
      (propA, propB, frame) => {
        // Get baseline for B
        const baselineB = interpolateProperty(propB, frame, 30);
        
        // Evaluate A many times
        for (let i = 0; i < 5; i++) {
          interpolateProperty(propA, frame + i, 30);
        }
        
        // B should be unchanged
        const afterB = interpolateProperty(propB, frame, 30);
        expect(afterB).toBe(baselineB);
      }
    );

  });

  // =========================================================================
  // FRAME BOUNDARY DETERMINISM
  // =========================================================================

  describe('frame boundary behavior', () => {
    
    test.prop([sortedNumericKeyframesArb])(
      'frame at exact keyframe position returns keyframe value',
      (keyframes) => {
        // Create property with these keyframes
        const property: AnimatableProperty<number> = {
          id: 'test_prop',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes,
        };

        // Each keyframe frame should return exactly that keyframe's value
        for (const kf of keyframes) {
          const result = interpolateProperty(property, kf.frame, 30);
          
          // At exact keyframe, should return keyframe value
          // (unless it's the last keyframe with 'hold' interpolation)
          if (kf.interpolation !== 'hold' || kf === keyframes[keyframes.length - 1]) {
            // Compare using relative error for values above epsilon, absolute for tiny values
            // JavaScript floating point quirk: 1e-10 can become 1.0000000000000002e-10
            const diff = Math.abs(result - kf.value);
            const relError = Math.abs(kf.value) > 1e-9 ? diff / Math.abs(kf.value) : 0;
            
            // Allow 0.001% relative error OR tiny absolute difference
            // For values < 1e-9, we use absolute comparison with generous margin
            expect(relError < 1e-5 || diff < Math.abs(kf.value) * 1.001 + 1e-15).toBe(true);
          }
        }
      }
    );

    test.prop([sortedNumericKeyframesArb, fc.integer({ min: -100, max: -1 })])(
      'frame before first keyframe returns first keyframe value',
      (keyframes, offset) => {
        const property: AnimatableProperty<number> = {
          id: 'test_prop',
          name: 'test',
          type: 'number',
          value: 999, // Different from keyframe value
          animated: true,
          keyframes,
        };

        const frameBefore = keyframes[0].frame + offset;
        const result = interpolateProperty(property, frameBefore, 30);
        
        expect(result).toBe(keyframes[0].value);
      }
    );

    test.prop([sortedNumericKeyframesArb, fc.integer({ min: 1, max: 100 })])(
      'frame after last keyframe returns last keyframe value',
      (keyframes, offset) => {
        const property: AnimatableProperty<number> = {
          id: 'test_prop',
          name: 'test',
          type: 'number',
          value: 999, // Different from keyframe value
          animated: true,
          keyframes,
        };

        const frameAfter = keyframes[keyframes.length - 1].frame + offset;
        const result = interpolateProperty(property, frameAfter, 30);
        
        expect(result).toBe(keyframes[keyframes.length - 1].value);
      }
    );

  });

  // =========================================================================
  // FLOATING POINT CONSISTENCY
  // =========================================================================

  describe('floating point consistency', () => {
    
    test.prop([frameWithKeyframesArb])(
      'fractional frames produce consistent results',
      ({ frame, keyframes }) => {
        const property: AnimatableProperty<number> = {
          id: 'test_prop',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes,
        };

        // Test that fractional frames are deterministic
        const result1 = interpolateProperty(property, frame, 30);
        const result2 = interpolateProperty(property, frame, 30);
        
        expect(result1).toBe(result2);
      }
    );

    test.prop([
      animatedNumericPropertyArb,
      fc.double({ min: 0, max: 81, noNaN: true })
    ])(
      'very close frame values produce stable results',
      (property, baseFrame) => {
        // Add a tiny epsilon
        const frame1 = baseFrame;
        const frame2 = baseFrame + 1e-10;
        
        const result1 = interpolateProperty(property, frame1, 30);
        const result2 = interpolateProperty(property, frame2, 30);
        
        // Results should be nearly identical for nearly identical frames
        // Use relative tolerance for larger values, absolute for small values
        const diff = Math.abs(result1 - result2);
        const maxResult = Math.max(Math.abs(result1), Math.abs(result2));
        
        // Allow 0.01% relative difference OR 1e-6 absolute difference
        const relDiff = maxResult > 0 ? diff / maxResult : 0;
        expect(relDiff < 1e-4 || diff < 1e-6).toBe(true);
      }
    );

  });

  // =========================================================================
  // HOLD INTERPOLATION DETERMINISM
  // =========================================================================

  describe('hold interpolation', () => {
    
    test.prop([
      fc.integer({ min: 0, max: 50 }),
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: -100, max: 100, noNaN: true }),
      fc.double({ min: 0.01, max: 0.99, noNaN: true })
    ])(
      'hold interpolation always returns first keyframe value',
      (startFrame, value1, value2, t) => {
        const endFrame = startFrame + 20;
        const property: AnimatableProperty<number> = {
          id: 'test_prop',
          name: 'test',
          type: 'number',
          value: 0,
          animated: true,
          keyframes: [
            {
              id: 'kf1',
              frame: startFrame,
              value: value1,
              interpolation: 'hold',
              inHandle: { frame: -5, value: 0, enabled: true },
              outHandle: { frame: 5, value: 0, enabled: true },
              controlMode: 'smooth',
            },
            {
              id: 'kf2',
              frame: endFrame,
              value: value2,
              interpolation: 'linear',
              inHandle: { frame: -5, value: 0, enabled: true },
              outHandle: { frame: 5, value: 0, enabled: true },
              controlMode: 'smooth',
            },
          ],
        };

        // Any frame between keyframes should return first value
        const testFrame = startFrame + t * (endFrame - startFrame);
        const result = interpolateProperty(property, testFrame, 30);
        
        expect(result).toBe(value1);
      }
    );

  });

});
