/**
 * STRICT Interpolation Property Tests
 * 
 * Tests the core interpolation engine with REALISTIC value ranges.
 * These tests will expose precision issues and edge cases.
 */

import { describe, expect, it } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { interpolateProperty } from '@/services/interpolation';
import type { AnimatableProperty, Keyframe, BezierHandle } from '@/types/project';

// ============================================================================
// STRICT TOLERANCE
// ============================================================================
const STRICT_TOLERANCE = 1e-10;
const FLOAT_TOLERANCE = 1e-8;

// ============================================================================
// REALISTIC VALUE GENERATORS
// ============================================================================

/**
 * Realistic numeric property values
 * Covers opacity (0-100), position (-10000 to 10000), scale (0.001 to 1000)
 */
const realisticNumberArb = fc.double({ 
  min: -10000, 
  max: 10000, 
  noNaN: true,
  noDefaultInfinity: true 
});

/**
 * Very small values that might cause precision issues
 */
const tinyNumberArb = fc.double({ 
  min: -1e-8, 
  max: 1e-8, 
  noNaN: true,
  noDefaultInfinity: true 
});

/**
 * Very large values
 */
const largeNumberArb = fc.double({ 
  min: 1e6, 
  max: 1e9, 
  noNaN: true,
  noDefaultInfinity: true 
});

/**
 * Realistic frame numbers (0 to 10000 frames = ~7 minutes at 24fps)
 */
const frameArb = fc.integer({ min: 0, max: 10000 });

/**
 * Default bezier handle
 */
const defaultHandle: BezierHandle = { frame: 0, value: 0, enabled: false };

/**
 * Create a keyframe with value
 */
function createKeyframe<T>(frame: number, value: T, interpolation: string = 'linear'): Keyframe<T> {
  return {
    frame,
    value,
    interpolation: interpolation as any,
    inHandle: { ...defaultHandle },
    outHandle: { ...defaultHandle },
  };
}

/**
 * Create animatable property with keyframes
 */
function createAnimatedProperty<T>(
  keyframes: Keyframe<T>[],
  name: string = 'test'
): AnimatableProperty<T> {
  return {
    name,
    value: keyframes[0]?.value ?? (0 as T),
    animated: true,
    keyframes,
    expression: { type: 'none', enabled: false },
  };
}

/**
 * Create static property
 */
function createStaticProperty<T>(value: T, name: string = 'test'): AnimatableProperty<T> {
  return {
    name,
    value,
    animated: false,
    keyframes: [],
    expression: { type: 'none', enabled: false },
  };
}

// ============================================================================
// BOUNDARY TESTS - STRICT
// ============================================================================

describe('STRICT: Interpolation Boundaries', () => {

  test.prop([realisticNumberArb, realisticNumberArb, frameArb])(
    'frame at first keyframe returns exact first value',
    (v1, v2, frameDiff) => {
      fc.pre(frameDiff > 0); // Ensure frames are different
      
      const kf1 = createKeyframe(0, v1);
      const kf2 = createKeyframe(frameDiff, v2);
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 0);
      
      // STRICT: Should be exactly equal
      expect(result).toBe(v1);
    }
  );

  test.prop([realisticNumberArb, realisticNumberArb, frameArb])(
    'frame at last keyframe returns exact last value',
    (v1, v2, frameDiff) => {
      fc.pre(frameDiff > 0);
      
      const kf1 = createKeyframe(0, v1);
      const kf2 = createKeyframe(frameDiff, v2);
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, frameDiff);
      
      // STRICT: Should be exactly equal
      expect(result).toBe(v2);
    }
  );

  test.prop([realisticNumberArb, realisticNumberArb, frameArb])(
    'frame before first keyframe returns exact first value',
    (v1, v2, frameDiff) => {
      fc.pre(frameDiff > 0);
      
      const kf1 = createKeyframe(10, v1);
      const kf2 = createKeyframe(10 + frameDiff, v2);
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 0);
      
      expect(result).toBe(v1);
    }
  );

  test.prop([realisticNumberArb, realisticNumberArb, frameArb])(
    'frame after last keyframe returns exact last value',
    (v1, v2, frameDiff) => {
      fc.pre(frameDiff > 0);
      
      const kf1 = createKeyframe(0, v1);
      const kf2 = createKeyframe(frameDiff, v2);
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, frameDiff + 100);
      
      expect(result).toBe(v2);
    }
  );

});

// ============================================================================
// LINEAR INTERPOLATION - STRICT
// ============================================================================

describe('STRICT: Linear Interpolation', () => {

  test.prop([realisticNumberArb, realisticNumberArb])(
    'midpoint is exactly (a + b) / 2',
    (v1, v2) => {
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 50);
      const expected = (v1 + v2) / 2;
      
      // Linear interpolation should be very precise
      expect(Math.abs(result - expected)).toBeLessThan(FLOAT_TOLERANCE);
    }
  );

  test.prop([realisticNumberArb, realisticNumberArb])(
    'quarter point is exactly a + (b - a) * 0.25',
    (v1, v2) => {
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 25);
      const expected = v1 + (v2 - v1) * 0.25;
      
      expect(Math.abs(result - expected)).toBeLessThan(FLOAT_TOLERANCE);
    }
  );

  test.prop([realisticNumberArb, realisticNumberArb, fc.integer({ min: 1, max: 99 })])(
    'result is always between v1 and v2 for t in (0,1)',
    (v1, v2, framePercent) => {
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, framePercent);
      
      const min = Math.min(v1, v2);
      const max = Math.max(v1, v2);
      
      expect(result).toBeGreaterThanOrEqual(min - FLOAT_TOLERANCE);
      expect(result).toBeLessThanOrEqual(max + FLOAT_TOLERANCE);
    }
  );

  test.prop([realisticNumberArb])(
    'interpolating same value returns that value',
    (v) => {
      const kf1 = createKeyframe(0, v, 'linear');
      const kf2 = createKeyframe(100, v, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 50);
      
      expect(Math.abs(result - v)).toBeLessThan(FLOAT_TOLERANCE);
    }
  );

});

// ============================================================================
// HOLD INTERPOLATION - STRICT
// ============================================================================

describe('STRICT: Hold Interpolation', () => {

  test.prop([realisticNumberArb, realisticNumberArb, fc.integer({ min: 0, max: 99 })])(
    'hold always returns first keyframe value until next keyframe',
    (v1, v2, frameOffset) => {
      const kf1 = createKeyframe(0, v1, 'hold');
      const kf2 = createKeyframe(100, v2, 'hold');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, frameOffset);
      
      // STRICT: Hold should return EXACTLY the first value
      expect(result).toBe(v1);
    }
  );

  test.prop([realisticNumberArb, realisticNumberArb])(
    'hold returns second value at exactly second keyframe',
    (v1, v2) => {
      const kf1 = createKeyframe(0, v1, 'hold');
      const kf2 = createKeyframe(100, v2, 'hold');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 100);
      
      expect(result).toBe(v2);
    }
  );

});

// ============================================================================
// STATIC PROPERTY - STRICT
// ============================================================================

describe('STRICT: Static Properties', () => {

  test.prop([realisticNumberArb, frameArb])(
    'static property returns exact value at any frame',
    (value, frame) => {
      const prop = createStaticProperty(value);
      
      const result = interpolateProperty(prop, frame);
      
      // STRICT: Should be exactly equal
      expect(result).toBe(value);
    }
  );

  test.prop([realisticNumberArb, frameArb])(
    'static property ignores keyframes',
    (value, frame) => {
      // Property with keyframes but animated=false
      const kf1 = createKeyframe(0, value * 2);
      const kf2 = createKeyframe(100, value * 3);
      const prop: AnimatableProperty<number> = {
        name: 'test',
        value,
        animated: false, // This should override keyframes
        keyframes: [kf1, kf2],
        expression: { type: 'none', enabled: false },
      };
      
      const result = interpolateProperty(prop, frame);
      
      expect(result).toBe(value);
    }
  );

});

// ============================================================================
// VECTOR INTERPOLATION - STRICT
// ============================================================================

describe('STRICT: Vector Interpolation', () => {

  test.prop([
    fc.record({
      x: realisticNumberArb,
      y: realisticNumberArb,
    }),
    fc.record({
      x: realisticNumberArb,
      y: realisticNumberArb,
    }),
  ])(
    '2D vector midpoint is component-wise average',
    (v1, v2) => {
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 50) as { x: number; y: number };
      
      expect(Math.abs(result.x - (v1.x + v2.x) / 2)).toBeLessThan(FLOAT_TOLERANCE);
      expect(Math.abs(result.y - (v1.y + v2.y) / 2)).toBeLessThan(FLOAT_TOLERANCE);
    }
  );

  test.prop([
    fc.record({
      x: realisticNumberArb,
      y: realisticNumberArb,
      z: realisticNumberArb,
    }),
    fc.record({
      x: realisticNumberArb,
      y: realisticNumberArb,
      z: realisticNumberArb,
    }),
  ])(
    '3D vector midpoint is component-wise average',
    (v1, v2) => {
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 50) as { x: number; y: number; z: number };
      
      expect(Math.abs(result.x - (v1.x + v2.x) / 2)).toBeLessThan(FLOAT_TOLERANCE);
      expect(Math.abs(result.y - (v1.y + v2.y) / 2)).toBeLessThan(FLOAT_TOLERANCE);
      expect(Math.abs(result.z - (v1.z + v2.z) / 2)).toBeLessThan(FLOAT_TOLERANCE);
    }
  );

});

// ============================================================================
// COLOR INTERPOLATION - STRICT
// ============================================================================

describe('STRICT: Color Interpolation', () => {

  test.prop([
    fc.integer({ min: 0, max: 255 }),
    fc.integer({ min: 0, max: 255 }),
    fc.integer({ min: 0, max: 255 }),
    fc.integer({ min: 0, max: 255 }),
    fc.integer({ min: 0, max: 255 }),
    fc.integer({ min: 0, max: 255 }),
  ])(
    'color midpoint is component-wise average (rounded)',
    (r1, g1, b1, r2, g2, b2) => {
      const c1 = `#${r1.toString(16).padStart(2, '0')}${g1.toString(16).padStart(2, '0')}${b1.toString(16).padStart(2, '0')}`;
      const c2 = `#${r2.toString(16).padStart(2, '0')}${g2.toString(16).padStart(2, '0')}${b2.toString(16).padStart(2, '0')}`;
      
      const kf1 = createKeyframe(0, c1, 'linear');
      const kf2 = createKeyframe(100, c2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 50);
      
      expect(typeof result).toBe('string');
      expect(result).toMatch(/^#[0-9a-f]{6}$/i);
      
      // Parse result
      const rr = parseInt((result as string).slice(1, 3), 16);
      const rg = parseInt((result as string).slice(3, 5), 16);
      const rb = parseInt((result as string).slice(5, 7), 16);
      
      // Expected (rounded average)
      const er = Math.round((r1 + r2) / 2);
      const eg = Math.round((g1 + g2) / 2);
      const eb = Math.round((b1 + b2) / 2);
      
      // Allow ±1 for rounding differences
      expect(Math.abs(rr - er)).toBeLessThanOrEqual(1);
      expect(Math.abs(rg - eg)).toBeLessThanOrEqual(1);
      expect(Math.abs(rb - eb)).toBeLessThanOrEqual(1);
    }
  );

});

// ============================================================================
// DETERMINISM TESTS - CRITICAL
// ============================================================================

describe('STRICT: Determinism', () => {

  test.prop([realisticNumberArb, realisticNumberArb, frameArb])(
    'same input produces identical output (multiple calls)',
    (v1, v2, targetFrame) => {
      fc.pre(targetFrame >= 0 && targetFrame <= 100);
      
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      // Call multiple times
      const results = [
        interpolateProperty(prop, targetFrame),
        interpolateProperty(prop, targetFrame),
        interpolateProperty(prop, targetFrame),
        interpolateProperty(prop, targetFrame),
        interpolateProperty(prop, targetFrame),
      ];
      
      // ALL results must be IDENTICAL
      for (let i = 1; i < results.length; i++) {
        expect(results[i]).toBe(results[0]);
      }
    }
  );

  test.prop([realisticNumberArb, realisticNumberArb])(
    'tiny frame changes produce proportionally tiny value changes (continuity)',
    (v1, v2) => {
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const frameA = 50;
      const frameB = 50.001; // Tiny change
      
      const resultA = interpolateProperty(prop, frameA);
      const resultB = interpolateProperty(prop, frameB);
      
      // Value change should be proportional to frame change
      const expectedChange = Math.abs(v2 - v1) * 0.00001;
      const actualChange = Math.abs(resultB - resultA);
      
      // Allow 2x margin for floating point
      expect(actualChange).toBeLessThan(expectedChange * 2 + FLOAT_TOLERANCE);
    }
  );

});

// ============================================================================
// EDGE CASE TESTS - Find bugs
// ============================================================================

describe('STRICT: Edge Cases', () => {

  test.prop([tinyNumberArb, tinyNumberArb, frameArb])(
    'very small values interpolate correctly',
    (v1, v2, framePercent) => {
      fc.pre(framePercent > 0 && framePercent < 100);
      
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, framePercent);
      
      // Result should be finite
      expect(Number.isFinite(result)).toBe(true);
      
      // Result should be in bounds (with tolerance for tiny values)
      const min = Math.min(v1, v2) - FLOAT_TOLERANCE;
      const max = Math.max(v1, v2) + FLOAT_TOLERANCE;
      expect(result).toBeGreaterThanOrEqual(min);
      expect(result).toBeLessThanOrEqual(max);
    }
  );

  test.prop([largeNumberArb, largeNumberArb, frameArb])(
    'very large values interpolate correctly',
    (v1, v2, framePercent) => {
      fc.pre(framePercent > 0 && framePercent < 100);
      
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, framePercent);
      
      // Result should be finite
      expect(Number.isFinite(result)).toBe(true);
      
      // Result should be in bounds
      const min = Math.min(v1, v2);
      const max = Math.max(v1, v2);
      expect(result).toBeGreaterThanOrEqual(min);
      expect(result).toBeLessThanOrEqual(max);
    }
  );

  it('handles zero duration between keyframes', () => {
    // Keyframes at same frame
    const kf1 = createKeyframe(50, 100, 'linear');
    const kf2 = createKeyframe(50, 200, 'linear');
    const prop = createAnimatedProperty([kf1, kf2]);
    
    const result = interpolateProperty(prop, 50);
    
    // Should not crash, should return one of the values
    expect([100, 200]).toContain(result);
  });

  it('handles single keyframe', () => {
    const kf1 = createKeyframe(50, 100, 'linear');
    const prop = createAnimatedProperty([kf1]);
    
    const before = interpolateProperty(prop, 0);
    const at = interpolateProperty(prop, 50);
    const after = interpolateProperty(prop, 100);
    
    expect(before).toBe(100);
    expect(at).toBe(100);
    expect(after).toBe(100);
  });

  it('handles many keyframes', () => {
    const keyframes = Array.from({ length: 100 }, (_, i) => 
      createKeyframe(i * 10, i * 100, 'linear')
    );
    const prop = createAnimatedProperty(keyframes);
    
    // Middle of animation
    const result = interpolateProperty(prop, 505);
    const expected = 50 * 100 + 50; // Between keyframe 50 (5000) and 51 (5100)
    
    expect(Math.abs(result - expected)).toBeLessThan(1);
  });

});

// ============================================================================
// STRESS TEST - Find precision limits
// ============================================================================

describe('STRESS: Interpolation Precision Limits', () => {

  it('documents precision at various value scales', () => {
    const scales = [1e-10, 1e-8, 1e-6, 1e-4, 1e-2, 1, 1e2, 1e4, 1e6, 1e8, 1e10];
    const results: { scale: number; error: number }[] = [];
    
    for (const scale of scales) {
      const v1 = scale;
      const v2 = scale * 2;
      
      const kf1 = createKeyframe(0, v1, 'linear');
      const kf2 = createKeyframe(100, v2, 'linear');
      const prop = createAnimatedProperty([kf1, kf2]);
      
      const result = interpolateProperty(prop, 50);
      const expected = (v1 + v2) / 2;
      
      const relativeError = Math.abs((result - expected) / expected);
      results.push({ scale, error: relativeError });
    }
    
    console.log('Interpolation precision by value scale:');
    console.table(results);
    
    // All should have < 1% relative error
    expect(results.every(r => r.error < 0.01)).toBe(true);
  });

});
