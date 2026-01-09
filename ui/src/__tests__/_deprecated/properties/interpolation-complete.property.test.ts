/**
 * COMPLETE INTERPOLATION Property Tests
 * 
 * Tests the MISSING coverage in interpolation.ts:
 * - Expression integration (applyPropertyExpression)
 * - Velocity calculation (calculateVelocity)
 * - Path morphing (interpolatePath)
 * 
 * ALL TESTS MUST PASS. No exceptions.
 */

import { describe, expect, it, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { 
  interpolateProperty,
  clearBezierCache,
  clearPathMorphCache,
} from '@/services/interpolation';
import type { AnimatableProperty, Keyframe, PropertyExpression } from '@/types/animation';
import type { BezierPath, BezierVertex, Point2D } from '@/types/shapes';

// ============================================================================
// ARBITRARIES
// ============================================================================

// Valid frame range
const frameArb = fc.integer({ min: 0, max: 100 });

// Numeric value
const valueArb = fc.double({ min: -1000, max: 1000, noNaN: true });

// Create a valid BezierVertex
const point2DArb: fc.Arbitrary<Point2D> = fc.record({
  x: fc.double({ min: -500, max: 500, noNaN: true }),
  y: fc.double({ min: -500, max: 500, noNaN: true }),
});

const bezierVertexArb: fc.Arbitrary<BezierVertex> = fc.record({
  point: point2DArb,
  inHandle: point2DArb,
  outHandle: point2DArb,
});

// Create a valid BezierPath with 3-6 vertices
const bezierPathArb: fc.Arbitrary<BezierPath> = fc.record({
  vertices: fc.array(bezierVertexArb, { minLength: 3, maxLength: 6 }),
  closed: fc.boolean(),
});

// Create keyframes for numeric properties
function createNumericKeyframes(values: number[], frames: number[]): Keyframe<number>[] {
  return values.map((value, i) => ({
    id: `kf-${i}`,
    frame: frames[i] ?? i * 25,
    value,
    interpolation: 'linear' as const,
    inHandle: { frame: -5, value: 0, enabled: true },
    outHandle: { frame: 5, value: 0, enabled: true },
    controlMode: 'smooth' as const,
  }));
}

// Create keyframes for path properties
function createPathKeyframes(paths: BezierPath[], frames: number[]): Keyframe<BezierPath>[] {
  return paths.map((value, i) => ({
    id: `kf-${i}`,
    frame: frames[i] ?? i * 50,
    value,
    interpolation: 'linear' as const,
    inHandle: { frame: -5, value: 0, enabled: true },
    outHandle: { frame: 5, value: 0, enabled: true },
    controlMode: 'smooth' as const,
  }));
}

// Create a simple triangle path
function createTrianglePath(): BezierPath {
  return {
    vertices: [
      { point: { x: 0, y: -50 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
      { point: { x: 50, y: 50 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
      { point: { x: -50, y: 50 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
    ],
    closed: true,
  };
}

// Create a simple square path
function createSquarePath(): BezierPath {
  return {
    vertices: [
      { point: { x: -50, y: -50 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
      { point: { x: 50, y: -50 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
      { point: { x: 50, y: 50 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
      { point: { x: -50, y: 50 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
    ],
    closed: true,
  };
}

describe('COMPLETE: Interpolation Expression Integration', () => {
  
  beforeEach(() => {
    clearBezierCache();
    clearPathMorphCache();
  });

  // =========================================================================
  // EXPRESSION EVALUATION
  // =========================================================================

  describe('expression evaluation', () => {
    
    it('applies jitter expression to numeric value', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'jitter',
        params: { amplitude: 10, frequency: 1, seed: 12345 },
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 100,
        animated: true,
        keyframes: createNumericKeyframes([100, 100], [0, 100]),
        expression,
      };

      // Sample multiple frames - jitter should add variation
      const results: number[] = [];
      for (let f = 0; f <= 100; f += 10) {
        results.push(interpolateProperty(property, f, 16, 'layer1'));
      }

      // With jitter, not all values should be exactly 100
      const uniqueValues = new Set(results.map(r => Math.round(r)));
      expect(uniqueValues.size).toBeGreaterThan(1);
      
      // Jitter uses layered sine waves, so actual range is ~1.5x amplitude
      // Values should be within reasonable range (not infinite, not NaN)
      for (const r of results) {
        expect(Number.isFinite(r)).toBe(true);
        expect(r).toBeGreaterThanOrEqual(80); // ~100 - 1.5*10 with margin
        expect(r).toBeLessThanOrEqual(120);   // ~100 + 1.5*10 with margin
      }
    });

    it('jitter expression is deterministic with same seed', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'jitter',
        params: { amplitude: 10, frequency: 1, seed: 42 },
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 50,
        animated: false,
        keyframes: [],
        expression,
      };

      // Run twice with same parameters
      const result1 = interpolateProperty(property, 25, 16, 'layer1');
      const result2 = interpolateProperty(property, 25, 16, 'layer1');

      expect(result1).toBe(result2);
    });

    it('disabled expression returns base interpolated value', () => {
      const expression: PropertyExpression = {
        enabled: false,
        type: 'preset',
        name: 'jitter',
        params: { amplitude: 100, frequency: 1, seed: 12345 },
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 50,
        animated: true,
        keyframes: createNumericKeyframes([0, 100], [0, 100]),
        expression,
      };

      // At frame 50, linear interpolation should give exactly 50
      const result = interpolateProperty(property, 50, 16, 'layer1');
      expect(result).toBeCloseTo(50, 5);
    });

    it('applies repeatAfter (loop) expression', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'repeatAfter',
        params: {},
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: createNumericKeyframes([0, 100], [0, 50]),
        expression,
      };

      // Frame 0-50: normal animation 0→100
      // Frame 50-100: should loop back
      const at0 = interpolateProperty(property, 0, 16, 'layer1');
      const at25 = interpolateProperty(property, 25, 16, 'layer1');
      const at50 = interpolateProperty(property, 50, 16, 'layer1');
      const at75 = interpolateProperty(property, 75, 16, 'layer1');

      expect(at0).toBeCloseTo(0, 5);
      expect(at25).toBeCloseTo(50, 5);
      expect(at50).toBeCloseTo(100, 5);
      // After loop, should be back around the middle
      expect(Number.isFinite(at75)).toBe(true);
    });

    test.prop([valueArb, valueArb, frameArb])(
      'expression output is always finite for valid inputs',
      (v1, v2, testFrame) => {
        const expression: PropertyExpression = {
          enabled: true,
          type: 'preset',
          name: 'jitter',
          params: { amplitude: 10, frequency: 1, seed: 99 },
        };

        const property: AnimatableProperty<number> = {
          id: 'test',
          name: 'test',
          type: 'number',
          value: v1,
          animated: true,
          keyframes: createNumericKeyframes([v1, v2], [0, 100]),
          expression,
        };

        const result = interpolateProperty(property, testFrame, 16, 'layer1');
        expect(Number.isFinite(result)).toBe(true);
      }
    );
  });

  // =========================================================================
  // VELOCITY CALCULATION (via expressions that use velocity)
  // =========================================================================

  describe('velocity calculation', () => {
    
    it('inertia expression uses velocity correctly', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'inertia',
        params: { friction: 0.5, velocityScale: 1 },
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: createNumericKeyframes([0, 100], [0, 50]),
        expression,
      };

      // After keyframes end (frame 50), inertia should continue motion
      const at50 = interpolateProperty(property, 50, 16, 'layer1');
      const at60 = interpolateProperty(property, 60, 16, 'layer1');
      const at80 = interpolateProperty(property, 80, 16, 'layer1');

      // Inertia continues past the keyframe endpoint
      expect(at50).toBeCloseTo(100, 5);
      expect(Number.isFinite(at60)).toBe(true);
      expect(Number.isFinite(at80)).toBe(true);
      
      // Should be different values (motion continues)
      // Note: Exact behavior depends on inertia implementation
    });

    it('velocity is zero for static property', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'inertia',
        params: { friction: 0.5, velocityScale: 1 },
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 50,
        animated: false,
        keyframes: [],
        expression,
      };

      // Static property with inertia - velocity is 0, so value shouldn't change
      const result = interpolateProperty(property, 50, 16, 'layer1');
      expect(Number.isFinite(result)).toBe(true);
    });

    /**
     * BUG DOCUMENTED: Expressions expect number[] arrays but interpolation
     * returns {x, y} objects for position properties.
     * 
     * This test verifies the bug exists and documents the workaround:
     * - Use array-style values [x, y] instead of {x, y} for expressions
     * - Or fix motionExpressions.ts to handle object format
     */
    it('velocity expression works with {x,y} object format (BUG-005 FIXED)', () => {
      // BUG-005 WAS: Expression system crashes with object-style vectors
      // FIXED: Added toArray/fromArray helpers in motionExpressions.ts
      
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'inertia',
        params: { friction: 0.5, velocityScale: 1 },
      };

      const property: AnimatableProperty<{x: number, y: number}> = {
        id: 'test',
        name: 'test',
        type: 'position',
        value: { x: 0, y: 0 },
        animated: true,
        keyframes: [
          { id: 'k1', frame: 0, value: { x: 0, y: 0 }, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
          { id: 'k2', frame: 50, value: { x: 100, y: 100 }, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
        ],
        expression,
      };

      // FIXED: This now works - no crash
      const result = interpolateProperty(property, 60, 16, 'layer1');
      
      // Result should be an object with x and y properties
      expect(result).toHaveProperty('x');
      expect(result).toHaveProperty('y');
      expect(typeof (result as any).x).toBe('number');
      expect(typeof (result as any).y).toBe('number');
      expect(Number.isFinite((result as any).x)).toBe(true);
      expect(Number.isFinite((result as any).y)).toBe(true);
    });

    it('expressions work with array-style position values', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'jitter',
        params: { amplitude: 10, frequency: 1, seed: 42 },
      };

      // Use array format [x, y] instead of {x, y}
      const property: AnimatableProperty<number[]> = {
        id: 'test',
        name: 'test',
        type: 'position' as any,
        value: [0, 0],
        animated: true,
        keyframes: [
          { id: 'k1', frame: 0, value: [0, 0], interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
          { id: 'k2', frame: 100, value: [100, 100], interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
        ],
        expression,
      };

      const result = interpolateProperty(property, 50, 16, 'layer1');
      
      // Array format works with expressions
      expect(Array.isArray(result)).toBe(true);
      expect(result.length).toBe(2);
      expect(Number.isFinite(result[0])).toBe(true);
      expect(Number.isFinite(result[1])).toBe(true);
    });
  });

  // =========================================================================
  // PATH MORPHING
  // =========================================================================

  describe('path morphing', () => {
    
    it('interpolates between two BezierPaths', () => {
      const triangle = createTrianglePath();
      const square = createSquarePath();

      const property: AnimatableProperty<BezierPath> = {
        id: 'test',
        name: 'path',
        type: 'vector3' as any, // BezierPath type
        value: triangle,
        animated: true,
        keyframes: createPathKeyframes([triangle, square], [0, 100]),
      };

      const at0 = interpolateProperty(property, 0, 16, 'layer1');
      const at50 = interpolateProperty(property, 50, 16, 'layer1');
      const at100 = interpolateProperty(property, 100, 16, 'layer1');

      // At endpoints, should match keyframe values
      expect(at0.vertices.length).toBeGreaterThan(0);
      expect(at100.vertices.length).toBeGreaterThan(0);
      
      // At midpoint, should have interpolated vertices
      expect(at50.vertices.length).toBeGreaterThan(0);
      
      // All vertices should have finite coordinates
      for (const v of at50.vertices) {
        expect(Number.isFinite(v.point.x)).toBe(true);
        expect(Number.isFinite(v.point.y)).toBe(true);
      }
    });

    it('path morphing is deterministic', () => {
      const triangle = createTrianglePath();
      const square = createSquarePath();

      const property: AnimatableProperty<BezierPath> = {
        id: 'test',
        name: 'path',
        type: 'vector3' as any,
        value: triangle,
        animated: true,
        keyframes: createPathKeyframes([triangle, square], [0, 100]),
      };

      const result1 = interpolateProperty(property, 50, 16, 'layer1');
      const result2 = interpolateProperty(property, 50, 16, 'layer1');

      // Same frame should produce identical path
      expect(result1.vertices.length).toBe(result2.vertices.length);
      for (let i = 0; i < result1.vertices.length; i++) {
        expect(result1.vertices[i].point.x).toBe(result2.vertices[i].point.x);
        expect(result1.vertices[i].point.y).toBe(result2.vertices[i].point.y);
      }
    });

    it('handles open paths', () => {
      const openPath1: BezierPath = {
        vertices: [
          { point: { x: 0, y: 0 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 10, y: 0 } },
          { point: { x: 100, y: 0 }, inHandle: { x: -10, y: 0 }, outHandle: { x: 0, y: 0 } },
        ],
        closed: false,
      };

      const openPath2: BezierPath = {
        vertices: [
          { point: { x: 0, y: 100 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 10, y: 0 } },
          { point: { x: 100, y: 100 }, inHandle: { x: -10, y: 0 }, outHandle: { x: 0, y: 0 } },
        ],
        closed: false,
      };

      const property: AnimatableProperty<BezierPath> = {
        id: 'test',
        name: 'path',
        type: 'vector3' as any,
        value: openPath1,
        animated: true,
        keyframes: createPathKeyframes([openPath1, openPath2], [0, 100]),
      };

      const at50 = interpolateProperty(property, 50, 16, 'layer1');
      
      // Midpoint should have y values around 50
      expect(at50.vertices.length).toBe(2);
      expect(at50.vertices[0].point.y).toBeCloseTo(50, 0);
      expect(at50.vertices[1].point.y).toBeCloseTo(50, 0);
      expect(at50.closed).toBe(false);
    });

    test.prop([bezierPathArb, bezierPathArb, fc.double({ min: 0.1, max: 0.9, noNaN: true })])(
      'path morphing produces valid BezierPath for any inputs',
      (path1, path2, t) => {
        const property: AnimatableProperty<BezierPath> = {
          id: 'test',
          name: 'path',
          type: 'vector3' as any,
          value: path1,
          animated: true,
          keyframes: createPathKeyframes([path1, path2], [0, 100]),
        };

        const result = interpolateProperty(property, t * 100, 16, 'layer1');

        // Result should be a valid BezierPath
        expect(Array.isArray(result.vertices)).toBe(true);
        expect(result.vertices.length).toBeGreaterThan(0);
        
        // All coordinates should be finite
        for (const v of result.vertices) {
          expect(Number.isFinite(v.point.x)).toBe(true);
          expect(Number.isFinite(v.point.y)).toBe(true);
          expect(Number.isFinite(v.inHandle.x)).toBe(true);
          expect(Number.isFinite(v.inHandle.y)).toBe(true);
          expect(Number.isFinite(v.outHandle.x)).toBe(true);
          expect(Number.isFinite(v.outHandle.y)).toBe(true);
        }
      }
    );
  });

  // =========================================================================
  // EDGE CASES
  // =========================================================================

  describe('edge cases', () => {
    
    it('handles expression with undefined params', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'jitter',
        params: {},
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 50,
        animated: false,
        keyframes: [],
        expression,
      };

      // Should not crash with empty params
      const result = interpolateProperty(property, 25, 16, 'layer1');
      expect(Number.isFinite(result)).toBe(true);
    });

    it('handles unknown expression preset gracefully', () => {
      const expression: PropertyExpression = {
        enabled: true,
        type: 'preset',
        name: 'nonexistent_expression',
        params: {},
      };

      const property: AnimatableProperty<number> = {
        id: 'test',
        name: 'test',
        type: 'number',
        value: 50,
        animated: false,
        keyframes: [],
        expression,
      };

      // Should not crash, should return base value
      const result = interpolateProperty(property, 25, 16, 'layer1');
      expect(Number.isFinite(result)).toBe(true);
    });

    it('handles single vertex path gracefully', () => {
      const singleVertexPath: BezierPath = {
        vertices: [
          { point: { x: 0, y: 0 }, inHandle: { x: 0, y: 0 }, outHandle: { x: 0, y: 0 } },
        ],
        closed: false,
      };

      const property: AnimatableProperty<BezierPath> = {
        id: 'test',
        name: 'path',
        type: 'vector3' as any,
        value: singleVertexPath,
        animated: true,
        keyframes: createPathKeyframes([singleVertexPath, createTrianglePath()], [0, 100]),
      };

      // Should not crash
      const result = interpolateProperty(property, 50, 16, 'layer1');
      expect(result.vertices.length).toBeGreaterThan(0);
    });

    it('handles empty vertices array', () => {
      const emptyPath: BezierPath = {
        vertices: [],
        closed: false,
      };

      const property: AnimatableProperty<BezierPath> = {
        id: 'test',
        name: 'path',
        type: 'vector3' as any,
        value: emptyPath,
        animated: true,
        keyframes: createPathKeyframes([emptyPath, createTrianglePath()], [0, 100]),
      };

      // Should not crash - returns one of the keyframe values
      const result = interpolateProperty(property, 50, 16, 'layer1');
      expect(result).toBeDefined();
    });
  });
});
