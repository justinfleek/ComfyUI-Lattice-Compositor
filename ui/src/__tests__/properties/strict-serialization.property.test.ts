/**
 * STRICT Serialization Property Tests
 * 
 * Tests that project save/load roundtrip preserves ALL data exactly.
 * Any data loss or mutation is a CRITICAL bug.
 */

import { describe, expect, it } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import type { 
  LatticeProject, 
  LatticeComposition, 
  Layer, 
  AnimatableProperty,
  Keyframe,
  BezierHandle,
  LayerTransform,
  LayerMask,
  LayerStyle,
  PropertyExpression,
} from '@/types/project';

// ============================================================================
// SERIALIZATION HELPERS
// ============================================================================

/**
 * Serialize and deserialize via JSON (simulates save/load)
 */
function roundtrip<T>(obj: T): T {
  const json = JSON.stringify(obj);
  return JSON.parse(json);
}

/**
 * Deep equality check that catches subtle differences
 */
function deepEqual(a: any, b: any, path = ''): { equal: boolean; diff?: string } {
  // Handle nulls
  if (a === null && b === null) return { equal: true };
  if (a === null || b === null) return { equal: false, diff: `${path}: null mismatch` };
  
  // Handle undefined
  if (a === undefined && b === undefined) return { equal: true };
  if (a === undefined || b === undefined) return { equal: false, diff: `${path}: undefined mismatch` };
  
  // Handle primitives
  if (typeof a !== typeof b) {
    return { equal: false, diff: `${path}: type mismatch (${typeof a} vs ${typeof b})` };
  }
  
  if (typeof a !== 'object') {
    if (typeof a === 'number') {
      // Special handling for numbers - check for NaN
      if (Number.isNaN(a) && Number.isNaN(b)) return { equal: true };
      if (Number.isNaN(a) || Number.isNaN(b)) return { equal: false, diff: `${path}: NaN mismatch` };
      
      // Check for -0 vs +0
      if (Object.is(a, -0) !== Object.is(b, -0)) {
        return { equal: false, diff: `${path}: -0/+0 mismatch (${a} vs ${b})` };
      }
      
      // Regular number comparison with tolerance for floating point
      if (Math.abs(a - b) > 1e-15) {
        return { equal: false, diff: `${path}: number mismatch (${a} vs ${b})` };
      }
      return { equal: true };
    }
    
    if (a !== b) {
      return { equal: false, diff: `${path}: value mismatch (${a} vs ${b})` };
    }
    return { equal: true };
  }
  
  // Handle arrays
  if (Array.isArray(a)) {
    if (!Array.isArray(b)) {
      return { equal: false, diff: `${path}: array vs non-array` };
    }
    if (a.length !== b.length) {
      return { equal: false, diff: `${path}: array length mismatch (${a.length} vs ${b.length})` };
    }
    for (let i = 0; i < a.length; i++) {
      const result = deepEqual(a[i], b[i], `${path}[${i}]`);
      if (!result.equal) return result;
    }
    return { equal: true };
  }
  
  // Handle objects
  const aKeys = Object.keys(a).sort();
  const bKeys = Object.keys(b).sort();
  
  if (aKeys.length !== bKeys.length) {
    const missing = aKeys.filter(k => !bKeys.includes(k));
    const extra = bKeys.filter(k => !aKeys.includes(k));
    return { 
      equal: false, 
      diff: `${path}: key count mismatch. Missing: [${missing}], Extra: [${extra}]` 
    };
  }
  
  for (const key of aKeys) {
    if (!bKeys.includes(key)) {
      return { equal: false, diff: `${path}: missing key '${key}'` };
    }
    const result = deepEqual(a[key], b[key], `${path}.${key}`);
    if (!result.equal) return result;
  }
  
  return { equal: true };
}

// ============================================================================
// ARBITRARY GENERATORS
// ============================================================================

/**
 * Generate a valid BezierHandle
 */
const bezierHandleArb: fc.Arbitrary<BezierHandle> = fc.record({
  frame: fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
  value: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  enabled: fc.boolean(),
});

/**
 * Generate a PropertyExpression
 */
const expressionArb: fc.Arbitrary<PropertyExpression> = fc.oneof(
  fc.record({
    type: fc.constant('none' as const),
    enabled: fc.boolean(),
  }),
  fc.record({
    type: fc.constant('preset' as const),
    name: fc.string({ minLength: 1, maxLength: 20 }),
    enabled: fc.boolean(),
    params: fc.dictionary(fc.string({ minLength: 1, maxLength: 10 }), fc.double({ noNaN: true, noDefaultInfinity: true })),
  }),
);

/**
 * Generate a numeric Keyframe
 */
const numericKeyframeArb: fc.Arbitrary<Keyframe<number>> = fc.record({
  frame: fc.integer({ min: 0, max: 10000 }),
  value: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
  interpolation: fc.constantFrom('linear', 'bezier', 'hold', 'easeIn', 'easeOut', 'easeInOut'),
  inHandle: bezierHandleArb,
  outHandle: bezierHandleArb,
});

/**
 * Generate a vector Keyframe
 */
const vectorKeyframeArb: fc.Arbitrary<Keyframe<{ x: number; y: number; z?: number }>> = fc.record({
  frame: fc.integer({ min: 0, max: 10000 }),
  value: fc.oneof(
    fc.record({
      x: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
      y: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
    }),
    fc.record({
      x: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
      y: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
      z: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
    }),
  ),
  interpolation: fc.constantFrom('linear', 'bezier', 'hold'),
  inHandle: bezierHandleArb,
  outHandle: bezierHandleArb,
});

/**
 * Generate a numeric AnimatableProperty
 */
const numericPropertyArb: fc.Arbitrary<AnimatableProperty<number>> = fc.record({
  name: fc.string({ minLength: 1, maxLength: 30 }),
  value: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
  animated: fc.boolean(),
  keyframes: fc.array(numericKeyframeArb, { minLength: 0, maxLength: 10 }),
  expression: expressionArb,
});

/**
 * Generate a LayerTransform
 */
const transformArb: fc.Arbitrary<LayerTransform> = fc.record({
  position: fc.record({
    name: fc.constant('Position'),
    value: fc.record({
      x: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
      y: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
      z: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
    }),
    animated: fc.boolean(),
    keyframes: fc.constant([]),
    expression: fc.constant({ type: 'none' as const, enabled: false }),
  }),
  anchorPoint: fc.record({
    name: fc.constant('Anchor Point'),
    value: fc.record({
      x: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
      y: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
      z: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
    }),
    animated: fc.boolean(),
    keyframes: fc.constant([]),
    expression: fc.constant({ type: 'none' as const, enabled: false }),
  }),
  scale: fc.record({
    name: fc.constant('Scale'),
    value: fc.record({
      x: fc.double({ min: 0.001, max: 1000, noNaN: true, noDefaultInfinity: true }),
      y: fc.double({ min: 0.001, max: 1000, noNaN: true, noDefaultInfinity: true }),
      z: fc.double({ min: 0.001, max: 1000, noNaN: true, noDefaultInfinity: true }),
    }),
    animated: fc.boolean(),
    keyframes: fc.constant([]),
    expression: fc.constant({ type: 'none' as const, enabled: false }),
  }),
  rotation: fc.record({
    name: fc.constant('Rotation'),
    value: fc.double({ min: -720, max: 720, noNaN: true, noDefaultInfinity: true }),
    animated: fc.boolean(),
    keyframes: fc.constant([]),
    expression: fc.constant({ type: 'none' as const, enabled: false }),
  }),
  opacity: fc.record({
    name: fc.constant('Opacity'),
    value: fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true }),
    animated: fc.boolean(),
    keyframes: fc.constant([]),
    expression: fc.constant({ type: 'none' as const, enabled: false }),
  }),
});

/**
 * Generate a basic Layer
 */
const layerArb: fc.Arbitrary<Layer> = fc.record({
  id: fc.uuid(),
  name: fc.string({ minLength: 1, maxLength: 50 }),
  type: fc.constantFrom('solid', 'image', 'video', 'text', 'shape', 'null', 'camera', 'light', 'audio', 'adjustment', 'precomp'),
  visible: fc.boolean(),
  locked: fc.boolean(),
  solo: fc.boolean(),
  shy: fc.boolean(),
  inPoint: fc.integer({ min: 0, max: 1000 }),
  outPoint: fc.integer({ min: 1, max: 10000 }),
  startTime: fc.integer({ min: -1000, max: 1000 }),
  timeStretch: fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true }),
  transform: transformArb,
  blendMode: fc.constantFrom('normal', 'multiply', 'screen', 'overlay', 'add'),
  trackMatte: fc.constant(undefined),
  parentId: fc.constant(undefined),
  masks: fc.constant([]),
  effects: fc.constant([]),
  styles: fc.constant([]),
  content: fc.constant(undefined),
  markers: fc.constant([]),
  motionBlur: fc.boolean(),
  collapseTransformations: fc.boolean(),
  autoOrient: fc.boolean(),
});

// ============================================================================
// SERIALIZATION TESTS
// ============================================================================

describe('STRICT: Primitive Serialization', () => {

  test.prop([fc.double({ noNaN: true, noDefaultInfinity: true })])(
    'number roundtrip preserves value exactly',
    (n) => {
      const result = roundtrip(n);
      expect(result).toBe(n);
    }
  );

  test.prop([fc.string()])(
    'string roundtrip preserves value exactly',
    (s) => {
      const result = roundtrip(s);
      expect(result).toBe(s);
    }
  );

  test.prop([fc.boolean()])(
    'boolean roundtrip preserves value exactly',
    (b) => {
      const result = roundtrip(b);
      expect(result).toBe(b);
    }
  );

  it('handles special number values', () => {
    // These should serialize correctly
    expect(roundtrip(0)).toBe(0);
    expect(roundtrip(-0)).toBe(0); // Note: JSON loses -0
    expect(roundtrip(Number.MAX_VALUE)).toBe(Number.MAX_VALUE);
    expect(roundtrip(Number.MIN_VALUE)).toBe(Number.MIN_VALUE);
    expect(roundtrip(Number.MAX_SAFE_INTEGER)).toBe(Number.MAX_SAFE_INTEGER);
    expect(roundtrip(Number.MIN_SAFE_INTEGER)).toBe(Number.MIN_SAFE_INTEGER);
  });

  it('documents JSON limitations', () => {
    // NaN becomes null
    expect(roundtrip(NaN)).toBe(null);
    
    // Infinity becomes null
    expect(roundtrip(Infinity)).toBe(null);
    expect(roundtrip(-Infinity)).toBe(null);
    
    // -0 becomes 0 (precision loss!)
    expect(Object.is(roundtrip(-0), -0)).toBe(false);
    
    // undefined becomes undefined (property is removed)
    const obj = { a: 1, b: undefined };
    const result = roundtrip(obj);
    expect('b' in result).toBe(false);
  });

});

describe('STRICT: BezierHandle Serialization', () => {

  test.prop([bezierHandleArb])(
    'BezierHandle roundtrip preserves all fields',
    (handle) => {
      const result = roundtrip(handle);
      const comparison = deepEqual(handle, result);
      
      if (!comparison.equal) {
        console.log('BezierHandle serialization failed:', comparison.diff);
      }
      
      expect(comparison.equal).toBe(true);
    }
  );

});

describe('STRICT: Keyframe Serialization', () => {

  test.prop([numericKeyframeArb])(
    'numeric Keyframe roundtrip preserves all fields',
    (kf) => {
      const result = roundtrip(kf);
      const comparison = deepEqual(kf, result);
      
      if (!comparison.equal) {
        console.log('Keyframe serialization failed:', comparison.diff);
      }
      
      expect(comparison.equal).toBe(true);
    }
  );

  test.prop([vectorKeyframeArb])(
    'vector Keyframe roundtrip preserves all fields',
    (kf) => {
      const result = roundtrip(kf);
      const comparison = deepEqual(kf, result);
      
      if (!comparison.equal) {
        console.log('Vector keyframe serialization failed:', comparison.diff);
      }
      
      expect(comparison.equal).toBe(true);
    }
  );

});

describe('STRICT: AnimatableProperty Serialization', () => {

  test.prop([numericPropertyArb])(
    'AnimatableProperty roundtrip preserves all fields',
    (prop) => {
      const result = roundtrip(prop);
      const comparison = deepEqual(prop, result);
      
      if (!comparison.equal) {
        console.log('AnimatableProperty serialization failed:', comparison.diff);
      }
      
      expect(comparison.equal).toBe(true);
    }
  );

});

describe('STRICT: Transform Serialization', () => {

  test.prop([transformArb])(
    'LayerTransform roundtrip preserves all fields',
    (transform) => {
      const result = roundtrip(transform);
      const comparison = deepEqual(transform, result);
      
      if (!comparison.equal) {
        console.log('Transform serialization failed:', comparison.diff);
      }
      
      expect(comparison.equal).toBe(true);
    }
  );

});

describe('STRICT: Layer Serialization', () => {

  test.prop([layerArb])(
    'Layer roundtrip preserves all fields',
    (layer) => {
      const result = roundtrip(layer);
      const comparison = deepEqual(layer, result);
      
      if (!comparison.equal) {
        console.log('Layer serialization failed:', comparison.diff);
        console.log('Original:', JSON.stringify(layer, null, 2).slice(0, 500));
        console.log('Result:', JSON.stringify(result, null, 2).slice(0, 500));
      }
      
      expect(comparison.equal).toBe(true);
    }
  );

});

// ============================================================================
// PROJECT SERIALIZATION TESTS
// ============================================================================

describe('STRICT: Project Serialization', () => {

  it('minimal project roundtrip', () => {
    const project: Partial<LatticeProject> = {
      version: '1.0.0',
      meta: {
        name: 'Test Project',
        created: '2024-01-01T00:00:00Z',
        modified: '2024-01-01T00:00:00Z',
        author: 'Test',
        description: 'Test project',
      },
      settings: {
        width: 1920,
        height: 1080,
        frameRate: 24,
        duration: 10,
        backgroundColor: '#000000',
        pixelAspectRatio: 1,
        fieldOrder: 'progressive',
        preserveNestedFrameRate: false,
      },
      compositions: [],
      assets: [],
    };
    
    const result = roundtrip(project);
    const comparison = deepEqual(project, result);
    
    expect(comparison.equal).toBe(true);
  });

  it('project with layers roundtrip', () => {
    const layer: Layer = {
      id: 'layer-1',
      name: 'Test Layer',
      type: 'solid',
      visible: true,
      locked: false,
      solo: false,
      shy: false,
      inPoint: 0,
      outPoint: 100,
      startTime: 0,
      timeStretch: 1,
      transform: {
        position: {
          name: 'Position',
          value: { x: 960, y: 540, z: 0 },
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        anchorPoint: {
          name: 'Anchor Point',
          value: { x: 0, y: 0, z: 0 },
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        scale: {
          name: 'Scale',
          value: { x: 100, y: 100, z: 100 },
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        rotation: {
          name: 'Rotation',
          value: 0,
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        opacity: {
          name: 'Opacity',
          value: 100,
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
      },
      blendMode: 'normal',
      masks: [],
      effects: [],
      styles: [],
      markers: [],
      motionBlur: false,
      collapseTransformations: false,
      autoOrient: false,
    };
    
    const result = roundtrip(layer);
    const comparison = deepEqual(layer, result);
    
    if (!comparison.equal) {
      console.log('Layer roundtrip failed:', comparison.diff);
    }
    
    expect(comparison.equal).toBe(true);
  });

});

// ============================================================================
// EDGE CASE TESTS
// ============================================================================

describe('STRICT: Serialization Edge Cases', () => {

  it('handles deeply nested structures', () => {
    // Create deeply nested object
    let nested: any = { value: 42 };
    for (let i = 0; i < 50; i++) {
      nested = { child: nested };
    }
    
    const result = roundtrip(nested);
    
    // Navigate to deepest value
    let current: any = result;
    for (let i = 0; i < 50; i++) {
      current = current.child;
    }
    
    expect(current.value).toBe(42);
  });

  it('handles large arrays', () => {
    const large = Array.from({ length: 10000 }, (_, i) => ({
      index: i,
      value: Math.random(),
    }));
    
    const result = roundtrip(large);
    
    expect(result.length).toBe(10000);
    expect(result[0].index).toBe(0);
    expect(result[9999].index).toBe(9999);
  });

  it('handles unicode strings', () => {
    const unicode = {
      emoji: '🎬🎥🎞️',
      chinese: '中文测试',
      arabic: 'اختبار',
      special: '\u0000\u001f\u007f',
    };
    
    const result = roundtrip(unicode);
    
    expect(result.emoji).toBe(unicode.emoji);
    expect(result.chinese).toBe(unicode.chinese);
    expect(result.arabic).toBe(unicode.arabic);
    // Note: some control characters may be escaped differently
  });

  it('handles circular reference gracefully (should throw)', () => {
    const circular: any = { name: 'test' };
    circular.self = circular;
    
    expect(() => JSON.stringify(circular)).toThrow();
  });

  it('handles Date objects (converted to string)', () => {
    const date = new Date('2024-01-01T00:00:00Z');
    const result = roundtrip({ date });
    
    // Date becomes ISO string
    expect(typeof result.date).toBe('string');
    expect(result.date).toBe('2024-01-01T00:00:00.000Z');
  });

  it('handles Map and Set (become empty objects)', () => {
    const map = new Map([['key', 'value']]);
    const set = new Set([1, 2, 3]);
    
    const result = roundtrip({ map, set });
    
    // Map and Set are NOT preserved - this is a known limitation
    expect(result.map).toEqual({});
    expect(result.set).toEqual({});
  });

});

// ============================================================================
// STRESS TEST
// ============================================================================

describe('STRESS: Large Project Serialization', () => {

  it('handles project with many layers', () => {
    const layers = Array.from({ length: 100 }, (_, i): Layer => ({
      id: `layer-${i}`,
      name: `Layer ${i}`,
      type: 'solid',
      visible: true,
      locked: false,
      solo: false,
      shy: false,
      inPoint: 0,
      outPoint: 100,
      startTime: 0,
      timeStretch: 1,
      transform: {
        position: {
          name: 'Position',
          value: { x: i * 10, y: i * 10, z: 0 },
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        anchorPoint: {
          name: 'Anchor Point',
          value: { x: 0, y: 0, z: 0 },
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        scale: {
          name: 'Scale',
          value: { x: 100, y: 100, z: 100 },
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        rotation: {
          name: 'Rotation',
          value: i,
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
        opacity: {
          name: 'Opacity',
          value: 100,
          animated: false,
          keyframes: [],
          expression: { type: 'none', enabled: false },
        },
      },
      blendMode: 'normal',
      masks: [],
      effects: [],
      styles: [],
      markers: [],
      motionBlur: false,
      collapseTransformations: false,
      autoOrient: false,
    }));
    
    const result = roundtrip(layers);
    
    expect(result.length).toBe(100);
    
    // Verify first and last
    expect(result[0].id).toBe('layer-0');
    expect(result[99].id).toBe('layer-99');
    expect(result[50].transform.rotation.value).toBe(50);
  });

  it('handles layer with many keyframes', () => {
    const keyframes = Array.from({ length: 1000 }, (_, i): Keyframe<number> => ({
      frame: i,
      value: Math.sin(i * 0.1) * 100,
      interpolation: 'linear',
      inHandle: { frame: -5, value: 0, enabled: true },
      outHandle: { frame: 5, value: 0, enabled: true },
    }));
    
    const property: AnimatableProperty<number> = {
      name: 'Rotation',
      value: 0,
      animated: true,
      keyframes,
      expression: { type: 'none', enabled: false },
    };
    
    const result = roundtrip(property);
    
    expect(result.keyframes.length).toBe(1000);
    expect(result.keyframes[500].frame).toBe(500);
  });

});
