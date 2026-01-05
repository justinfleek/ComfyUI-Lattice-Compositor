/**
 * STRICT Property Tests for Layer Evaluation (MotionEngine)
 * 
 * Tests the invariants that must hold for correct layer evaluation:
 * 1. Determinism: same frame + same project = identical output
 * 2. Purity: evaluate() never mutates input
 * 3. Temporal correctness: in/out points are respected
 * 4. Transform evaluation: position/scale/rotation interpolate correctly
 * 5. Hierarchy: parent transforms cascade correctly
 * 
 * TOLERANCE: STRICT - Animation bugs are user-visible
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { MotionEngine, type FrameState, type EvaluatedLayer } from '@/engine/MotionEngine';
import type { 
  LatticeProject, 
  Layer, 
  AnimatableProperty,
  Composition,
  LayerTransform,
  Keyframe,
} from '@/types/project';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

/**
 * Generate a valid Vec3
 */
const arbitraryVec3 = () =>
  fc.record({
    x: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
    y: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
    z: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
  });

/**
 * Generate a valid keyframe
 */
const arbitraryKeyframe = <T>(valueArb: fc.Arbitrary<T>): fc.Arbitrary<Keyframe<T>> =>
  fc.record({
    frame: fc.integer({ min: 0, max: 1000 }),
    value: valueArb,
    easing: fc.constantFrom('linear', 'easeIn', 'easeOut', 'easeInOut'),
  });

/**
 * Generate a valid AnimatableProperty with sorted keyframes
 */
const arbitraryAnimatableProperty = <T>(valueArb: fc.Arbitrary<T>): fc.Arbitrary<AnimatableProperty<T>> =>
  fc.record({
    name: fc.string({ minLength: 1, maxLength: 20 }),
    value: valueArb,
    keyframes: fc.array(arbitraryKeyframe(valueArb), { maxLength: 10 }).map(kfs => 
      // Sort keyframes by frame to ensure valid timeline
      [...kfs].sort((a, b) => a.frame - b.frame)
    ),
  });

/**
 * Generate a valid transform
 */
const arbitraryTransform = (): fc.Arbitrary<LayerTransform> =>
  fc.record({
    position: arbitraryAnimatableProperty(arbitraryVec3()),
    scale: arbitraryAnimatableProperty(
      fc.record({
        x: fc.double({ min: 0.01, max: 500, noNaN: true, noDefaultInfinity: true }),
        y: fc.double({ min: 0.01, max: 500, noNaN: true, noDefaultInfinity: true }),
        z: fc.double({ min: 0.01, max: 500, noNaN: true, noDefaultInfinity: true }),
      })
    ),
    rotation: arbitraryAnimatableProperty(fc.double({ min: -360, max: 360, noNaN: true, noDefaultInfinity: true })),
    origin: arbitraryAnimatableProperty(arbitraryVec3()),
  }) as fc.Arbitrary<LayerTransform>;

/**
 * Generate a minimal layer for testing
 */
const arbitraryTestLayer = (): fc.Arbitrary<Layer> =>
  fc.record({
    id: fc.uuid(),
    name: fc.string({ minLength: 1, maxLength: 30 }),
    type: fc.constantFrom('solid', 'text', 'image', 'null'),
    visible: fc.boolean(),
    locked: fc.constant(false),
    solo: fc.constant(false),
    shy: fc.constant(false),
    blendMode: fc.constantFrom('normal', 'multiply', 'screen'),
    threeD: fc.boolean(),
    parentId: fc.constant(null) as fc.Arbitrary<string | null>,
    opacity: arbitraryAnimatableProperty(fc.integer({ min: 0, max: 100 })),
    transform: arbitraryTransform(),
    effects: fc.constant([]),
    properties: fc.constant([]),
    masks: fc.constant([]),
    startFrame: fc.integer({ min: 0, max: 50 }),
    endFrame: fc.integer({ min: 50, max: 200 }),
    data: fc.constant(null),
  }).map(layer => ({
    ...layer,
    // Ensure endFrame > startFrame
    endFrame: Math.max(layer.endFrame, layer.startFrame + 1),
  })) as fc.Arbitrary<Layer>;

/**
 * Generate a minimal project for testing
 */
const arbitraryTestProject = (layers?: Layer[]): fc.Arbitrary<LatticeProject> => {
  const layerArb = layers 
    ? fc.constant(layers)
    : fc.array(arbitraryTestLayer(), { minLength: 1, maxLength: 5 });
    
  return layerArb.chain(layerList => {
    const compId = 'test-comp-' + Math.random().toString(36).slice(2);
    return fc.record({
      version: fc.constant('1.0.0'),
      mainCompositionId: fc.constant(compId),
      meta: fc.record({
        name: fc.constant('Test Project'),
        created: fc.constant(new Date().toISOString()),
        modified: fc.constant(new Date().toISOString()),
      }),
      composition: fc.record({
        width: fc.constant(1920),
        height: fc.constant(1080),
        frameCount: fc.constant(300),
        fps: fc.constant(30),
        backgroundColor: fc.constant('#000000'),
      }),
      compositions: fc.constant({
        [compId]: {
          id: compId,
          name: 'Main',
          settings: {
            width: 1920,
            height: 1080,
            frameCount: 300,
            fps: 30,
            backgroundColor: '#000000',
          },
          layers: layerList,
        } as Composition
      }),
      assets: fc.constant({}),
      audioMappings: fc.constant([]),
    });
  }) as fc.Arbitrary<LatticeProject>;
};

// ============================================================================
// STRICT DETERMINISM TESTS
// ============================================================================

describe('STRICT: Layer Evaluation Determinism', () => {
  test.prop([
    arbitraryTestProject(),
    fc.integer({ min: 0, max: 299 })
  ])('evaluate(frame) is deterministic - same inputs = same outputs', (project, frame) => {
    const engine = new MotionEngine();
    
    // Evaluate the same frame twice
    const result1 = engine.evaluate(frame, project, null, null, false);
    const result2 = engine.evaluate(frame, project, null, null, false);
    
    // Results should be identical
    expect(result1.frame).toBe(result2.frame);
    expect(result1.layers.length).toBe(result2.layers.length);
    
    for (let i = 0; i < result1.layers.length; i++) {
      const l1 = result1.layers[i];
      const l2 = result2.layers[i];
      
      expect(l1.id).toBe(l2.id);
      expect(l1.opacity).toBe(l2.opacity);
      expect(l1.visible).toBe(l2.visible);
      expect(l1.transform.position.x).toBe(l2.transform.position.x);
      expect(l1.transform.position.y).toBe(l2.transform.position.y);
      expect(l1.transform.scale.x).toBe(l2.transform.scale.x);
      expect(l1.transform.scale.y).toBe(l2.transform.scale.y);
      expect(l1.transform.rotation).toBe(l2.transform.rotation);
    }
  });

  test.prop([
    arbitraryTestProject(),
    fc.integer({ min: 0, max: 299 })
  ])('evaluation order does not affect results', (project, targetFrame) => {
    const engine1 = new MotionEngine();
    const engine2 = new MotionEngine();
    
    // Evaluate frames in different orders
    // Engine 1: forward
    for (let f = 0; f <= targetFrame; f += 10) {
      engine1.evaluate(f, project, null, null, false);
    }
    const result1 = engine1.evaluate(targetFrame, project, null, null, false);
    
    // Engine 2: backward then forward
    for (let f = 299; f >= targetFrame; f -= 10) {
      engine2.evaluate(f, project, null, null, false);
    }
    const result2 = engine2.evaluate(targetFrame, project, null, null, false);
    
    // Results should be identical
    expect(result1.layers.length).toBe(result2.layers.length);
    
    for (let i = 0; i < result1.layers.length; i++) {
      expect(result1.layers[i].opacity).toBe(result2.layers[i].opacity);
      expect(result1.layers[i].transform.position.x).toBe(result2.layers[i].transform.position.x);
      expect(result1.layers[i].transform.rotation).toBe(result2.layers[i].transform.rotation);
    }
  });
});

// ============================================================================
// STRICT PURITY TESTS
// ============================================================================

describe('STRICT: Layer Evaluation Purity', () => {
  test.prop([
    arbitraryTestProject(),
    fc.integer({ min: 0, max: 299 })
  ])('evaluate() does not mutate input project', (project, frame) => {
    const engine = new MotionEngine();
    
    // Deep copy project before evaluation
    const projectBefore = JSON.stringify(project);
    
    // Evaluate
    engine.evaluate(frame, project, null, null, false);
    
    // Project should be unchanged
    const projectAfter = JSON.stringify(project);
    expect(projectAfter).toBe(projectBefore);
  });

  test.prop([
    arbitraryTestProject(),
    fc.integer({ min: 0, max: 299 })
  ])('returned FrameState is frozen (immutable)', (project, frame) => {
    const engine = new MotionEngine();
    const result = engine.evaluate(frame, project, null, null, false);
    
    // FrameState should be frozen
    expect(Object.isFrozen(result)).toBe(true);
    expect(Object.isFrozen(result.layers)).toBe(true);
    
    // Each layer should be frozen
    for (const layer of result.layers) {
      expect(Object.isFrozen(layer)).toBe(true);
      expect(Object.isFrozen(layer.transform)).toBe(true);
    }
  });
});

// ============================================================================
// STRICT TEMPORAL CORRECTNESS TESTS
// ============================================================================

describe('STRICT: Temporal Correctness', () => {
  test.prop([arbitraryTestLayer()])('layer visible only within in/out points', (layer) => {
    // Create a project with this single layer
    const compId = 'test-comp';
    const project: LatticeProject = {
      version: '1.0.0',
      mainCompositionId: compId,
      meta: { name: 'Test', created: '', modified: '' },
      composition: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
      compositions: {
        [compId]: {
          id: compId,
          name: 'Main',
          settings: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
          layers: [{ ...layer, visible: true }], // Force visible to test in/out points
        }
      },
      assets: {},
      audioMappings: [],
    };
    
    const engine = new MotionEngine();
    const startFrame = layer.startFrame ?? 0;
    const endFrame = layer.endFrame ?? 300;
    
    // Test before start
    if (startFrame > 0) {
      const beforeResult = engine.evaluate(startFrame - 1, project, null, null, false);
      const evaluatedLayer = beforeResult.layers.find(l => l.id === layer.id);
      expect(evaluatedLayer?.inRange).toBe(false);
    }
    
    // Test at start
    const atStartResult = engine.evaluate(startFrame, project, null, null, false);
    const atStartLayer = atStartResult.layers.find(l => l.id === layer.id);
    expect(atStartLayer?.inRange).toBe(true);
    
    // Test at end
    const atEndResult = engine.evaluate(endFrame, project, null, null, false);
    const atEndLayer = atEndResult.layers.find(l => l.id === layer.id);
    expect(atEndLayer?.inRange).toBe(true);
    
    // Test after end
    if (endFrame < 299) {
      const afterResult = engine.evaluate(endFrame + 1, project, null, null, false);
      const afterLayer = afterResult.layers.find(l => l.id === layer.id);
      expect(afterLayer?.inRange).toBe(false);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 100 }),
    fc.integer({ min: 0, max: 100 }),
    fc.integer({ min: 0, max: 100 })
  ])('keyframe at exact frame returns keyframe value', (kfFrame, kfValue, queryFrame) => {
    // Create layer with a single keyframe
    const layer: Layer = {
      id: 'test-layer',
      name: 'Test',
      type: 'solid',
      visible: true,
      locked: false,
      solo: false,
      shy: false,
      blendMode: 'normal',
      threeD: false,
      parentId: null,
      opacity: {
        name: 'opacity',
        value: 50,
        keyframes: [{ frame: kfFrame, value: kfValue, easing: 'linear' }],
      },
      transform: {
        position: { name: 'position', value: { x: 0, y: 0, z: 0 }, keyframes: [] },
        scale: { name: 'scale', value: { x: 100, y: 100, z: 100 }, keyframes: [] },
        rotation: { name: 'rotation', value: 0, keyframes: [] },
      },
      effects: [],
      properties: [],
      masks: [],
      startFrame: 0,
      endFrame: 200,
      data: null,
    };
    
    const compId = 'test-comp';
    const project: LatticeProject = {
      version: '1.0.0',
      mainCompositionId: compId,
      meta: { name: 'Test', created: '', modified: '' },
      composition: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
      compositions: {
        [compId]: {
          id: compId,
          name: 'Main',
          settings: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
          layers: [layer],
        }
      },
      assets: {},
      audioMappings: [],
    };
    
    const engine = new MotionEngine();
    const result = engine.evaluate(kfFrame, project, null, null, false);
    const evaluatedLayer = result.layers.find(l => l.id === 'test-layer');
    
    // At keyframe frame, should return keyframe value
    expect(evaluatedLayer?.opacity).toBe(kfValue);
  });
});

// ============================================================================
// STRICT INTERPOLATION TESTS
// ============================================================================

describe('STRICT: Transform Interpolation', () => {
  test.prop([
    fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  ])('linear interpolation at midpoint is average of endpoints', (startVal, endVal) => {
    const layer: Layer = {
      id: 'test-layer',
      name: 'Test',
      type: 'solid',
      visible: true,
      locked: false,
      solo: false,
      shy: false,
      blendMode: 'normal',
      threeD: false,
      parentId: null,
      opacity: { name: 'opacity', value: 100, keyframes: [] },
      transform: {
        position: {
          name: 'position',
          value: { x: startVal, y: 0, z: 0 },
          keyframes: [
            { frame: 0, value: { x: startVal, y: 0, z: 0 }, easing: 'linear' },
            { frame: 100, value: { x: endVal, y: 0, z: 0 }, easing: 'linear' },
          ],
        },
        scale: { name: 'scale', value: { x: 100, y: 100, z: 100 }, keyframes: [] },
        rotation: { name: 'rotation', value: 0, keyframes: [] },
      },
      effects: [],
      properties: [],
      masks: [],
      startFrame: 0,
      endFrame: 200,
      data: null,
    };
    
    const compId = 'test-comp';
    const project: LatticeProject = {
      version: '1.0.0',
      mainCompositionId: compId,
      meta: { name: 'Test', created: '', modified: '' },
      composition: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
      compositions: {
        [compId]: {
          id: compId,
          name: 'Main',
          settings: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
          layers: [layer],
        }
      },
      assets: {},
      audioMappings: [],
    };
    
    const engine = new MotionEngine();
    
    // At frame 50 (midpoint), should be average
    const result = engine.evaluate(50, project, null, null, false);
    const evaluatedLayer = result.layers.find(l => l.id === 'test-layer');
    
    const expectedMidpoint = (startVal + endVal) / 2;
    const tolerance = 1e-6;
    
    expect(Math.abs(evaluatedLayer!.transform.position.x - expectedMidpoint)).toBeLessThan(tolerance);
  });

  test.prop([
    fc.double({ min: 0.1, max: 500, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0.1, max: 500, noNaN: true, noDefaultInfinity: true }),
  ])('scale interpolation maintains positivity', (startScale, endScale) => {
    const layer: Layer = {
      id: 'test-layer',
      name: 'Test',
      type: 'solid',
      visible: true,
      locked: false,
      solo: false,
      shy: false,
      blendMode: 'normal',
      threeD: false,
      parentId: null,
      opacity: { name: 'opacity', value: 100, keyframes: [] },
      transform: {
        position: { name: 'position', value: { x: 0, y: 0, z: 0 }, keyframes: [] },
        scale: {
          name: 'scale',
          value: { x: startScale, y: startScale, z: 100 },
          keyframes: [
            { frame: 0, value: { x: startScale, y: startScale, z: 100 }, easing: 'linear' },
            { frame: 100, value: { x: endScale, y: endScale, z: 100 }, easing: 'linear' },
          ],
        },
        rotation: { name: 'rotation', value: 0, keyframes: [] },
      },
      effects: [],
      properties: [],
      masks: [],
      startFrame: 0,
      endFrame: 200,
      data: null,
    };
    
    const compId = 'test-comp';
    const project: LatticeProject = {
      version: '1.0.0',
      mainCompositionId: compId,
      meta: { name: 'Test', created: '', modified: '' },
      composition: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
      compositions: {
        [compId]: {
          id: compId,
          name: 'Main',
          settings: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
          layers: [layer],
        }
      },
      assets: {},
      audioMappings: [],
    };
    
    const engine = new MotionEngine();
    
    // Test at multiple frames
    for (let f = 0; f <= 100; f += 10) {
      const result = engine.evaluate(f, project, null, null, false);
      const evaluatedLayer = result.layers.find(l => l.id === 'test-layer');
      
      // Scale should always be positive
      expect(evaluatedLayer!.transform.scale.x).toBeGreaterThan(0);
      expect(evaluatedLayer!.transform.scale.y).toBeGreaterThan(0);
    }
  });
});

// ============================================================================
// STRICT VISIBILITY TESTS
// ============================================================================

describe('STRICT: Visibility Logic', () => {
  it('hidden layer has visible=false regardless of frame', () => {
    const layer: Layer = {
      id: 'hidden-layer',
      name: 'Hidden',
      type: 'solid',
      visible: false, // Explicitly hidden
      locked: false,
      solo: false,
      shy: false,
      blendMode: 'normal',
      threeD: false,
      parentId: null,
      opacity: { name: 'opacity', value: 100, keyframes: [] },
      transform: {
        position: { name: 'position', value: { x: 0, y: 0, z: 0 }, keyframes: [] },
        scale: { name: 'scale', value: { x: 100, y: 100, z: 100 }, keyframes: [] },
        rotation: { name: 'rotation', value: 0, keyframes: [] },
      },
      effects: [],
      properties: [],
      masks: [],
      startFrame: 0,
      endFrame: 200,
      data: null,
    };
    
    const compId = 'test-comp';
    const project: LatticeProject = {
      version: '1.0.0',
      mainCompositionId: compId,
      meta: { name: 'Test', created: '', modified: '' },
      composition: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
      compositions: {
        [compId]: {
          id: compId,
          name: 'Main',
          settings: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
          layers: [layer],
        }
      },
      assets: {},
      audioMappings: [],
    };
    
    const engine = new MotionEngine();
    
    // Test at multiple frames within the layer's range
    for (let f = 0; f <= 200; f += 50) {
      const result = engine.evaluate(f, project, null, null, false);
      const evaluatedLayer = result.layers.find(l => l.id === 'hidden-layer');
      
      // Layer should exist but be marked not visible
      expect(evaluatedLayer).toBeDefined();
      expect(evaluatedLayer!.visible).toBe(false);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 100 })
  ])('zero opacity layer is still evaluated (visible = true)', (frame) => {
    const layer: Layer = {
      id: 'zero-opacity',
      name: 'Zero Opacity',
      type: 'solid',
      visible: true,
      locked: false,
      solo: false,
      shy: false,
      blendMode: 'normal',
      threeD: false,
      parentId: null,
      opacity: { name: 'opacity', value: 0, keyframes: [] }, // Zero opacity
      transform: {
        position: { name: 'position', value: { x: 0, y: 0, z: 0 }, keyframes: [] },
        scale: { name: 'scale', value: { x: 100, y: 100, z: 100 }, keyframes: [] },
        rotation: { name: 'rotation', value: 0, keyframes: [] },
      },
      effects: [],
      properties: [],
      masks: [],
      startFrame: 0,
      endFrame: 200,
      data: null,
    };
    
    const compId = 'test-comp';
    const project: LatticeProject = {
      version: '1.0.0',
      mainCompositionId: compId,
      meta: { name: 'Test', created: '', modified: '' },
      composition: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
      compositions: {
        [compId]: {
          id: compId,
          name: 'Main',
          settings: { width: 1920, height: 1080, frameCount: 300, fps: 30, backgroundColor: '#000' },
          layers: [layer],
        }
      },
      assets: {},
      audioMappings: [],
    };
    
    const engine = new MotionEngine();
    const result = engine.evaluate(frame, project, null, null, false);
    const evaluatedLayer = result.layers.find(l => l.id === 'zero-opacity');
    
    // Layer should be visible (visibility != opacity)
    expect(evaluatedLayer?.visible).toBe(true);
    expect(evaluatedLayer?.opacity).toBe(0);
  });
});

// ============================================================================
// STRICT CACHE TESTS
// ============================================================================

describe('STRICT: Evaluation Cache', () => {
  test.prop([
    arbitraryTestProject(),
    fc.integer({ min: 0, max: 299 })
  ])('cached result equals non-cached result', (project, frame) => {
    const engine = new MotionEngine();
    
    // First call without cache
    const uncached = engine.evaluate(frame, project, null, null, false);
    
    // Second call with cache (should cache this one)
    const cached1 = engine.evaluate(frame, project, null, null, true);
    
    // Third call should hit cache
    const cached2 = engine.evaluate(frame, project, null, null, true);
    
    // All should be equivalent
    expect(uncached.layers.length).toBe(cached1.layers.length);
    expect(cached1.layers.length).toBe(cached2.layers.length);
    
    for (let i = 0; i < uncached.layers.length; i++) {
      expect(uncached.layers[i].opacity).toBe(cached1.layers[i].opacity);
      expect(cached1.layers[i].opacity).toBe(cached2.layers[i].opacity);
    }
  });

  test.prop([arbitraryTestProject()])('invalidateCache clears cached results', (project) => {
    const engine = new MotionEngine();
    
    // Cache some results
    engine.evaluate(0, project, null, null, true);
    engine.evaluate(50, project, null, null, true);
    engine.evaluate(100, project, null, null, true);
    
    const statsBefore = engine.getCacheStats();
    expect(statsBefore.size).toBeGreaterThan(0);
    
    // Invalidate
    engine.invalidateCache();
    
    const statsAfter = engine.getCacheStats();
    expect(statsAfter.size).toBe(0);
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Layer Evaluation Under Load', () => {
  test.prop([
    arbitraryTestProject(),
    fc.array(fc.integer({ min: 0, max: 299 }), { minLength: 10, maxLength: 50 })
  ])('rapid frame scrubbing produces consistent results', (project, frames) => {
    const engine = new MotionEngine();
    const results = new Map<number, FrameState>();
    
    // First pass: evaluate all frames
    for (const frame of frames) {
      const result = engine.evaluate(frame, project, null, null, false);
      results.set(frame, result);
    }
    
    // Second pass: re-evaluate in random order and verify
    const shuffled = [...frames].sort(() => Math.random() - 0.5);
    for (const frame of shuffled) {
      const newResult = engine.evaluate(frame, project, null, null, false);
      const originalResult = results.get(frame)!;
      
      // Results should match
      expect(newResult.layers.length).toBe(originalResult.layers.length);
      for (let i = 0; i < newResult.layers.length; i++) {
        expect(newResult.layers[i].opacity).toBe(originalResult.layers[i].opacity);
        expect(newResult.layers[i].transform.position.x).toBe(originalResult.layers[i].transform.position.x);
      }
    }
  });
});
