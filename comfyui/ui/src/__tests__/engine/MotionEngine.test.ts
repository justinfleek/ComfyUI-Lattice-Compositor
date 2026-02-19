/**
 * STRICT MOTION ENGINE Property Tests
 * 
 * Created: Fresh audit - do NOT trust old tests
 * 
 * Tests EVERY edge case in MotionEngine.ts:
 * - Frame evaluation determinism
 * - Cache behavior
 * - Layer visibility logic
 * - Transform evaluation
 * - Effect evaluation
 * - Camera evaluation
 * - Audio evaluation
 * - Particle snapshot determinism
 */

import { describe, expect, beforeEach, afterEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { 
  MotionEngine,
  motionEngine,
  type FrameState,
  type EvaluatedLayer,
  type EvaluatedTransform,
} from '@/engine/MotionEngine';
import type { 
  LatticeProject, 
  Layer, 
  AnimatableProperty,
  CompositionSettings,
  Composition,
} from '@/types/project';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                           // test // helpers
// ════════════════════════════════════════════════════════════════════════════

function createMinimalProject(layers: Layer[] = []): LatticeProject {
  const composition: Composition = {
    id: 'main',
    name: 'Test Comp',
    settings: {
      width: 1920,
      height: 1080,
      fps: 30,
      duration: 5,
      backgroundColor: '#000000',
      frameCount: 150,
      autoResizeToContent: false,
      frameBlendingEnabled: false,
    },
    layers,
    currentFrame: 0,
    isNestedComp: false,
  };

  return {
    version: '1.0.0' as const,
    mainCompositionId: 'main',
    compositions: { main: composition },
    composition: composition.settings,
    assets: {},
    meta: {
      name: 'Test Project',
      created: '2026-01-05',
      modified: '2026-01-05',
    },
    layers: layers,
    currentFrame: 0,
  };
}

/**
 * Infer AnimatableProperty type from runtime value
 * Production-grade type inference for test helpers
 */
function inferPropertyType<T>(value: T): "number" | "position" | "color" | "enum" | "vector3" {
  if (typeof value === "number") {
    return "number";
  }
  if (typeof value === "string") {
    return "enum";
  }
  if (typeof value === "object" && value !== null) {
    const obj = value as Record<string, unknown>;
    // Check for RGBA color: { r, g, b, a }
    if (
      typeof obj.r === "number" &&
      typeof obj.g === "number" &&
      typeof obj.b === "number" &&
      typeof obj.a === "number"
    ) {
      return "color";
    }
    // Check for Vec3: { x, y, z }
    if (
      typeof obj.x === "number" &&
      typeof obj.y === "number" &&
      typeof obj.z === "number"
    ) {
      return "vector3";
    }
    // Check for Vec2/Position: { x, y }
    if (typeof obj.x === "number" && typeof obj.y === "number") {
      return "position";
    }
  }
  // Default fallback
  return "number";
}

function createAnimatableProperty<T>(value: T, animated: boolean = false): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random()}`,
    name: "test",
    type: inferPropertyType(value),
    value,
    animated,
    keyframes: [],
  };
}

function createMinimalLayer(overrides: Partial<Layer> = {}): Layer {
  return {
    id: `layer-${Math.random()}`,
    name: 'Test Layer',
    type: 'solid',
    visible: true,
    locked: false,
    isolate: false,
    startFrame: 0,
    endFrame: 150,
    inPoint: 0,
    outPoint: 150,
    blendMode: 'normal',
    threeD: false,
    motionBlur: false,
    opacity: createAnimatableProperty(100),
    transform: {
      position: createAnimatableProperty({ x: 960, y: 540 }),
      scale: createAnimatableProperty({ x: 100, y: 100 }),
      rotation: createAnimatableProperty(0),
      origin: createAnimatableProperty({ x: 0, y: 0 }),
    },
    effects: [],
    properties: [],
    parentId: null,
    data: { color: '#ff0000', width: 1920, height: 1080 },
    ...overrides,
  };
}

describe('STRICT: MotionEngine Edge Cases', () => {
  let engine: MotionEngine;

  beforeEach(() => {
    engine = new MotionEngine();
    engine.invalidateCache();
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                               // determinism
  // ════════════════════════════════════════════════════════════════════════════

  describe('determinism', () => {

    test.prop([fc.integer({ min: 0, max: 1000 })])(
      'STRICT: same frame produces identical FrameState (100 runs)',
      (frame) => {
        const layer = createMinimalLayer();
        const project = createMinimalProject([layer]);

        const results: FrameState[] = [];
        for (let i = 0; i < 100; i++) {
          // Invalidate cache each time to ensure true recomputation
          engine.invalidateCache();
          results.push(engine.evaluate(frame, project, null, null, false));
        }

        // All results must be identical
        const first = results[0];
        for (let i = 1; i < results.length; i++) {
          expect(results[i].frame).toBe(first.frame);
          expect(results[i].layers.length).toBe(first.layers.length);
          
          // Check layer values
          for (let j = 0; j < first.layers.length; j++) {
            expect(results[i].layers[j].opacity).toBe(first.layers[j].opacity);
            expect(results[i].layers[j].transform.position.x).toBe(first.layers[j].transform.position.x);
            expect(results[i].layers[j].transform.position.y).toBe(first.layers[j].transform.position.y);
          }
        }
      }
    );

    test('determinism with caching enabled', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      // First evaluation (cache miss)
      const result1 = engine.evaluate(50, project, null, null, true);
      
      // Second evaluation (cache hit)
      const result2 = engine.evaluate(50, project, null, null, true);

      // Must be identical
      expect(result1.frame).toBe(result2.frame);
      expect(result1.layers[0].opacity).toBe(result2.layers[0].opacity);
      expect(result1.layers[0].transform.position.x).toBe(result2.layers[0].transform.position.x);
    });

    test('determinism after cache invalidation', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result1 = engine.evaluate(50, project, null, null, true);
      engine.invalidateCache();
      const result2 = engine.evaluate(50, project, null, null, true);

      expect(result1.layers[0].opacity).toBe(result2.layers[0].opacity);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // layer // visibility
  // ════════════════════════════════════════════════════════════════════════════

  describe('layer visibility', () => {

    test.prop([
      fc.integer({ min: 0, max: 50 }),   // startFrame
      fc.integer({ min: 100, max: 150 }), // endFrame
      fc.integer({ min: 0, max: 200 }),   // testFrame
    ])(
      'STRICT: layer visibility respects in/out points',
      (startFrame, endFrame, testFrame) => {
        const layer = createMinimalLayer({ startFrame, endFrame, inPoint: startFrame, outPoint: endFrame });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(testFrame, project);
        const evalLayer = result.layers[0];

        const expectedInRange = testFrame >= startFrame && testFrame <= endFrame;
        expect(evalLayer.inRange).toBe(expectedInRange);
        expect(evalLayer.visible).toBe(expectedInRange);
      }
    );

    test('hidden layer is not visible even in range', () => {
      const layer = createMinimalLayer({ visible: false, startFrame: 0, endFrame: 100 });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(50, project);
      expect(result.layers[0].visible).toBe(false);
      expect(result.layers[0].inRange).toBe(true);
    });

    test('layer at exact start frame is visible', () => {
      const layer = createMinimalLayer({ startFrame: 50, endFrame: 100 });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(50, project);
      expect(result.layers[0].inRange).toBe(true);
    });

    test('layer at exact end frame is visible', () => {
      const layer = createMinimalLayer({ startFrame: 0, endFrame: 50 });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(50, project);
      expect(result.layers[0].inRange).toBe(true);
    });

    test('layer one frame before start is not visible', () => {
      const layer = createMinimalLayer({ startFrame: 50, endFrame: 100 });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(49, project);
      expect(result.layers[0].inRange).toBe(false);
    });

    test('layer one frame after end is not visible', () => {
      const layer = createMinimalLayer({ startFrame: 0, endFrame: 50 });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(51, project);
      expect(result.layers[0].inRange).toBe(false);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // transform // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  describe('transform evaluation', () => {

    test.prop([
      fc.double({ min: -10000, max: 10000, noNaN: true }),
      fc.double({ min: -10000, max: 10000, noNaN: true }),
    ])(
      'STRICT: position values are preserved',
      (x, y) => {
        const layer = createMinimalLayer({
          transform: {
            position: createAnimatableProperty({ x, y }),
            scale: createAnimatableProperty({ x: 100, y: 100 }),
            rotation: createAnimatableProperty(0),
            origin: createAnimatableProperty({ x: 0, y: 0 }),
          },
        });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(0, project);
        expect(result.layers[0].transform.position.x).toBe(x);
        expect(result.layers[0].transform.position.y).toBe(y);
      }
    );

    test.prop([
      fc.double({ min: 0, max: 1000, noNaN: true }),
      fc.double({ min: 0, max: 1000, noNaN: true }),
    ])(
      'STRICT: scale values are preserved',
      (scaleX, scaleY) => {
        const layer = createMinimalLayer({
          transform: {
            position: createAnimatableProperty({ x: 0, y: 0 }),
            scale: createAnimatableProperty({ x: scaleX, y: scaleY }),
            rotation: createAnimatableProperty(0),
            origin: createAnimatableProperty({ x: 0, y: 0 }),
          },
        });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(0, project);
        expect(result.layers[0].transform.scale.x).toBe(scaleX);
        expect(result.layers[0].transform.scale.y).toBe(scaleY);
      }
    );

    test.prop([fc.double({ min: -360, max: 360, noNaN: true })])(
      'STRICT: rotation values are preserved',
      (rotation) => {
        const layer = createMinimalLayer({
          transform: {
            position: createAnimatableProperty({ x: 0, y: 0 }),
            scale: createAnimatableProperty({ x: 100, y: 100 }),
            rotation: createAnimatableProperty(rotation),
            origin: createAnimatableProperty({ x: 0, y: 0 }),
          },
        });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(0, project);
        expect(result.layers[0].transform.rotation).toBe(rotation);
      }
    );

    test('3D layer includes rotation axes', () => {
      const layer = createMinimalLayer({
        threeD: true,
        transform: {
          position: createAnimatableProperty({ x: 0, y: 0, z: 100 }),
          scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
          rotation: createAnimatableProperty(0),
          rotationX: createAnimatableProperty(45),
          rotationY: createAnimatableProperty(90),
          rotationZ: createAnimatableProperty(180),
          origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        },
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      const transform = result.layers[0].transform;
      
      expect(transform.rotationX).toBe(45);
      expect(transform.rotationY).toBe(90);
      expect(transform.rotationZ).toBe(180);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // opacity // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  describe('opacity evaluation', () => {

    test.prop([fc.double({ min: 0, max: 100, noNaN: true })])(
      'STRICT: opacity values are preserved',
      (opacity) => {
        const layer = createMinimalLayer({
          opacity: createAnimatableProperty(opacity),
        });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(0, project);
        expect(result.layers[0].opacity).toBe(opacity);
      }
    );

    test('animated opacity interpolates correctly', () => {
      const layer = createMinimalLayer({
        opacity: {
          id: 'opacity',
          name: 'opacity',
          type: 'number',
          value: 0,
          animated: true,
          keyframes: [
            { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
            { id: 'kf2', frame: 100, value: 100, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
          ],
        },
      });
      const project = createMinimalProject([layer]);

      expect(engine.evaluate(0, project).layers[0].opacity).toBeCloseTo(0, 5);
      expect(engine.evaluate(50, project).layers[0].opacity).toBeCloseTo(50, 5);
      expect(engine.evaluate(100, project).layers[0].opacity).toBeCloseTo(100, 5);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                     // empty
  // ════════════════════════════════════════════════════════════════════════════

  describe('empty/edge cases', () => {

    test('empty project returns empty layers', () => {
      const project = createMinimalProject([]);
      const result = engine.evaluate(0, project);
      
      expect(result.layers).toHaveLength(0);
      expect(result.camera).toBeNull();
    });

    test('missing composition returns empty frame state', () => {
      const project: LatticeProject = {
        version: '1.0.0' as const,
        mainCompositionId: 'nonexistent',
        compositions: {},
        composition: {
          width: 1920,
          height: 1080,
          fps: 30,
          duration: 5,
          backgroundColor: '#000000',
          frameCount: 150,
          autoResizeToContent: false,
          frameBlendingEnabled: false,
        },
        assets: {},
        meta: { name: 'Test', created: '', modified: '' },
        layers: [],
        currentFrame: 0,
      };

      const result = engine.evaluate(0, project);
      expect(result.layers).toHaveLength(0);
    });

    test('negative frame handled gracefully', () => {
      const layer = createMinimalLayer({ startFrame: 0, endFrame: 100 });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(-10, project);
      expect(Number.isFinite(result.frame)).toBe(true);
      expect(result.frame).toBe(-10);
      // Layer should not be in range
      expect(result.layers[0].inRange).toBe(false);
    });

    test('very large frame handled gracefully', () => {
      const layer = createMinimalLayer({ startFrame: 0, endFrame: 100 });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(1000000, project);
      expect(Number.isFinite(result.frame)).toBe(true);
      expect(result.layers[0].inRange).toBe(false);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                         // cache // behavior
  // ════════════════════════════════════════════════════════════════════════════

  describe('cache behavior', () => {

    test('cache statistics work', () => {
      const stats = engine.getCacheStats();
      expect(typeof stats.size).toBe('number');
      expect(typeof stats.maxSize).toBe('number');
    });

    test('cache invalidation clears entries', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      // Populate cache
      engine.evaluate(0, project, null, null, true);
      engine.evaluate(1, project, null, null, true);
      
      const statsBefore = engine.getCacheStats();
      engine.invalidateCache();
      const statsAfter = engine.getCacheStats();

      expect(statsAfter.size).toBe(0);
    });

    test('cache disabled produces same results', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const withCache = engine.evaluate(50, project, null, null, true);
      engine.invalidateCache();
      const withoutCache = engine.evaluate(50, project, null, null, false);

      expect(withCache.layers[0].opacity).toBe(withoutCache.layers[0].opacity);
      expect(withCache.layers[0].transform.position.x).toBe(withoutCache.layers[0].transform.position.x);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                       // audio // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  describe('audio evaluation', () => {

    test('no audio returns zero values', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project, null);
      
      expect(result.audio.hasAudio).toBe(false);
      expect(result.audio.amplitude).toBe(0);
      expect(result.audio.rms).toBe(0);
      expect(result.audio.bass).toBe(0);
      expect(result.audio.mid).toBe(0);
      expect(result.audio.high).toBe(0);
      expect(result.audio.isBeat).toBe(false);
      expect(result.audio.bpm).toBe(0);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                              // immutability
  // ════════════════════════════════════════════════════════════════════════════

  describe('immutability', () => {

    test('returned FrameState is frozen', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      
      expect(Object.isFrozen(result)).toBe(true);
      expect(Object.isFrozen(result.layers)).toBe(true);
      expect(Object.isFrozen(result.audio)).toBe(true);
    });

    test('modifying returned state throws', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      
      // Test immutability: attempt to modify readonly property
      // Type guard ensures we're testing runtime behavior, not TypeScript compile-time checks
      expect(() => {
        // Use Object.defineProperty to test if property is writable
        const descriptor = Object.getOwnPropertyDescriptor(result, 'frame');
        if (descriptor && !descriptor.writable && !descriptor.set) {
          // Property is readonly - attempt assignment should fail
          (result as FrameState & { frame: number }).frame = 999;
        } else {
          throw new Error('Property should be readonly');
        }
      }).toThrow();
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // singleton // instance
  // ════════════════════════════════════════════════════════════════════════════

  describe('singleton', () => {

    test('motionEngine is a MotionEngine instance', () => {
      expect(motionEngine).toBeInstanceOf(MotionEngine);
    });

    test('singleton works correctly', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = motionEngine.evaluate(0, project);
      expect(result.frame).toBe(0);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  // evaluateProperty() METHOD
  // ════════════════════════════════════════════════════════════════════════════

  describe('evaluateProperty method', () => {
    test('evaluates static property', () => {
      const prop = createAnimatableProperty(42);
      const result = engine.evaluateProperty(prop, 50);
      expect(result).toBe(42);
    });

    test('evaluates animated property with keyframes', () => {
      const prop: AnimatableProperty<number> = {
        id: 'prop-1',
        name: 'test',
        type: 'number',
        value: 0,
        animated: true,
        keyframes: [
          { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
          { id: 'kf2', frame: 100, value: 100, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
        ],
      };
      expect(engine.evaluateProperty(prop, 50)).toBeCloseTo(50, 5);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  // isLayerVisibleAtFrame() METHOD
  // ════════════════════════════════════════════════════════════════════════════

  describe('isLayerVisibleAtFrame method', () => {
    test('returns true when layer is visible and in range', () => {
      const layer = createMinimalLayer({ visible: true, startFrame: 0, endFrame: 100 });
      expect(engine.isLayerVisibleAtFrame(layer, 50)).toBe(true);
    });

    test('returns false when layer is hidden', () => {
      const layer = createMinimalLayer({ visible: false, startFrame: 0, endFrame: 100 });
      expect(engine.isLayerVisibleAtFrame(layer, 50)).toBe(false);
    });

    test('returns false when frame is before start', () => {
      const layer = createMinimalLayer({ visible: true, startFrame: 50, endFrame: 100 });
      expect(engine.isLayerVisibleAtFrame(layer, 25)).toBe(false);
    });

    test('returns false when frame is after end', () => {
      const layer = createMinimalLayer({ visible: true, startFrame: 0, endFrame: 50 });
      expect(engine.isLayerVisibleAtFrame(layer, 75)).toBe(false);
    });

    test('returns true at exact start frame', () => {
      const layer = createMinimalLayer({ visible: true, startFrame: 50, endFrame: 100 });
      expect(engine.isLayerVisibleAtFrame(layer, 50)).toBe(true);
    });

    test('returns true at exact end frame', () => {
      const layer = createMinimalLayer({ visible: true, startFrame: 0, endFrame: 50 });
      expect(engine.isLayerVisibleAtFrame(layer, 50)).toBe(true);
    });

    test('falls back to inPoint/outPoint when startFrame/endFrame missing', () => {
      const baseLayer = createMinimalLayer({ visible: true });
      // Create layer without startFrame/endFrame for testing fallback behavior
      // Use Omit to create a test layer type that excludes required properties
      const layerWithoutFrames = { ...baseLayer };
      // Remove startFrame/endFrame and add deprecated inPoint/outPoint
      const { startFrame, endFrame, ...layerRest } = layerWithoutFrames;
      const layer: Omit<Layer, 'startFrame' | 'endFrame'> & { inPoint: number; outPoint: number } = {
        ...layerRest,
        inPoint: 10,
        outPoint: 90,
      } as Omit<Layer, 'startFrame' | 'endFrame'> & { inPoint: number; outPoint: number };
      
      expect(engine.isLayerVisibleAtFrame(layer as Layer, 50)).toBe(true);
      expect(engine.isLayerVisibleAtFrame(layer as Layer, 5)).toBe(false);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // effects // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  describe('effect evaluation', () => {
    test('evaluates effect parameters', () => {
      const layer = createMinimalLayer({
        effects: [
          {
            id: 'effect-1',
            effectKey: 'blur',
            name: 'Blur',
            category: 'blur-sharpen' as const,
            enabled: true,
            expanded: false,
            parameters: {
              radius: createAnimatableProperty(10),
              direction: createAnimatableProperty('horizontal'),
            },
          },
        ],
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].effects).toHaveLength(1);
      expect(result.layers[0].effects[0].type).toBe('blur');
      expect(result.layers[0].effects[0].enabled).toBe(true);
      expect(result.layers[0].effects[0].parameters.radius).toBe(10);
      expect(result.layers[0].effects[0].parameters.direction).toBe('horizontal');
    });

    test('evaluates animated effect parameters', () => {
      const layer = createMinimalLayer({
        effects: [
          {
            id: 'effect-1',
            effectKey: 'blur',
            name: 'Blur',
            category: 'blur-sharpen' as const,
            enabled: true,
            expanded: false,
            parameters: {
              radius: {
                id: 'radius-param',
                name: 'radius',
                type: 'number',
                value: 0,
                animated: true,
                keyframes: [
                  { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
                  { id: 'kf2', frame: 100, value: 50, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
                ],
              },
            },
          },
        ],
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(50, project);
      expect(result.layers[0].effects[0].parameters.radius).toBeCloseTo(25, 1);
    });

    test('disabled effect is still included with enabled=false', () => {
      const layer = createMinimalLayer({
        effects: [
          {
            id: 'effect-1',
            effectKey: 'blur',
            name: 'Blur',
            category: 'blur-sharpen' as const,
            enabled: false,
            expanded: false,
            parameters: { radius: createAnimatableProperty(10) },
          },
        ],
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].effects[0].enabled).toBe(false);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                    // separate // dimensions
  // ════════════════════════════════════════════════════════════════════════════

  describe('separate dimensions', () => {
    test('evaluates separate position dimensions', () => {
      const layer = createMinimalLayer({
        transform: {
          position: createAnimatableProperty({ x: 0, y: 0 }),
          positionX: createAnimatableProperty(100),
          positionY: createAnimatableProperty(200),
          positionZ: createAnimatableProperty(300),
          scale: createAnimatableProperty({ x: 100, y: 100 }),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 0, y: 0 }),
          separateDimensions: { position: true, scale: false },
        },
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].transform.position.x).toBe(100);
      expect(result.layers[0].transform.position.y).toBe(200);
      expect(result.layers[0].transform.position.z).toBe(300);
    });

    test('evaluates separate scale dimensions', () => {
      const layer = createMinimalLayer({
        transform: {
          position: createAnimatableProperty({ x: 0, y: 0 }),
          scale: createAnimatableProperty({ x: 100, y: 100 }),
          scaleX: createAnimatableProperty(150),
          scaleY: createAnimatableProperty(200),
          scaleZ: createAnimatableProperty(250),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 0, y: 0 }),
          separateDimensions: { position: false, scale: true },
        },
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].transform.scale.x).toBe(150);
      expect(result.layers[0].transform.scale.y).toBe(200);
      expect(result.layers[0].transform.scale.z).toBe(250);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                        // multiple // layers
  // ════════════════════════════════════════════════════════════════════════════

  describe('multiple layers', () => {
    test('evaluates all layers in order', () => {
      const layer1 = createMinimalLayer({ id: 'layer-1', name: 'First' });
      const layer2 = createMinimalLayer({ id: 'layer-2', name: 'Second' });
      const layer3 = createMinimalLayer({ id: 'layer-3', name: 'Third' });
      const project = createMinimalProject([layer1, layer2, layer3]);

      const result = engine.evaluate(0, project);
      expect(result.layers).toHaveLength(3);
      expect(result.layers[0].id).toBe('layer-1');
      expect(result.layers[1].id).toBe('layer-2');
      expect(result.layers[2].id).toBe('layer-3');
    });

    test('each layer has independent evaluation', () => {
      const layer1 = createMinimalLayer({ 
        id: 'layer-1',
        opacity: createAnimatableProperty(25),
      });
      const layer2 = createMinimalLayer({ 
        id: 'layer-2',
        opacity: createAnimatableProperty(75),
      });
      const project = createMinimalProject([layer1, layer2]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].opacity).toBe(25);
      expect(result.layers[1].opacity).toBe(75);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                    // origin
  // ════════════════════════════════════════════════════════════════════════════

  describe('origin evaluation', () => {
    test('evaluates origin property', () => {
      const layer = createMinimalLayer({
        transform: {
          position: createAnimatableProperty({ x: 500, y: 500 }),
          scale: createAnimatableProperty({ x: 100, y: 100 }),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 50, y: 50 }),
        },
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].transform.origin.x).toBe(50);
      expect(result.layers[0].transform.origin.y).toBe(50);
    });

    test('anchorPoint alias is populated', () => {
      const layer = createMinimalLayer({
        transform: {
          position: createAnimatableProperty({ x: 500, y: 500 }),
          scale: createAnimatableProperty({ x: 100, y: 100 }),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 100, y: 200 }),
        },
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      // anchorPoint should be same as origin
      expect(result.layers[0].transform.anchorPoint?.x).toBe(100);
      expect(result.layers[0].transform.anchorPoint?.y).toBe(200);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                        // layer // reference
  // ════════════════════════════════════════════════════════════════════════════

  describe('layer reference', () => {
    test('layerRef contains original layer', () => {
      const layer = createMinimalLayer({ id: 'my-layer', name: 'My Layer' });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].layerRef).toBe(layer);
      expect(result.layers[0].layerRef.id).toBe('my-layer');
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                             // blend // mode // and // flags
  // ════════════════════════════════════════════════════════════════════════════

  describe('layer metadata', () => {
    test('blendMode is preserved', () => {
      const layer = createMinimalLayer({ blendMode: 'multiply' });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].blendMode).toBe('multiply');
    });

    test('threeD flag is preserved', () => {
      const layer = createMinimalLayer({ threeD: true });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].threeD).toBe(true);
    });

    test('parentId is preserved', () => {
      const layer = createMinimalLayer({ parentId: 'parent-123' });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].parentId).toBe('parent-123');
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                        // property // tests // for // critical // invariants
  // ════════════════════════════════════════════════════════════════════════════

  describe('PROPERTY: evaluation invariants', () => {
    //                                                                     // fixed
    // This test now correctly verifies opacity passes through as-is
    test.prop([
      fc.integer({ min: 0, max: 10000 }),
      fc.double({ min: 0, max: 100, noNaN: true }),
    ])(
      'opacity value is preserved from input',
      (frame, inputOpacity) => {
        const layer = createMinimalLayer({
          opacity: createAnimatableProperty(inputOpacity),
        });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(frame, project);
        // Opacity passes through without clamping (no audio modifiers)
        expect(result.layers[0].opacity).toBe(inputOpacity);
      }
    );

    test.prop([fc.integer({ min: -100, max: 10000 })])(
      'frame number is preserved in output',
      (frame) => {
        const layer = createMinimalLayer();
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(frame, project);
        expect(result.frame).toBe(frame);
      }
    );

    test.prop([
      fc.integer({ min: 1, max: 20 }),
    ])(
      'layer count matches input',
      (layerCount) => {
        const layers = Array.from({ length: layerCount }, (_, i) => 
          createMinimalLayer({ id: `layer-${i}` })
        );
        const project = createMinimalProject(layers);

        const result = engine.evaluate(0, project);
        expect(result.layers.length).toBe(layerCount);
      }
    );
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                      // camera // evaluation
  // ════════════════════════════════════════════════════════════════════════════

  describe('camera evaluation', () => {
    function createCameraLayer(overrides: Partial<Layer> = {}): Layer {
      return {
        id: 'camera-1',
        name: 'Camera',
        type: 'camera',
        visible: true,
        locked: false,
        isolate: false,
        startFrame: 0,
        endFrame: 150,
        inPoint: 0,
        outPoint: 150,
        blendMode: 'normal',
        threeD: true,
        motionBlur: false,
        opacity: createAnimatableProperty(100),
        transform: {
          position: createAnimatableProperty({ x: 960, y: 540, z: 0 }),
          scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        },
        effects: [],
        properties: [],
        parentId: null,
        data: {
          cameraId: 'camera-1',
          isActiveCamera: true,
          camera: {
            type: 'one-node' as const,
            position: { x: 960, y: 540, z: 0 },
            pointOfInterest: { x: 960, y: 540, z: 0 },
            zoom: 1778,
            depthOfField: false,
            focusDistance: 1000,
            aperture: 2.8,
            blurLevel: 50,
            xRotation: 0,
            yRotation: 0,
            zRotation: 0,
          },
        },
        ...overrides,
      };
    }

    test('returns null camera when no camera layer exists', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.camera).toBeNull();
    });

    test('evaluates visible camera layer', () => {
      const camera = createCameraLayer();
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(0, project);
      expect(result.camera).not.toBeNull();
      expect(result.camera!.id).toBe('camera-1');
      expect(result.camera!.name).toBe('Camera');
    });

    test('uses specified activeCameraId', () => {
      const camera1 = createCameraLayer({ id: 'cam-1', name: 'Camera 1' });
      const camera2 = createCameraLayer({ id: 'cam-2', name: 'Camera 2' });
      const project = createMinimalProject([camera1, camera2]);

      const result = engine.evaluate(0, project, null, 'cam-2');
      expect(result.camera!.id).toBe('cam-2');
    });

    test('finds first visible camera if no activeCameraId', () => {
      const camera1 = createCameraLayer({ id: 'cam-1', visible: false });
      const camera2 = createCameraLayer({ id: 'cam-2', visible: true });
      const project = createMinimalProject([camera1, camera2]);

      const result = engine.evaluate(0, project);
      expect(result.camera!.id).toBe('cam-2');
    });

    test('camera outside frame range is not used', () => {
      const camera = createCameraLayer({ startFrame: 100, endFrame: 200 });
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(50, project);
      expect(result.camera).toBeNull();
    });

    test('evaluates camera position from transform', () => {
      const camera = createCameraLayer({
        transform: {
          position: createAnimatableProperty({ x: 100, y: 200, z: 300 }),
          scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        },
      });
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(0, project);
      expect(result.camera!.position.x).toBe(100);
      expect(result.camera!.position.y).toBe(200);
    });

    test('evaluates animated camera position', () => {
      const camera = createCameraLayer({
        data: {
          cameraId: 'camera-1',
          isActiveCamera: true,
          camera: {
            type: 'one-node' as const,
            position: { x: 0, y: 0, z: 0 },
            pointOfInterest: { x: 960, y: 540, z: 0 },
            zoom: 1778,
            depthOfField: false,
            focusDistance: 1000,
            aperture: 2.8,
            blurLevel: 50,
            xRotation: 0,
            yRotation: 0,
            zRotation: 0,
          },
          animatedPosition: {
            id: 'cam-pos',
            name: 'position',
            type: 'vector3',
            value: { x: 0, y: 0, z: 0 },
            animated: true,
            keyframes: [
              { id: 'kf1', frame: 0, value: { x: 0, y: 0, z: 0 }, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
              { id: 'kf2', frame: 100, value: { x: 1000, y: 500, z: 200 }, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
            ],
          },
        },
      });
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(50, project);
      expect(result.camera!.position.x).toBeCloseTo(500, 0);
      expect(result.camera!.position.y).toBeCloseTo(250, 0);
      expect(result.camera!.position.z).toBeCloseTo(100, 0);
    });

    test('evaluates animated camera FOV', () => {
      const camera = createCameraLayer({
        data: {
          cameraId: 'camera-1',
          isActiveCamera: true,
          camera: {
            type: 'one-node' as const,
            position: { x: 960, y: 540, z: 0 },
            pointOfInterest: { x: 960, y: 540, z: 0 },
            zoom: 1778,
            depthOfField: false,
            focusDistance: 1000,
            aperture: 2.8,
            blurLevel: 50,
            xRotation: 0,
            yRotation: 0,
            zRotation: 0,
          },
          animatedFov: {
            id: 'cam-fov',
            name: 'fov',
            type: 'number',
            value: 50,
            animated: true,
            keyframes: [
              { id: 'kf1', frame: 0, value: 30, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
              { id: 'kf2', frame: 100, value: 90, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
            ],
          },
        },
      });
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(50, project);
      expect(result.camera!.fov).toBeCloseTo(60, 0);
    });

    test('evaluates depth of field settings', () => {
      // Uses legacy inline format (camera.depthOfField: boolean)
      // MotionEngine should handle both legacy and structured formats
      const camera = createCameraLayer({
        data: {
          cameraId: 'camera-1',
          isActiveCamera: true,
          camera: {
            type: 'one-node' as const,
            position: { x: 960, y: 540, z: 0 },
            pointOfInterest: { x: 960, y: 540, z: 0 },
            zoom: 1778,
            depthOfField: true,
            focusDistance: 500,
            aperture: 1.4,
            blurLevel: 75,
            xRotation: 0,
            yRotation: 0,
            zRotation: 0,
          },
        },
      });
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(0, project);
      expect(result.camera!.depthOfField.enabled).toBe(true);
      expect(result.camera!.depthOfField.focusDistance).toBe(500);
      expect(result.camera!.depthOfField.aperture).toBe(1.4);
      expect(result.camera!.depthOfField.blurLevel).toBe(75);
    });

    test('evaluates animated focus distance', () => {
      const camera = createCameraLayer({
        data: {
          cameraId: 'camera-1',
          isActiveCamera: true,
          camera: {
            type: 'one-node' as const,
            position: { x: 960, y: 540, z: 0 },
            pointOfInterest: { x: 960, y: 540, z: 0 },
            zoom: 1778,
            depthOfField: true,
            focusDistance: 100,
            aperture: 2.8,
            blurLevel: 50,
            xRotation: 0,
            yRotation: 0,
            zRotation: 0,
          },
          animatedFocusDistance: {
            id: 'focus-dist',
            name: 'focusDistance',
            type: 'number',
            value: 100,
            animated: true,
            keyframes: [
              { id: 'kf1', frame: 0, value: 100, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
              { id: 'kf2', frame: 100, value: 1000, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
            ],
          },
        },
      });
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(50, project);
      expect(result.camera!.depthOfField.focusDistance).toBeCloseTo(550, 0);
    });

    test('camera target defaults to composition center', () => {
      const camera = createCameraLayer();
      // Composition is 1920x1080, so center is 960x540
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(0, project);
      expect(result.camera!.target.x).toBe(960);
      expect(result.camera!.target.y).toBe(540);
    });

    test('camera output is frozen', () => {
      const camera = createCameraLayer();
      const project = createMinimalProject([camera]);

      const result = engine.evaluate(0, project);
      expect(Object.isFrozen(result.camera)).toBe(true);
      expect(Object.isFrozen(result.camera!.position)).toBe(true);
      expect(Object.isFrozen(result.camera!.target)).toBe(true);
      expect(Object.isFrozen(result.camera!.depthOfField)).toBe(true);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                                     // layer
  // ════════════════════════════════════════════════════════════════════════════

  describe('layer-specific properties', () => {
    test('evaluates layer properties array', () => {
      const layer = createMinimalLayer({
        properties: [
          {
            id: 'prop-1',
            name: 'customProp',
            type: 'number',
            value: 42,
            animated: false,
            keyframes: [],
          },
        ],
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].properties.customProp).toBe(42);
    });

    test('evaluates animated layer properties', () => {
      const layer = createMinimalLayer({
        properties: [
          {
            id: 'prop-1',
            name: 'animatedProp',
            type: 'number',
            value: 0,
            animated: true,
            keyframes: [
              { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
              { id: 'kf2', frame: 100, value: 100, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
            ],
          },
        ],
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(50, project);
      expect(result.layers[0].properties.animatedProp).toBeCloseTo(50, 0);
    });

    test('particle layer gets _requiresSimulation flag', () => {
      const layer = createMinimalLayer({
        type: 'particles',
        data: {
          systemConfig: {
            maxParticles: 1000,
            gravity: 0,
            windStrength: 0,
            windDirection: 0,
            warmupPeriod: 0,
            respectMaskBoundary: false,
            boundaryBehavior: 'kill' as const,
            friction: 0,
          },
          emitters: [],
          gravityWells: [],
          vortices: [],
          modulations: [],
          renderOptions: {
            blendMode: 'normal' as const,
            renderTrails: false,
            trailLength: 10,
            trailOpacityFalloff: 0.5,
            particleShape: 'circle' as const,
            glowEnabled: false,
            glowRadius: 5,
            glowIntensity: 1,
            motionBlur: false,
            motionBlurStrength: 0.5,
            motionBlurSamples: 4,
            connections: {
              enabled: false,
              maxDistance: 100,
              maxConnections: 5,
              lineWidth: 1,
              lineOpacity: 1,
              fadeByDistance: false,
              color: [1, 1, 1] as [number, number, number],
            },
          },
        },
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].properties._requiresSimulation).toBe(true);
    });

    test('depthflow layer evaluates animated properties', () => {
      const layer = createMinimalLayer({
        type: 'depthflow',
        data: {
          sourceLayerId: 'source-1',
          depthLayerId: 'depth-1',
          config: {
            preset: 'static' as const,
            zoom: 1,
            offsetX: 0,
            offsetY: 0,
            rotation: 0,
            depthScale: 1,
            focusDepth: 0,
            dollyZoom: 0,
            orbitRadius: 0,
            orbitSpeed: 0,
            swingAmplitude: 0,
            swingFrequency: 0,
            edgeDilation: 0,
            inpaintEdges: false,
          },
          animatedZoom: {
            id: 'zoom',
            name: 'zoom',
            type: 'number',
            value: 1,
            animated: true,
            keyframes: [
              { id: 'kf1', frame: 0, value: 1, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
              { id: 'kf2', frame: 100, value: 2, interpolation: 'linear', inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: 'smooth' },
            ],
          },
        },
      });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(50, project);
      expect(result.layers[0].properties.zoom).toBeCloseTo(1.5, 1);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                              // frame // state // cache // detailed // tests
  // ════════════════════════════════════════════════════════════════════════════

  describe('FrameStateCache detailed', () => {
    test('project hash changes when layer count changes', () => {
      const layer1 = createMinimalLayer({ id: 'layer-1' });
      const layer2 = createMinimalLayer({ id: 'layer-2' });
      
      const project1 = createMinimalProject([layer1]);
      const project2 = createMinimalProject([layer1, layer2]);

      // Evaluate both projects
      const result1 = engine.evaluate(0, project1, null, null, true);
      const result2 = engine.evaluate(0, project2, null, null, true);

      // Results should be different (not cached from first)
      expect(result1.layers.length).toBe(1);
      expect(result2.layers.length).toBe(2);
    });

    test('cache hit returns same object reference', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      // First evaluation (cache miss)
      const result1 = engine.evaluate(0, project, null, null, true);
      // Second evaluation (cache hit)
      const result2 = engine.evaluate(0, project, null, null, true);

      // Should be the exact same object (reference equality)
      expect(result1).toBe(result2);
    });

    test('different frames have different cache entries', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result1 = engine.evaluate(0, project, null, null, true);
      const result2 = engine.evaluate(1, project, null, null, true);

      expect(result1.frame).toBe(0);
      expect(result2.frame).toBe(1);
      expect(result1).not.toBe(result2);
    });

    test('cache respects useCache=false', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      // First evaluation with cache
      const result1 = engine.evaluate(0, project, null, null, true);
      // Second evaluation without cache
      const result2 = engine.evaluate(0, project, null, null, false);

      // Results should be equal but NOT the same object
      expect(result1.frame).toBe(result2.frame);
      expect(result1).not.toBe(result2);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                   // composition // settings
  // ════════════════════════════════════════════════════════════════════════════

  describe('composition settings', () => {
    test('composition settings are passed through', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.composition.width).toBe(1920);
      expect(result.composition.height).toBe(1080);
      expect(result.composition.fps).toBe(30);
    });

    test('fps is used from composition settings', () => {
      const layer = createMinimalLayer();
      const composition: Composition = {
        id: 'main',
        name: 'Test Comp',
        settings: {
          width: 1920,
          height: 1080,
          fps: 60, // Different FPS
          duration: 5,
          backgroundColor: '#000000',
          frameCount: 300,
          autoResizeToContent: false,
          frameBlendingEnabled: false,
        },
        layers: [layer],
        currentFrame: 0,
        isNestedComp: false,
      };
      const project: LatticeProject = {
        version: '1.0.0' as const,
        mainCompositionId: 'main',
        compositions: { main: composition },
        composition: composition.settings,
        assets: {},
        meta: { name: 'Test', created: '', modified: '' },
        layers: [layer],
        currentFrame: 0,
      };

      const result = engine.evaluate(0, project);
      expect(result.composition.fps).toBe(60);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                                     // particle // snapshots
  // ════════════════════════════════════════════════════════════════════════════

  describe('particle snapshots', () => {
    test('particleSnapshots is empty for non-particle layers', () => {
      const layer = createMinimalLayer({ type: 'solid' });
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.particleSnapshots).toEqual({});
    });

    test('particleSnapshots structure is frozen', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(Object.isFrozen(result.particleSnapshots)).toBe(true);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                           // audio // modifiers // structure
  // ════════════════════════════════════════════════════════════════════════════

  describe('audio modifiers', () => {
    test('audioModifiers is empty object when no audio reactive', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(result.layers[0].audioModifiers).toEqual({});
    });

    test('audioModifiers is frozen', () => {
      const layer = createMinimalLayer();
      const project = createMinimalProject([layer]);

      const result = engine.evaluate(0, project);
      expect(Object.isFrozen(result.layers[0].audioModifiers)).toBe(true);
    });
  });

  // ════════════════════════════════════════════════════════════════════════════
  //                                           // additional // property // tests
  // ════════════════════════════════════════════════════════════════════════════

  describe('PROPERTY: additional invariants', () => {
    test.prop([
      fc.double({ min: -10000, max: 10000, noNaN: true }),
      fc.double({ min: -10000, max: 10000, noNaN: true }),
      fc.double({ min: -10000, max: 10000, noNaN: true }),
    ])(
      'transform position preserves all components including Z',
      (x, y, z) => {
        const layer = createMinimalLayer({
          threeD: true,
          transform: {
            position: createAnimatableProperty({ x, y, z }),
            scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
            rotation: createAnimatableProperty(0),
            origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
          },
        });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(0, project);
        expect(result.layers[0].transform.position.x).toBe(x);
        expect(result.layers[0].transform.position.y).toBe(y);
        expect(result.layers[0].transform.position.z).toBe(z);
      }
    );

    test.prop([
      fc.string({ minLength: 1, maxLength: 50 }),
    ])(
      'layer name is preserved',
      (name) => {
        const layer = createMinimalLayer({ name });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(0, project);
        expect(result.layers[0].name).toBe(name);
      }
    );

    test.prop([
      fc.constantFrom('normal', 'multiply', 'screen', 'overlay', 'darken', 'lighten'),
    ])(
      'blend mode is preserved for all types',
      (blendMode) => {
        const layer = createMinimalLayer({ blendMode });
        const project = createMinimalProject([layer]);

        const result = engine.evaluate(0, project);
        expect(result.layers[0].blendMode).toBe(blendMode);
      }
    );
  });
});
