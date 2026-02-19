/**
 * REGRESSION TEST: Dimension Separation Export Bug
 *
 * @fixed 2026-01-10
 * @file services/layerEvaluationCache.ts
 * @rootCause The evaluateTransform function in layerEvaluationCache.ts did NOT handle
 *            separated dimensions (positionX/Y/Z and scaleX/Y/Z). It always read from
 *            transform.position and transform.scale directly, ignoring the
 *            separateDimensions flag and individual dimension properties.
 * @fix Added separateDimensions checks to evaluateTransform to match MotionEngine.ts behavior.
 * @counterexample Layers with separated dimensions would export using only the combined
 *                 position/scale property values, ignoring keyframes on individual X/Y/Z
 *                 dimension properties.
 * @impact CRITICAL - Export pipeline would produce incorrect animation data for layers
 *         using separated dimension keyframes. This affects WanMove, camera tracking,
 *         and all other exports that rely on evaluateLayerCached.
 */

import { describe, test, expect, beforeEach } from 'vitest';
import { evaluateLayerCached, clearEvaluationCache } from '@/services/layerEvaluationCache';
import { separatePositionDimensions, separateScaleDimensions } from '@/types/transform';
import type { Layer, Keyframe } from '@/types/project';

// Track layer ID to ensure unique IDs across tests
let testLayerCounter = 0;

function createKeyframe<T>(frame: number, value: T): Keyframe<T> {
  return {
    id: `kf-${frame}-${Math.random().toString(36).slice(2, 9)}`,
    frame,
    value,
    interpolation: 'linear',
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: 'smooth',
  };
}

function createTestLayer(): Layer {
  testLayerCounter++;
  const origin = {
    id: 'origin',
    name: 'Origin',
    type: 'vector3' as const,
    value: { x: 0, y: 0, z: 0 },
    animated: false,
    keyframes: [],
  };
  return {
    id: `test-layer-${testLayerCounter}-${Date.now()}`,
    name: 'Test Layer',
    type: 'solid',
    visible: true,
    locked: false,
    isolate: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: 100,
    parentId: null,
    threeD: false,
    blendMode: 'normal',
    transform: {
      position: {
        id: 'position',
        name: 'Position',
        type: 'vector3',
        value: { x: 0, y: 0, z: 0 },
        animated: false,
        keyframes: [],
      },
      scale: {
        id: 'scale',
        name: 'Scale',
        type: 'vector3',
        value: { x: 100, y: 100, z: 100 },
        animated: false,
        keyframes: [],
      },
      rotation: {
        id: 'rotation',
        name: 'Rotation',
        type: 'number',
        value: 0,
        animated: false,
        keyframes: [],
      },
      origin,
      anchorPoint: origin,
    },
    opacity: {
      id: 'opacity',
      name: 'Opacity',
      type: 'number',
      value: 100,
      animated: false,
      keyframes: [],
    },
    effects: [],
    properties: [],
    masks: [],
    data: { color: '#000000', width: 100, height: 100 },
  } as Layer;
}

describe('Dimension Separation Export Regression', () => {
  // Clear cache before each test to avoid cross-test pollution
  beforeEach(() => {
    clearEvaluationCache();
  });

  describe('Position separation in exports', () => {
    /**
     * Original bug: When position was separated, evaluateLayerCached would
     * read from transform.position instead of positionX/Y/Z, producing
     * incorrect export data.
     */
    test('evaluateLayerCached uses separated positionX/Y/Z when enabled', () => {
      const layer = createTestLayer();

      // Set up separated dimensions with keyframes that differ from combined position
      separatePositionDimensions(layer.transform);

      // Add keyframes to separated dimensions
      layer.transform.positionX!.animated = true;
      layer.transform.positionX!.keyframes = [
        createKeyframe(0, 0),
        createKeyframe(30, 100), // X moves to 100 at frame 30
      ];

      layer.transform.positionY!.animated = true;
      layer.transform.positionY!.keyframes = [
        createKeyframe(0, 0),
        createKeyframe(30, 200), // Y moves to 200 at frame 30
      ];

      // Combined position has different values (this should be IGNORED)
      layer.transform.position.keyframes = [
        createKeyframe(0, { x: 999, y: 999, z: 0 }), // Wrong values
        createKeyframe(30, { x: 999, y: 999, z: 0 }),
      ];

      // Evaluate at frame 15 (midpoint)
      const evaluated = evaluateLayerCached(layer, 15, 30);

      // Should use separated dimensions (interpolated 50% between keyframes)
      //                                                                       // not
      expect(evaluated.transform.position.x).toBeCloseTo(50, 1);
      expect(evaluated.transform.position.y).toBeCloseTo(100, 1);
    });

    test('evaluateLayerCached falls back to combined position when not separated', () => {
      const layer = createTestLayer();

      //                                                                       // not
      layer.transform.position.animated = true;
      layer.transform.position.keyframes = [
        createKeyframe(0, { x: 0, y: 0, z: 0 }),
        createKeyframe(30, { x: 100, y: 200, z: 0 }),
      ];

      // Evaluate at frame 15
      const evaluated = evaluateLayerCached(layer, 15, 30);

      // Should use combined position values
      expect(evaluated.transform.position.x).toBeCloseTo(50, 1);
      expect(evaluated.transform.position.y).toBeCloseTo(100, 1);
    });
  });

  describe('Scale separation in exports', () => {
    /**
     * Same bug pattern for scale - separated scaleX/Y/Z were ignored.
     */
    test('evaluateLayerCached uses separated scaleX/Y/Z when enabled', () => {
      const layer = createTestLayer();

      // Set up separated scale dimensions
      separateScaleDimensions(layer.transform);

      // Add keyframes to separated dimensions
      layer.transform.scaleX!.animated = true;
      layer.transform.scaleX!.keyframes = [
        createKeyframe(0, 100),
        createKeyframe(30, 200), // X scale to 200% at frame 30
      ];

      layer.transform.scaleY!.animated = true;
      layer.transform.scaleY!.keyframes = [
        createKeyframe(0, 100),
        createKeyframe(30, 50), // Y scale to 50% at frame 30
      ];

      // Combined scale has wrong values (should be IGNORED)
      layer.transform.scale.keyframes = [
        createKeyframe(0, { x: 999, y: 999, z: 100 }),
        createKeyframe(30, { x: 999, y: 999, z: 100 }),
      ];

      // Evaluate at frame 15 (midpoint)
      const evaluated = evaluateLayerCached(layer, 15, 30);

      // Should use separated dimensions
      expect(evaluated.transform.scale.x).toBeCloseTo(150, 1); // 100 + (200-100)*0.5
      expect(evaluated.transform.scale.y).toBeCloseTo(75, 1); // 100 + (50-100)*0.5
    });

    test('evaluateLayerCached falls back to combined scale when not separated', () => {
      const layer = createTestLayer();

      //                                                                       // not
      layer.transform.scale.animated = true;
      layer.transform.scale.keyframes = [
        createKeyframe(0, { x: 100, y: 100, z: 100 }),
        createKeyframe(30, { x: 200, y: 50, z: 100 }),
      ];

      // Evaluate at frame 15
      const evaluated = evaluateLayerCached(layer, 15, 30);

      // Should use combined scale values
      expect(evaluated.transform.scale.x).toBeCloseTo(150, 1);
      expect(evaluated.transform.scale.y).toBeCloseTo(75, 1);
    });
  });

  describe('Export pipeline consistency', () => {
    /**
     * Ensure separation handling is consistent across frames
     */
    test('separated dimensions produce consistent interpolation across frames', () => {
      const layer = createTestLayer();
      separatePositionDimensions(layer.transform);

      // Linear motion from (0, 0) to (300, 600)
      layer.transform.positionX!.animated = true;
      layer.transform.positionX!.keyframes = [
        createKeyframe(0, 0),
        createKeyframe(30, 300),
      ];

      layer.transform.positionY!.animated = true;
      layer.transform.positionY!.keyframes = [
        createKeyframe(0, 0),
        createKeyframe(30, 600),
      ];

      // Test multiple frames
      const results = [0, 10, 20, 30].map((frame) => {
        const evaluated = evaluateLayerCached(layer, frame, 30);
        return { frame, x: evaluated.transform.position.x, y: evaluated.transform.position.y };
      });

      // Frame 0: (0, 0)
      expect(results[0].x).toBeCloseTo(0, 1);
      expect(results[0].y).toBeCloseTo(0, 1);

      // Frame 10: (100, 200) - 1/3 of the way
      expect(results[1].x).toBeCloseTo(100, 1);
      expect(results[1].y).toBeCloseTo(200, 1);

      // Frame 20: (200, 400) - 2/3 of the way
      expect(results[2].x).toBeCloseTo(200, 1);
      expect(results[2].y).toBeCloseTo(400, 1);

      // Frame 30: (300, 600)
      expect(results[3].x).toBeCloseTo(300, 1);
      expect(results[3].y).toBeCloseTo(600, 1);
    });
  });
});
