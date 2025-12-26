/**
 * Tutorial 05: Motion Paths & Graph Editor Mastery
 *
 * Comprehensive tests for all features implemented in Tutorial 05:
 * - Phase A: Keyframe Velocity, Convert Expression to Keyframes
 * - Phase B: Auto Bezier Tangents, Break Handles (Ctrl+drag), Keyframe Icons
 * - Phase C: Motion Sketch Panel, Smoother Panel
 * - Phase D: True Separate Dimensions
 * - Phase E: Sequence Layers, Exponential Scale
 */

import { describe, test, expect, beforeEach, vi } from 'vitest';
import { setActivePinia, createPinia } from 'pinia';
import { useCompositorStore } from '../../stores/compositorStore';
import type { Keyframe, VelocitySettings } from '../../types/animation';
import {
  separatePositionDimensions,
  linkPositionDimensions,
  separateScaleDimensions,
  linkScaleDimensions,
  createDefaultTransform
} from '../../types/transform';

describe('Tutorial 05: Motion Paths & Graph Editor Mastery', () => {
  let store: ReturnType<typeof useCompositorStore>;

  beforeEach(() => {
    const pinia = createPinia();
    setActivePinia(pinia);
    store = useCompositorStore();
    // Create a composition for testing
    store.createComposition('Test Comp', {
      width: 1920,
      height: 1080,
      fps: 30,
      frameCount: 90,
      duration: 3
    });
  });

  // ============================================================================
  // PHASE A: KEYFRAME VELOCITY
  // ============================================================================

  describe('Phase A: Keyframe Velocity', () => {
    test('applyKeyframeVelocity converts velocity to bezier handles', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'transform.position', { x: 0, y: 0 }, 0);
      store.addKeyframe(layer.id, 'transform.position', { x: 100, y: 100 }, 30);

      const keyframes = layer.transform.position.keyframes;
      expect(keyframes.length).toBe(2);

      const settings: VelocitySettings = {
        incomingVelocity: 50,
        outgoingVelocity: 75,
        incomingInfluence: 25,
        outgoingInfluence: 40
      };

      const result = store.applyKeyframeVelocity(
        layer.id,
        'transform.position',
        keyframes[0].id,
        settings
      );

      expect(result).toBe(true);
      // Velocity gets converted to handle values - handles should be enabled
      expect(keyframes[0].outHandle.enabled).toBe(true);
      // With 40% outgoingInfluence over 30 frames, handle frame should be ~12
      expect(keyframes[0].outHandle.frame).toBeCloseTo(12, 0);
    });

    test('getKeyframeVelocity returns velocity derived from handles', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'transform.position', { x: 0, y: 0 }, 0);
      store.addKeyframe(layer.id, 'transform.position', { x: 100, y: 100 }, 30);

      const keyframes = layer.transform.position.keyframes;

      // Apply velocity settings which get converted to handles
      store.applyKeyframeVelocity(layer.id, 'transform.position', keyframes[0].id, {
        incomingVelocity: 50,
        outgoingVelocity: 100,
        incomingInfluence: 33,
        outgoingInfluence: 50
      });

      // getKeyframeVelocity should derive velocity back from handles
      const velocity = store.getKeyframeVelocity(
        layer.id,
        'transform.position',
        keyframes[0].id
      );

      // The returned values should roughly match what we set
      // (might not be exact due to handle-to-velocity conversion)
      expect(velocity.outgoingInfluence).toBeCloseTo(50, 0);
    });

    test('velocity settings modify keyframe handle values proportionally', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'opacity', 0, 0);
      store.addKeyframe(layer.id, 'opacity', 100, 30);

      const keyframes = layer.opacity.keyframes;

      const settings: VelocitySettings = {
        incomingVelocity: 100,
        outgoingVelocity: 100,
        incomingInfluence: 50,
        outgoingInfluence: 50
      };

      store.applyKeyframeVelocity(layer.id, 'opacity', keyframes[0].id, settings);

      // Handle should be enabled and have non-zero influence
      expect(keyframes[0].outHandle.enabled).toBe(true);
      // With 50% influence over 30 frames, handle should extend ~15 frames
      expect(keyframes[0].outHandle.frame).toBeCloseTo(15, 0);
      // Handle value reflects velocity: 100 units/sec / 30fps * 15 frames ≈ 50
      expect(keyframes[0].outHandle.value).toBeCloseTo(50, 0);
    });
  });

  // ============================================================================
  // PHASE A: CONVERT EXPRESSION TO KEYFRAMES
  // ============================================================================

  describe('Phase A: Convert Expression to Keyframes', () => {
    test('canBakeExpression returns false when no expression', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      const canBake = store.canBakeExpression(layer.id, 'transform.position');
      expect(canBake).toBe(false);
    });

    test('convertExpressionToKeyframes requires enabled expression', () => {
      const layer = store.createLayer('solid', 'Test Layer');

      // Without an expression, should return 0
      const count = store.convertExpressionToKeyframes(layer.id, 'transform.position');
      expect(count).toBe(0);
    });
  });

  // ============================================================================
  // PHASE B: AUTO BEZIER TANGENT CALCULATION
  // ============================================================================

  describe('Phase B: Auto Bezier Tangent Calculation', () => {
    test('autoCalculateBezierTangents calculates tangents for single keyframe', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'opacity', 0, 0);
      store.addKeyframe(layer.id, 'opacity', 50, 15);
      store.addKeyframe(layer.id, 'opacity', 100, 30);

      const keyframes = layer.opacity.keyframes;
      const result = store.autoCalculateBezierTangents(
        layer.id,
        'opacity',
        keyframes[1].id
      );

      expect(result).toBe(true);
      expect(keyframes[1].interpolation).toBe('bezier');
      expect(keyframes[1].controlMode).toBe('smooth');
    });

    test('autoCalculateAllBezierTangents calculates tangents for all keyframes', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'opacity', 0, 0);
      store.addKeyframe(layer.id, 'opacity', 50, 15);
      store.addKeyframe(layer.id, 'opacity', 75, 22);
      store.addKeyframe(layer.id, 'opacity', 100, 30);

      const count = store.autoCalculateAllBezierTangents(layer.id, 'opacity');

      expect(count).toBe(4);

      layer.opacity.keyframes.forEach(kf => {
        expect(kf.interpolation).toBe('bezier');
        expect(kf.inHandle.enabled).toBe(true);
        expect(kf.outHandle.enabled).toBe(true);
      });
    });

    test('autoCalculateBezierTangents respects keyframe values', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      // Opacity goes from 0 to 100 over 30 frames
      // Slope = (100 - 0) / (30 - 0) = 3.33 per frame
      store.addKeyframe(layer.id, 'opacity', 0, 0);
      store.addKeyframe(layer.id, 'opacity', 100, 30);

      const result = store.autoCalculateAllBezierTangents(layer.id, 'opacity');
      expect(result).toBe(2);

      const keyframes = layer.opacity.keyframes;

      // First keyframe outHandle: slope * defaultHandleLength (typically 1/3 of frame span = 10)
      // Expected outHandle.value ≈ 3.33 * 10 = 33.3
      expect(keyframes[0].outHandle.value).toBeCloseTo(33.3, 0);
      expect(keyframes[0].outHandle.frame).toBeCloseTo(10, 0);

      // Last keyframe inHandle: should mirror the approach slope
      // inHandle.value should be negative (coming from below)
      expect(keyframes[1].inHandle.value).toBeCloseTo(-33.3, 0);
      expect(keyframes[1].inHandle.frame).toBeCloseTo(-10, 0);
    });
  });

  // ============================================================================
  // PHASE B: HANDLE CONTROL MODE
  // ============================================================================

  describe('Phase B: Handle Control Mode (Break Handles)', () => {
    test('setKeyframeHandleWithMode without break maintains smooth mode', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'opacity', 50, 15);

      const keyframes = layer.opacity.keyframes;
      const kfId = keyframes[0].id;

      store.setKeyframeHandleWithMode(
        layer.id,
        'opacity',
        kfId,
        'out',
        { frame: 5, value: 10, enabled: true },
        false // Don't break
      );

      expect(keyframes[0].controlMode).toBe('smooth');
    });

    test('setKeyframeHandleWithMode with break sets corner mode', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'opacity', 50, 15);

      const keyframes = layer.opacity.keyframes;
      const kfId = keyframes[0].id;

      store.setKeyframeHandleWithMode(
        layer.id,
        'opacity',
        kfId,
        'out',
        { frame: 5, value: 10, enabled: true },
        true // Break handle
      );

      expect(keyframes[0].controlMode).toBe('corner');
    });

    test('setKeyframeControlMode changes control mode', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'opacity', 50, 15);

      const keyframes = layer.opacity.keyframes;

      store.setKeyframeControlMode(layer.id, 'opacity', keyframes[0].id, 'symmetric');
      expect(keyframes[0].controlMode).toBe('symmetric');

      store.setKeyframeControlMode(layer.id, 'opacity', keyframes[0].id, 'corner');
      expect(keyframes[0].controlMode).toBe('corner');

      store.setKeyframeControlMode(layer.id, 'opacity', keyframes[0].id, 'smooth');
      expect(keyframes[0].controlMode).toBe('smooth');
    });
  });

  // ============================================================================
  // PHASE D: TRUE SEPARATE DIMENSIONS
  // ============================================================================

  describe('Phase D: True Separate Dimensions', () => {
    test('separatePositionDimensions creates X, Y, Z properties with correct values', () => {
      const transform = createDefaultTransform();
      transform.position.value = { x: 100, y: 200, z: 50 };

      separatePositionDimensions(transform);

      expect(transform.separateDimensions?.position).toBe(true);
      // Verify the separate properties have the correct values
      expect(transform.positionX!.value).toBe(100);
      expect(transform.positionX!.name).toBe('Position X');
      expect(transform.positionY!.value).toBe(200);
      expect(transform.positionY!.name).toBe('Position Y');
      expect(transform.positionZ!.value).toBe(50);
      expect(transform.positionZ!.name).toBe('Position Z');
    });

    test('separatePositionDimensions copies keyframes to each dimension', () => {
      const transform = createDefaultTransform();
      transform.position.animated = true;
      transform.position.keyframes = [
        {
          id: 'kf1',
          frame: 0,
          value: { x: 0, y: 0, z: 0 },
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: 'smooth'
        },
        {
          id: 'kf2',
          frame: 30,
          value: { x: 100, y: 200, z: 50 },
          interpolation: 'bezier',
          inHandle: { frame: -5, value: 0, enabled: true },
          outHandle: { frame: 5, value: 0, enabled: true },
          controlMode: 'smooth'
        }
      ];

      separatePositionDimensions(transform);

      expect(transform.positionX!.keyframes.length).toBe(2);
      expect(transform.positionY!.keyframes.length).toBe(2);
      expect(transform.positionZ!.keyframes.length).toBe(2);

      // Check values
      expect(transform.positionX!.keyframes[0].value).toBe(0);
      expect(transform.positionX!.keyframes[1].value).toBe(100);
      expect(transform.positionY!.keyframes[0].value).toBe(0);
      expect(transform.positionY!.keyframes[1].value).toBe(200);
    });

    test('linkPositionDimensions merges back to combined property', () => {
      const transform = createDefaultTransform();
      transform.position.animated = true;
      transform.position.keyframes = [
        {
          id: 'kf1',
          frame: 0,
          value: { x: 0, y: 0, z: 0 },
          interpolation: 'linear',
          inHandle: { frame: -5, value: 0, enabled: false },
          outHandle: { frame: 5, value: 0, enabled: false },
          controlMode: 'smooth'
        }
      ];

      // Separate
      separatePositionDimensions(transform);

      // Modify individual dimensions
      transform.positionX!.value = 150;
      transform.positionY!.value = 250;

      // Link back
      linkPositionDimensions(transform);

      expect(transform.separateDimensions?.position).toBe(false);
      expect(transform.positionX).toBeUndefined();
      expect(transform.positionY).toBeUndefined();
      expect(transform.position.value.x).toBe(150);
      expect(transform.position.value.y).toBe(250);
    });

    test('separateScaleDimensions creates X, Y, Z scale properties with correct values', () => {
      const transform = createDefaultTransform();
      transform.scale.value = { x: 100, y: 150, z: 75 };

      separateScaleDimensions(transform);

      expect(transform.separateDimensions?.scale).toBe(true);
      // Verify exact values and property names
      expect(transform.scaleX!.value).toBe(100);
      expect(transform.scaleX!.name).toBe('Scale X');
      expect(transform.scaleY!.value).toBe(150);
      expect(transform.scaleY!.name).toBe('Scale Y');
      expect(transform.scaleZ!.value).toBe(75);
      expect(transform.scaleZ!.name).toBe('Scale Z');
    });

    test('store actions for separate dimensions work correctly', () => {
      const layer = store.createLayer('solid', 'Test Layer');

      // Initially not separated
      expect(store.hasPositionSeparated(layer.id)).toBe(false);
      expect(store.hasScaleSeparated(layer.id)).toBe(false);

      // Separate position
      store.separatePositionDimensions(layer.id);
      expect(store.hasPositionSeparated(layer.id)).toBe(true);

      // Separate scale
      store.separateScaleDimensions(layer.id);
      expect(store.hasScaleSeparated(layer.id)).toBe(true);

      // Link back
      store.linkPositionDimensions(layer.id);
      expect(store.hasPositionSeparated(layer.id)).toBe(false);

      store.linkScaleDimensions(layer.id);
      expect(store.hasScaleSeparated(layer.id)).toBe(false);
    });
  });

  // ============================================================================
  // PHASE E: SEQUENCE LAYERS
  // ============================================================================

  describe('Phase E: Sequence Layers', () => {
    test('sequenceLayers arranges layers in sequence', () => {
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');
      const layer3 = store.createLayer('solid', 'Layer 3');

      // Set initial durations
      layer1.startFrame = 0;
      layer1.endFrame = 30;
      layer2.startFrame = 0;
      layer2.endFrame = 30;
      layer3.startFrame = 0;
      layer3.endFrame = 30;

      const count = store.sequenceLayers(
        [layer1.id, layer2.id, layer3.id],
        { startFrame: 0, gapFrames: 0 }
      );

      expect(count).toBe(3);
      expect(layer1.startFrame).toBe(0);
      expect(layer1.endFrame).toBe(30);
      expect(layer2.startFrame).toBe(30);
      expect(layer2.endFrame).toBe(60);
      expect(layer3.startFrame).toBe(60);
      expect(layer3.endFrame).toBe(90);
    });

    test('sequenceLayers with gap adds space between layers', () => {
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');

      layer1.startFrame = 0;
      layer1.endFrame = 20;
      layer2.startFrame = 0;
      layer2.endFrame = 20;

      store.sequenceLayers(
        [layer1.id, layer2.id],
        { startFrame: 0, gapFrames: 10 }
      );

      expect(layer1.endFrame).toBe(20);
      expect(layer2.startFrame).toBe(30); // 20 + 10 gap
      expect(layer2.endFrame).toBe(50);
    });

    test('sequenceLayers with negative gap creates overlap', () => {
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');

      layer1.startFrame = 0;
      layer1.endFrame = 30;
      layer2.startFrame = 0;
      layer2.endFrame = 30;

      store.sequenceLayers(
        [layer1.id, layer2.id],
        { startFrame: 0, gapFrames: -10 }
      );

      expect(layer1.endFrame).toBe(30);
      expect(layer2.startFrame).toBe(20); // 30 - 10 overlap
    });

    test('sequenceLayers with reverse option reverses order', () => {
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');

      layer1.startFrame = 0;
      layer1.endFrame = 30;
      layer2.startFrame = 0;
      layer2.endFrame = 30;

      store.sequenceLayers(
        [layer1.id, layer2.id],
        { startFrame: 0, gapFrames: 0, reverse: true }
      );

      // In reverse, layer2 comes first
      expect(layer2.startFrame).toBe(0);
      expect(layer2.endFrame).toBe(30);
      expect(layer1.startFrame).toBe(30);
      expect(layer1.endFrame).toBe(60);
    });

    test('sequenceLayers preserves layer durations', () => {
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');

      layer1.startFrame = 10;
      layer1.endFrame = 25; // Duration: 15
      layer2.startFrame = 5;
      layer2.endFrame = 50; // Duration: 45

      store.sequenceLayers(
        [layer1.id, layer2.id],
        { startFrame: 0, gapFrames: 0 }
      );

      expect(layer1.endFrame - layer1.startFrame).toBe(15);
      expect(layer2.endFrame - layer2.startFrame).toBe(45);
    });
  });

  // ============================================================================
  // PHASE E: EXPONENTIAL SCALE
  // ============================================================================

  describe('Phase E: Exponential Scale', () => {
    test('applyExponentialScale creates keyframes with exponential values', () => {
      const layer = store.createLayer('solid', 'Test Layer');

      const count = store.applyExponentialScale(layer.id, {
        startScale: 100,
        endScale: 400,
        startFrame: 0,
        endFrame: 30,
        keyframeCount: 10
      });

      expect(count).toBe(11); // 10 intervals = 11 keyframes

      const keyframes = layer.transform.scale.keyframes;
      expect(keyframes.length).toBe(11);

      // First keyframe should be startScale
      expect(keyframes[0].value.x).toBeCloseTo(100, 1);
      expect(keyframes[0].value.y).toBeCloseTo(100, 1);

      // Last keyframe should be endScale
      expect(keyframes[10].value.x).toBeCloseTo(400, 1);
      expect(keyframes[10].value.y).toBeCloseTo(400, 1);

      // Middle keyframe should be geometric mean (for t=0.5, should be 200)
      expect(keyframes[5].value.x).toBeCloseTo(200, 0);
    });

    test('exponential scale follows correct formula', () => {
      const layer = store.createLayer('solid', 'Test Layer');

      store.applyExponentialScale(layer.id, {
        startScale: 100,
        endScale: 200,
        startFrame: 0,
        endFrame: 30,
        keyframeCount: 4
      });

      const keyframes = layer.transform.scale.keyframes;

      // For 100 to 200 with exponential: scale(t) = 100 * 2^t
      // t=0: 100 * 2^0 = 100
      // t=0.25: 100 * 2^0.25 ≈ 118.9
      // t=0.5: 100 * 2^0.5 ≈ 141.4
      // t=0.75: 100 * 2^0.75 ≈ 168.2
      // t=1: 100 * 2^1 = 200

      expect(keyframes[0].value.x).toBeCloseTo(100, 0);
      expect(keyframes[1].value.x).toBeCloseTo(118.9, 0);
      expect(keyframes[2].value.x).toBeCloseTo(141.4, 0);
      expect(keyframes[3].value.x).toBeCloseTo(168.2, 0);
      expect(keyframes[4].value.x).toBeCloseTo(200, 0);
    });

    test('exponential scale axis option works', () => {
      const layer = store.createLayer('solid', 'Test Layer');

      // Set initial scale
      layer.transform.scale.value = { x: 100, y: 100, z: 100 };

      store.applyExponentialScale(layer.id, {
        startScale: 100,
        endScale: 200,
        startFrame: 0,
        endFrame: 30,
        keyframeCount: 2,
        axis: 'x'
      });

      const keyframes = layer.transform.scale.keyframes;

      // Only X should change
      expect(keyframes[0].value.x).toBeCloseTo(100, 1);
      expect(keyframes[2].value.x).toBeCloseTo(200, 1);

      // Y should stay at 100
      expect(keyframes[0].value.y).toBe(100);
      expect(keyframes[2].value.y).toBe(100);
    });
  });

  // ============================================================================
  // UNDO/REDO VERIFICATION
  // ============================================================================

  describe('Undo/Redo', () => {
    test('sequenceLayers can be undone', () => {
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');

      layer1.startFrame = 0;
      layer1.endFrame = 30;
      layer2.startFrame = 0;
      layer2.endFrame = 30;

      // Must push history after initial setup to capture the "before" state
      store.pushHistory();

      const originalLayer2Start = 0;
      const layer2Id = layer2.id;

      store.sequenceLayers([layer1.id, layer2.id], { startFrame: 0, gapFrames: 0 });

      // Re-fetch layer after modification using getActiveCompLayers
      const layer2AfterSequence = store.getActiveCompLayers().find(l => l.id === layer2Id);
      expect(layer2AfterSequence?.startFrame).toBe(30); // After sequence

      store.undo();

      // Re-fetch layer after undo to get updated state
      const layer2AfterUndo = store.getActiveCompLayers().find(l => l.id === layer2Id);
      expect(layer2AfterUndo?.startFrame).toBe(originalLayer2Start);
    });

    test('separatePositionDimensions can be undone', () => {
      const layer = store.createLayer('solid', 'Test Layer');

      expect(store.hasPositionSeparated(layer.id)).toBe(false);

      store.separatePositionDimensions(layer.id);
      expect(store.hasPositionSeparated(layer.id)).toBe(true);

      store.undo();
      expect(store.hasPositionSeparated(layer.id)).toBe(false);
    });

    test('applyExponentialScale can be undone', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      const layerId = layer.id;

      expect(layer.transform.scale.keyframes.length).toBe(0);

      // Push history to capture "before" state
      store.pushHistory();

      store.applyExponentialScale(layerId, {
        startScale: 100,
        endScale: 200,
        startFrame: 0,
        endFrame: 30,
        keyframeCount: 5
      });

      // Re-fetch layer after modification using getActiveCompLayers
      const layerAfterScale = store.getActiveCompLayers().find(l => l.id === layerId);
      expect(layerAfterScale?.transform.scale.keyframes.length).toBe(6);

      store.undo();

      // Re-fetch layer after undo
      const layerAfterUndo = store.getActiveCompLayers().find(l => l.id === layerId);
      expect(layerAfterUndo?.transform.scale.keyframes.length).toBe(0);
    });
  });

  // ============================================================================
  // DETERMINISM VERIFICATION
  // ============================================================================

  describe('Determinism', () => {
    test('exponential scale produces identical results', () => {
      const layer1 = store.createLayer('solid', 'Layer 1');
      const layer2 = store.createLayer('solid', 'Layer 2');

      const options = {
        startScale: 100,
        endScale: 400,
        startFrame: 0,
        endFrame: 60,
        keyframeCount: 10
      };

      store.applyExponentialScale(layer1.id, options);
      store.applyExponentialScale(layer2.id, options);

      const kf1 = layer1.transform.scale.keyframes;
      const kf2 = layer2.transform.scale.keyframes;

      expect(kf1.length).toBe(kf2.length);

      for (let i = 0; i < kf1.length; i++) {
        expect(kf1[i].value.x).toBeCloseTo(kf2[i].value.x, 5);
        expect(kf1[i].value.y).toBeCloseTo(kf2[i].value.y, 5);
        expect(kf1[i].frame).toBe(kf2[i].frame);
      }
    });

    test('auto bezier tangents produce deterministic results', () => {
      const layer = store.createLayer('solid', 'Test Layer');
      store.addKeyframe(layer.id, 'opacity', 0, 0);
      store.addKeyframe(layer.id, 'opacity', 50, 15);
      store.addKeyframe(layer.id, 'opacity', 100, 30);

      // Calculate tangents multiple times
      const results: number[][] = [];

      for (let run = 0; run < 3; run++) {
        // Reset and recalculate
        layer.opacity.keyframes.forEach(kf => {
          kf.interpolation = 'linear';
          kf.inHandle = { frame: -5, value: 0, enabled: false };
          kf.outHandle = { frame: 5, value: 0, enabled: false };
        });

        store.autoCalculateAllBezierTangents(layer.id, 'opacity');

        results.push(layer.opacity.keyframes.map(kf => kf.outHandle.value));
      }

      // All runs should produce same results
      expect(results[0]).toEqual(results[1]);
      expect(results[1]).toEqual(results[2]);
    });
  });
});
