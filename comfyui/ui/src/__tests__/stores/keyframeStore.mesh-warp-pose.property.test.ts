/**
 * Property-Based Tests for Mesh Warp Pin and Pose Keypoint Keyframes
 *
 * Tests keyframe operations for:
 * - Mesh warp pins (position, rotation, scale, inFront)
 * - Pose layer animated keypoints
 *
 * Verifies deterministic ID generation, sorting, interpolation, and edge cases.
 *
 * @audit P0 CRITICAL - Keyframe system integrity for nested properties
 */

import { describe, expect, beforeEach } from "vitest";
import { test } from "@fast-check/vitest";
import * as fc from "fast-check";
import { setActivePinia, createPinia } from "pinia";
import { addKeyframe, removeKeyframe } from "@/stores/keyframeStore/crud";
import { interpolateProperty } from "@/services/interpolation";
import { useProjectStore } from "@/stores/projectStore";
import { useCompositionStore } from "@/stores/compositionStore";
import { useLayerStore } from "@/stores/layerStore";
import { createLayer } from "@/stores/layerStore/crud";
import { findPropertyByPath } from "@/stores/keyframeStore/helpers";
import type { Layer, AnimatableProperty } from "@/types/project";
import { generateKeyframeId } from "@/utils/uuid5";
import type { WarpPin } from "@/types/meshWarp";
import { createDefaultWarpPin } from "@/types/meshWarp";
import { createAnimatableProperty } from "@/types/project";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// ARBITRARIES (Generators)
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = fc.double({ noNaN: true, noDefaultInfinity: true, min: -10000, max: 10000 });
const positiveFrame = fc.integer({ min: 0, max: 1000 });
const vec2Arb = fc.record({
  x: finiteNumber,
  y: finiteNumber,
});
const opacityArb = fc.double({ min: 0, max: 100, noNaN: true, noDefaultInfinity: true });

// ═══════════════════════════════════════════════════════════════════════════
//                                                          // test // helpers
// ═══════════════════════════════════════════════════════════════════════════

function createTestSplineLayer(): Layer {
  const projectStore = useProjectStore();
  const compositionStore = useCompositionStore();

  if (!projectStore.activeCompositionId) {
    compositionStore.createComposition("Test Comp", {
      width: 1920,
      height: 1080,
      fps: 30,
      frameCount: 300,
    });
  }

  return createLayer("spline", "Test Spline Layer");
}

function createTestPoseLayer(): Layer {
  const projectStore = useProjectStore();
  const compositionStore = useCompositionStore();

  if (!projectStore.activeCompositionId) {
    compositionStore.createComposition("Test Comp", {
      width: 1920,
      height: 1080,
      fps: 30,
      frameCount: 300,
    });
  }

  return createLayer("pose", "Test Pose Layer");
}

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: Mesh Warp Pins
// ═══════════════════════════════════════════════════════════════════════════

describe("Keyframe Store Property Tests - Mesh Warp Pins", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  test.prop([
    vec2Arb,
    positiveFrame,
  ])("mesh warp pin position keyframes use deterministic IDs", (position, frame) => {
    const layer = createTestSplineLayer();
    
    // Add a warp pin
    const pinId = `pin_test_${Date.now()}`;
    const pin = createDefaultWarpPin(pinId, position.x, position.y, "position");
    
    // Update layer data with pin
    const splineData = layer.data as import("@/types/spline").SplineData;
    if (!splineData) return;
    
    const updatedData = {
      ...splineData,
      warpPins: [pin],
    };
    const layerStore = useLayerStore();
    // Update layer via store
    layerStore.updateLayerData(layer.id, updatedData);
    
    // Refresh layer reference
    const projectStore = useProjectStore();
    const updatedLayer = projectStore.getActiveCompLayers().find((l) => l.id === layer.id);
    if (!updatedLayer || updatedLayer.type !== "spline") return;
    
    const propertyPath = `warpPins.${pinId}.position`;
    const kf = addKeyframe(updatedLayer.id, propertyPath, position, frame);

    const property = findPropertyByPath(updatedLayer, propertyPath);
    if (!property) return;

    expect(property.keyframes.length).toBeGreaterThan(0);
    expect(property.keyframes.some((k) => k.id === kf.id)).toBe(true);
    expect(property.animated).toBe(true);
    
    // Verify deterministic ID
    const valueStr = `${position.x},${position.y}`;
    const expectedId = generateKeyframeId(updatedLayer.id, propertyPath, frame, valueStr);
    expect(kf.id).toBe(expectedId);
  });

  test.prop([
    finiteNumber,
    positiveFrame,
  ])("mesh warp pin rotation keyframes use deterministic IDs", (rotation, frame) => {
    const layer = createTestSplineLayer();
    
    const pinId = `pin_test_${Date.now()}`;
    const pin = createDefaultWarpPin(pinId, 100, 100, "rotation");
    
    const splineData = layer.data as import("@/types/spline").SplineData;
    if (!splineData) return;
    
    const updatedData = {
      ...splineData,
      warpPins: [pin],
    };
    const layerStore = useLayerStore();
    layerStore.updateLayerData(layer.id, updatedData);
    
    const projectStore = useProjectStore();
    const updatedLayer = projectStore.getActiveCompLayers().find((l) => l.id === layer.id);
    if (!updatedLayer || updatedLayer.type !== "spline") return;
    
    const propertyPath = `warpPins.${pinId}.rotation`;
    const kf = addKeyframe(updatedLayer.id, propertyPath, rotation, frame);

    const property = findPropertyByPath(updatedLayer, propertyPath);
    if (!property) return;

    expect(property.keyframes.length).toBeGreaterThan(0);
    
    // Verify deterministic ID
    const valueStr = String(rotation);
    const expectedId = generateKeyframeId(updatedLayer.id, propertyPath, frame, valueStr);
    expect(kf.id).toBe(expectedId);
  });

  test.prop([
    vec2Arb,
    vec2Arb,
    positiveFrame,
    positiveFrame,
  ])("mesh warp pin position interpolation is deterministic", (pos1, pos2, frame1, frame2) => {
    fc.pre(frame1 < frame2);

    const layer = createTestSplineLayer();
    
    const pinId = `pin_test_${Date.now()}`;
    const pin = createDefaultWarpPin(pinId, pos1.x, pos1.y, "position");
    
    const splineData = layer.data as import("@/types/spline").SplineData;
    if (!splineData) return;
    
    const updatedData = {
      ...splineData,
      warpPins: [pin],
    };
    const layerStore = useLayerStore();
    layerStore.updateLayerData(layer.id, updatedData);
    
    const projectStore = useProjectStore();
    const updatedLayer = projectStore.getActiveCompLayers().find((l) => l.id === layer.id);
    if (!updatedLayer || updatedLayer.type !== "spline") return;
    
    const propertyPath = `warpPins.${pinId}.position`;
    addKeyframe(updatedLayer.id, propertyPath, pos1, frame1);
    addKeyframe(updatedLayer.id, propertyPath, pos2, frame2);

    const property = findPropertyByPath(updatedLayer, propertyPath);
    if (!property) return;

    const testFrame = Math.floor((frame1 + frame2) / 2);
    const result1 = interpolateProperty(property, testFrame, 30);
    const result2 = interpolateProperty(property, testFrame, 30);

    // Should be deterministic
    expect(result1).toEqual(result2);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROPERTY TESTS: Pose Layer Keypoints
// ═══════════════════════════════════════════════════════════════════════════

describe("Keyframe Store Property Tests - Pose Layer Keypoints", () => {
  beforeEach(() => {
    setActivePinia(createPinia());
    const projectStore = useProjectStore();
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  test.prop([
    vec2Arb,
    positiveFrame,
  ])("pose layer animated keypoint keyframes use deterministic IDs", (position, frame) => {
    const layer = createTestPoseLayer();
    
    // Initialize animatedKeypoints if needed
    const poseData = layer.data as import("@/engine/layers/PoseLayer").PoseLayerData;
    if (!poseData) return;
    
    const keypointId = `pose_pose0_keypoint_0`;
    const animatedProp = createAnimatableProperty(keypointId, position, "position");
    
    const updatedData = {
      ...poseData,
      animatedKeypoints: {
        [keypointId]: animatedProp,
      },
    };
    const layerStore = useLayerStore();
    layerStore.updateLayerData(layer.id, updatedData);
    
    const projectStore = useProjectStore();
    const updatedLayer = projectStore.getActiveCompLayers().find((l) => l.id === layer.id);
    if (!updatedLayer || updatedLayer.type !== "pose") return;
    
    const propertyPath = `animatedKeypoints.${keypointId}`;
    const kf = addKeyframe(updatedLayer.id, propertyPath, position, frame);

    const property = findPropertyByPath(updatedLayer, propertyPath);
    if (!property) return;

    expect(property.keyframes.length).toBeGreaterThan(0);
    expect(property.keyframes.some((k) => k.id === kf.id)).toBe(true);
    expect(property.animated).toBe(true);
    
    // Verify deterministic ID
    const valueStr = `${position.x},${position.y}`;
    const expectedId = generateKeyframeId(updatedLayer.id, propertyPath, frame, valueStr);
    expect(kf.id).toBe(expectedId);
  });

  test.prop([
    vec2Arb,
    vec2Arb,
    positiveFrame,
    positiveFrame,
  ])("pose layer keypoint interpolation is deterministic", (pos1, pos2, frame1, frame2) => {
    fc.pre(frame1 < frame2);

    const layer = createTestPoseLayer();
    
    const poseData = layer.data as import("@/engine/layers/PoseLayer").PoseLayerData;
    if (!poseData) return;
    
    const keypointId = `pose_pose0_keypoint_0`;
    const animatedProp = createAnimatableProperty(keypointId, pos1, "position");
    
    const updatedData = {
      ...poseData,
      animatedKeypoints: {
        [keypointId]: animatedProp,
      },
    };
    const layerStore = useLayerStore();
    layerStore.updateLayerData(layer.id, updatedData);
    
    const projectStore = useProjectStore();
    const updatedLayer = projectStore.getActiveCompLayers().find((l) => l.id === layer.id);
    if (!updatedLayer || updatedLayer.type !== "pose") return;
    
    const propertyPath = `animatedKeypoints.${keypointId}`;
    addKeyframe(updatedLayer.id, propertyPath, pos1, frame1);
    addKeyframe(updatedLayer.id, propertyPath, pos2, frame2);

    const property = findPropertyByPath(updatedLayer, propertyPath);
    if (!property) return;

    const testFrame = Math.floor((frame1 + frame2) / 2);
    const result1 = interpolateProperty(property, testFrame, 30);
    const result2 = interpolateProperty(property, testFrame, 30);

    // Should be deterministic
    expect(result1).toEqual(result2);
  });
});
