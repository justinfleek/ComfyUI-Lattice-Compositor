/**
 * Browser Tests for Keyframe System
 *
 * Runs in REAL Chromium browser with WebGL support.
 * Tests keyframe CRUD, interpolation, sorting, and determinism in browser environment.
 *
 * To watch these tests:
 * 1. Install Vitest extension in Cursor (if not already installed)
 * 2. Run: npm run test:browser -- --ui
 * 3. Tests will open in browser with live reload
 */

import { describe, expect, it, beforeEach, afterEach } from "vitest";
import { setActivePinia, createPinia } from "pinia";
import { useProjectStore } from "@/stores/projectStore";
import { useKeyframeStore } from "@/stores/keyframeStore";
import { useAnimationStore } from "@/stores/animationStore";
import { useLayerStore } from "@/stores/layerStore";
import { useCompositionStore } from "@/stores/compositionStore";
import { interpolateProperty } from "@/services/interpolation";
import type { Layer, Keyframe } from "@/types/project";

describe("Keyframe System Browser Tests", () => {
  let projectStore: ReturnType<typeof useProjectStore>;
  let keyframeStore: ReturnType<typeof useKeyframeStore>;
  let animationStore: ReturnType<typeof useAnimationStore>;
  let layerStore: ReturnType<typeof useLayerStore>;
  let testLayer: Layer;

  beforeEach(() => {
    setActivePinia(createPinia());
    projectStore = useProjectStore();
    keyframeStore = useKeyframeStore();
    animationStore = useAnimationStore();
    layerStore = useLayerStore();
    const compositionStore = useCompositionStore();

    // Create a test composition
    compositionStore.createComposition("Test Comp", {
      width: 1920,
      height: 1080,
      fps: 30,
      frameCount: 300,
    });

    // Create a test layer
    testLayer = layerStore.createLayer("solid", "Test Layer");
  });

  afterEach(() => {
    // Clean up
    projectStore.project.compositions = {};
    projectStore.activeCompositionId = "";
  });

  describe("Deterministic Keyframe ID Generation", () => {
    it("should generate same ID for same layer/property/frame/value", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";
      const frame = 10;
      const value = { x: 100, y: 200, z: 0 };

      // Add keyframe twice with same parameters
      const kf1 = keyframeStore.addKeyframe(layerId, propertyPath, value, frame);
      const kf2 = keyframeStore.addKeyframe(layerId, propertyPath, value, frame);

      // Should have same ID (deterministic)
      expect(kf1?.id).toBe(kf2?.id);
    });

    it("should generate different IDs for different values", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";
      const frame = 10;

      const kf1 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 200, z: 0 }, frame);
      const kf2 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 150, y: 250, z: 0 }, frame);

      // Should have different IDs
      expect(kf1?.id).not.toBe(kf2?.id);
    });

    it("should generate different IDs for different frames", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";
      const value = { x: 100, y: 200, z: 0 };

      const kf1 = keyframeStore.addKeyframe(layerId, propertyPath, value, 10);
      const kf2 = keyframeStore.addKeyframe(layerId, propertyPath, value, 20);

      // Should have different IDs
      expect(kf1?.id).not.toBe(kf2?.id);
    });
  });

  describe("Keyframe CRUD Operations", () => {
    it("should add keyframe and maintain sorting", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      // Add keyframes out of order
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 30);
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 200, y: 200, z: 0 }, 10);
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 300, y: 300, z: 0 }, 20);

      const property = layerStore.getLayerById(layerId)?.transform.position;
      expect(property?.keyframes).toBeDefined();
      expect(property?.keyframes.length).toBe(3);

      // Verify sorted order
      // Deterministic: Explicit null check after toBeDefined() assertion
      if (!property || !property.keyframes) {
        throw new Error("Property and keyframes should be defined");
      }
      const frames = property.keyframes.map((kf) => kf.frame);
      expect(frames).toEqual([10, 20, 30]);
    });

    it("should replace keyframe at same frame", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";
      const frame = 10;

      const kf1 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, frame);
      const kf2 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 200, y: 200, z: 0 }, frame);

      const property = layerStore.getLayerById(layerId)?.transform.position;
      expect(property?.keyframes.length).toBe(1);
      expect(property?.keyframes[0].id).toBe(kf2?.id);
      expect(property?.keyframes[0].value).toEqual({ x: 200, y: 200, z: 0 });
    });

    it("should remove keyframe", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      const kf = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);
      expect(kf).not.toBeNull();
      // Deterministic: Explicit null check after toBeNull() assertion
      if (!kf) {
        throw new Error("Keyframe should be defined");
      }
      keyframeStore.removeKeyframe(layerId, propertyPath, kf.id);

      const property = layerStore.getLayerById(layerId)?.transform.position;
      expect(property?.keyframes.length).toBe(0);
    });

    it("should clear all keyframes", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 200, y: 200, z: 0 }, 20);
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 300, y: 300, z: 0 }, 30);

      keyframeStore.clearKeyframes(layerId, propertyPath);

      const property = layerStore.getLayerById(layerId)?.transform.position;
      expect(property?.keyframes.length).toBe(0);
      expect(property?.animated).toBe(false);
    });

    it("should move keyframe to new frame", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      const kf = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);
      // Deterministic: Explicit null check before using keyframe
      if (!kf) {
        throw new Error("Keyframe should be defined");
      }
      keyframeStore.moveKeyframe(layerId, propertyPath, kf.id, 50);

      const property = layerStore.getLayerById(layerId)?.transform.position;
      expect(property?.keyframes[0].frame).toBe(50);
      expect(property?.keyframes[0].value).toEqual({ x: 100, y: 100, z: 0 });
    });
  });

  describe("Keyframe Interpolation", () => {
    it("should interpolate linearly between two keyframes", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      // Add keyframes at frame 0 and 30
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 0, y: 0, z: 0 }, 0);
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 300, y: 300, z: 0 }, 30);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;

      // At frame 15 (halfway), should be halfway between values
      const value15 = interpolateProperty(property, 15, 30);
      expect(value15).toEqual({ x: 150, y: 150, z: 0 });

      // At frame 0, should be first keyframe value
      const value0 = interpolateProperty(property, 0, 30);
      expect(value0).toEqual({ x: 0, y: 0, z: 0 });

      // At frame 30, should be second keyframe value
      const value30 = interpolateProperty(property, 30, 30);
      expect(value30).toEqual({ x: 300, y: 300, z: 0 });
    });

    it("should hold value before first keyframe", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;

      // Before first keyframe, should return first keyframe value
      const value5 = interpolateProperty(property, 5, 30);
      expect(value5).toEqual({ x: 100, y: 100, z: 0 });
    });

    it("should hold value after last keyframe", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;

      // After last keyframe, should return last keyframe value
      const value50 = interpolateProperty(property, 50, 30);
      expect(value50).toEqual({ x: 100, y: 100, z: 0 });
    });

    it("should handle hold interpolation", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      const kf1 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 0, y: 0, z: 0 }, 0);
      const kf2 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 30);

      // Set first keyframe to hold
      // Deterministic: Explicit null check before using keyframe
      if (!kf1) {
        throw new Error("Keyframe should be defined");
      }
      keyframeStore.setKeyframeInterpolation(layerId, propertyPath, kf1.id, "hold");

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;

      // At frame 15, should still be first keyframe value (hold)
      const value15 = interpolateProperty(property, 15, 30);
      expect(value15).toEqual({ x: 0, y: 0, z: 0 });
    });

    it("should handle single keyframe", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;

      // At any frame, should return the single keyframe value
      const value5 = interpolateProperty(property, 5, 30);
      const value10 = interpolateProperty(property, 10, 30);
      const value50 = interpolateProperty(property, 50, 30);

      expect(value5).toEqual({ x: 100, y: 100, z: 0 });
      expect(value10).toEqual({ x: 100, y: 100, z: 0 });
      expect(value50).toEqual({ x: 100, y: 100, z: 0 });
    });
  });

  describe("Keyframe Sorting Invariants", () => {
    it("should maintain sort order after multiple operations", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      // Add keyframes
      const kf1 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 30);
      const kf2 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 200, y: 200, z: 0 }, 10);
      const kf3 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 300, y: 300, z: 0 }, 20);

      // Move middle keyframe
      // Deterministic: Explicit null check before using keyframe
      if (!kf2) {
        throw new Error("Keyframe should be defined");
      }
      keyframeStore.moveKeyframe(layerId, propertyPath, kf2.id, 25);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;
      const frames = property.keyframes.map((kf) => kf.frame);
      expect(frames).toEqual([20, 25, 30]);
    });

    it("should handle keyframes at identical frames (replacement)", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      const kf1 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);
      const kf2 = keyframeStore.addKeyframe(layerId, propertyPath, { x: 200, y: 200, z: 0 }, 10);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;
      expect(property.keyframes.length).toBe(1);
      expect(property.keyframes[0].id).toBe(kf2?.id);
    });
  });

  describe("Edge Cases", () => {
    it("should handle empty keyframe array", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;
      property.animated = true;
      property.keyframes = [];

      // Should return static value
      const value = interpolateProperty(property, 10, 30);
      expect(value).toEqual(property.value);
    });

    it("should handle frame 0 correctly", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      keyframeStore.addKeyframe(layerId, propertyPath, { x: 0, y: 0, z: 0 }, 0);
      keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;
      const value0 = interpolateProperty(property, 0, 30);
      expect(value0).toEqual({ x: 0, y: 0, z: 0 });
    });

    it("should clamp negative frames to 0 when moving", () => {
      const layerId = testLayer.id;
      const propertyPath = "transform.position";

      const kf = keyframeStore.addKeyframe(layerId, propertyPath, { x: 100, y: 100, z: 0 }, 10);
      // Deterministic: Explicit null check before using keyframe
      if (!kf) {
        throw new Error("Keyframe should be defined");
      }
      keyframeStore.moveKeyframe(layerId, propertyPath, kf.id, -5);

      // Deterministic: Explicit null check before using property
      const propertyValue = layerStore.getLayerById(layerId)?.transform.position;
      if (!propertyValue) {
        throw new Error("Property should be defined");
      }
      const property = propertyValue;
      expect(property.keyframes[0].frame).toBeGreaterThanOrEqual(0);
    });
  });
});
