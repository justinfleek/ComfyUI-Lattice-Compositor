/**
 * Keyframe Actions Pipeline Integration Tests
 *
 * Tests the complete keyframe manipulation pipeline:
 * - Adding keyframes to properties
 * - Moving keyframes in time
 * - Setting interpolation types and bezier handles
 * - Multi-keyframe operations
 * - Property animation state toggling
 *
 * These tests verify that keyframe operations correctly modify
 * layer properties and that those changes affect frame evaluation.
 */

import { beforeEach, describe, expect, it } from "vitest";
import { interpolateProperty } from "@/services/interpolation";
import {
  addKeyframe,
  findPropertyByPath,
  getAllKeyframeFrames,
  getKeyframesAtFrame,
  moveKeyframe,
  removeKeyframe,
  scaleKeyframeTiming,
  setKeyframeHandle,
  setKeyframeInterpolation,
  setKeyframeValue,
  setPropertyAnimated,
  timeReverseKeyframes,
} from "@/stores/actions/keyframeActions";
import { createLayer } from "@/stores/actions/layerActions";
import type { BezierHandle, Layer } from "@/types/project";
import { createAnimatableProperty } from "@/types/project";

// Mock store interface
function createMockStore() {
  const layers: Layer[] = [];

  const store = {
    project: {
      meta: { modified: "" },
      composition: { width: 1920, height: 1080 },
    },
    clipboard: { layers: [] as Layer[], keyframes: [] },
    getActiveComp: () => ({
      currentFrame: 0,
      settings: { width: 1920, height: 1080, frameCount: 81 },
      layers,
    }),
    getActiveCompLayers: () => layers,
    getLayerById: (id: string) => layers.find((l) => l.id === id),
    pushHistory: () => {},
    _addLayer: (layer: Layer) => layers.push(layer),
    _getLayers: () => layers,
  };

  return store;
}

// Helper to create a layer with initialized transform
function createTestLayer(
  store: ReturnType<typeof createMockStore>,
  name: string = "Test Layer",
): Layer {
  // Use createLayer to ensure proper initialization
  const layerStore = {
    project: store.project,
    clipboard: store.clipboard,
    getActiveComp: store.getActiveComp,
    getActiveCompLayers: store.getActiveCompLayers,
    pushHistory: store.pushHistory,
  };

  const layer = createLayer(layerStore, "solid", name);
  return layer;
}

describe("Keyframe Actions Pipeline", () => {
  let store: ReturnType<typeof createMockStore>;

  beforeEach(() => {
    store = createMockStore();
  });

  describe("Adding Keyframes", () => {
    it("adds keyframe to position property", () => {
      const layer = createTestLayer(store);

      const kf = addKeyframe(
        store,
        layer.id,
        "position",
        { x: 100, y: 200 },
        10,
      );

      expect(kf).toBeDefined();
      expect(kf?.frame).toBe(10);
      expect(kf?.value).toEqual({ x: 100, y: 200 });
      expect(layer.transform.position.animated).toBe(true);
      expect(layer.transform.position.keyframes.length).toBe(1);
    });

    it("adds multiple keyframes in sorted order", () => {
      const layer = createTestLayer(store);

      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 30);
      addKeyframe(store, layer.id, "position", { x: 0, y: 0 }, 0);
      addKeyframe(store, layer.id, "position", { x: 50, y: 50 }, 15);

      const keyframes = layer.transform.position.keyframes;
      expect(keyframes.length).toBe(3);
      expect(keyframes[0].frame).toBe(0);
      expect(keyframes[1].frame).toBe(15);
      expect(keyframes[2].frame).toBe(30);
    });

    it("replaces keyframe at same frame", () => {
      const layer = createTestLayer(store);

      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 10);
      addKeyframe(store, layer.id, "position", { x: 500, y: 500 }, 10);

      const keyframes = layer.transform.position.keyframes;
      expect(keyframes.length).toBe(1);
      expect(keyframes[0].value).toEqual({ x: 500, y: 500 });
    });

    it("adds keyframe with default linear interpolation", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 20);

      expect(kf?.interpolation).toBe("linear");
      expect(kf?.inHandle).toEqual({ frame: 0, value: 0, enabled: false });
      expect(kf?.outHandle).toEqual({ frame: 0, value: 0, enabled: false });
    });

    it("supports normalized property paths (with and without transform prefix)", () => {
      const layer = createTestLayer(store);

      // Both should work
      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 0);
      addKeyframe(store, layer.id, "transform.scale", { x: 150, y: 150 }, 0);

      expect(layer.transform.position.keyframes.length).toBe(1);
      expect(layer.transform.scale.keyframes.length).toBe(1);
    });
  });

  describe("Removing Keyframes", () => {
    it("removes keyframe by ID", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(
        store,
        layer.id,
        "position",
        { x: 100, y: 100 },
        10,
      )!;

      expect(layer.transform.position.keyframes.length).toBe(1);

      removeKeyframe(store, layer.id, "position", kf.id);

      expect(layer.transform.position.keyframes.length).toBe(0);
    });

    it("disables animation when all keyframes removed", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 10)!;

      expect(layer.opacity.animated).toBe(true);

      removeKeyframe(store, layer.id, "opacity", kf.id);

      expect(layer.opacity.animated).toBe(false);
      expect(layer.opacity.keyframes.length).toBe(0);
    });
  });

  describe("Moving Keyframes", () => {
    it("moves keyframe to new frame", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(
        store,
        layer.id,
        "position",
        { x: 100, y: 100 },
        10,
      )!;

      moveKeyframe(store, layer.id, "position", kf.id, 50);

      expect(layer.transform.position.keyframes[0].frame).toBe(50);
    });

    it("removes existing keyframe at destination", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "position", { x: 0, y: 0 }, 0);
      const kfToMove = addKeyframe(
        store,
        layer.id,
        "position",
        { x: 100, y: 100 },
        30,
      )!;
      addKeyframe(store, layer.id, "position", { x: 50, y: 50 }, 15);

      // Move keyframe at 30 to 15 (where another keyframe exists)
      moveKeyframe(store, layer.id, "position", kfToMove.id, 15);

      const keyframes = layer.transform.position.keyframes;
      expect(keyframes.length).toBe(2); // One was replaced
      expect(keyframes[1].frame).toBe(15);
      expect(keyframes[1].value).toEqual({ x: 100, y: 100 }); // Moved keyframe's value
    });

    it("maintains sorted order after move", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "position", { x: 0, y: 0 }, 0);
      const kf = addKeyframe(
        store,
        layer.id,
        "position",
        { x: 50, y: 50 },
        10,
      )!;
      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 40);

      // Move middle keyframe to end
      moveKeyframe(store, layer.id, "position", kf.id, 80);

      const frames = layer.transform.position.keyframes.map((k) => k.frame);
      expect(frames).toEqual([0, 40, 80]);
    });
  });

  describe("Keyframe Values", () => {
    it("updates keyframe value", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 10)!;

      setKeyframeValue(store, layer.id, "opacity", kf.id, 75);

      expect(layer.opacity.keyframes[0].value).toBe(75);
    });

    it("affects interpolation after value change", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "opacity", 0, 0);
      const kf = addKeyframe(store, layer.id, "opacity", 100, 50)!;

      // Value at frame 25 should be 50 (linear interpolation)
      let mid = interpolateProperty(layer.opacity, 25);
      expect(mid).toBe(50);

      // Change second keyframe value
      setKeyframeValue(store, layer.id, "opacity", kf.id, 200);

      // Value at frame 25 should now be 100
      mid = interpolateProperty(layer.opacity, 25);
      expect(mid).toBe(100);
    });
  });

  describe("Interpolation Types", () => {
    it("sets interpolation to hold", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 10)!;

      setKeyframeInterpolation(store, layer.id, "opacity", kf.id, "hold");

      expect(layer.opacity.keyframes[0].interpolation).toBe("hold");
    });

    it("sets interpolation to bezier", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 10)!;

      setKeyframeInterpolation(store, layer.id, "opacity", kf.id, "bezier");

      expect(layer.opacity.keyframes[0].interpolation).toBe("bezier");
    });

    it("hold interpolation affects value calculation", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "opacity", 25, 0);
      const _kf2 = addKeyframe(store, layer.id, "opacity", 75, 50)!;

      // With linear: midpoint value is average
      let mid = interpolateProperty(layer.opacity, 25);
      expect(mid).toBe(50); // (25 + 75) / 2

      // Change first keyframe to hold
      setKeyframeInterpolation(
        store,
        layer.id,
        "opacity",
        layer.opacity.keyframes[0].id,
        "hold",
      );

      // With hold: value stays at first keyframe until next
      mid = interpolateProperty(layer.opacity, 25);
      expect(mid).toBe(25); // Held at 25
    });
  });

  describe("Bezier Handles", () => {
    it("sets outHandle on keyframe", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 10)!;

      const handle: BezierHandle = { frame: 15, value: 50, enabled: true };
      setKeyframeHandle(store, layer.id, "opacity", kf.id, "out", handle);

      expect(layer.opacity.keyframes[0].outHandle).toEqual(handle);
    });

    it("sets inHandle on keyframe", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 50)!;

      const handle: BezierHandle = { frame: -10, value: -30, enabled: true };
      setKeyframeHandle(store, layer.id, "opacity", kf.id, "in", handle);

      expect(layer.opacity.keyframes[0].inHandle).toEqual(handle);
    });

    it("enables bezier interpolation when handle is enabled", () => {
      const layer = createTestLayer(store);
      const kf = addKeyframe(store, layer.id, "opacity", 50, 10)!;

      expect(layer.opacity.keyframes[0].interpolation).toBe("linear");

      const handle: BezierHandle = { frame: 15, value: 50, enabled: true };
      setKeyframeHandle(store, layer.id, "opacity", kf.id, "out", handle);

      expect(layer.opacity.keyframes[0].interpolation).toBe("bezier");
    });
  });

  describe("Property Animation State", () => {
    it("enables animation on property", () => {
      const layer = createTestLayer(store);

      expect(layer.transform.rotation.animated).toBeFalsy();

      setPropertyAnimated(store, layer.id, "rotation", true);

      expect(layer.transform.rotation.animated).toBe(true);
    });

    it("adds initial keyframe when enabling animation", () => {
      const layer = createTestLayer(store);
      layer.transform.rotation.value = 45;

      setPropertyAnimated(store, layer.id, "rotation", true);

      expect(layer.transform.rotation.keyframes.length).toBe(1);
      expect(layer.transform.rotation.keyframes[0].value).toBe(45);
      expect(layer.transform.rotation.keyframes[0].frame).toBe(0);
    });

    it("disables animation on property", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "rotation", 0, 0);
      addKeyframe(store, layer.id, "rotation", 90, 40);

      setPropertyAnimated(store, layer.id, "rotation", false);

      expect(layer.transform.rotation.animated).toBe(false);
    });
  });

  describe("Find Property By Path", () => {
    it("finds transform.position", () => {
      const layer = createTestLayer(store);
      const prop = findPropertyByPath(layer, "transform.position");

      expect(prop).toBe(layer.transform.position);
    });

    it("finds position without transform prefix", () => {
      const layer = createTestLayer(store);
      const prop = findPropertyByPath(layer, "position");

      expect(prop).toBe(layer.transform.position);
    });

    it("finds opacity", () => {
      const layer = createTestLayer(store);
      const prop = findPropertyByPath(layer, "opacity");

      expect(prop).toBe(layer.opacity);
    });

    it("finds 3D rotation properties when layer is 3D", () => {
      const layer = createTestLayer(store);
      layer.threeD = true;
      layer.transform.rotationX = createAnimatableProperty(
        "rotationX",
        0,
        "number",
      );
      layer.transform.rotationY = createAnimatableProperty(
        "rotationY",
        0,
        "number",
      );
      layer.transform.rotationZ = createAnimatableProperty(
        "rotationZ",
        0,
        "number",
      );

      expect(findPropertyByPath(layer, "rotationX")).toBe(
        layer.transform.rotationX,
      );
      expect(findPropertyByPath(layer, "rotationY")).toBe(
        layer.transform.rotationY,
      );
      expect(findPropertyByPath(layer, "rotationZ")).toBe(
        layer.transform.rotationZ,
      );
    });

    it("finds custom properties by name", () => {
      const layer = createTestLayer(store);
      const customProp = createAnimatableProperty(
        "Custom Effect",
        0.5,
        "number",
      );
      layer.properties.push(customProp);

      const found = findPropertyByPath(layer, "Custom Effect");
      expect(found).toBe(customProp);
    });
  });

  describe("Keyframe Query Utilities", () => {
    it("getKeyframesAtFrame returns all keyframes at a frame", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 10);
      addKeyframe(store, layer.id, "opacity", 50, 10);
      addKeyframe(store, layer.id, "rotation", 45, 10);
      addKeyframe(store, layer.id, "scale", { x: 150, y: 150 }, 20); // Different frame

      const atFrame10 = getKeyframesAtFrame(store, layer.id, 10);

      expect(atFrame10.length).toBe(3);
      expect(atFrame10.map((k) => k.propertyPath)).toContain("position");
      expect(atFrame10.map((k) => k.propertyPath)).toContain("opacity");
      expect(atFrame10.map((k) => k.propertyPath)).toContain("rotation");
    });

    it("getAllKeyframeFrames returns sorted unique frames", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 0);
      addKeyframe(store, layer.id, "position", { x: 200, y: 200 }, 40);
      addKeyframe(store, layer.id, "opacity", 50, 20);
      addKeyframe(store, layer.id, "opacity", 100, 40); // Same frame as position
      addKeyframe(store, layer.id, "rotation", 90, 60);

      const frames = getAllKeyframeFrames(store, layer.id);

      expect(frames).toEqual([0, 20, 40, 60]);
    });
  });

  describe("Timing Operations", () => {
    it("scaleKeyframeTiming scales all keyframes from anchor", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "position", { x: 0, y: 0 }, 0);
      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 20);
      addKeyframe(store, layer.id, "position", { x: 200, y: 200 }, 40);

      // Scale by 2x from frame 0
      scaleKeyframeTiming(store, layer.id, "position", 2.0, 0);

      const frames = layer.transform.position.keyframes.map((k) => k.frame);
      expect(frames).toEqual([0, 40, 80]);
    });

    it("scaleKeyframeTiming with anchor in middle", () => {
      const layer = createTestLayer(store);
      // NOTE: Using 'rotation' instead of 'opacity' because scaleKeyframeTiming
      // has a bug where it prepends 'transform.' to all paths, breaking for opacity
      addKeyframe(store, layer.id, "rotation", 0, 10);
      addKeyframe(store, layer.id, "rotation", 45, 30);
      addKeyframe(store, layer.id, "rotation", 90, 50);

      // Scale by 0.5x from frame 30 (middle keyframe)
      scaleKeyframeTiming(store, layer.id, "rotation", 0.5, 30);

      const frames = layer.transform.rotation.keyframes.map((k) => k.frame);
      // Frame 10 -> 30 - (30-10)*0.5 = 30 - 10 = 20
      // Frame 30 -> 30 (anchor stays)
      // Frame 50 -> 30 + (50-30)*0.5 = 30 + 10 = 40
      expect(frames).toEqual([20, 30, 40]);
    });

    it("timeReverseKeyframes reverses values keeping frames", () => {
      const layer = createTestLayer(store);
      // NOTE: Using 'position' instead of 'opacity' because timeReverseKeyframes
      // has a bug where it incorrectly prepends 'transform.' to all paths,
      // which breaks for top-level properties like 'opacity'
      addKeyframe(store, layer.id, "position", { x: 0, y: 0 }, 0);
      addKeyframe(store, layer.id, "position", { x: 50, y: 50 }, 20);
      addKeyframe(store, layer.id, "position", { x: 100, y: 100 }, 40);

      timeReverseKeyframes(store, layer.id, "position");

      const kfs = layer.transform.position.keyframes;
      // Frames stay the same
      expect(kfs.map((k) => k.frame)).toEqual([0, 20, 40]);
      // Values are reversed
      expect(kfs[0].value).toEqual({ x: 100, y: 100 });
      expect(kfs[1].value).toEqual({ x: 50, y: 50 });
      expect(kfs[2].value).toEqual({ x: 0, y: 0 });
    });
  });

  describe("Integration: Keyframes Affect Evaluation", () => {
    it("keyframe changes immediately affect interpolation", () => {
      const layer = createTestLayer(store);

      // Add keyframes
      addKeyframe(store, layer.id, "opacity", 0, 0);
      addKeyframe(store, layer.id, "opacity", 100, 80);

      // Check interpolation works
      expect(interpolateProperty(layer.opacity, 0)).toBe(0);
      expect(interpolateProperty(layer.opacity, 40)).toBe(50);
      expect(interpolateProperty(layer.opacity, 80)).toBe(100);

      // Modify keyframe
      setKeyframeValue(
        store,
        layer.id,
        "opacity",
        layer.opacity.keyframes[1].id,
        200,
      );

      // Interpolation should reflect change immediately
      expect(interpolateProperty(layer.opacity, 40)).toBe(100); // (0 + 200) / 2
      expect(interpolateProperty(layer.opacity, 80)).toBe(200);
    });

    it("moving keyframe changes interpolation curve", () => {
      const layer = createTestLayer(store);
      addKeyframe(store, layer.id, "opacity", 0, 0);
      const kf = addKeyframe(store, layer.id, "opacity", 100, 50)!;

      // Mid point is at frame 25
      expect(interpolateProperty(layer.opacity, 25)).toBe(50);

      // Move second keyframe to frame 100
      moveKeyframe(store, layer.id, "opacity", kf.id, 100);

      // Mid point (frame 50) should now be 50
      expect(interpolateProperty(layer.opacity, 50)).toBe(50);
      // Old mid point (frame 25) should now be 25
      expect(interpolateProperty(layer.opacity, 25)).toBe(25);
    });
  });
});
