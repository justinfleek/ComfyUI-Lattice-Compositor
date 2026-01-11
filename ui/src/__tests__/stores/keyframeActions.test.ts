/**
 * Keyframe Actions Tests
 *
 * Tests for keyframe manipulation: add, remove, move, update, interpolation.
 *
 * CRITICAL: These functions handle animation data. Bugs here = broken animations.
 *
 * @audit P0 CRITICAL - Animation integrity
 */

import { describe, it, expect, beforeEach, vi } from "vitest";
import { findPropertyByPath } from "@/stores/keyframeStore/helpers";
import { addKeyframe, removeKeyframe, clearKeyframes, moveKeyframe, moveKeyframes, setKeyframeValue } from "@/stores/keyframeStore/crud";
import { setKeyframeInterpolation } from "@/stores/keyframeStore/interpolation";
import { setPropertyValue, setPropertyAnimated } from "@/stores/keyframeStore/property";
import { getKeyframesAtFrame, getAllKeyframeFrames, findNextKeyframeFrame, findPrevKeyframeFrame, findSurroundingKeyframes } from "@/stores/keyframeStore/query";
import { scaleKeyframeTiming, timeReverseKeyframes } from "@/stores/keyframeStore/timing";
import type { KeyframeStoreAccess as KeyframeStore } from "@/stores/keyframeStore/types";
import type { Layer, AnimatableProperty, Keyframe, Composition } from "@/types/project";

// ============================================================================
// Test Helpers
// ============================================================================

function createMockKeyframe<T>(frame: number, value: T, id?: string): Keyframe<T> {
  return {
    id: id || `kf-${frame}`,
    frame,
    value,
    interpolation: "linear",
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: "smooth",
  };
}

function createAnimatableProperty<T>(
  value: T,
  keyframes: Keyframe<T>[] = [],
  animated = false
): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random().toString(36).slice(2, 8)}`,
    name: "test",
    type: "number" as any,
    value,
    animated: animated || keyframes.length > 0,
    keyframes,
  };
}

function createMockLayer(id: string, overrides: Partial<Layer> = {}): Layer {
  return {
    id,
    name: `Layer ${id}`,
    type: "solid",
    visible: true,
    locked: false,
    isolate: false,
    motionBlur: false,
    startFrame: 0,
    endFrame: 100,
    inPoint: 0,
    outPoint: 100,
    blendMode: "normal",
    threeD: false,
    opacity: createAnimatableProperty(100),
    transform: {
      position: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
      rotation: createAnimatableProperty(0),
      origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      anchorPoint: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
    },
    effects: [],
    properties: [],
    parentId: null,
    data: { color: "#ff0000", width: 1920, height: 1080 },
    ...overrides,
  };
}

function createMockStore(layers: Layer[] = []): KeyframeStore {
  const comp: Composition = {
    id: "main",
    name: "Main Comp",
    settings: {
      width: 1920,
      height: 1080,
      frameCount: 150,
      fps: 30,
      duration: 5,
      backgroundColor: "#000000",
      autoResizeToContent: false,
      frameBlendingEnabled: false,
    },
    layers,
    currentFrame: 0,
    isNestedComp: false,
  };

  return {
    project: {
      meta: { modified: new Date().toISOString() },
    },
    getActiveComp: () => comp,
    getActiveCompLayers: () => layers,
    getLayerById: (id: string) => layers.find((l) => l.id === id) || null,
    pushHistory: vi.fn(),
  };
}

// ============================================================================
// findPropertyByPath Tests
// ============================================================================

describe("findPropertyByPath", () => {
  it("finds opacity property", () => {
    const layer = createMockLayer("layer-1");
    const prop = findPropertyByPath(layer, "opacity");
    expect(prop).toBe(layer.opacity);
  });

  it("finds transform.position", () => {
    const layer = createMockLayer("layer-1");
    const prop = findPropertyByPath(layer, "transform.position");
    expect(prop).toBe(layer.transform.position);
  });

  it("finds position without transform prefix", () => {
    const layer = createMockLayer("layer-1");
    const prop = findPropertyByPath(layer, "position");
    expect(prop).toBe(layer.transform.position);
  });

  it("finds transform.scale", () => {
    const layer = createMockLayer("layer-1");
    const prop = findPropertyByPath(layer, "scale");
    expect(prop).toBe(layer.transform.scale);
  });

  it("finds transform.rotation", () => {
    const layer = createMockLayer("layer-1");
    const prop = findPropertyByPath(layer, "rotation");
    expect(prop).toBe(layer.transform.rotation);
  });

  it("finds transform.origin", () => {
    const layer = createMockLayer("layer-1");
    const prop = findPropertyByPath(layer, "origin");
    expect(prop).toBe(layer.transform.origin);
  });

  it("finds custom property by name", () => {
    const customProp = createAnimatableProperty(42);
    customProp.name = "customValue";
    const layer = createMockLayer("layer-1", {
      properties: [customProp],
    });

    const prop = findPropertyByPath(layer, "customValue");
    expect(prop).toBe(customProp);
  });

  it("finds custom property by id", () => {
    const customProp = createAnimatableProperty(42);
    customProp.id = "custom-prop-id";
    const layer = createMockLayer("layer-1", {
      properties: [customProp],
    });

    const prop = findPropertyByPath(layer, "custom-prop-id");
    expect(prop).toBe(customProp);
  });

  it("returns undefined for unknown property", () => {
    const layer = createMockLayer("layer-1");
    const prop = findPropertyByPath(layer, "nonexistent");
    expect(prop).toBeUndefined();
  });

  it("finds 3D rotation properties when they exist", () => {
    const layer = createMockLayer("layer-1", {
      transform: {
        position: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
        rotation: createAnimatableProperty(0),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        rotationX: createAnimatableProperty(0),
        rotationY: createAnimatableProperty(0),
        rotationZ: createAnimatableProperty(0),
      },
    });

    expect(findPropertyByPath(layer, "rotationX")).toBeDefined();
    expect(findPropertyByPath(layer, "rotationY")).toBeDefined();
    expect(findPropertyByPath(layer, "rotationZ")).toBeDefined();
  });
});

// ============================================================================
// addKeyframe Tests
// ============================================================================

describe("addKeyframe", () => {
  it("adds keyframe to property", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    const keyframe = addKeyframe(store, "layer-1", "opacity", 50, 30);

    expect(keyframe).not.toBeNull();
    expect(keyframe!.frame).toBe(30);
    expect(keyframe!.value).toBe(50);
    expect(layer.opacity.keyframes.length).toBe(1);
    expect(layer.opacity.animated).toBe(true);
  });

  it("uses current frame when atFrame not specified", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);
    (store.getActiveComp() as any).currentFrame = 15;

    const keyframe = addKeyframe(store, "layer-1", "opacity", 75);

    expect(keyframe!.frame).toBe(15);
  });

  it("replaces existing keyframe at same frame", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 25)]),
    });
    const store = createMockStore([layer]);

    addKeyframe(store, "layer-1", "opacity", 75, 30);

    expect(layer.opacity.keyframes.length).toBe(1);
    expect(layer.opacity.keyframes[0].value).toBe(75);
  });

  it("sorts keyframes by frame after adding", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0),
        createMockKeyframe(60, 100),
      ]),
    });
    const store = createMockStore([layer]);

    addKeyframe(store, "layer-1", "opacity", 50, 30);

    expect(layer.opacity.keyframes.map((k) => k.frame)).toEqual([0, 30, 60]);
  });

  it("returns null for unknown layer", () => {
    const store = createMockStore([]);
    const keyframe = addKeyframe(store, "unknown", "opacity", 50, 30);
    expect(keyframe).toBeNull();
  });

  it("returns null for unknown property", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    const keyframe = addKeyframe(store, "layer-1", "nonexistent", 50, 30);
    expect(keyframe).toBeNull();
  });

  it("calls pushHistory after adding", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    addKeyframe(store, "layer-1", "opacity", 50, 30);

    expect(store.pushHistory).toHaveBeenCalled();
  });

  it("handles NaN frame by using fallback", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    const keyframe = addKeyframe(store, "layer-1", "opacity", 50, NaN);

    expect(keyframe!.frame).toBe(0); // Fallback
  });

  it("handles undefined frame by using currentFrame", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);
    (store.getActiveComp() as any).currentFrame = 45;

    const keyframe = addKeyframe(store, "layer-1", "opacity", 50, undefined);

    expect(keyframe!.frame).toBe(45);
  });

  it("adds keyframe to vector property (position)", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    const keyframe = addKeyframe(
      store,
      "layer-1",
      "position",
      { x: 100, y: 200, z: 0 },
      30
    );

    expect(keyframe).not.toBeNull();
    expect(keyframe!.value).toEqual({ x: 100, y: 200, z: 0 });
  });
});

// ============================================================================
// removeKeyframe Tests
// ============================================================================

describe("removeKeyframe", () => {
  it("removes keyframe by ID", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0, "kf-0"),
        createMockKeyframe(30, 50, "kf-30"),
        createMockKeyframe(60, 100, "kf-60"),
      ]),
    });
    const store = createMockStore([layer]);

    removeKeyframe(store, "layer-1", "opacity", "kf-30");

    expect(layer.opacity.keyframes.length).toBe(2);
    expect(layer.opacity.keyframes.find((k) => k.id === "kf-30")).toBeUndefined();
  });

  it("disables animation when last keyframe removed", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")], true),
    });
    const store = createMockStore([layer]);

    removeKeyframe(store, "layer-1", "opacity", "kf-30");

    expect(layer.opacity.keyframes.length).toBe(0);
    expect(layer.opacity.animated).toBe(false);
  });

  it("does nothing for unknown layer", () => {
    const store = createMockStore([]);
    expect(() => removeKeyframe(store, "unknown", "opacity", "kf-1")).not.toThrow();
  });

  it("does nothing for unknown keyframe", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    removeKeyframe(store, "layer-1", "opacity", "unknown-kf");

    expect(layer.opacity.keyframes.length).toBe(1);
  });
});

// ============================================================================
// clearKeyframes Tests
// ============================================================================

describe("clearKeyframes", () => {
  it("removes all keyframes from property", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(
        100,
        [
          createMockKeyframe(0, 0),
          createMockKeyframe(30, 50),
          createMockKeyframe(60, 100),
        ],
        true
      ),
    });
    const store = createMockStore([layer]);

    clearKeyframes(store, "layer-1", "opacity");

    expect(layer.opacity.keyframes.length).toBe(0);
    expect(layer.opacity.animated).toBe(false);
  });
});

// ============================================================================
// moveKeyframe Tests
// ============================================================================

describe("moveKeyframe", () => {
  it("moves keyframe to new frame", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    moveKeyframe(store, "layer-1", "opacity", "kf-30", 45);

    expect(layer.opacity.keyframes[0].frame).toBe(45);
  });

  it("removes existing keyframe at target frame", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(30, 50, "kf-30"),
        createMockKeyframe(60, 100, "kf-60"),
      ]),
    });
    const store = createMockStore([layer]);

    // Move kf-30 to frame 60 (where kf-60 exists)
    moveKeyframe(store, "layer-1", "opacity", "kf-30", 60);

    expect(layer.opacity.keyframes.length).toBe(1);
    expect(layer.opacity.keyframes[0].id).toBe("kf-30");
    expect(layer.opacity.keyframes[0].frame).toBe(60);
  });

  it("re-sorts keyframes after move", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0, "kf-0"),
        createMockKeyframe(30, 50, "kf-30"),
        createMockKeyframe(60, 100, "kf-60"),
      ]),
    });
    const store = createMockStore([layer]);

    // Move kf-30 to frame 90
    moveKeyframe(store, "layer-1", "opacity", "kf-30", 90);

    expect(layer.opacity.keyframes.map((k) => k.frame)).toEqual([0, 60, 90]);
  });

  it("ignores invalid frame (NaN)", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    moveKeyframe(store, "layer-1", "opacity", "kf-30", NaN);

    expect(layer.opacity.keyframes[0].frame).toBe(30); // Unchanged
  });

  it("ignores Infinity frame", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    moveKeyframe(store, "layer-1", "opacity", "kf-30", Infinity);

    expect(layer.opacity.keyframes[0].frame).toBe(30); // Unchanged
  });
});

// ============================================================================
// moveKeyframes (batch) Tests
// ============================================================================

describe("moveKeyframes", () => {
  it("moves multiple keyframes by delta", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0, "kf-0"),
        createMockKeyframe(30, 50, "kf-30"),
      ]),
    });
    const store = createMockStore([layer]);

    moveKeyframes(
      store,
      [
        { layerId: "layer-1", propertyPath: "opacity", keyframeId: "kf-0" },
        { layerId: "layer-1", propertyPath: "opacity", keyframeId: "kf-30" },
      ],
      10
    );

    expect(layer.opacity.keyframes.map((k) => k.frame)).toEqual([10, 40]);
  });

  it("clamps frame to minimum 0", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(5, 50, "kf-5")]),
    });
    const store = createMockStore([layer]);

    moveKeyframes(
      store,
      [{ layerId: "layer-1", propertyPath: "opacity", keyframeId: "kf-5" }],
      -20
    );

    expect(layer.opacity.keyframes[0].frame).toBe(0); // Clamped to 0
  });

  it("ignores invalid frameDelta (NaN)", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    moveKeyframes(
      store,
      [{ layerId: "layer-1", propertyPath: "opacity", keyframeId: "kf-30" }],
      NaN
    );

    expect(layer.opacity.keyframes[0].frame).toBe(30); // Unchanged
  });
});

// ============================================================================
// setKeyframeValue Tests
// ============================================================================

describe("setKeyframeValue", () => {
  it("updates keyframe value", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    setKeyframeValue(store, "layer-1", "opacity", "kf-30", 75);

    expect(layer.opacity.keyframes[0].value).toBe(75);
  });

  it("does nothing for unknown keyframe", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    setKeyframeValue(store, "layer-1", "opacity", "unknown", 75);

    expect(layer.opacity.keyframes[0].value).toBe(50); // Unchanged
  });
});

// ============================================================================
// setKeyframeInterpolation Tests
// ============================================================================

describe("setKeyframeInterpolation", () => {
  it("updates interpolation type", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    setKeyframeInterpolation(store, "layer-1", "opacity", "kf-30", "bezier");

    expect(layer.opacity.keyframes[0].interpolation).toBe("bezier");
  });

  it("accepts hold interpolation", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")]),
    });
    const store = createMockStore([layer]);

    setKeyframeInterpolation(store, "layer-1", "opacity", "kf-30", "hold");

    expect(layer.opacity.keyframes[0].interpolation).toBe("hold");
  });
});

// ============================================================================
// setPropertyValue Tests
// ============================================================================

describe("setPropertyValue", () => {
  it("sets property value", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    setPropertyValue(store, "layer-1", "opacity", 75);

    expect(layer.opacity.value).toBe(75);
  });

  it("sets vector property value", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    setPropertyValue(store, "layer-1", "position", { x: 100, y: 200, z: 50 });

    expect(layer.transform.position.value).toEqual({ x: 100, y: 200, z: 50 });
  });
});

// ============================================================================
// setPropertyAnimated Tests
// ============================================================================

describe("setPropertyAnimated", () => {
  it("enables animation on property", () => {
    const layer = createMockLayer("layer-1");
    layer.opacity.animated = false;
    const store = createMockStore([layer]);

    setPropertyAnimated(store, "layer-1", "opacity", true);

    expect(layer.opacity.animated).toBe(true);
  });

  it("disables animation on property", () => {
    const layer = createMockLayer("layer-1");
    layer.opacity.animated = true;
    const store = createMockStore([layer]);

    setPropertyAnimated(store, "layer-1", "opacity", false);

    expect(layer.opacity.animated).toBe(false);
  });
});

// ============================================================================
// getKeyframesAtFrame Tests
// ============================================================================

describe("getKeyframesAtFrame", () => {
  it("returns keyframes at specified frame with propertyPath", () => {
    const posKeyframes = [
      createMockKeyframe(30, { x: 100, y: 100, z: 0 }, "pos-kf-30"),
    ];
    const posProperty = createAnimatableProperty({ x: 0, y: 0, z: 0 }, posKeyframes, true);

    const layer = createMockLayer("layer-1", {
      transform: {
        position: posProperty,
        scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
        rotation: createAnimatableProperty(0),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const store = createMockStore([layer]);

    const keyframes = getKeyframesAtFrame(store, "layer-1", 30);

    // Returns array of { propertyPath, keyframe }
    expect(keyframes.length).toBe(1);
    expect(keyframes[0].propertyPath).toBe("position");
    expect(keyframes[0].keyframe.id).toBe("pos-kf-30");
  });

  it("returns empty array when no keyframes at frame", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50, "kf-30")], true),
    });
    const store = createMockStore([layer]);

    const keyframes = getKeyframesAtFrame(store, "layer-1", 45);

    expect(keyframes.length).toBe(0);
  });
});

// ============================================================================
// getAllKeyframeFrames Tests
// ============================================================================

describe("getAllKeyframeFrames", () => {
  it("returns all unique frame numbers sorted", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0),
        createMockKeyframe(30, 50),
      ]),
      transform: {
        position: createAnimatableProperty({ x: 0, y: 0, z: 0 }, [
          createMockKeyframe(15, { x: 0, y: 0, z: 0 }),
          createMockKeyframe(30, { x: 100, y: 100, z: 0 }), // Duplicate frame
        ]),
        scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
        rotation: createAnimatableProperty(0),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const store = createMockStore([layer]);

    const frames = getAllKeyframeFrames(store, "layer-1");

    expect(frames).toEqual([0, 15, 30]); // Sorted, unique
  });

  it("returns empty array for layer with no keyframes", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    const frames = getAllKeyframeFrames(store, "layer-1");

    expect(frames).toEqual([]);
  });
});

// ============================================================================
// findNextKeyframeFrame / findPrevKeyframeFrame Tests
// ============================================================================

describe("findNextKeyframeFrame", () => {
  it("finds next keyframe frame after current", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0),
        createMockKeyframe(30, 50),
        createMockKeyframe(60, 100),
      ], true),
    });
    const store = createMockStore([layer]);

    // Signature: findNextKeyframeFrame(store, currentFrame, layerIds[])
    const next = findNextKeyframeFrame(store, 15, ["layer-1"]);

    expect(next).toBe(30);
  });

  it("returns null when no next keyframe", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50)], true),
    });
    const store = createMockStore([layer]);

    const next = findNextKeyframeFrame(store, 60, ["layer-1"]);

    expect(next).toBeNull();
  });
});

describe("findPrevKeyframeFrame", () => {
  it("finds previous keyframe frame before current", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0),
        createMockKeyframe(30, 50),
        createMockKeyframe(60, 100),
      ], true),
    });
    const store = createMockStore([layer]);

    // Signature: findPrevKeyframeFrame(store, currentFrame, layerIds[])
    const prev = findPrevKeyframeFrame(store, 45, ["layer-1"]);

    expect(prev).toBe(30);
  });

  it("returns null when no previous keyframe", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50)], true),
    });
    const store = createMockStore([layer]);

    const prev = findPrevKeyframeFrame(store, 15, ["layer-1"]);

    expect(prev).toBeNull();
  });
});

// ============================================================================
// findSurroundingKeyframes Tests
// ============================================================================

describe("findSurroundingKeyframes", () => {
  it("finds keyframes before and after frame", () => {
    const keyframes = [
      createMockKeyframe(0, 0),
      createMockKeyframe(30, 50),
      createMockKeyframe(60, 100),
    ];
    const property = createAnimatableProperty(100, keyframes, true);

    // Signature: findSurroundingKeyframes(property, frame)
    const result = findSurroundingKeyframes(property, 45);

    expect(result.before?.frame).toBe(30);
    expect(result.after?.frame).toBe(60);
  });

  it("returns { before: null, after: null } when no keyframes", () => {
    const property = createAnimatableProperty(100, [], false);

    const result = findSurroundingKeyframes(property, 15);

    expect(result.before).toBeNull();
    expect(result.after).toBeNull();
  });

  it("returns before=kf, after=null when at or after last keyframe", () => {
    const keyframes = [createMockKeyframe(30, 50)];
    const property = createAnimatableProperty(100, keyframes, true);

    const result = findSurroundingKeyframes(property, 60);

    expect(result.before?.frame).toBe(30);
    expect(result.after).toBeNull();
  });
});

// ============================================================================
// scaleKeyframeTiming Tests
// ============================================================================

describe("scaleKeyframeTiming", () => {
  it("scales keyframe timing by factor", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0, "kf-0"),
        createMockKeyframe(30, 50, "kf-30"),
        createMockKeyframe(60, 100, "kf-60"),
      ]),
    });
    const store = createMockStore([layer]);

    scaleKeyframeTiming(store, "layer-1", "opacity", 2.0);

    expect(layer.opacity.keyframes.map((k) => k.frame)).toEqual([0, 60, 120]);
  });

  it("scales with custom anchor frame", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(30, 0, "kf-30"),
        createMockKeyframe(60, 100, "kf-60"),
      ]),
    });
    const store = createMockStore([layer]);

    // Scale by 2x from anchor at frame 30
    scaleKeyframeTiming(store, "layer-1", "opacity", 2.0, 30);

    // Frame 30 stays at 30, frame 60 becomes 30 + (60-30)*2 = 90
    expect(layer.opacity.keyframes[0].frame).toBe(30);
    expect(layer.opacity.keyframes[1].frame).toBe(90);
  });

  it("handles scale factor < 1 (compress)", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0),
        createMockKeyframe(100, 100),
      ]),
    });
    const store = createMockStore([layer]);

    scaleKeyframeTiming(store, "layer-1", "opacity", 0.5);

    expect(layer.opacity.keyframes.map((k) => k.frame)).toEqual([0, 50]);
  });
});

// ============================================================================
// timeReverseKeyframes Tests
// ============================================================================

describe("timeReverseKeyframes", () => {
  it("reverses keyframe timing order", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [
        createMockKeyframe(0, 0, "kf-0"),
        createMockKeyframe(30, 50, "kf-30"),
        createMockKeyframe(60, 100, "kf-60"),
      ]),
    });
    const store = createMockStore([layer]);

    const count = timeReverseKeyframes(store, "layer-1", "opacity");

    expect(count).toBe(3);
    // Values should be reversed: 0→100, 30→50, 60→0
    expect(layer.opacity.keyframes[0].value).toBe(100);
    expect(layer.opacity.keyframes[1].value).toBe(50);
    expect(layer.opacity.keyframes[2].value).toBe(0);
    // Frames stay the same
    expect(layer.opacity.keyframes.map((k) => k.frame)).toEqual([0, 30, 60]);
  });

  it("returns 0 for property with no keyframes", () => {
    const layer = createMockLayer("layer-1");
    const store = createMockStore([layer]);

    const count = timeReverseKeyframes(store, "layer-1", "opacity");

    expect(count).toBe(0);
  });

  it("returns 0 for single keyframe (nothing to reverse)", () => {
    const layer = createMockLayer("layer-1", {
      opacity: createAnimatableProperty(100, [createMockKeyframe(30, 50)], true),
    });
    const store = createMockStore([layer]);

    const count = timeReverseKeyframes(store, "layer-1", "opacity");

    // Single keyframe has nothing to reverse with
    expect(count).toBe(0);
  });
});

// ============================================================================
// Determinism Tests
// ============================================================================

describe("Determinism", () => {
  it("same operations produce identical keyframe arrays", () => {
    const layer1 = createMockLayer("layer-1");
    const store1 = createMockStore([layer1]);

    const layer2 = createMockLayer("layer-1");
    const store2 = createMockStore([layer2]);

    // Perform identical operations
    addKeyframe(store1, "layer-1", "opacity", 0, 0);
    addKeyframe(store1, "layer-1", "opacity", 50, 30);
    addKeyframe(store1, "layer-1", "opacity", 100, 60);

    addKeyframe(store2, "layer-1", "opacity", 0, 0);
    addKeyframe(store2, "layer-1", "opacity", 50, 30);
    addKeyframe(store2, "layer-1", "opacity", 100, 60);

    // Compare values (IDs will differ due to random generation)
    const values1 = layer1.opacity.keyframes.map((k) => ({ frame: k.frame, value: k.value }));
    const values2 = layer2.opacity.keyframes.map((k) => ({ frame: k.frame, value: k.value }));

    expect(values1).toEqual(values2);
  });
});
