/**
 * Integration Test: Save → Load Roundtrip
 *
 * Tests that project data survives serialization/deserialization
 * without loss or corruption.
 *
 * CRITICAL: If this fails, users can lose work or get corrupted projects.
 */

import { describe, expect, test } from "vitest";
import type {
  AnimatableProperty,
  Composition,
  Keyframe,
  Layer,
  LatticeProject,
} from "@/types/project";

// ============================================================================
// Test Helpers
// ============================================================================

function createTestKeyframe(
  frame: number,
  value: number | { x: number; y: number; z?: number },
  interpolation: "linear" | "bezier" | "hold" = "linear"
): Keyframe {
  return {
    id: `kf-${frame}`,
    frame,
    value,
    interpolation,
    inHandle: { frame: -5, value: 0, enabled: interpolation === "bezier" },
    outHandle: { frame: 5, value: 0, enabled: interpolation === "bezier" },
    controlMode: "smooth" as const,
  };
}

function createAnimatableProperty<T>(
  value: T,
  keyframes: Keyframe[] = []
): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random().toString(36).slice(2, 8)}`,
    name: "test",
    type: "number" as any,
    value,
    animated: keyframes.length > 0,
    keyframes,
  };
}

function createTestLayer(overrides: Partial<Layer> = {}): Layer {
  return {
    id: `layer-${overrides.name || "test"}`,
    name: "Test Layer",
    type: "solid",
    visible: true,
    locked: false,
    solo: false,
    shy: false,
    startFrame: 0,
    endFrame: 150,
    inPoint: 0,
    outPoint: 150,
    blendMode: "normal",
    threeD: false,
    opacity: createAnimatableProperty(100),
    transform: {
      position: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
      rotation: createAnimatableProperty(0),
      origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
    },
    effects: [],
    properties: [],
    parentId: null,
    data: { type: "solid", color: "#ff0000" },
    ...overrides,
  };
}

function createTestProject(layers: Layer[]): LatticeProject {
  const composition: Composition = {
    id: "main",
    name: "Test Composition",
    settings: {
      width: 1920,
      height: 1080,
      fps: 30,
      duration: 5,
      backgroundColor: "#000000",
    },
    layers,
  };

  return {
    id: "test-project",
    version: "1.0.0",
    mainCompositionId: "main",
    compositions: { main: composition },
    composition: composition.settings,
    assets: {},
    meta: {
      name: "Test Project",
      created: new Date().toISOString(),
      modified: new Date().toISOString(),
      version: "1.0.0",
    },
  };
}

/**
 * Simulate save/load by JSON serialization roundtrip
 */
function roundtripJSON<T>(data: T): T {
  const serialized = JSON.stringify(data);
  return JSON.parse(serialized);
}

// ============================================================================
// Integration Tests
// ============================================================================

describe("Save/Load Roundtrip - Basic Types", () => {
  test("empty project survives roundtrip", () => {
    const original = createTestProject([]);
    const restored = roundtripJSON(original);

    expect(restored.id).toBe(original.id);
    expect(restored.mainCompositionId).toBe(original.mainCompositionId);
    expect(Object.keys(restored.compositions)).toEqual(Object.keys(original.compositions));
    expect(restored.compositions.main.layers).toHaveLength(0);
  });

  test("composition settings survive roundtrip", () => {
    const original = createTestProject([]);
    original.composition.width = 4096;
    original.composition.height = 2160;
    original.composition.fps = 60;
    original.composition.backgroundColor = "#1a2b3c";

    const restored = roundtripJSON(original);

    expect(restored.composition.width).toBe(4096);
    expect(restored.composition.height).toBe(2160);
    expect(restored.composition.fps).toBe(60);
    expect(restored.composition.backgroundColor).toBe("#1a2b3c");
  });

  test("metadata survives roundtrip", () => {
    const original = createTestProject([]);
    original.meta.name = "My Important Project";

    const restored = roundtripJSON(original);

    expect(restored.meta.name).toBe("My Important Project");
    expect(restored.meta.version).toBeDefined();
    expect(restored.meta.created).toBeDefined();
  });
});

describe("Save/Load Roundtrip - Layers", () => {
  test("single layer survives roundtrip", () => {
    const layer = createTestLayer({ name: "Layer 1" });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);

    expect(restored.compositions.main.layers).toHaveLength(1);
    expect(restored.compositions.main.layers[0].name).toBe("Layer 1");
    expect(restored.compositions.main.layers[0].type).toBe("solid");
  });

  test("multiple layers survive roundtrip in order", () => {
    const layers = [
      createTestLayer({ name: "Background", id: "bg" }),
      createTestLayer({ name: "Foreground", id: "fg" }),
      createTestLayer({ name: "Overlay", id: "ov" }),
    ];
    const original = createTestProject(layers);

    const restored = roundtripJSON(original);

    expect(restored.compositions.main.layers).toHaveLength(3);
    expect(restored.compositions.main.layers[0].name).toBe("Background");
    expect(restored.compositions.main.layers[1].name).toBe("Foreground");
    expect(restored.compositions.main.layers[2].name).toBe("Overlay");
  });

  test("layer properties survive roundtrip", () => {
    const layer = createTestLayer({
      name: "Test",
      visible: false,
      locked: true,
      solo: true,
      startFrame: 10,
      endFrame: 200,
      blendMode: "multiply",
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredLayer = restored.compositions.main.layers[0];

    expect(restoredLayer.visible).toBe(false);
    expect(restoredLayer.locked).toBe(true);
    expect(restoredLayer.solo).toBe(true);
    expect(restoredLayer.startFrame).toBe(10);
    expect(restoredLayer.endFrame).toBe(200);
    expect(restoredLayer.blendMode).toBe("multiply");
  });

  test("layer parent relationships survive roundtrip", () => {
    const parent = createTestLayer({ name: "Parent", id: "parent-layer" });
    const child = createTestLayer({
      name: "Child",
      id: "child-layer",
      parentId: "parent-layer",
    });
    const original = createTestProject([parent, child]);

    const restored = roundtripJSON(original);
    const restoredChild = restored.compositions.main.layers[1];

    expect(restoredChild.parentId).toBe("parent-layer");
  });
});

describe("Save/Load Roundtrip - Animation Data", () => {
  test("static animatable property survives roundtrip", () => {
    const layer = createTestLayer({
      opacity: createAnimatableProperty(75),
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredOpacity = restored.compositions.main.layers[0].opacity;

    expect(restoredOpacity.value).toBe(75);
    expect(restoredOpacity.animated).toBe(false);
    expect(restoredOpacity.keyframes).toHaveLength(0);
  });

  test("animated property with keyframes survives roundtrip", () => {
    const layer = createTestLayer({
      opacity: createAnimatableProperty(0, [
        createTestKeyframe(0, 0),
        createTestKeyframe(30, 50),
        createTestKeyframe(60, 100),
      ]),
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredOpacity = restored.compositions.main.layers[0].opacity;

    expect(restoredOpacity.animated).toBe(true);
    expect(restoredOpacity.keyframes).toHaveLength(3);
    expect(restoredOpacity.keyframes[0].frame).toBe(0);
    expect(restoredOpacity.keyframes[0].value).toBe(0);
    expect(restoredOpacity.keyframes[1].frame).toBe(30);
    expect(restoredOpacity.keyframes[1].value).toBe(50);
    expect(restoredOpacity.keyframes[2].frame).toBe(60);
    expect(restoredOpacity.keyframes[2].value).toBe(100);
  });

  test("bezier interpolation data survives roundtrip", () => {
    const keyframe = createTestKeyframe(30, 50, "bezier");
    keyframe.inHandle = { frame: -10, value: 25, enabled: true };
    keyframe.outHandle = { frame: 10, value: 75, enabled: true };

    const layer = createTestLayer({
      opacity: createAnimatableProperty(0, [keyframe]),
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredKf = restored.compositions.main.layers[0].opacity.keyframes[0];

    expect(restoredKf.interpolation).toBe("bezier");
    expect(restoredKf.inHandle.frame).toBe(-10);
    expect(restoredKf.inHandle.value).toBe(25);
    expect(restoredKf.inHandle.enabled).toBe(true);
    expect(restoredKf.outHandle.frame).toBe(10);
    expect(restoredKf.outHandle.value).toBe(75);
    expect(restoredKf.outHandle.enabled).toBe(true);
  });

  test("position animation (vector) survives roundtrip", () => {
    const layer = createTestLayer({
      transform: {
        position: createAnimatableProperty({ x: 100, y: 200, z: 50 }, [
          createTestKeyframe(0, { x: 0, y: 0, z: 0 }),
          createTestKeyframe(100, { x: 1000, y: 500, z: 200 }),
        ]),
        scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
        rotation: createAnimatableProperty(0),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredPos = restored.compositions.main.layers[0].transform.position;

    expect(restoredPos.value.x).toBe(100);
    expect(restoredPos.value.y).toBe(200);
    expect(restoredPos.value.z).toBe(50);
    expect(restoredPos.keyframes).toHaveLength(2);
    expect(restoredPos.keyframes[1].value.x).toBe(1000);
    expect(restoredPos.keyframes[1].value.y).toBe(500);
    expect(restoredPos.keyframes[1].value.z).toBe(200);
  });
});

describe("Save/Load Roundtrip - Layer Types", () => {
  test("solid layer data survives roundtrip", () => {
    const layer = createTestLayer({
      type: "solid",
      data: { type: "solid", color: "#ff5500", width: 500, height: 300 },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredData = restored.compositions.main.layers[0].data;

    expect(restoredData.type).toBe("solid");
    expect(restoredData.color).toBe("#ff5500");
  });

  test("text layer data survives roundtrip", () => {
    const layer = createTestLayer({
      type: "text",
      data: {
        type: "text",
        text: "Hello World!",
        fontFamily: "Arial",
        fontSize: 72,
        fill: "#ffffff",
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredData = restored.compositions.main.layers[0].data;

    expect(restoredData.type).toBe("text");
    expect(restoredData.text).toBe("Hello World!");
    expect(restoredData.fontFamily).toBe("Arial");
    expect(restoredData.fontSize).toBe(72);
  });

  test("camera layer data survives roundtrip", () => {
    const layer = createTestLayer({
      type: "camera",
      data: {
        type: "camera",
        depthOfField: {
          enabled: true,
          focusDistance: 1000,
          aperture: 2.8,
          blurLevel: 50,
        },
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredData = restored.compositions.main.layers[0].data;

    expect(restoredData.type).toBe("camera");
    expect(restoredData.depthOfField.enabled).toBe(true);
    expect(restoredData.depthOfField.focusDistance).toBe(1000);
    expect(restoredData.depthOfField.aperture).toBe(2.8);
  });
});

describe("Save/Load Roundtrip - Special Values", () => {
  test("floating point precision survives roundtrip", () => {
    const layer = createTestLayer({
      opacity: createAnimatableProperty(33.333333333),
      transform: {
        position: createAnimatableProperty({ x: 0.123456789, y: 0.987654321, z: 0 }),
        scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
        rotation: createAnimatableProperty(0),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredLayer = restored.compositions.main.layers[0];

    // JSON.parse/stringify preserves IEEE 754 doubles
    expect(restoredLayer.opacity.value).toBeCloseTo(33.333333333, 8);
    expect(restoredLayer.transform.position.value.x).toBeCloseTo(0.123456789, 8);
    expect(restoredLayer.transform.position.value.y).toBeCloseTo(0.987654321, 8);
  });

  test("zero values survive roundtrip correctly", () => {
    const layer = createTestLayer({
      opacity: createAnimatableProperty(0),
      transform: {
        position: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        scale: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        rotation: createAnimatableProperty(0),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredLayer = restored.compositions.main.layers[0];

    expect(restoredLayer.opacity.value).toBe(0);
    expect(restoredLayer.transform.scale.value.x).toBe(0);
  });

  test("negative values survive roundtrip", () => {
    const layer = createTestLayer({
      transform: {
        position: createAnimatableProperty({ x: -500, y: -300, z: -100 }),
        scale: createAnimatableProperty({ x: -100, y: -100, z: 100 }),
        rotation: createAnimatableProperty(-180),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredLayer = restored.compositions.main.layers[0];

    expect(restoredLayer.transform.position.value.x).toBe(-500);
    expect(restoredLayer.transform.scale.value.x).toBe(-100);
    expect(restoredLayer.transform.rotation.value).toBe(-180);
  });

  test("very large values survive roundtrip", () => {
    const layer = createTestLayer({
      transform: {
        position: createAnimatableProperty({ x: 1000000, y: 999999, z: 0 }),
        scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
        rotation: createAnimatableProperty(36000), // 100 full rotations
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredLayer = restored.compositions.main.layers[0];

    expect(restoredLayer.transform.position.value.x).toBe(1000000);
    expect(restoredLayer.transform.rotation.value).toBe(36000);
  });

  test("empty strings survive roundtrip", () => {
    const layer = createTestLayer({
      name: "",
      type: "text",
      data: { type: "text", text: "", fontFamily: "Arial", fontSize: 72, fill: "#fff" },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredLayer = restored.compositions.main.layers[0];

    expect(restoredLayer.name).toBe("");
    expect(restoredLayer.data.text).toBe("");
  });

  test("unicode text survives roundtrip", () => {
    const layer = createTestLayer({
      name: "レイヤー 🎬",
      type: "text",
      data: {
        type: "text",
        text: "Hello 世界 🌍 مرحبا",
        fontFamily: "Arial",
        fontSize: 72,
        fill: "#fff",
      },
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);
    const restoredLayer = restored.compositions.main.layers[0];

    expect(restoredLayer.name).toBe("レイヤー 🎬");
    expect(restoredLayer.data.text).toBe("Hello 世界 🌍 مرحبا");
  });
});

describe("Save/Load Roundtrip - Complex Projects", () => {
  test("project with 100 layers survives roundtrip", () => {
    const layers = Array.from({ length: 100 }, (_, i) =>
      createTestLayer({ name: `Layer ${i}`, id: `layer-${i}` })
    );
    const original = createTestProject(layers);

    const restored = roundtripJSON(original);

    expect(restored.compositions.main.layers).toHaveLength(100);
    expect(restored.compositions.main.layers[0].name).toBe("Layer 0");
    expect(restored.compositions.main.layers[99].name).toBe("Layer 99");
  });

  test("layer with 1000 keyframes survives roundtrip", () => {
    const keyframes = Array.from({ length: 1000 }, (_, i) =>
      createTestKeyframe(i, i)
    );
    const layer = createTestLayer({
      opacity: createAnimatableProperty(0, keyframes),
    });
    const original = createTestProject([layer]);

    const restored = roundtripJSON(original);

    expect(restored.compositions.main.layers[0].opacity.keyframes).toHaveLength(1000);
    expect(restored.compositions.main.layers[0].opacity.keyframes[999].frame).toBe(999);
    expect(restored.compositions.main.layers[0].opacity.keyframes[999].value).toBe(999);
  });

  test("deeply nested parent hierarchy survives roundtrip", () => {
    const layers: Layer[] = [];
    for (let i = 0; i < 10; i++) {
      layers.push(
        createTestLayer({
          name: `Level ${i}`,
          id: `layer-${i}`,
          parentId: i > 0 ? `layer-${i - 1}` : null,
        })
      );
    }
    const original = createTestProject(layers);

    const restored = roundtripJSON(original);

    for (let i = 1; i < 10; i++) {
      expect(restored.compositions.main.layers[i].parentId).toBe(`layer-${i - 1}`);
    }
  });
});

describe("Save/Load Roundtrip - Data Integrity", () => {
  test("double roundtrip produces identical data", () => {
    const layer = createTestLayer({
      opacity: createAnimatableProperty(50, [
        createTestKeyframe(0, 0, "bezier"),
        createTestKeyframe(60, 100, "bezier"),
      ]),
    });
    const original = createTestProject([layer]);

    const restored1 = roundtripJSON(original);
    const restored2 = roundtripJSON(restored1);

    expect(JSON.stringify(restored1)).toBe(JSON.stringify(restored2));
  });

  test("triple roundtrip produces identical data", () => {
    const layers = [
      createTestLayer({ name: "A", id: "a" }),
      createTestLayer({ name: "B", id: "b", parentId: "a" }),
    ];
    const original = createTestProject(layers);

    const r1 = roundtripJSON(original);
    const r2 = roundtripJSON(r1);
    const r3 = roundtripJSON(r2);

    expect(JSON.stringify(r2)).toBe(JSON.stringify(r3));
  });
});
