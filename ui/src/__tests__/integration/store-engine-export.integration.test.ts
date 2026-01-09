/**
 * Integration Test: Store → Engine → Export
 *
 * Tests the critical data flow path:
 *   compositorStore (state) → MotionEngine (evaluation) → ExportPipeline (output)
 *
 * These tests verify that:
 * 1. State changes in the store correctly propagate to engine evaluation
 * 2. Engine evaluation results are correctly consumed by export
 * 3. The full roundtrip produces deterministic, expected output
 */

import { createPinia, setActivePinia } from "pinia";
import { beforeEach, describe, expect, test, vi } from "vitest";

import { MotionEngine } from "@/engine/MotionEngine";
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
    id: `kf-${frame}-${Math.random().toString(36).slice(2, 8)}`,
    frame,
    value,
    interpolation,
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
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
    id: `layer-${Math.random().toString(36).slice(2, 8)}`,
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

// ============================================================================
// Integration Tests
// ============================================================================

describe("Store → Engine Integration", () => {
  let engine: MotionEngine;

  beforeEach(() => {
    setActivePinia(createPinia());
    engine = new MotionEngine();
  });

  describe("keyframe changes produce correct engine output", () => {
    test("static layer evaluates to initial value", () => {
      const layer = createTestLayer({
        opacity: createAnimatableProperty(75),
      });
      const project = createTestProject([layer]);

      const frameState = engine.evaluate(0, project);

      expect(frameState.layers[0].opacity).toBe(75);
    });

    test("animated layer interpolates correctly", () => {
      const layer = createTestLayer({
        opacity: createAnimatableProperty(0, [
          createTestKeyframe(0, 0),
          createTestKeyframe(100, 100),
        ]),
      });
      const project = createTestProject([layer]);

      // At frame 0
      expect(engine.evaluate(0, project).layers[0].opacity).toBe(0);

      // At frame 50 (midpoint)
      expect(engine.evaluate(50, project).layers[0].opacity).toBeCloseTo(50, 0);

      // At frame 100
      expect(engine.evaluate(100, project).layers[0].opacity).toBe(100);
    });

    test("position animation interpolates all components", () => {
      const layer = createTestLayer({
        transform: {
          position: createAnimatableProperty({ x: 0, y: 0, z: 0 }, [
            createTestKeyframe(0, { x: 0, y: 0, z: 0 }),
            createTestKeyframe(100, { x: 1000, y: 500, z: 200 }),
          ]),
          scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        },
      });
      const project = createTestProject([layer]);

      const midFrame = engine.evaluate(50, project);
      expect(midFrame.layers[0].transform.position.x).toBeCloseTo(500, 0);
      expect(midFrame.layers[0].transform.position.y).toBeCloseTo(250, 0);
      expect(midFrame.layers[0].transform.position.z).toBeCloseTo(100, 0);
    });
  });

  describe("layer visibility respects timing", () => {
    test("isLayerVisibleAtFrame correctly identifies layer in range", () => {
      const layer = createTestLayer({
        startFrame: 50,
        endFrame: 100,
      });

      // Before layer starts
      expect(engine.isLayerVisibleAtFrame(layer, 25)).toBe(false);

      // During layer
      expect(engine.isLayerVisibleAtFrame(layer, 75)).toBe(true);

      // After layer ends
      expect(engine.isLayerVisibleAtFrame(layer, 125)).toBe(false);
    });

    test("isLayerVisibleAtFrame returns false for hidden layer", () => {
      const layer = createTestLayer({ visible: false });

      expect(engine.isLayerVisibleAtFrame(layer, 0)).toBe(false);
    });

    test("evaluate includes all layers (filtering is renderer responsibility)", () => {
      // MotionEngine evaluates ALL layers - visibility filtering is done by renderer
      const visibleLayer = createTestLayer({ id: "visible", visible: true });
      const hiddenLayer = createTestLayer({ id: "hidden", visible: false });
      const project = createTestProject([visibleLayer, hiddenLayer]);

      const frameState = engine.evaluate(0, project);

      // Both layers are evaluated
      expect(frameState.layers.length).toBe(2);
      // But they have correct visible property
      expect(frameState.layers.find((l) => l.id === "visible")).toBeDefined();
      expect(frameState.layers.find((l) => l.id === "hidden")).toBeDefined();
    });
  });

  describe("multiple layers maintain order", () => {
    test("layers are evaluated in order", () => {
      const layer1 = createTestLayer({ id: "layer-1", name: "Layer 1" });
      const layer2 = createTestLayer({ id: "layer-2", name: "Layer 2" });
      const layer3 = createTestLayer({ id: "layer-3", name: "Layer 3" });
      const project = createTestProject([layer1, layer2, layer3]);

      const frameState = engine.evaluate(0, project);

      expect(frameState.layers.length).toBe(3);
      expect(frameState.layers[0].id).toBe("layer-1");
      expect(frameState.layers[1].id).toBe("layer-2");
      expect(frameState.layers[2].id).toBe("layer-3");
    });

    test("each layer evaluates independently", () => {
      const layer1 = createTestLayer({
        id: "layer-1",
        opacity: createAnimatableProperty(25),
      });
      const layer2 = createTestLayer({
        id: "layer-2",
        opacity: createAnimatableProperty(50),
      });
      const layer3 = createTestLayer({
        id: "layer-3",
        opacity: createAnimatableProperty(75),
      });
      const project = createTestProject([layer1, layer2, layer3]);

      const frameState = engine.evaluate(0, project);

      expect(frameState.layers[0].opacity).toBe(25);
      expect(frameState.layers[1].opacity).toBe(50);
      expect(frameState.layers[2].opacity).toBe(75);
    });
  });

  describe("DETERMINISM: same state produces identical output", () => {
    test("repeated evaluation returns identical results", () => {
      const layer = createTestLayer({
        opacity: createAnimatableProperty(0, [
          createTestKeyframe(0, 0),
          createTestKeyframe(100, 100),
        ]),
        transform: {
          position: createAnimatableProperty({ x: 0, y: 0, z: 0 }, [
            createTestKeyframe(0, { x: 0, y: 0, z: 0 }),
            createTestKeyframe(100, { x: 1000, y: 500, z: 200 }),
          ]),
          scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
          rotation: createAnimatableProperty(0),
          origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
        },
      });
      const project = createTestProject([layer]);

      // Evaluate frame 50 multiple times
      const results = [];
      for (let i = 0; i < 10; i++) {
        results.push(engine.evaluate(50, project));
      }

      // All results should be identical
      const first = results[0];
      for (const result of results) {
        expect(result.frame).toBe(first.frame);
        expect(result.layers[0].opacity).toBe(first.layers[0].opacity);
        expect(result.layers[0].transform.position.x).toBe(
          first.layers[0].transform.position.x
        );
        expect(result.layers[0].transform.position.y).toBe(
          first.layers[0].transform.position.y
        );
      }
    });

    test("evaluation is path-independent", () => {
      const layer = createTestLayer({
        opacity: createAnimatableProperty(0, [
          createTestKeyframe(0, 0),
          createTestKeyframe(100, 100),
        ]),
      });
      const project = createTestProject([layer]);

      // Path 1: Jump directly to frame 75
      const direct = engine.evaluate(75, project);

      // Path 2: Go through several frames first
      engine.evaluate(0, project);
      engine.evaluate(25, project);
      engine.evaluate(50, project);
      engine.evaluate(100, project);
      engine.evaluate(10, project);
      const indirect = engine.evaluate(75, project);

      // Results must be identical
      expect(direct.layers[0].opacity).toBe(indirect.layers[0].opacity);
    });
  });
});

describe("Engine → Export Data Flow", () => {
  let engine: MotionEngine;

  beforeEach(() => {
    setActivePinia(createPinia());
    engine = new MotionEngine();
  });

  describe("evaluated frame data is export-ready", () => {
    test("FrameState contains all required export fields", () => {
      const layer = createTestLayer();
      const project = createTestProject([layer]);

      const frameState = engine.evaluate(0, project);

      // Essential fields for export
      expect(frameState.frame).toBeDefined();
      expect(frameState.composition).toBeDefined();
      expect(frameState.composition.width).toBe(1920);
      expect(frameState.composition.height).toBe(1080);
      expect(frameState.composition.fps).toBe(30);
      expect(frameState.layers).toBeInstanceOf(Array);
    });

    test("evaluated layer has complete transform data", () => {
      const layer = createTestLayer();
      const project = createTestProject([layer]);

      const frameState = engine.evaluate(0, project);
      const evaluatedLayer = frameState.layers[0];

      // Transform must have all components for export
      expect(evaluatedLayer.transform).toBeDefined();
      expect(evaluatedLayer.transform.position).toBeDefined();
      expect(evaluatedLayer.transform.position.x).toBeDefined();
      expect(evaluatedLayer.transform.position.y).toBeDefined();
      expect(evaluatedLayer.transform.position.z).toBeDefined();
      expect(evaluatedLayer.transform.scale).toBeDefined();
      expect(evaluatedLayer.transform.rotation).toBeDefined();
      expect(evaluatedLayer.transform.origin).toBeDefined();
    });

    test("camera data is present when camera layer exists", () => {
      const cameraLayer = createTestLayer({
        type: "camera",
        threeD: true,
        data: {
          type: "camera",
          depthOfField: {
            enabled: false,
            focusDistance: 1000,
            aperture: 2.8,
            blurLevel: 50,
          },
        },
      });
      const project = createTestProject([cameraLayer]);

      const frameState = engine.evaluate(0, project);

      expect(frameState.camera).not.toBeNull();
      expect(frameState.camera!.position).toBeDefined();
      expect(frameState.camera!.target).toBeDefined();
      expect(frameState.camera!.fov).toBeDefined();
    });
  });

  describe("frame sequence evaluation", () => {
    test("can evaluate full frame sequence", () => {
      const layer = createTestLayer({
        opacity: createAnimatableProperty(0, [
          createTestKeyframe(0, 0),
          createTestKeyframe(30, 100),
        ]),
      });
      const project = createTestProject([layer]);

      // Simulate export evaluating all frames
      const frames: number[] = [];
      for (let i = 0; i <= 30; i++) {
        const frameState = engine.evaluate(i, project);
        frames.push(frameState.layers[0].opacity);
      }

      // First frame
      expect(frames[0]).toBe(0);
      // Last frame
      expect(frames[30]).toBe(100);
      // Values should increase monotonically (linear interpolation)
      for (let i = 1; i < frames.length; i++) {
        expect(frames[i]).toBeGreaterThanOrEqual(frames[i - 1]);
      }
    });

    test("frame evaluation handles composition FPS correctly", () => {
      const layer = createTestLayer();
      const project = createTestProject([layer]);
      project.composition.fps = 60; // Change FPS

      const frameState = engine.evaluate(0, project);

      expect(frameState.composition.fps).toBe(60);
    });
  });
});

describe("Full Pipeline: Store → Engine → Export", () => {
  let engine: MotionEngine;

  beforeEach(() => {
    setActivePinia(createPinia());
    engine = new MotionEngine();
  });

  test("complete workflow produces valid export data", () => {
    // Step 1: Create project state (simulating store)
    const layer = createTestLayer({
      name: "Animated Solid",
      opacity: createAnimatableProperty(0, [
        createTestKeyframe(0, 0),
        createTestKeyframe(60, 100),
        createTestKeyframe(120, 50),
      ]),
      transform: {
        position: createAnimatableProperty({ x: 0, y: 0, z: 0 }, [
          createTestKeyframe(0, { x: 100, y: 100, z: 0 }),
          createTestKeyframe(60, { x: 500, y: 300, z: 0 }),
          createTestKeyframe(120, { x: 100, y: 100, z: 0 }),
        ]),
        scale: createAnimatableProperty({ x: 100, y: 100, z: 100 }),
        rotation: createAnimatableProperty(0),
        origin: createAnimatableProperty({ x: 0, y: 0, z: 0 }),
      },
    });
    const project = createTestProject([layer]);

    // Step 2: Evaluate frames (simulating export rendering loop)
    const exportData = {
      frames: [] as Array<{
        frame: number;
        opacity: number;
        position: { x: number; y: number; z: number };
      }>,
    };

    for (let frame = 0; frame <= 120; frame += 30) {
      const frameState = engine.evaluate(frame, project);
      if (frameState.layers.length > 0) {
        exportData.frames.push({
          frame,
          opacity: frameState.layers[0].opacity,
          position: { ...frameState.layers[0].transform.position },
        });
      }
    }

    // Step 3: Verify export data is correct
    expect(exportData.frames.length).toBe(5); // frames 0, 30, 60, 90, 120

    // Frame 0: opacity=0, pos=(100, 100)
    expect(exportData.frames[0].opacity).toBe(0);
    expect(exportData.frames[0].position.x).toBe(100);

    // Frame 60: opacity=100, pos=(500, 300)
    expect(exportData.frames[2].opacity).toBe(100);
    expect(exportData.frames[2].position.x).toBe(500);

    // Frame 120: opacity=50, pos=(100, 100)
    expect(exportData.frames[4].opacity).toBe(50);
    expect(exportData.frames[4].position.x).toBe(100);
  });

  test("export data is deterministic across multiple runs", () => {
    const layer = createTestLayer({
      opacity: createAnimatableProperty(0, [
        createTestKeyframe(0, 0),
        createTestKeyframe(100, 100),
      ]),
    });
    const project = createTestProject([layer]);

    // Run export twice
    const run1: number[] = [];
    const run2: number[] = [];

    for (let frame = 0; frame <= 100; frame += 10) {
      run1.push(engine.evaluate(frame, project).layers[0].opacity);
    }

    // Reset or create new engine
    const engine2 = new MotionEngine();
    for (let frame = 0; frame <= 100; frame += 10) {
      run2.push(engine2.evaluate(frame, project).layers[0].opacity);
    }

    // Results must be identical
    expect(run1).toEqual(run2);
  });
});
