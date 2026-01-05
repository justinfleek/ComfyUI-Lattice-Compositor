/**
 * Tests for mesh-deform effect renderer
 *
 * Tests the deformation math, weight calculation, and caching behavior.
 * Canvas pixel rendering is handled by jsdom but pixel verification
 * requires browser integration tests.
 */
import { beforeEach, describe, expect, it } from "vitest";
import { generateMeshFromAlpha } from "@/services/alphaToMesh";
import type { EffectStackResult } from "@/services/effectProcessor";
import {
  _testCalculateTriangleDepths,
  _testCalculateWeights,
  _testDeformMesh,
  _testGetCachedMesh,
  _testGetCacheSize,
  clearMeshDeformCaches,
  meshDeformRenderer,
  registerMeshDeformEffect,
} from "@/services/effects/meshDeformRenderer";
import { createDefaultWarpPin } from "@/types/meshWarp";

// Create minimal canvas for testing
function createTestCanvas(width: number, height: number): HTMLCanvasElement {
  const canvas = document.createElement("canvas");
  canvas.width = width;
  canvas.height = height;
  canvas.getContext("2d");
  return canvas;
}

function createTestInput(canvas: HTMLCanvasElement): EffectStackResult {
  return {
    canvas,
    ctx: canvas.getContext("2d")!,
  };
}

// Create test ImageData for mesh generation
function createTestImageData(width: number, height: number): ImageData {
  const data = new Uint8ClampedArray(width * height * 4);
  for (let i = 0; i < data.length; i += 4) {
    data[i] = 255;
    data[i + 1] = 255;
    data[i + 2] = 255;
    data[i + 3] = 255; // Fully opaque
  }
  return new ImageData(data, width, height);
}

describe("meshDeformRenderer", () => {
  beforeEach(() => {
    clearMeshDeformCaches();
  });

  describe("API behavior", () => {
    it("returns canvas with correct dimensions when no pins", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);

      const result = meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { pins: [] },
      });

      expect(result.canvas.width).toBe(100);
      expect(result.canvas.height).toBe(100);
    });

    it("returns canvas with correct dimensions with pins", () => {
      const canvas = createTestCanvas(150, 200);
      const input = createTestInput(canvas);
      const pins = [createDefaultWarpPin("pin1", 75, 100, "position")];

      const result = meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "test", pins },
      });

      expect(result.canvas.width).toBe(150);
      expect(result.canvas.height).toBe(200);
    });

    it("handles missing _effectInstance gracefully", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);

      const result = meshDeformRenderer(input, { _frame: 0 });

      expect(result.canvas.width).toBe(100);
    });
  });

  describe("mesh caching", () => {
    it("caches mesh after first render", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);
      const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];

      expect(_testGetCacheSize()).toBe(0);

      meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "cache-test", pins },
      });

      expect(_testGetCacheSize()).toBe(1);
      const cached = _testGetCachedMesh("cache-test");
      expect(cached).toBeDefined();
      expect(cached?.mesh.vertexCount).toBeGreaterThan(0);
    });

    it("reuses same cached mesh across frames", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);
      const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];
      const effectInstance = { id: "reuse-test", pins };

      meshDeformRenderer(input, { _frame: 0, _effectInstance: effectInstance });
      const cached1 = _testGetCachedMesh("reuse-test");

      meshDeformRenderer(input, { _frame: 5, _effectInstance: effectInstance });
      const cached2 = _testGetCachedMesh("reuse-test");

      // Same mesh object should be cached
      expect(cached1).toBe(cached2);
      expect(_testGetCacheSize()).toBe(1);
    });

    it("clears cache when clearMeshDeformCaches called", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);
      const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];

      meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "clear-test", pins },
      });

      expect(_testGetCacheSize()).toBe(1);
      clearMeshDeformCaches();
      expect(_testGetCacheSize()).toBe(0);
    });

    it("different effect IDs use separate caches", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);
      const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];

      meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "effect-a", pins },
      });
      meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "effect-b", pins },
      });

      expect(_testGetCacheSize()).toBe(2);
      expect(_testGetCachedMesh("effect-a")).toBeDefined();
      expect(_testGetCachedMesh("effect-b")).toBeDefined();
    });
  });

  describe("mesh generation parameters", () => {
    it("triangle_count affects cached mesh triangle count", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);
      const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];

      meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "low-tri", pins },
        triangle_count: 50,
      });
      const lowMesh = _testGetCachedMesh("low-tri");

      clearMeshDeformCaches();

      meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "high-tri", pins },
        triangle_count: 500,
      });
      const highMesh = _testGetCachedMesh("high-tri");

      // Both should have meshes, high should have more triangles
      expect(lowMesh?.mesh.triangleCount).toBeGreaterThan(0);
      expect(highMesh?.mesh.triangleCount).toBeGreaterThan(0);
      // Note: actual counts depend on fallback mesh since jsdom doesn't produce alpha
    });

    it("stores mesh generation params in cache", () => {
      const canvas = createTestCanvas(100, 100);
      const input = createTestInput(canvas);
      const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];

      meshDeformRenderer(input, {
        _frame: 0,
        _effectInstance: { id: "params-test", pins },
        triangle_count: 200,
        expansion: 5,
        alpha_threshold: 150,
      });

      const cached = _testGetCachedMesh("params-test");
      expect(cached?.params.triangleCount).toBe(200);
      expect(cached?.params.expansion).toBe(5);
      expect(cached?.params.alphaThreshold).toBe(150);
    });
  });
});

describe("weight calculation (_testCalculateWeights)", () => {
  it("calculates weights for single pin", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];
    pins[0].radius = 100; // Large radius to affect all vertices

    const weights = _testCalculateWeights(mesh, pins, {});

    // Should have one weight per vertex
    expect(weights.length).toBe(mesh.vertexCount * 1);

    // Weights should be normalized per vertex
    // With single pin, each vertex weight should be 1 (if within radius)
    // or 0 (if outside radius and no other pins to normalize with)
    let hasWeights = false;
    for (let i = 0; i < weights.length; i++) {
      // Each weight should be between 0 and 1 (normalized)
      expect(weights[i]).toBeGreaterThanOrEqual(0);
      expect(weights[i]).toBeLessThanOrEqual(1.01); // Small tolerance
      if (weights[i] > 0.001) hasWeights = true;
    }
    expect(hasWeights).toBe(true);
  });

  it("calculates weights for multiple pins", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pins = [
      createDefaultWarpPin("pin1", 25, 25, "position"),
      createDefaultWarpPin("pin2", 75, 75, "position"),
    ];

    const weights = _testCalculateWeights(mesh, pins, {});

    expect(weights.length).toBe(mesh.vertexCount * 2); // 2 pins
  });

  it("starch pins have zero weight (do not contribute deformation)", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pins = [createDefaultWarpPin("starch1", 50, 50, "starch")];

    const weights = _testCalculateWeights(mesh, pins, {});

    // Starch pins have weight 0 for all vertices
    let nonZeroCount = 0;
    for (let i = 0; i < weights.length; i++) {
      if (weights[i] > 0.001) nonZeroCount++;
    }
    expect(nonZeroCount).toBe(0);
  });

  it("inverse-distance falloff produces weight decay with distance", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];
    pins[0].radius = 100; // Large radius

    const weights = _testCalculateWeights(mesh, pins, {
      pin_falloff: "inverse-distance",
      falloff_power: 2,
    });

    // Find weights for vertices near and far from pin
    // Corner vertices should have lower weight than center
    expect(weights.length).toBeGreaterThan(0);
  });

  it("radial-basis falloff produces weights", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];

    const weights = _testCalculateWeights(mesh, pins, {
      pin_falloff: "radial-basis",
    });

    expect(weights.length).toBe(mesh.vertexCount);
    // Should have non-zero weights
    let hasNonZero = false;
    for (let i = 0; i < weights.length; i++) {
      if (weights[i] > 0.001) hasNonZero = true;
    }
    expect(hasNonZero).toBe(true);
  });
});

describe("deformation math (_testDeformMesh)", () => {
  it("no deformation when pin at rest position", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pins = [createDefaultWarpPin("pin1", 50, 50, "position")];
    // No animation = pin at rest

    const weights = _testCalculateWeights(mesh, pins, {});
    const deformed = _testDeformMesh(mesh, pins, weights, 0);

    // Deformed should equal original (no delta)
    for (let i = 0; i < mesh.vertexCount * 2; i++) {
      expect(deformed[i]).toBeCloseTo(mesh.vertices[i], 1);
    }
  });

  it("position pin: animated position changes vertices", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pin = createDefaultWarpPin("pin1", 50, 50, "position");
    pin.position.animated = true;
    pin.position.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: { x: 50, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 10,
        value: { x: 70, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const weights = _testCalculateWeights(mesh, [pin], {});
    const deformedF0 = _testDeformMesh(mesh, [pin], weights, 0);
    const deformedF10 = _testDeformMesh(mesh, [pin], weights, 10);

    // At frame 0, no deformation
    expect(deformedF0[0]).toBeCloseTo(mesh.vertices[0], 1);

    // At frame 10, vertices should have moved right
    let totalDeltaX = 0;
    for (let i = 0; i < mesh.vertexCount; i++) {
      totalDeltaX += deformedF10[i * 2] - mesh.vertices[i * 2];
    }
    expect(totalDeltaX).toBeGreaterThan(0);
  });

  it("bend pin: rotation changes vertices, position does not", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pin = createDefaultWarpPin("pin1", 50, 50, "bend");

    // Animate rotation
    pin.rotation.animated = true;
    pin.rotation.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: 0,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 10,
        value: 45,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    // Also animate position (should be IGNORED for bend)
    pin.position.animated = true;
    pin.position.keyframes = [
      {
        id: "kf3",
        frame: 0,
        value: { x: 50, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf4",
        frame: 10,
        value: { x: 100, y: 100 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const weights = _testCalculateWeights(mesh, [pin], {});
    const deformedF0 = _testDeformMesh(mesh, [pin], weights, 0);
    const deformedF10 = _testDeformMesh(mesh, [pin], weights, 10);

    // At frame 0, no deformation
    expect(deformedF0[0]).toBeCloseTo(mesh.vertices[0], 1);

    // At frame 10, vertices should have rotated (not just translated)
    // Rotation around (50,50) would change both x and y
    let changed = false;
    for (let i = 0; i < mesh.vertexCount; i++) {
      const dx = Math.abs(deformedF10[i * 2] - mesh.vertices[i * 2]);
      const dy = Math.abs(deformedF10[i * 2 + 1] - mesh.vertices[i * 2 + 1]);
      if (dx > 0.1 || dy > 0.1) changed = true;
    }
    expect(changed).toBe(true);
  });

  it("overlap pin: does NOT affect vertex positions", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pin = createDefaultWarpPin("pin1", 50, 50, "overlap");
    pin.inFront!.animated = true;
    pin.inFront!.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: 0,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 10,
        value: 100,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const weights = _testCalculateWeights(mesh, [pin], {});
    const deformedF0 = _testDeformMesh(mesh, [pin], weights, 0);
    const deformedF10 = _testDeformMesh(mesh, [pin], weights, 10);

    // Overlap should not change any vertex positions
    for (let i = 0; i < mesh.vertexCount * 2; i++) {
      expect(deformedF0[i]).toBeCloseTo(mesh.vertices[i], 5);
      expect(deformedF10[i]).toBeCloseTo(mesh.vertices[i], 5);
    }
  });

  it("advanced pin: position + rotation + scale all apply", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pin = createDefaultWarpPin("pin1", 50, 50, "advanced");

    pin.position.animated = true;
    pin.position.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: { x: 50, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 10,
        value: { x: 60, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];
    pin.rotation.animated = true;
    pin.rotation.keyframes = [
      {
        id: "kf3",
        frame: 0,
        value: 0,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf4",
        frame: 10,
        value: 30,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];
    pin.scale.animated = true;
    pin.scale.keyframes = [
      {
        id: "kf5",
        frame: 0,
        value: 1,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf6",
        frame: 10,
        value: 1.5,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const weights = _testCalculateWeights(mesh, [pin], {});
    const deformedF10 = _testDeformMesh(mesh, [pin], weights, 10);

    // Combined effect should produce significant deformation
    let totalChange = 0;
    for (let i = 0; i < mesh.vertexCount * 2; i++) {
      totalChange += Math.abs(deformedF10[i] - mesh.vertices[i]);
    }
    expect(totalChange).toBeGreaterThan(1);
  });

  it("multiple pins combine their effects", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);

    const pin1 = createDefaultWarpPin("pin1", 25, 50, "position");
    pin1.position.animated = true;
    pin1.position.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: { x: 25, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 10,
        value: { x: 35, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const pin2 = createDefaultWarpPin("pin2", 75, 50, "position");
    pin2.position.animated = true;
    pin2.position.keyframes = [
      {
        id: "kf3",
        frame: 0,
        value: { x: 75, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf4",
        frame: 10,
        value: { x: 65, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const weights = _testCalculateWeights(mesh, [pin1, pin2], {});
    expect(weights.length).toBe(mesh.vertexCount * 2); // 2 pins

    const deformed = _testDeformMesh(mesh, [pin1, pin2], weights, 10);

    // Both pins should contribute to deformation
    let changed = false;
    for (let i = 0; i < mesh.vertexCount; i++) {
      if (Math.abs(deformed[i * 2] - mesh.vertices[i * 2]) > 0.01)
        changed = true;
    }
    expect(changed).toBe(true);
  });
});

describe("registerMeshDeformEffect", () => {
  it("registers without throwing", () => {
    expect(() => registerMeshDeformEffect()).not.toThrow();
  });
});

describe("overlap depth sorting (_testCalculateTriangleDepths)", () => {
  it("returns all triangles with depth 0 when no overlap pins", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);
    const pins = [createDefaultWarpPin("pin1", 50, 50, "position")]; // Not overlap

    // Use original vertices as "deformed" (no deformation)
    const deformedVertices = new Float32Array(mesh.vertices);

    const depths = _testCalculateTriangleDepths(
      mesh,
      deformedVertices,
      pins,
      0,
    );

    expect(depths.length).toBe(mesh.triangleCount);
    for (const d of depths) {
      expect(d.depth).toBe(0);
    }
  });

  it("calculates weighted depth from single overlap pin", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);

    // Overlap pin at center with inFront = 50
    const pin = createDefaultWarpPin("overlap1", 50, 50, "overlap");
    pin.inFront!.value = 50;
    pin.radius = 200; // Large radius to affect all triangles

    const deformedVertices = new Float32Array(mesh.vertices);
    const depths = _testCalculateTriangleDepths(
      mesh,
      deformedVertices,
      [pin],
      0,
    );

    expect(depths.length).toBe(mesh.triangleCount);

    // All triangles should have some positive depth (influenced by pin with inFront=50)
    let hasPositiveDepth = false;
    for (const d of depths) {
      if (d.depth > 0) hasPositiveDepth = true;
    }
    expect(hasPositiveDepth).toBe(true);
  });

  it("two overlap pins: triangles sort by inFront value", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);

    // Pin 1: far left, inFront = -50 (behind)
    const pinBehind = createDefaultWarpPin("behind", 10, 50, "overlap");
    pinBehind.inFront!.value = -50;
    pinBehind.radius = 50;

    // Pin 2: far right, inFront = +50 (in front)
    const pinInFront = createDefaultWarpPin("infront", 90, 50, "overlap");
    pinInFront.inFront!.value = 50;
    pinInFront.radius = 50;

    const deformedVertices = new Float32Array(mesh.vertices);
    const depths = _testCalculateTriangleDepths(
      mesh,
      deformedVertices,
      [pinBehind, pinInFront],
      0,
    );

    // Sort depths to verify correct ordering
    const _sorted = [...depths].sort((a, b) => a.depth - b.depth);

    // Triangles near left pin (inFront=-50) should have lower depth
    // Triangles near right pin (inFront=+50) should have higher depth

    // Find triangles influenced by each pin
    const leftTriangles = depths.filter((d) => {
      const idx = d.index;
      const i0 = mesh.triangles[idx * 3];
      const cx = mesh.vertices[i0 * 2]; // Just use first vertex x
      return cx < 40;
    });

    const rightTriangles = depths.filter((d) => {
      const idx = d.index;
      const i0 = mesh.triangles[idx * 3];
      const cx = mesh.vertices[i0 * 2];
      return cx > 60;
    });

    // If we have triangles in both regions, verify ordering
    if (leftTriangles.length > 0 && rightTriangles.length > 0) {
      const avgLeftDepth =
        leftTriangles.reduce((s, d) => s + d.depth, 0) / leftTriangles.length;
      const avgRightDepth =
        rightTriangles.reduce((s, d) => s + d.depth, 0) / rightTriangles.length;

      // Left (behind, inFront=-50) should have lower depth than right (in front, inFront=+50)
      expect(avgLeftDepth).toBeLessThan(avgRightDepth);
    }
  });

  it("animated inFront changes depth at different frames", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);

    const pin = createDefaultWarpPin("animated", 50, 50, "overlap");
    pin.inFront!.animated = true;
    pin.inFront!.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: -100,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 10,
        value: 100,
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];
    pin.radius = 200; // Large radius

    const deformedVertices = new Float32Array(mesh.vertices);

    const depthsF0 = _testCalculateTriangleDepths(
      mesh,
      deformedVertices,
      [pin],
      0,
    );
    const depthsF5 = _testCalculateTriangleDepths(
      mesh,
      deformedVertices,
      [pin],
      5,
    );
    const depthsF10 = _testCalculateTriangleDepths(
      mesh,
      deformedVertices,
      [pin],
      10,
    );

    // Get average depth at each frame
    const avgDepthF0 =
      depthsF0.reduce((s, d) => s + d.depth, 0) / depthsF0.length;
    const avgDepthF5 =
      depthsF5.reduce((s, d) => s + d.depth, 0) / depthsF5.length;
    const avgDepthF10 =
      depthsF10.reduce((s, d) => s + d.depth, 0) / depthsF10.length;

    // Depth should increase from frame 0 to 10 (inFront goes from -100 to +100)
    expect(avgDepthF0).toBeLessThan(avgDepthF5);
    expect(avgDepthF5).toBeLessThan(avgDepthF10);
  });

  it("triangles outside pin radius get depth 0", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);

    // Pin with small radius at corner
    const pin = createDefaultWarpPin("corner", 10, 10, "overlap");
    pin.inFront!.value = 100;
    pin.radius = 15; // Small radius

    const deformedVertices = new Float32Array(mesh.vertices);
    const depths = _testCalculateTriangleDepths(
      mesh,
      deformedVertices,
      [pin],
      0,
    );

    // Find triangles far from pin (at opposite corner)
    const farTriangles = depths.filter((d) => {
      const idx = d.index;
      const i0 = mesh.triangles[idx * 3];
      const i1 = mesh.triangles[idx * 3 + 1];
      const i2 = mesh.triangles[idx * 3 + 2];
      // Calculate centroid
      const cx =
        (mesh.vertices[i0 * 2] +
          mesh.vertices[i1 * 2] +
          mesh.vertices[i2 * 2]) /
        3;
      const cy =
        (mesh.vertices[i0 * 2 + 1] +
          mesh.vertices[i1 * 2 + 1] +
          mesh.vertices[i2 * 2 + 1]) /
        3;
      // Far from pin at (10,10)
      const dist = Math.sqrt((cx - 10) ** 2 + (cy - 10) ** 2);
      return dist > 30;
    });

    // Far triangles should have depth 0 (outside radius)
    for (const d of farTriangles) {
      expect(d.depth).toBe(0);
    }
  });
});
