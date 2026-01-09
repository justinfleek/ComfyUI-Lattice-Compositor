/**
 * Tests for mesh deform export functions
 * Verifies trajectory, depth, and mask export for AI video tools
 */
import { describe, expect, it } from "vitest";
import { generateMeshFromAlpha } from "@/services/alphaToMesh";
import {
  depthBufferToImageData,
  exportDeformedMeshMask,
  exportDeformedMeshMaskBinary,
  exportOverlapAsDepth,
  exportPinPositionsPerFrame,
  exportPinsAsTrajectory,
  exportPinsAsTrajectoryWithMetadata,
} from "@/services/export/meshDeformExport";
import { createDefaultWarpPin } from "@/types/meshWarp";

// Helper to create test ImageData
function createTestImageData(width: number, height: number): ImageData {
  const data = new Uint8ClampedArray(width * height * 4);
  for (let i = 0; i < data.length; i += 4) {
    data[i] = 255;
    data[i + 1] = 255;
    data[i + 2] = 255;
    data[i + 3] = 255;
  }
  return new ImageData(data, width, height);
}

describe("exportPinsAsTrajectory", () => {
  const defaultComposition = { width: 100, height: 100, frameRate: 30 };

  it("exports single static pin as trajectory", () => {
    const pin = createDefaultWarpPin("pin1", 50, 50, "position");
    const result = exportPinsAsTrajectory([pin], [0, 9], defaultComposition);

    expect(result.tracks.length).toBe(1);
    expect(result.tracks[0].length).toBe(10); // 10 frames
    expect(result.visibility.length).toBe(1);
    expect(result.visibility[0].length).toBe(10);

    // Static pin should have same position for all frames
    for (const pos of result.tracks[0]) {
      expect(pos[0]).toBe(50);
      expect(pos[1]).toBe(50);
    }

    // All frames visible
    for (const vis of result.visibility[0]) {
      expect(vis).toBe(true);
    }
  });

  it("exports animated pin position changes", () => {
    const pin = createDefaultWarpPin("pin1", 0, 50, "position");
    pin.position.animated = true;
    pin.position.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: { x: 0, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 10,
        value: { x: 100, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const result = exportPinsAsTrajectory([pin], [0, 10], defaultComposition);

    // Frame 0: x=0
    expect(result.tracks[0][0][0]).toBeCloseTo(0, 1);
    // Frame 5: x=50 (linear interpolation)
    expect(result.tracks[0][5][0]).toBeCloseTo(50, 1);
    // Frame 10: x=100
    expect(result.tracks[0][10][0]).toBeCloseTo(99, 1); // Clamped to width-1
  });

  it("exports multiple pins as separate tracks", () => {
    const pin1 = createDefaultWarpPin("pin1", 25, 25, "position");
    const pin2 = createDefaultWarpPin("pin2", 75, 75, "position");

    const result = exportPinsAsTrajectory(
      [pin1, pin2],
      [0, 4],
      defaultComposition,
    );

    expect(result.tracks.length).toBe(2);
    expect(result.metadata.numPoints).toBe(2);
    expect(result.metadata.numFrames).toBe(5);

    // Track 1 at (25, 25)
    expect(result.tracks[0][0]).toEqual([25, 25]);
    // Track 2 at (75, 75)
    expect(result.tracks[1][0]).toEqual([75, 75]);
  });

  it("filters out starch and overlap pins", () => {
    const positionPin = createDefaultWarpPin("pos", 50, 50, "position");
    const starchPin = createDefaultWarpPin("starch", 30, 30, "starch");
    const overlapPin = createDefaultWarpPin("overlap", 70, 70, "overlap");

    const result = exportPinsAsTrajectory(
      [positionPin, starchPin, overlapPin],
      [0, 4],
      defaultComposition,
    );

    // Only position pin should be exported
    expect(result.tracks.length).toBe(1);
    expect(result.metadata.numPoints).toBe(1);
  });

  it("includes bend and advanced pins", () => {
    const bendPin = createDefaultWarpPin("bend", 40, 40, "bend");
    const advancedPin = createDefaultWarpPin("advanced", 60, 60, "advanced");

    const result = exportPinsAsTrajectory(
      [bendPin, advancedPin],
      [0, 4],
      defaultComposition,
    );

    expect(result.tracks.length).toBe(2);
    expect(result.tracks[0][0]).toEqual([40, 40]);
    expect(result.tracks[1][0]).toEqual([60, 60]);
  });

  it("clamps coordinates to composition bounds", () => {
    const pin = createDefaultWarpPin("pin1", 150, -20, "position"); // Out of bounds

    const result = exportPinsAsTrajectory([pin], [0, 0], defaultComposition);

    // Should be clamped to valid range [0, width-1] and [0, height-1]
    expect(result.tracks[0][0][0]).toBe(99); // max x = 99
    expect(result.tracks[0][0][1]).toBe(0); // min y = 0
  });

  it("exports correct metadata", () => {
    const pin = createDefaultWarpPin("pin1", 50, 50, "position");
    const comp = { width: 1920, height: 1080, frameRate: 24 };

    const result = exportPinsAsTrajectory([pin], [0, 23], comp);

    expect(result.metadata.width).toBe(1920);
    expect(result.metadata.height).toBe(1080);
    expect(result.metadata.fps).toBe(24);
    expect(result.metadata.numFrames).toBe(24);
    expect(result.metadata.numPoints).toBe(1);
  });

  it("returns empty trajectory for no trackable pins", () => {
    const starchPin = createDefaultWarpPin("starch", 50, 50, "starch");

    const result = exportPinsAsTrajectory(
      [starchPin],
      [0, 9],
      defaultComposition,
    );

    expect(result.tracks.length).toBe(0);
    expect(result.visibility.length).toBe(0);
    expect(result.metadata.numPoints).toBe(0);
  });
});

describe("exportPinsAsTrajectoryWithMetadata", () => {
  it("includes pin metadata in export", () => {
    const pin1 = createDefaultWarpPin("pin-a", 25, 25, "position");
    pin1.name = "Left Arm";
    const pin2 = createDefaultWarpPin("pin-b", 75, 75, "bend");
    pin2.name = "Elbow Joint";

    const result = exportPinsAsTrajectoryWithMetadata([pin1, pin2], [0, 4], {
      width: 100,
      height: 100,
      frameRate: 30,
    });

    expect(result.pinMetadata.length).toBe(2);
    expect(result.pinMetadata[0]).toEqual({
      id: "pin-a",
      name: "Left Arm",
      type: "position",
    });
    expect(result.pinMetadata[1]).toEqual({
      id: "pin-b",
      name: "Elbow Joint",
      type: "bend",
    });
  });
});

describe("exportOverlapAsDepth", () => {
  it("returns zero depth when no overlap pins", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);
    const positionPin = createDefaultWarpPin("pos", 25, 25, "position");

    const depth = exportOverlapAsDepth(
      mesh,
      deformed,
      [positionPin],
      0,
      50,
      50,
      "uint8",
    );

    expect(depth).toBeInstanceOf(Uint8Array);
    expect(depth.length).toBe(50 * 50);

    // All zeros (no overlap influence)
    let sum = 0;
    for (let i = 0; i < depth.length; i++) sum += depth[i];
    expect(sum).toBe(0);
  });

  it("generates depth from overlap pin inFront value", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const overlapPin = createDefaultWarpPin("overlap1", 25, 25, "overlap");
    overlapPin.inFront!.value = 100; // Maximum front
    overlapPin.radius = 100; // Large radius

    const depth = exportOverlapAsDepth(
      mesh,
      deformed,
      [overlapPin],
      0,
      50,
      50,
      "uint8",
    );

    // Should have non-zero values where triangles exist
    let maxDepth = 0;
    for (let i = 0; i < depth.length; i++) {
      if (depth[i] > maxDepth) maxDepth = depth[i];
    }
    expect(maxDepth).toBeGreaterThan(200); // Near 255 for inFront=100
  });

  it("maps inFront -100 to low depth values", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const overlapPin = createDefaultWarpPin("overlap1", 25, 25, "overlap");
    overlapPin.inFront!.value = -100; // Maximum back
    overlapPin.radius = 100;

    const depth = exportOverlapAsDepth(
      mesh,
      deformed,
      [overlapPin],
      0,
      50,
      50,
      "uint8",
    );

    // All values should be 0 (inFront=-100 maps to depth=0)
    let maxDepth = 0;
    for (let i = 0; i < depth.length; i++) {
      if (depth[i] > maxDepth) maxDepth = depth[i];
    }
    expect(maxDepth).toBeLessThan(10); // Near 0
  });

  it("supports uint16 format", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const overlapPin = createDefaultWarpPin("overlap1", 25, 25, "overlap");
    overlapPin.inFront!.value = 100;
    overlapPin.radius = 100;

    const depth = exportOverlapAsDepth(
      mesh,
      deformed,
      [overlapPin],
      0,
      50,
      50,
      "uint16",
    );

    expect(depth).toBeInstanceOf(Uint16Array);
    expect(depth.length).toBe(50 * 50);

    let maxDepth = 0;
    for (let i = 0; i < depth.length; i++) {
      if (depth[i] > maxDepth) maxDepth = depth[i];
    }
    expect(maxDepth).toBeGreaterThan(60000); // Near 65535
  });

  it("supports float32 format", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const overlapPin = createDefaultWarpPin("overlap1", 25, 25, "overlap");
    overlapPin.inFront!.value = 50; // Middle value
    overlapPin.radius = 100;

    const depth = exportOverlapAsDepth(
      mesh,
      deformed,
      [overlapPin],
      0,
      50,
      50,
      "float32",
    );

    expect(depth).toBeInstanceOf(Float32Array);

    let maxDepth = 0;
    for (let i = 0; i < depth.length; i++) {
      if (depth[i] > maxDepth) maxDepth = depth[i];
    }
    // inFront=50 maps to (50+100)/200 = 0.75
    expect(maxDepth).toBeGreaterThan(0.7);
    expect(maxDepth).toBeLessThan(0.8);
  });

  it("respects animated inFront at different frames", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const overlapPin = createDefaultWarpPin("overlap1", 25, 25, "overlap");
    overlapPin.inFront!.animated = true;
    overlapPin.inFront!.keyframes = [
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
    overlapPin.radius = 100;

    const depthF0 = exportOverlapAsDepth(
      mesh,
      deformed,
      [overlapPin],
      0,
      50,
      50,
      "uint8",
    );
    const depthF10 = exportOverlapAsDepth(
      mesh,
      deformed,
      [overlapPin],
      10,
      50,
      50,
      "uint8",
    );

    const maxF0 = Math.max(...Array.from(depthF0));
    const maxF10 = Math.max(...Array.from(depthF10));

    // Frame 0 should have low depth, frame 10 should have high depth
    expect(maxF10).toBeGreaterThan(maxF0 + 100);
  });
});

describe("depthBufferToImageData", () => {
  it("converts uint8 to ImageData", () => {
    const depth = new Uint8Array([0, 128, 255, 64]);
    const result = depthBufferToImageData(depth, 2, 2);

    expect(result.width).toBe(2);
    expect(result.height).toBe(2);
    expect(result.data[0]).toBe(0); // R
    expect(result.data[4]).toBe(128); // Second pixel R
    expect(result.data[8]).toBe(255); // Third pixel R
    expect(result.data[3]).toBe(255); // Alpha = 255
  });

  it("converts float32 to ImageData", () => {
    const depth = new Float32Array([0, 0.5, 1.0, 0.25]);
    const result = depthBufferToImageData(depth, 2, 2);

    expect(result.data[0]).toBe(0);
    expect(result.data[4]).toBe(128); // 0.5 * 255 rounded
    expect(result.data[8]).toBe(255);
    expect(result.data[12]).toBe(64); // 0.25 * 255 rounded
  });
});

describe("exportDeformedMeshMask", () => {
  it("generates white mask where mesh exists", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const mask = exportDeformedMeshMask(mesh, deformed, 50, 50);

    expect(mask.width).toBe(50);
    expect(mask.height).toBe(50);

    // Should have white pixels where triangles rasterize
    let whiteCount = 0;
    let blackCount = 0;
    for (let i = 0; i < mask.data.length; i += 4) {
      if (mask.data[i] === 255) whiteCount++;
      else blackCount++;
    }

    // Most of the 50x50 area should be covered by the mesh
    expect(whiteCount).toBeGreaterThan(blackCount);
  });

  it("respects deformed vertex positions", () => {
    const imageData = createTestImageData(100, 100);
    const mesh = generateMeshFromAlpha(imageData);

    // Move all vertices 25px right
    const deformed = new Float32Array(mesh.vertices.length);
    for (let i = 0; i < mesh.vertexCount; i++) {
      deformed[i * 2] = mesh.vertices[i * 2] + 25;
      deformed[i * 2 + 1] = mesh.vertices[i * 2 + 1];
    }

    const mask = exportDeformedMeshMask(mesh, deformed, 100, 100);

    // Check left edge (should be black due to shift)
    let leftEdgeWhite = 0;
    for (let y = 0; y < 100; y++) {
      if (mask.data[y * 100 * 4] === 255) leftEdgeWhite++;
    }

    // Check center-right (should have white)
    let centerRightWhite = 0;
    for (let y = 0; y < 100; y++) {
      const x = 60;
      if (mask.data[(y * 100 + x) * 4] === 255) centerRightWhite++;
    }

    expect(centerRightWhite).toBeGreaterThan(leftEdgeWhite);
  });

  it("handles empty mesh gracefully", () => {
    const emptyMesh = {
      vertices: new Float32Array(0),
      triangles: new Uint32Array(0),
      vertexCount: 0,
      triangleCount: 0,
      bounds: { x: 0, y: 0, width: 100, height: 100 },
    };

    const mask = exportDeformedMeshMask(
      emptyMesh,
      new Float32Array(0),
      100,
      100,
    );

    // Should be all black
    let whiteCount = 0;
    for (let i = 0; i < mask.data.length; i += 4) {
      if (mask.data[i] === 255) whiteCount++;
    }
    expect(whiteCount).toBe(0);
  });
});

describe("exportDeformedMeshMaskBinary", () => {
  it("returns Uint8Array with 0 and 255 values", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const mask = exportDeformedMeshMaskBinary(mesh, deformed, 50, 50);

    expect(mask).toBeInstanceOf(Uint8Array);
    expect(mask.length).toBe(50 * 50);

    // Only 0 or 255 values
    for (let i = 0; i < mask.length; i++) {
      expect(mask[i] === 0 || mask[i] === 255).toBe(true);
    }
  });

  it("produces same coverage as ImageData version", () => {
    const imageData = createTestImageData(50, 50);
    const mesh = generateMeshFromAlpha(imageData);
    const deformed = new Float32Array(mesh.vertices);

    const binaryMask = exportDeformedMeshMaskBinary(mesh, deformed, 50, 50);
    const imageDataMask = exportDeformedMeshMask(mesh, deformed, 50, 50);

    // Count white pixels in both
    let binaryWhite = 0;
    let imageDataWhite = 0;

    for (let i = 0; i < 50 * 50; i++) {
      if (binaryMask[i] === 255) binaryWhite++;
      if (imageDataMask.data[i * 4] === 255) imageDataWhite++;
    }

    expect(binaryWhite).toBe(imageDataWhite);
  });
});

describe("exportPinPositionsPerFrame", () => {
  it("exports positions with pin IDs", () => {
    const pin1 = createDefaultWarpPin("arm", 25, 25, "position");
    const pin2 = createDefaultWarpPin("leg", 75, 75, "position");

    const result = exportPinPositionsPerFrame([pin1, pin2], [0, 2], 30);

    expect(result.length).toBe(3); // 3 frames
    expect(result[0].frame).toBe(0);
    expect(result[0].positions.length).toBe(2);
    expect(result[0].positions[0]).toEqual({ id: "arm", x: 25, y: 25 });
    expect(result[0].positions[1]).toEqual({ id: "leg", x: 75, y: 75 });
  });

  it("tracks animated positions correctly", () => {
    const pin = createDefaultWarpPin("moving", 0, 50, "position");
    pin.position.animated = true;
    pin.position.keyframes = [
      {
        id: "kf1",
        frame: 0,
        value: { x: 0, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
      {
        id: "kf2",
        frame: 4,
        value: { x: 100, y: 50 },
        interpolation: "linear" as const,
        inHandle: { frame: -5, value: 0, enabled: false },
        outHandle: { frame: 5, value: 0, enabled: false },
        controlMode: "smooth" as const,
      },
    ];

    const result = exportPinPositionsPerFrame([pin], [0, 4], 30);

    expect(result[0].positions[0].x).toBeCloseTo(0, 1);
    expect(result[2].positions[0].x).toBeCloseTo(50, 1); // Midpoint
    expect(result[4].positions[0].x).toBeCloseTo(100, 1);
  });
});
