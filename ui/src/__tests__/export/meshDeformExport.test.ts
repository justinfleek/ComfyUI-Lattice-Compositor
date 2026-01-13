/**
 * Mesh Deform Export Tests
 *
 * Tests for mesh deformation data export to AI video generation formats:
 * - Wan-Move/ATI: Pin trajectories as point tracks
 * - ControlNet: Overlap pin depth maps
 * - TTM: Motion masks from deformed mesh
 *
 * CRITICAL: These formats are strictly defined by AI models.
 *
 * @audit P0 CRITICAL - Wan-Move, ATI, TTM format compliance
 */

import { describe, it, expect, beforeEach } from "vitest";
import {
  exportPinsAsTrajectory,
  exportPinsAsTrajectoryWithMetadata,
  exportPinPositionsPerFrame,
  exportOverlapAsDepth,
  exportOverlapDepthSequence,
  exportDeformedMeshMaskBinary,
  type CompositionInfo,
  type DepthFormat,
} from "@/services/export/meshDeformExport";
import type { MeshFromAlphaResult } from "@/services/alphaToMesh";
import type { WarpPin, WarpPinType } from "@/types/meshWarp";
import type { AnimatableProperty, Keyframe } from "@/types/project";

// ============================================================================
// Test Fixtures
// ============================================================================

function createKeyframe<T>(frame: number, value: T): Keyframe<T> {
  return {
    id: `kf-${frame}`,
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
  keyframes: Keyframe<T>[] = []
): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random().toString(36).slice(2, 8)}`,
    name: "test",
    type: "vector2" as any,
    value,
    animated: keyframes.length > 0,
    keyframes,
  };
}

function createMockPin(
  id: string,
  type: WarpPinType,
  position: { x: number; y: number },
  keyframes: Keyframe<{ x: number; y: number }>[] = []
): WarpPin {
  return {
    id,
    name: `Pin ${id}`,
    type,
    position: createAnimatableProperty(position, keyframes),
    radius: 50,
    stiffness: 0.5,
    rotation: createAnimatableProperty(0),
    scale: createAnimatableProperty(1),
    depth: 0,
    selected: false,
  };
}

function createComposition(
  width: number = 1920,
  height: number = 1080,
  frameRate: number = 16
): CompositionInfo {
  return { width, height, frameRate };
}

// ============================================================================
// exportPinsAsTrajectory Tests
// ============================================================================

describe("exportPinsAsTrajectory", () => {
  describe("Trajectory Shape [N][T][2]", () => {
    it("should create tracks with shape [numPins][numFrames][2]", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: 100, y: 200 }),
        createMockPin("pin-2", "position", { x: 300, y: 400 }),
      ];
      const comp = createComposition();

      const result = exportPinsAsTrajectory(pins, [0, 10], comp);

      // 2 pins, 11 frames (0-10 inclusive), 2 coords per point
      expect(result.tracks.length).toBe(2); // N = 2 pins
      expect(result.tracks[0].length).toBe(11); // T = 11 frames
      expect(result.tracks[0][0].length).toBe(2); // 2 = x, y
    });

    it("should have visibility shape [N][T]", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: 100, y: 200 }),
      ];
      const comp = createComposition();

      const result = exportPinsAsTrajectory(pins, [0, 20], comp);

      expect(result.visibility.length).toBe(1); // N = 1 pin
      expect(result.visibility[0].length).toBe(21); // T = 21 frames
    });

    it("should match track and visibility dimensions", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: 100, y: 200 }),
        createMockPin("pin-2", "advanced", { x: 300, y: 400 }),
        createMockPin("pin-3", "rotation", { x: 500, y: 600 }),
      ];
      const comp = createComposition();

      const result = exportPinsAsTrajectory(pins, [5, 25], comp);

      expect(result.tracks.length).toBe(result.visibility.length);
      for (let i = 0; i < result.tracks.length; i++) {
        expect(result.tracks[i].length).toBe(result.visibility[i].length);
      }
    });
  });

  describe("Pin Type Filtering", () => {
    it("should include position pins", () => {
      const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

      expect(result.tracks.length).toBe(1);
    });

    it("should include advanced pins", () => {
      const pins = [createMockPin("pin-1", "advanced", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

      expect(result.tracks.length).toBe(1);
    });

    it("should include bend pins", () => {
      const pins = [createMockPin("pin-1", "bend", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

      expect(result.tracks.length).toBe(1);
    });

    it("should include rotation pins", () => {
      const pins = [createMockPin("pin-1", "rotation", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

      expect(result.tracks.length).toBe(1);
    });

    it("should EXCLUDE starch pins (no trackable position)", () => {
      const pins = [createMockPin("pin-1", "starch", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

      expect(result.tracks.length).toBe(0);
    });

    it("should EXCLUDE overlap pins (no trackable position)", () => {
      const pins = [createMockPin("pin-1", "overlap", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

      expect(result.tracks.length).toBe(0);
    });

    it("should filter mixed pin types correctly", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: 100, y: 200 }),
        createMockPin("pin-2", "starch", { x: 300, y: 400 }),
        createMockPin("pin-3", "advanced", { x: 500, y: 600 }),
        createMockPin("pin-4", "overlap", { x: 700, y: 800 }),
      ];
      const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

      // Only position and advanced pins should be included
      expect(result.tracks.length).toBe(2);
    });
  });

  describe("Coordinate Clamping", () => {
    it("should clamp X coordinates to [0, width-1]", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: -50, y: 500 }),
        createMockPin("pin-2", "position", { x: 2000, y: 500 }),
      ];
      const comp = createComposition(1920, 1080);

      const result = exportPinsAsTrajectory(pins, [0, 0], comp);

      // First pin x should be clamped to 0
      expect(result.tracks[0][0][0]).toBe(0);
      // Second pin x should be clamped to 1919
      expect(result.tracks[1][0][0]).toBe(1919);
    });

    it("should clamp Y coordinates to [0, height-1]", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: 500, y: -100 }),
        createMockPin("pin-2", "position", { x: 500, y: 1200 }),
      ];
      const comp = createComposition(1920, 1080);

      const result = exportPinsAsTrajectory(pins, [0, 0], comp);

      // First pin y should be clamped to 0
      expect(result.tracks[0][0][1]).toBe(0);
      // Second pin y should be clamped to 1079
      expect(result.tracks[1][0][1]).toBe(1079);
    });

    it("should preserve coordinates within bounds", () => {
      const pins = [createMockPin("pin-1", "position", { x: 500, y: 300 })];
      const comp = createComposition(1920, 1080);

      const result = exportPinsAsTrajectory(pins, [0, 0], comp);

      expect(result.tracks[0][0][0]).toBe(500);
      expect(result.tracks[0][0][1]).toBe(300);
    });
  });

  describe("Metadata", () => {
    it("should include correct numPoints", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: 100, y: 200 }),
        createMockPin("pin-2", "position", { x: 300, y: 400 }),
      ];
      const result = exportPinsAsTrajectory(pins, [0, 10], createComposition());

      expect(result.metadata.numPoints).toBe(2);
    });

    it("should include correct numFrames", () => {
      const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [5, 25], createComposition());

      expect(result.metadata.numFrames).toBe(21); // 25 - 5 + 1
    });

    it("should include composition dimensions", () => {
      const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
      const comp = createComposition(1280, 720, 24);

      const result = exportPinsAsTrajectory(pins, [0, 10], comp);

      expect(result.metadata.width).toBe(1280);
      expect(result.metadata.height).toBe(720);
      expect(result.metadata.fps).toBe(24);
    });
  });

  describe("Animation Interpolation", () => {
    it("should interpolate animated pin positions", () => {
      const keyframes = [
        createKeyframe(0, { x: 0, y: 0 }),
        createKeyframe(10, { x: 100, y: 100 }),
      ];
      const pins = [createMockPin("pin-1", "position", { x: 0, y: 0 }, keyframes)];
      const comp = createComposition();

      const result = exportPinsAsTrajectory(pins, [0, 10], comp);

      // Frame 0 should be at (0, 0)
      expect(result.tracks[0][0][0]).toBeCloseTo(0, 0);
      expect(result.tracks[0][0][1]).toBeCloseTo(0, 0);

      // Frame 5 should be interpolated to ~(50, 50)
      expect(result.tracks[0][5][0]).toBeCloseTo(50, 0);
      expect(result.tracks[0][5][1]).toBeCloseTo(50, 0);

      // Frame 10 should be at (100, 100)
      expect(result.tracks[0][10][0]).toBeCloseTo(100, 0);
      expect(result.tracks[0][10][1]).toBeCloseTo(100, 0);
    });

    it("should hold static pin positions across frames", () => {
      const pins = [createMockPin("pin-1", "position", { x: 250, y: 350 })];
      const comp = createComposition();

      const result = exportPinsAsTrajectory(pins, [0, 20], comp);

      // All frames should have the same position
      for (let f = 0; f < 21; f++) {
        expect(result.tracks[0][f][0]).toBe(250);
        expect(result.tracks[0][f][1]).toBe(350);
      }
    });
  });

  describe("Visibility", () => {
    it("should set all visibility to true for pins", () => {
      const pins = [
        createMockPin("pin-1", "position", { x: 100, y: 200 }),
        createMockPin("pin-2", "position", { x: 300, y: 400 }),
      ];
      const result = exportPinsAsTrajectory(pins, [0, 10], createComposition());

      for (const vis of result.visibility) {
        for (const v of vis) {
          expect(v).toBe(true);
        }
      }
    });
  });

  describe("Edge Cases", () => {
    it("should handle empty pins array", () => {
      const result = exportPinsAsTrajectory([], [0, 10], createComposition());

      expect(result.tracks.length).toBe(0);
      expect(result.visibility.length).toBe(0);
      expect(result.metadata.numPoints).toBe(0);
    });

    it("should handle single frame range", () => {
      const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [5, 5], createComposition());

      expect(result.tracks[0].length).toBe(1);
      expect(result.metadata.numFrames).toBe(1);
    });

    it("should handle large frame ranges", () => {
      const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
      const result = exportPinsAsTrajectory(pins, [0, 999], createComposition());

      expect(result.tracks[0].length).toBe(1000);
      expect(result.metadata.numFrames).toBe(1000);
    });
  });
});

// ============================================================================
// exportPinsAsTrajectoryWithMetadata Tests
// ============================================================================

describe("exportPinsAsTrajectoryWithMetadata", () => {
  it("should include all trajectory data", () => {
    const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
    const result = exportPinsAsTrajectoryWithMetadata(pins, [0, 5], createComposition());

    expect(result.tracks).toBeDefined();
    expect(result.visibility).toBeDefined();
    expect(result.metadata).toBeDefined();
  });

  it("should include pinMetadata array", () => {
    const pins = [
      createMockPin("pin-1", "position", { x: 100, y: 200 }),
      createMockPin("pin-2", "advanced", { x: 300, y: 400 }),
    ];
    const result = exportPinsAsTrajectoryWithMetadata(pins, [0, 5], createComposition());

    expect(result.pinMetadata).toBeDefined();
    expect(result.pinMetadata.length).toBe(2);
  });

  it("should include pin id, name, and type in metadata", () => {
    const pin = createMockPin("my-pin-id", "rotation", { x: 100, y: 200 });
    pin.name = "My Custom Pin";

    const result = exportPinsAsTrajectoryWithMetadata([pin], [0, 5], createComposition());

    expect(result.pinMetadata[0].id).toBe("my-pin-id");
    expect(result.pinMetadata[0].name).toBe("My Custom Pin");
    expect(result.pinMetadata[0].type).toBe("rotation");
  });

  it("should only include trackable pins in metadata", () => {
    const pins = [
      createMockPin("pin-1", "position", { x: 100, y: 200 }),
      createMockPin("pin-2", "starch", { x: 300, y: 400 }),
      createMockPin("pin-3", "overlap", { x: 500, y: 600 }),
    ];
    const result = exportPinsAsTrajectoryWithMetadata(pins, [0, 5], createComposition());

    // Only position pin should be in metadata
    expect(result.pinMetadata.length).toBe(1);
    expect(result.pinMetadata[0].id).toBe("pin-1");
  });
});

// ============================================================================
// exportPinPositionsPerFrame Tests
// ============================================================================

describe("exportPinPositionsPerFrame", () => {
  it("should export positions for each frame", () => {
    const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];

    const result = exportPinPositionsPerFrame(pins, [0, 5], 16);

    expect(result.length).toBe(6); // Frames 0-5
    result.forEach((frame, i) => {
      expect(frame.frame).toBe(i);
      expect(frame.positions.length).toBe(1);
    });
  });

  it("should include pin id in position data", () => {
    const pins = [createMockPin("my-pin", "position", { x: 100, y: 200 })];

    const result = exportPinPositionsPerFrame(pins, [0, 2], 16);

    expect(result[0].positions[0].id).toBe("my-pin");
  });

  it("should include x and y coordinates", () => {
    const pins = [createMockPin("pin-1", "position", { x: 150, y: 250 })];

    const result = exportPinPositionsPerFrame(pins, [0, 0], 16);

    expect(result[0].positions[0].x).toBe(150);
    expect(result[0].positions[0].y).toBe(250);
  });

  it("should filter non-trackable pins", () => {
    const pins = [
      createMockPin("pin-1", "position", { x: 100, y: 200 }),
      createMockPin("pin-2", "starch", { x: 300, y: 400 }),
    ];

    const result = exportPinPositionsPerFrame(pins, [0, 0], 16);

    expect(result[0].positions.length).toBe(1);
  });

  it("should interpolate animated positions", () => {
    const keyframes = [
      createKeyframe(0, { x: 0, y: 0 }),
      createKeyframe(10, { x: 200, y: 200 }),
    ];
    const pins = [createMockPin("pin-1", "position", { x: 0, y: 0 }, keyframes)];

    const result = exportPinPositionsPerFrame(pins, [0, 10], 16);

    expect(result[5].positions[0].x).toBeCloseTo(100, 0);
    expect(result[5].positions[0].y).toBeCloseTo(100, 0);
  });
});

// ============================================================================
// Wan-Move Format Compliance Tests
// ============================================================================

describe("Wan-Move Format Compliance", () => {
  it("should produce output compatible with WanMoveTrajectory interface", () => {
    const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
    const result = exportPinsAsTrajectory(pins, [0, 10], createComposition());

    // Verify the structure matches WanMoveTrajectory
    expect(result).toHaveProperty("tracks");
    expect(result).toHaveProperty("visibility");
    expect(result).toHaveProperty("metadata");
    expect(result.metadata).toHaveProperty("numPoints");
    expect(result.metadata).toHaveProperty("numFrames");
    expect(result.metadata).toHaveProperty("width");
    expect(result.metadata).toHaveProperty("height");
    expect(result.metadata).toHaveProperty("fps");
  });

  it("should have coordinate values as numbers", () => {
    const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
    const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

    for (const track of result.tracks) {
      for (const point of track) {
        expect(typeof point[0]).toBe("number");
        expect(typeof point[1]).toBe("number");
        expect(Number.isFinite(point[0])).toBe(true);
        expect(Number.isFinite(point[1])).toBe(true);
      }
    }
  });

  it("should have visibility values as booleans", () => {
    const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
    const result = exportPinsAsTrajectory(pins, [0, 5], createComposition());

    for (const vis of result.visibility) {
      for (const v of vis) {
        expect(typeof v).toBe("boolean");
      }
    }
  });

  it("should have metadata values as numbers", () => {
    const pins = [createMockPin("pin-1", "position", { x: 100, y: 200 })];
    const result = exportPinsAsTrajectory(pins, [0, 10], createComposition());

    expect(typeof result.metadata.numPoints).toBe("number");
    expect(typeof result.metadata.numFrames).toBe("number");
    expect(typeof result.metadata.width).toBe("number");
    expect(typeof result.metadata.height).toBe("number");
    expect(typeof result.metadata.fps).toBe("number");
  });
});

// ============================================================================
// Determinism Tests
// ============================================================================

describe("Determinism", () => {
  it("should produce identical output for identical input", () => {
    const pins = [
      createMockPin("pin-1", "position", { x: 100, y: 200 }),
      createMockPin("pin-2", "advanced", { x: 300, y: 400 }),
    ];
    const comp = createComposition();

    const result1 = exportPinsAsTrajectory(pins, [0, 20], comp);
    const result2 = exportPinsAsTrajectory(pins, [0, 20], comp);

    expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
  });

  it("should produce consistent interpolation results", () => {
    const keyframes = [
      createKeyframe(0, { x: 0, y: 0 }),
      createKeyframe(100, { x: 1000, y: 1000 }),
    ];
    const pins = [createMockPin("pin-1", "position", { x: 0, y: 0 }, keyframes)];
    const comp = createComposition();

    const result1 = exportPinsAsTrajectory(pins, [0, 100], comp);
    const result2 = exportPinsAsTrajectory(pins, [0, 100], comp);

    for (let f = 0; f < 101; f++) {
      expect(result1.tracks[0][f][0]).toBe(result2.tracks[0][f][0]);
      expect(result1.tracks[0][f][1]).toBe(result2.tracks[0][f][1]);
    }
  });
});

// ============================================================================
// Mesh-Based Export Tests
// ============================================================================

function createMockMesh(triangleCount: number = 2): MeshFromAlphaResult {
  // Create a simple 2-triangle mesh (a quad)
  // Triangle 1: (0,0), (100,0), (100,100)
  // Triangle 2: (0,0), (100,100), (0,100)
  const vertices = new Float32Array([
    0, 0,      // vertex 0
    100, 0,    // vertex 1
    100, 100,  // vertex 2
    0, 100,    // vertex 3
  ]);

  const triangles = new Uint32Array([
    0, 1, 2,   // triangle 1
    0, 2, 3,   // triangle 2
  ]);

  return {
    vertices,
    triangles,
    bounds: { x: 0, y: 0, width: 100, height: 100 },
    vertexCount: 4,
    triangleCount: triangleCount,
  };
}

function createDeformedVertices(mesh: MeshFromAlphaResult, offsetX: number = 0, offsetY: number = 0): Float32Array {
  const deformed = new Float32Array(mesh.vertices.length);
  for (let i = 0; i < mesh.vertices.length; i += 2) {
    deformed[i] = mesh.vertices[i] + offsetX;
    deformed[i + 1] = mesh.vertices[i + 1] + offsetY;
  }
  return deformed;
}

// ============================================================================
// exportDeformedMeshMaskBinary Tests
// ============================================================================

describe("exportDeformedMeshMaskBinary", () => {
  it("should return Uint8Array", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);

    const result = exportDeformedMeshMaskBinary(mesh, deformed, 200, 200);

    expect(result instanceof Uint8Array).toBe(true);
  });

  it("should have correct size (width * height)", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);

    const result = exportDeformedMeshMaskBinary(mesh, deformed, 200, 150);

    expect(result.length).toBe(200 * 150);
  });

  it("should contain only 0 or 255 values", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);

    const result = exportDeformedMeshMaskBinary(mesh, deformed, 200, 200);

    for (let i = 0; i < result.length; i++) {
      expect(result[i] === 0 || result[i] === 255).toBe(true);
    }
  });

  it("should mark pixels inside triangles as 255", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);

    const result = exportDeformedMeshMaskBinary(mesh, deformed, 200, 200);

    // Center of the quad (50, 50) should be marked
    const centerIdx = 50 * 200 + 50;
    expect(result[centerIdx]).toBe(255);
  });

  it("should mark pixels outside triangles as 0", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);

    const result = exportDeformedMeshMaskBinary(mesh, deformed, 200, 200);

    // Far corner (150, 150) should be outside the quad
    const outsideIdx = 150 * 200 + 150;
    expect(result[outsideIdx]).toBe(0);
  });

  it("should handle deformed mesh positions", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh, 50, 50); // Offset by 50,50

    const result = exportDeformedMeshMaskBinary(mesh, deformed, 200, 200);

    // Original quad was (0,0) to (100,100)
    // After offset, quad is (50,50) to (150,150)
    // Point (25, 25) should now be outside the deformed quad
    const outsideIdx = 25 * 200 + 25;
    expect(result[outsideIdx]).toBe(0);

    // Point (100, 100) should be inside the deformed quad
    const insideIdx = 100 * 200 + 100;
    expect(result[insideIdx]).toBe(255);
  });
});

// ============================================================================
// exportOverlapAsDepth Tests
// ============================================================================

describe("exportOverlapAsDepth", () => {
  it("should return Uint8Array for uint8 format", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);
    const pins: WarpPin[] = [];

    const result = exportOverlapAsDepth(mesh, deformed, pins, 0, 200, 200, "uint8");

    expect(result instanceof Uint8Array).toBe(true);
    expect(result.length).toBe(200 * 200);
  });

  it("should return Uint16Array for uint16 format", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);
    const pins: WarpPin[] = [];

    const result = exportOverlapAsDepth(mesh, deformed, pins, 0, 200, 200, "uint16");

    expect(result instanceof Uint16Array).toBe(true);
    expect(result.length).toBe(200 * 200);
  });

  it("should return Float32Array for float32 format", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);
    const pins: WarpPin[] = [];

    const result = exportOverlapAsDepth(mesh, deformed, pins, 0, 200, 200, "float32");

    expect(result instanceof Float32Array).toBe(true);
    expect(result.length).toBe(200 * 200);
  });

  it("should return empty (zero) buffer when no overlap pins", () => {
    const mesh = createMockMesh();
    const deformed = createDeformedVertices(mesh);
    const pins: WarpPin[] = [
      createMockPin("pin-1", "position", { x: 50, y: 50 }),
    ];

    const result = exportOverlapAsDepth(mesh, deformed, pins, 0, 100, 100, "uint8");

    // No overlap pins, so all values should be 0
    const sum = Array.from(result).reduce((a: number, b: number) => a + b, 0);
    expect(sum).toBe(0);
  });
});

// ============================================================================
// exportOverlapDepthSequence Tests
// ============================================================================

describe("exportOverlapDepthSequence", () => {
  it("should return array of frame data", () => {
    const mesh = createMockMesh();
    const deformedPerFrame = [
      createDeformedVertices(mesh, 0, 0),
      createDeformedVertices(mesh, 10, 10),
      createDeformedVertices(mesh, 20, 20),
    ];
    const pins: WarpPin[] = [];

    const result = exportOverlapDepthSequence(
      mesh,
      deformedPerFrame,
      pins,
      [0, 2],
      100,
      100,
      "uint8"
    );

    expect(result.length).toBe(3);
  });

  it("should include frame numbers in output", () => {
    const mesh = createMockMesh();
    const deformedPerFrame = [
      createDeformedVertices(mesh, 0, 0),
      createDeformedVertices(mesh, 10, 10),
    ];
    const pins: WarpPin[] = [];

    const result = exportOverlapDepthSequence(
      mesh,
      deformedPerFrame,
      pins,
      [5, 6],
      100,
      100,
      "uint8"
    );

    expect(result[0].frame).toBe(5);
    expect(result[1].frame).toBe(6);
  });

  it("should respect format parameter", () => {
    const mesh = createMockMesh();
    const deformedPerFrame = [createDeformedVertices(mesh)];
    const pins: WarpPin[] = [];

    const resultUint8 = exportOverlapDepthSequence(
      mesh,
      deformedPerFrame,
      pins,
      [0, 0],
      100,
      100,
      "uint8"
    );

    const resultFloat32 = exportOverlapDepthSequence(
      mesh,
      deformedPerFrame,
      pins,
      [0, 0],
      100,
      100,
      "float32"
    );

    expect(resultUint8[0].depth instanceof Uint8Array).toBe(true);
    expect(resultFloat32[0].depth instanceof Float32Array).toBe(true);
  });

  it("should skip frames without deformed vertices", () => {
    const mesh = createMockMesh();
    const deformedPerFrame = [
      createDeformedVertices(mesh),
      undefined as any, // Missing frame
      createDeformedVertices(mesh),
    ];
    const pins: WarpPin[] = [];

    const result = exportOverlapDepthSequence(
      mesh,
      deformedPerFrame,
      pins,
      [0, 2],
      100,
      100
    );

    // Should only have 2 frames (0 and 2), frame 1 is skipped
    expect(result.length).toBe(2);
    expect(result[0].frame).toBe(0);
    expect(result[1].frame).toBe(2);
  });
});
