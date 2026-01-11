/**
 * Regression Tests for OLD Export Functions
 *
 * These tests capture the CURRENT (broken) output format of the old export functions.
 * They are designed to FAIL after Step 4 (wiring new Kijai-compatible functions),
 * proving that the migration correctly changed the output format.
 *
 * OLD FORMAT (these tests verify):
 * - exportWanMoveTrajectories: Returns [x, y] arrays, NOT {x, y} objects
 * - exportATITrajectory: Returns semantic type ("pan", "free"), NOT 121 fixed frames
 * - exportCameraTrajectory: Returns 4x4 matrices, NOT CameraCtrl poses
 *
 * NEW FORMAT (Kijai-compatible, after migration):
 * - WanMove: [[{x, y}, ...], ...] with {x, y} objects
 * - ATI: Exactly 121 frames, raw pixel coordinates
 * - CameraCtrl: "time fx fy cx cy aspect flag1 flag2 w2c[12]" text format
 *
 * @see PHASE_1_EXECUTION_PLAN.md for migration details
 */

import { describe, it, expect } from "vitest";
import {
  exportWanMoveTrajectories,
  exportATITrajectory,
  exportCameraTrajectory,
  type PointTrajectory,
} from "@/services/modelExport";
import type { Camera3D } from "@/types/camera";

// ============================================================================
// TEST FIXTURES
// ============================================================================

/**
 * Create a simple trajectory for testing
 */
function createTestTrajectory(
  id: string,
  frames: number,
  startX: number = 100,
  startY: number = 100,
  deltaX: number = 10,
  deltaY: number = 5
): PointTrajectory {
  const points: PointTrajectory["points"] = [];
  const visibility: boolean[] = [];

  for (let f = 0; f < frames; f++) {
    points.push({
      frame: f,
      x: startX + f * deltaX,
      y: startY + f * deltaY,
    });
    visibility.push(true);
  }

  return { id, points, visibility };
}

/**
 * Create a test camera
 */
function createTestCamera(
  posX: number = 0,
  posY: number = 0,
  posZ: number = 500
): Camera3D {
  return {
    id: "test-camera",
    name: "Test Camera",
    type: "one-node",
    position: { x: posX, y: posY, z: posZ },
    pointOfInterest: { x: 0, y: 0, z: 0 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    zoom: 1778,
    focalLength: 50,
    angleOfView: 39.6,
    filmSize: 36,
    measureFilmSize: "horizontal",
    depthOfField: {
      enabled: false,
      focusDistance: 1000,
      aperture: 50,
      fStop: 2.8,
      blurLevel: 1,
      lockToZoom: false,
    },
    iris: {
      shape: 7,
      rotation: 0,
      roundness: 0,
      aspectRatio: 1,
      diffractionFringe: 0,
    },
    highlight: {
      gain: 1,
      threshold: 1,
      saturation: 1,
    },
    autoOrient: "off",
    nearClip: 1,
    farClip: 10000,
  };
}

// ============================================================================
// OLD FORMAT REGRESSION TESTS - exportWanMoveTrajectories
// ============================================================================

describe("OLD FORMAT: exportWanMoveTrajectories", () => {
  it("returns trajectories as [x, y] arrays, NOT {x, y} objects", () => {
    const trajectory = createTestTrajectory("test-1", 10);
    const result = exportWanMoveTrajectories([trajectory], 1920, 1080);

    // OLD FORMAT: trajectories are number[][][] (arrays of [x, y])
    expect(result.trajectories).toBeDefined();
    expect(Array.isArray(result.trajectories)).toBe(true);
    expect(result.trajectories.length).toBe(1); // 1 trajectory

    // Verify first point is an ARRAY [x, y], not an object {x, y}
    const firstPoint = result.trajectories[0][0];
    expect(Array.isArray(firstPoint)).toBe(true);
    expect(firstPoint.length).toBe(2); // [x, y]
    expect(typeof firstPoint[0]).toBe("number"); // x
    expect(typeof firstPoint[1]).toBe("number"); // y

    // This should NOT have x/y properties (that's the NEW format)
    expect((firstPoint as any).x).toBeUndefined();
    expect((firstPoint as any).y).toBeUndefined();
  });

  it("returns visibility as number[][] (0/1), not boolean[][]", () => {
    const trajectory = createTestTrajectory("test-1", 5);
    const result = exportWanMoveTrajectories([trajectory], 1920, 1080);

    // OLD FORMAT: visibility is number[][] (0 or 1)
    expect(result.visibility).toBeDefined();
    expect(result.visibility[0][0]).toBe(1); // number, not boolean
    expect(typeof result.visibility[0][0]).toBe("number");
  });

  it("includes metadata with imageWidth/imageHeight (not width/height)", () => {
    const trajectory = createTestTrajectory("test-1", 10);
    const result = exportWanMoveTrajectories([trajectory], 1920, 1080);

    // OLD FORMAT: uses imageWidth/imageHeight
    expect(result.metadata.imageWidth).toBe(1920);
    expect(result.metadata.imageHeight).toBe(1080);

    // These properties should NOT exist in old format
    expect((result.metadata as any).width).toBeUndefined();
    expect((result.metadata as any).height).toBeUndefined();
  });

  it("frame count matches input trajectory, NOT fixed 121", () => {
    const trajectory = createTestTrajectory("test-1", 30);
    const result = exportWanMoveTrajectories([trajectory], 1920, 1080);

    // OLD FORMAT: frame count matches input
    expect(result.metadata.numFrames).toBe(30);
    expect(result.trajectories[0].length).toBe(30);

    // NEW ATI format would be fixed at 121, but WanMove old format is variable
    expect(result.trajectories[0].length).not.toBe(121);
  });

  it("snapshot: complete output structure", () => {
    const trajectory = createTestTrajectory("test-1", 3, 100, 200, 10, 5);
    const result = exportWanMoveTrajectories([trajectory], 1920, 1080);

    // Snapshot the complete structure for regression detection
    expect(result).toEqual({
      trajectories: [
        [
          [100, 200], // frame 0
          [110, 205], // frame 1
          [120, 210], // frame 2
        ],
      ],
      visibility: [[1, 1, 1]],
      metadata: {
        numPoints: 1,
        numFrames: 3,
        imageWidth: 1920,
        imageHeight: 1080,
        is3D: false,
        hasRotation: false,
        hasScale: false,
      },
    });
  });
});

// ============================================================================
// OLD FORMAT REGRESSION TESTS - exportATITrajectory
// ============================================================================

describe("OLD FORMAT: exportATITrajectory", () => {
  it("returns semantic type ('pan', 'free', 'static'), NOT raw coordinates", () => {
    // Linear motion should be detected as "pan"
    const linearTrajectory = createTestTrajectory("linear", 10, 100, 100, 10, 0);
    const result = exportATITrajectory(linearTrajectory, 1920, 1080);

    // OLD FORMAT: returns semantic type detection
    expect(result.type).toBe("pan");
    expect(result.panSpeed).toBeDefined();
    expect(result.panSpeed?.x).toBeCloseTo(10);
    expect(result.panSpeed?.y).toBeCloseTo(0);

    // OLD FORMAT: does NOT return raw track coordinates for pan type
    expect(result.points).toBeUndefined();
  });

  it("returns 'free' type with points for non-linear motion", () => {
    // Create non-linear trajectory (curved path)
    const trajectory: PointTrajectory = {
      id: "curved",
      points: [
        { frame: 0, x: 100, y: 100 },
        { frame: 1, x: 150, y: 100 }, // Jump right
        { frame: 2, x: 150, y: 150 }, // Jump down
        { frame: 3, x: 100, y: 150 }, // Jump left
        { frame: 4, x: 100, y: 100 }, // Back to start
      ],
      visibility: [true, true, true, true, true],
    };

    const result = exportATITrajectory(trajectory, 1920, 1080);

    // OLD FORMAT: "free" type with points array
    expect(result.type).toBe("free");
    expect(result.points).toBeDefined();
    expect(result.points?.length).toBe(5);

    // Points are {x, y} objects in OLD format too (for free type)
    expect(result.points?.[0]).toEqual({ x: 100, y: 100 });
  });

  it("returns 'static' for single-point trajectory", () => {
    const trajectory: PointTrajectory = {
      id: "static",
      points: [{ frame: 0, x: 100, y: 100 }],
      visibility: [true],
    };

    const result = exportATITrajectory(trajectory, 1920, 1080);

    // OLD FORMAT: static type for insufficient points
    expect(result.type).toBe("static");
    expect(result.points).toBeUndefined();
    expect(result.panSpeed).toBeUndefined();
  });

  it("does NOT pad/truncate to 121 frames (that's NEW ATI format)", () => {
    const trajectory = createTestTrajectory("test", 50);
    const result = exportATITrajectory(trajectory, 1920, 1080);

    // OLD FORMAT: Returns semantic analysis, not fixed frame count
    // If it's "pan", there are no points
    // If it's "free", points match input length (50), NOT 121
    if (result.type === "free" && result.points) {
      expect(result.points.length).toBe(50);
      expect(result.points.length).not.toBe(121);
    }

    // The type field itself proves this is OLD format (NEW format is just raw coordinates)
    expect(["pan", "free", "static", "circular"]).toContain(result.type);
  });

  it("snapshot: pan detection output structure", () => {
    // 10 frames moving right at 10px/frame
    const trajectory = createTestTrajectory("pan-test", 10, 0, 0, 10, 0);
    const result = exportATITrajectory(trajectory, 1920, 1080);

    expect(result).toEqual({
      type: "pan",
      panSpeed: { x: 10, y: 0 },
    });
  });
});

// ============================================================================
// OLD FORMAT REGRESSION TESTS - exportCameraTrajectory
// ============================================================================

describe("OLD FORMAT: exportCameraTrajectory", () => {
  it("returns 4x4 matrices array, NOT CameraCtrl pose text", () => {
    const camera = createTestCamera(0, 0, 500);
    const result = exportCameraTrajectory([camera], 24, 1920, 1080);

    // OLD FORMAT: matrices are 4x4 arrays
    expect(result.matrices).toBeDefined();
    expect(Array.isArray(result.matrices)).toBe(true);
    expect(result.matrices.length).toBe(1);

    // Each matrix is 4x4
    const matrix = result.matrices[0];
    expect(matrix.length).toBe(4);
    expect(matrix[0].length).toBe(4);
    expect(matrix[1].length).toBe(4);
    expect(matrix[2].length).toBe(4);
    expect(matrix[3].length).toBe(4);
  });

  it("returns metadata object, NOT inline pose parameters", () => {
    const camera = createTestCamera();
    const result = exportCameraTrajectory([camera], 24, 1920, 1080);

    // OLD FORMAT: separate metadata object
    expect(result.metadata).toBeDefined();
    expect(result.metadata.frameCount).toBe(1);
    expect(result.metadata.fps).toBe(24);
    expect(result.metadata.fov).toBe(39.6);
    expect(result.metadata.width).toBe(1920);
    expect(result.metadata.height).toBe(1080);
  });

  it("matrix is proper 4x4 transformation matrix", () => {
    const camera = createTestCamera(100, 50, 500);
    const result = exportCameraTrajectory([camera], 24, 1920, 1080);

    const matrix = result.matrices[0];

    // Bottom row should be [0, 0, 0, 1] for valid transformation matrix
    expect(matrix[3]).toEqual([0, 0, 0, 1]);

    // All values should be numbers
    for (let row = 0; row < 4; row++) {
      for (let col = 0; col < 4; col++) {
        expect(typeof matrix[row][col]).toBe("number");
        expect(Number.isFinite(matrix[row][col])).toBe(true);
      }
    }
  });

  it("snapshot: complete output structure", () => {
    const camera = createTestCamera(0, 0, 500);
    const result = exportCameraTrajectory([camera], 24, 1920, 1080);

    // Verify structure (not exact matrix values due to floating point)
    expect(result).toHaveProperty("matrices");
    expect(result).toHaveProperty("metadata");
    expect(result.metadata).toEqual({
      frameCount: 1,
      fps: 24,
      fov: 39.6,
      nearClip: 1,
      farClip: 10000,
      width: 1920,
      height: 1080,
    });

    // Matrix should have translation in last column (col 3, rows 0-2)
    const matrix = result.matrices[0];
    expect(matrix[0][3]).toBeCloseTo(0); // x translation
    expect(matrix[1][3]).toBeCloseTo(0); // y translation
    expect(matrix[2][3]).toBeCloseTo(500); // z translation
  });

  it("output is NOT string format (that's CameraCtrl NEW format)", () => {
    const camera = createTestCamera();
    const result = exportCameraTrajectory([camera], 24, 1920, 1080);

    // OLD FORMAT: Returns object with matrices array
    expect(typeof result).toBe("object");
    expect(typeof result.matrices).not.toBe("string");

    // NEW CameraCtrl format would be a string like:
    // "0 fx fy 0.5 0.5 1.777 0 0 m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23"
    // This test ensures we're NOT returning that format yet
  });
});

// ============================================================================
// COMBINED REGRESSION MARKER
// ============================================================================

describe("FORMAT CHANGE DETECTION", () => {
  it("WanMove: [x,y] arrays will change to {x,y} objects after migration", () => {
    const trajectory = createTestTrajectory("test", 3);
    const result = exportWanMoveTrajectories([trajectory], 1920, 1080);

    // This assertion will FAIL after migration
    const point = result.trajectories[0][0];
    expect(Array.isArray(point)).toBe(true);
    // After migration, point will be {x, y} object and this will fail
  });

  it("ATI: semantic types will change to raw 121-frame coordinates after migration", () => {
    const trajectory = createTestTrajectory("test", 50);
    const result = exportATITrajectory(trajectory, 1920, 1080);

    // This assertion will FAIL after migration
    expect(result).toHaveProperty("type");
    // After migration, result will be raw JSON string with 121 frames
  });

  it("Camera: 4x4 matrices will change to CameraCtrl pose text after migration", () => {
    const camera = createTestCamera();
    const result = exportCameraTrajectory([camera], 24, 1920, 1080);

    // This assertion will FAIL after migration
    expect(result).toHaveProperty("matrices");
    // After migration, result will be text format or different structure
  });
});
