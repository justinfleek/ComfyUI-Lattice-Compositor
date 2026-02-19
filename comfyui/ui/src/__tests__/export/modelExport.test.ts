/**
 * Model Export Tests
 *
 * Tests for AI video generation model export formats:
 * - camera-comfyUI: 4x4 transformation matrices
 * - ATI (Any Trajectory Instruction): trajectory instructions
 * - Light-X: motion style detection
 * - NPY format generation
 *
 * CRITICAL: These formats are strictly defined by AI models.
 *
 * @audit P0 CRITICAL - camera-comfyUI, ATI, Light-X format compliance
 */

import { describe, it, expect, beforeEach } from "vitest";
import {
  camera3DToMatrix4x4,
  exportCameraTrajectory,
  detectMotionStyle,
  createNpyHeader,
  trajectoriesToNpy,
  extractLayerTrajectory,
  extractSplineTrajectories,
  exportTTMLayer,
  convertPointTrajectoriesToWanMove,
  exportForModel,
  type CameraMatrix4x4,
  type CameraTrajectoryExport,
  type LightXMotionStyle,
  type PointTrajectory,
  type UnifiedExportOptions,
  type ModelTarget,
} from "@/services/modelExport";
import type { Camera3D } from "@/types/camera";
import type { Layer } from "@/types/project";
import type { SplineData } from "@/types/spline";
import { createAnimatableProperty } from "@/types/animation";
import { createDefaultTransform } from "@/types/transform";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Test Fixtures
// ═══════════════════════════════════════════════════════════════════════════

function createTestCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  return {
    id: "test-camera",
    name: "Test Camera",
    type: "one-node",
    position: { x: 0, y: 0, z: 500 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    pointOfInterest: { x: 0, y: 0, z: 0 },
    focalLength: 50,
    filmSize: 36,
    measureFilmSize: "horizontal",
    zoom: 1,
    angleOfView: 39.6,
    depthOfField: {
      enabled: false,
      focusDistance: 100,
      aperture: 2.8,
      fStop: 2.8,
      blurLevel: 100,
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
      gain: 0,
      threshold: 1,
      saturation: 1,
    },
    autoOrient: "off",
    nearClip: 1,
    farClip: 10000,
    ...overrides,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
// camera3DToMatrix4x4 Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("camera3DToMatrix4x4", () => {
  describe("Matrix Structure", () => {
    it("should return a 4x4 matrix", () => {
      const camera = createTestCamera();
      const matrix = camera3DToMatrix4x4(camera);

      expect(matrix.length).toBe(4);
      matrix.forEach((row) => {
        expect(row.length).toBe(4);
      });
    });

    it("should have all finite values", () => {
      const camera = createTestCamera();
      const matrix = camera3DToMatrix4x4(camera);

      for (let i = 0; i < 4; i++) {
        for (let j = 0; j < 4; j++) {
          expect(Number.isFinite(matrix[i][j])).toBe(true);
        }
      }
    });

    it("should have bottom row [0, 0, 0, 1] for homogeneous coords", () => {
      const camera = createTestCamera();
      const matrix = camera3DToMatrix4x4(camera);

      expect(matrix[3][0]).toBeCloseTo(0);
      expect(matrix[3][1]).toBeCloseTo(0);
      expect(matrix[3][2]).toBeCloseTo(0);
      expect(matrix[3][3]).toBeCloseTo(1);
    });
  });

  describe("Position Encoding", () => {
    it("should encode camera position in last column", () => {
      const camera = createTestCamera({
        position: { x: 100, y: 200, z: 300 },
      });
      const matrix = camera3DToMatrix4x4(camera);

      // Position is in the last column (elements 12, 13, 14 in row-major)
      expect(matrix[0][3]).toBeCloseTo(100, 1);
      expect(matrix[1][3]).toBeCloseTo(200, 1);
      expect(matrix[2][3]).toBeCloseTo(300, 1);
    });

    it("should handle negative positions", () => {
      const camera = createTestCamera({
        position: { x: -500, y: -300, z: -100 },
      });
      const matrix = camera3DToMatrix4x4(camera);

      expect(matrix[0][3]).toBeCloseTo(-500, 1);
      expect(matrix[1][3]).toBeCloseTo(-300, 1);
      expect(matrix[2][3]).toBeCloseTo(-100, 1);
    });

    it("should handle zero position (origin)", () => {
      const camera = createTestCamera({
        position: { x: 0, y: 0, z: 0 },
      });
      const matrix = camera3DToMatrix4x4(camera);

      expect(matrix[0][3]).toBeCloseTo(0);
      expect(matrix[1][3]).toBeCloseTo(0);
      expect(matrix[2][3]).toBeCloseTo(0);
    });
  });

  describe("Rotation Encoding", () => {
    it("should be identity rotation submatrix for no rotation", () => {
      const camera = createTestCamera({
        orientation: { x: 0, y: 0, z: 0 },
        xRotation: 0,
        yRotation: 0,
        zRotation: 0,
      });
      const matrix = camera3DToMatrix4x4(camera);

      // Upper-left 3x3 should be approximately identity
      expect(matrix[0][0]).toBeCloseTo(1, 1);
      expect(matrix[1][1]).toBeCloseTo(1, 1);
      expect(matrix[2][2]).toBeCloseTo(1, 1);
    });

    it("should combine orientation and rotation values", () => {
      const camera1 = createTestCamera({
        orientation: { x: 45, y: 0, z: 0 },
        xRotation: 0,
      });
      const camera2 = createTestCamera({
        orientation: { x: 0, y: 0, z: 0 },
        xRotation: 45,
      });

      const matrix1 = camera3DToMatrix4x4(camera1);
      const matrix2 = camera3DToMatrix4x4(camera2);

      // Both should produce equivalent matrices
      for (let i = 0; i < 3; i++) {
        for (let j = 0; j < 3; j++) {
          expect(matrix1[i][j]).toBeCloseTo(matrix2[i][j], 1);
        }
      }
    });
  });

  describe("Determinism", () => {
    it("should produce identical matrices for identical cameras", () => {
      const camera1 = createTestCamera({
        position: { x: 100, y: 200, z: 300 },
        orientation: { x: 30, y: 45, z: 60 },
      });
      const camera2 = createTestCamera({
        position: { x: 100, y: 200, z: 300 },
        orientation: { x: 30, y: 45, z: 60 },
      });

      const matrix1 = camera3DToMatrix4x4(camera1);
      const matrix2 = camera3DToMatrix4x4(camera2);

      for (let i = 0; i < 4; i++) {
        for (let j = 0; j < 4; j++) {
          expect(matrix1[i][j]).toBe(matrix2[i][j]);
        }
      }
    });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// exportCameraTrajectory Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("exportCameraTrajectory", () => {
  describe("Matrix Array Shape", () => {
    it("should export array of 4x4 matrices", () => {
      const cameras = [
        createTestCamera(),
        createTestCamera({ position: { x: 100, y: 0, z: 500 } }),
        createTestCamera({ position: { x: 200, y: 0, z: 500 } }),
      ];

      const result = exportCameraTrajectory(cameras, 16, 1920, 1080);

      expect(result.matrices.length).toBe(3);
      result.matrices.forEach((matrix) => {
        expect(matrix.length).toBe(4);
        matrix.forEach((row) => {
          expect(row.length).toBe(4);
        });
      });
    });

    it("should handle single frame", () => {
      const cameras = [createTestCamera()];

      const result = exportCameraTrajectory(cameras, 16, 1920, 1080);

      expect(result.matrices.length).toBe(1);
    });

    it("should handle empty cameras array", () => {
      const result = exportCameraTrajectory([], 16, 1920, 1080);

      expect(result.matrices.length).toBe(0);
    });
  });

  describe("Metadata", () => {
    it("should include correct frame count", () => {
      const cameras = Array(81).fill(null).map(() => createTestCamera());

      const result = exportCameraTrajectory(cameras, 16, 1920, 1080);

      expect(result.metadata.frameCount).toBe(81);
    });

    it("should include correct fps", () => {
      const cameras = [createTestCamera()];

      const result = exportCameraTrajectory(cameras, 24, 1920, 1080);

      expect(result.metadata.fps).toBe(24);
    });

    it("should include correct dimensions", () => {
      const cameras = [createTestCamera()];

      const result = exportCameraTrajectory(cameras, 16, 1280, 720);

      expect(result.metadata.width).toBe(1280);
      expect(result.metadata.height).toBe(720);
    });

    it("should include fov from first camera", () => {
      const cameras = [
        createTestCamera({ angleOfView: 60 }),
        createTestCamera({ angleOfView: 90 }),
      ];

      const result = exportCameraTrajectory(cameras, 16, 1920, 1080);

      expect(result.metadata.fov).toBe(60);
    });

    it("should include clip planes", () => {
      const cameras = [createTestCamera({ nearClip: 0.1, farClip: 5000 })];

      const result = exportCameraTrajectory(cameras, 16, 1920, 1080);

      expect(result.metadata.nearClip).toBe(0.1);
      expect(result.metadata.farClip).toBe(5000);
    });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// detectMotionStyle Tests (Light-X)
// ═══════════════════════════════════════════════════════════════════════════

describe("detectMotionStyle", () => {
  it("should return gradual for smooth linear panning", () => {
    const cameras = Array(81).fill(null).map((_, i) =>
      createTestCamera({
        position: { x: i * 2, y: 0, z: 500 }, // Slow, smooth pan
      })
    );

    const style = detectMotionStyle(cameras);

    // Linear motion with constant velocity = gradual
    expect(style).toBe("gradual");
  });

  it("should return bullet for significant Y rotation change", () => {
    const cameras = Array(81).fill(null).map((_, i) =>
      createTestCamera({
        position: { x: 0, y: 0, z: 500 },
        yRotation: i * 1, // 80 degrees total rotation
      })
    );

    const style = detectMotionStyle(cameras);

    expect(style).toBe("bullet");
  });

  it("should return dolly-zoom for combined position and FOV change", () => {
    const cameras = Array(81).fill(null).map((_, i) =>
      createTestCamera({
        position: { x: 0, y: 0, z: 500 - i * 5 }, // Move forward 400 units
        angleOfView: 40 + i * 0.5, // Change FOV by 40 degrees
      })
    );

    const style = detectMotionStyle(cameras);

    expect(style).toBe("dolly-zoom");
  });

  it("should return direct for non-smooth motion with sudden velocity change", () => {
    // Motion with sudden velocity change > 10 per frame
    const cameras = Array(81).fill(null).map((_, i) =>
      createTestCamera({
        // First half: slow motion, second half: fast motion (creates > 10 vel change)
        position: { x: i < 40 ? i * 2 : 80 + (i - 40) * 30, y: 0, z: 500 },
      })
    );

    const style = detectMotionStyle(cameras);

    expect(style).toBe("direct");
  });

  it("should handle static camera (smooth = gradual)", () => {
    const cameras = Array(81).fill(null).map(() =>
      createTestCamera()
    );

    const style = detectMotionStyle(cameras);

    // Static camera has zero velocity change, so it's "smooth" -> gradual
    expect(style).toBe("gradual");
  });

  it("should handle single camera (returns static)", () => {
    const cameras = [createTestCamera()];

    const style = detectMotionStyle(cameras);

    // Single camera returns "static" (implementation behavior)
    expect(style).toBe("static");
  });

  it("should handle empty array (returns static)", () => {
    const style = detectMotionStyle([]);

    // Empty array returns "static" (implementation behavior)
    expect(style).toBe("static");
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// createNpyHeader Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("createNpyHeader", () => {
  // Note: createNpyHeader signature is (shape: number[], dtype: string) and returns Uint8Array
  
  it("should return Uint8Array", () => {
    const header = createNpyHeader([10, 3, 2], "<f4");

    expect(header instanceof Uint8Array).toBe(true);
  });

  it("should include NPY magic number", () => {
    const header = createNpyHeader([10, 3, 2], "<f4");

    // NPY magic: 0x93 'N' 'U' 'M' 'P' 'Y'
    expect(header[0]).toBe(0x93);
    expect(header[1]).toBe(0x4e); // 'N'
    expect(header[2]).toBe(0x55); // 'U'
    expect(header[3]).toBe(0x4d); // 'M'
    expect(header[4]).toBe(0x50); // 'P'
    expect(header[5]).toBe(0x59); // 'Y'
  });

  it("should have version bytes after magic", () => {
    const header = createNpyHeader([10, 10], "<f4");

    // Version 1.0
    expect(header[6]).toBe(0x01);
    expect(header[7]).toBe(0x00);
  });

  it("should handle different dtypes", () => {
    const header32 = createNpyHeader([10, 10], "<f4");
    const header64 = createNpyHeader([10, 10], "<f8");
    const headerU8 = createNpyHeader([10, 10], "|u1");

    expect(header32 instanceof Uint8Array).toBe(true);
    expect(header64 instanceof Uint8Array).toBe(true);
    expect(headerU8 instanceof Uint8Array).toBe(true);
  });

  it("should handle different shapes", () => {
    const header1D = createNpyHeader([100], "<f4");
    const header2D = createNpyHeader([10, 10], "<f4");
    const header3D = createNpyHeader([5, 10, 2], "<f4");
    const header4D = createNpyHeader([2, 3, 4, 5], "<f4");

    expect(header1D instanceof Uint8Array).toBe(true);
    expect(header2D instanceof Uint8Array).toBe(true);
    expect(header3D instanceof Uint8Array).toBe(true);
    expect(header4D instanceof Uint8Array).toBe(true);
  });

  it("should be aligned to 64 bytes", () => {
    const header = createNpyHeader([10, 10], "<f4");

    // NPY format requires header to be aligned to 64 bytes
    expect(header.length % 64).toBe(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// trajectoriesToNpy Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("trajectoriesToNpy", () => {
  it("should return a Blob", () => {
    const trajectories = [
      [[0, 0], [1, 1], [2, 2]],
      [[10, 10], [11, 11], [12, 12]],
    ];

    const blob = trajectoriesToNpy(trajectories);

    expect(blob instanceof Blob).toBe(true);
  });

  it("should have correct MIME type", () => {
    const trajectories = [[[0, 0]]];

    const blob = trajectoriesToNpy(trajectories);

    // NPY files typically use application/octet-stream
    expect(blob.type).toMatch(/octet-stream|npy/i);
  });

  it("should handle empty trajectories", () => {
    const blob = trajectoriesToNpy([]);

    expect(blob instanceof Blob).toBe(true);
    expect(blob.size).toBeGreaterThan(0); // Still has header
  });

  it("should have size proportional to data", () => {
    const small = trajectoriesToNpy([[[0, 0]]]);
    const large = trajectoriesToNpy([
      [[0, 0], [1, 1], [2, 2], [3, 3], [4, 4]],
      [[10, 10], [11, 11], [12, 12], [13, 13], [14, 14]],
      [[20, 20], [21, 21], [22, 22], [23, 23], [24, 24]],
    ]);

    expect(large.size).toBeGreaterThan(small.size);
  });

  it("should produce consistent size for same data", () => {
    const trajectories = [[[0, 0], [1, 1], [2, 2]]];

    const blob1 = trajectoriesToNpy(trajectories);
    const blob2 = trajectoriesToNpy(trajectories);

    expect(blob1.size).toBe(blob2.size);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// Determinism Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("Determinism", () => {
  it("should produce identical camera matrices for identical input", () => {
    const camera = createTestCamera({
      position: { x: 100, y: 200, z: 300 },
      orientation: { x: 15, y: 30, z: 45 },
    });

    const matrix1 = camera3DToMatrix4x4(camera);
    const matrix2 = camera3DToMatrix4x4(camera);

    expect(JSON.stringify(matrix1)).toBe(JSON.stringify(matrix2));
  });

  it("should produce identical trajectories for identical input", () => {
    const cameras = [
      createTestCamera({ position: { x: 0, y: 0, z: 500 } }),
      createTestCamera({ position: { x: 100, y: 50, z: 450 } }),
    ];

    const result1 = exportCameraTrajectory(cameras, 16, 1920, 1080);
    const result2 = exportCameraTrajectory(cameras, 16, 1920, 1080);

    expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
  });

});

// ═══════════════════════════════════════════════════════════════════════════
// extractLayerTrajectory Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("extractLayerTrajectory", () => {
  function createTestLayer(overrides: Partial<Layer> = {}): Layer {
    return {
      id: "test-layer",
      name: "Test Layer",
      type: "image",
      visible: true,
      locked: false,
      solo: false,
      shy: false,
      opacity: 100,
      blendMode: "normal",
      collapsed: false,
      selected: false,
      transform: {
        position: { x: 100, y: 100 },
        scale: { x: 100, y: 100 },
        rotation: 0,
        anchor: { x: 0, y: 0 },
        positionZ: 0,
      },
      inPoint: 0,
      outPoint: 100,
      startFrame: 0,
      endFrame: 100,
      ...overrides,
    } as Layer;
  }

  it("should extract positions for frame range", () => {
    const layer = createTestLayer();
    const getPosition = (_layer: Layer, frame: number) => ({
      x: frame * 10,
      y: frame * 5,
    });

    const result = extractLayerTrajectory(layer, 0, 10, getPosition);

    expect(result.id).toBe("test-layer");
    expect(result.points.length).toBe(11);
    expect(result.points[0]).toEqual({ frame: 0, x: 0, y: 0 });
    expect(result.points[5]).toEqual({ frame: 5, x: 50, y: 25 });
  });

  it("should track visibility based on layer range", () => {
    const layer = createTestLayer({
      startFrame: 5,
      endFrame: 15,
    });
    const getPosition = () => ({ x: 0, y: 0 });

    const result = extractLayerTrajectory(layer, 0, 20, getPosition);

    expect(result.visibility[0]).toBe(false); // Frame 0 - before start
    expect(result.visibility[5]).toBe(true);  // Frame 5 - at start
    expect(result.visibility[10]).toBe(true); // Frame 10 - in range
    expect(result.visibility[15]).toBe(true); // Frame 15 - at end
    expect(result.visibility[16]).toBe(false); // Frame 16 - after end
  });

  it("should handle invisible layers", () => {
    const layer = createTestLayer({ visible: false });
    const getPosition = () => ({ x: 0, y: 0 });

    const result = extractLayerTrajectory(layer, 0, 5, getPosition);

    // All visibility should be false because layer is invisible
    expect(result.visibility.every((v) => v === false)).toBe(true);
  });

  it("should include 3D transform data when getter provided", () => {
    const layer = createTestLayer();
    const getPosition = () => ({ x: 0, y: 0 });
    const getTransform = (_layer: Layer, frame: number) => ({
      position: { x: frame * 10, y: frame * 5, z: frame * 2 },
      rotation: { x: frame, y: frame * 2, z: frame * 3 },
      scale: { x: 100, y: 100 },
    });

    const result = extractLayerTrajectory(layer, 0, 5, getPosition, getTransform);

    expect(result.points[3].z).toBe(6);
    expect(result.rotation).toBeDefined();
    expect(result.rotation![3]).toEqual({ frame: 3, x: 3, y: 6, z: 9 });
    expect(result.scale).toBeDefined();
    expect(result.scale![0]).toEqual({ frame: 0, x: 100, y: 100 });
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// extractSplineTrajectories Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("extractSplineTrajectories", () => {
  it("should extract static control points as trajectories", () => {
    const splineData: SplineData = {
      pathData: "M 100 200 L 300 400",
      closed: false,
      controlPoints: [
        { id: "cp-1", x: 100, y: 200, handleIn: { x: 0, y: 0 }, handleOut: { x: 0, y: 0 }, type: "corner" },
        { id: "cp-2", x: 300, y: 400, handleIn: { x: 0, y: 0 }, handleOut: { x: 0, y: 0 }, type: "corner" },
      ],
      stroke: "#000000",
      strokeWidth: 1,
      fill: "",
    };

    const result = extractSplineTrajectories(splineData, 0, 10);

    expect(result.length).toBe(2);
    expect(result[0].id).toBe("cp-1");
    expect(result[0].points.length).toBe(11);
    // Static points should be same for all frames
    expect(result[0].points[0]).toEqual({ frame: 0, x: 100, y: 200 });
    expect(result[0].points[10]).toEqual({ frame: 10, x: 100, y: 200 });
  });

  it("should extract animated control points with interpolation", () => {
    const splineData: SplineData = {
      pathData: "M 100 50 L 200 100",
      closed: false,
      controlPoints: [],
      animated: true,
      animatedControlPoints: [
        {
          id: "acp-1",
          x: {
            id: "x-prop",
            name: "x",
            type: "number" as const,
            value: 100,
            animated: true,
            keyframes: [
              { id: "k1", frame: 0, value: 100, interpolation: "linear" as const, inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: "smooth" as const },
              { id: "k2", frame: 10, value: 200, interpolation: "linear" as const, inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: "smooth" as const },
            ],
          },
          y: {
            id: "y-prop",
            name: "y",
            type: "number" as const,
            value: 50,
            animated: true,
            keyframes: [
              { id: "k3", frame: 0, value: 50, interpolation: "linear" as const, inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: "smooth" as const },
              { id: "k4", frame: 10, value: 100, interpolation: "linear" as const, inHandle: { frame: 0, value: 0, enabled: false }, outHandle: { frame: 0, value: 0, enabled: false }, controlMode: "smooth" as const },
            ],
          },
          handleIn: null,
          handleOut: null,
          type: "corner",
        },
      ],
      stroke: "#000000",
      strokeWidth: 1,
      fill: "",
    };

    const result = extractSplineTrajectories(splineData, 0, 10);

    expect(result.length).toBe(1);
    expect(result[0].points[0].x).toBe(100);
    expect(result[0].points[5].x).toBe(150); // Linear interpolation midpoint
    expect(result[0].points[10].x).toBe(200);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// convertPointTrajectoriesToWanMove Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("convertPointTrajectoriesToWanMove", () => {
  it("converts single trajectory to WanMoveTrajectory format", () => {
    const trajectories: PointTrajectory[] = [
      {
        id: "track-1",
        points: [
          { frame: 0, x: 100, y: 200 },
          { frame: 1, x: 110, y: 205 },
          { frame: 2, x: 120, y: 210 },
        ],
        visibility: [true, true, false],
      },
    ];

    const result = convertPointTrajectoriesToWanMove(trajectories, 1920, 1080, 24);

    // Verify tracks structure: [N][T][2]
    expect(result.tracks).toHaveLength(1);
    expect(result.tracks[0]).toHaveLength(3);
    expect(result.tracks[0][0]).toEqual([100, 200]);
    expect(result.tracks[0][1]).toEqual([110, 205]);
    expect(result.tracks[0][2]).toEqual([120, 210]);

    // Verify visibility structure: [N][T]
    expect(result.visibility).toHaveLength(1);
    expect(result.visibility[0]).toEqual([true, true, false]);

    // Verify metadata
    expect(result.metadata).toEqual({
      numPoints: 1,
      numFrames: 3,
      width: 1920,
      height: 1080,
      fps: 24,
    });
  });

  it("converts multiple trajectories", () => {
    const trajectories: PointTrajectory[] = [
      {
        id: "track-1",
        points: [
          { frame: 0, x: 100, y: 100 },
          { frame: 1, x: 150, y: 100 },
        ],
        visibility: [true, true],
      },
      {
        id: "track-2",
        points: [
          { frame: 0, x: 500, y: 300 },
          { frame: 1, x: 550, y: 350 },
        ],
        visibility: [true, false],
      },
    ];

    const result = convertPointTrajectoriesToWanMove(trajectories, 1920, 1080, 16);

    expect(result.tracks).toHaveLength(2);
    expect(result.tracks[0][0]).toEqual([100, 100]);
    expect(result.tracks[1][0]).toEqual([500, 300]);
    expect(result.metadata.numPoints).toBe(2);
    expect(result.metadata.numFrames).toBe(2);
  });

  it("handles empty trajectories array", () => {
    const result = convertPointTrajectoriesToWanMove([], 1920, 1080, 24);

    expect(result.tracks).toEqual([]);
    expect(result.visibility).toEqual([]);
    expect(result.metadata.numPoints).toBe(0);
    expect(result.metadata.numFrames).toBe(0);
  });

  it("drops z coordinate (2D only)", () => {
    const trajectories: PointTrajectory[] = [
      {
        id: "track-3d",
        points: [
          { frame: 0, x: 100, y: 200, z: 50 },
          { frame: 1, x: 110, y: 205, z: 55 },
        ],
        visibility: [true, true],
      },
    ];

    const result = convertPointTrajectoriesToWanMove(trajectories, 1920, 1080, 24);

    // Should only have [x, y], not [x, y, z]
    expect(result.tracks[0][0]).toEqual([100, 200]);
    expect(result.tracks[0][0]).toHaveLength(2);
  });

  it("drops id field (not needed in WanMoveTrajectory)", () => {
    const trajectories: PointTrajectory[] = [
      {
        id: "my-unique-id",
        points: [{ frame: 0, x: 100, y: 200 }],
        visibility: [true],
      },
    ];

    const result = convertPointTrajectoriesToWanMove(trajectories, 1920, 1080, 24);

    // WanMoveTrajectory has no id field
    expect(result).not.toHaveProperty("id");
    expect(result.tracks).toBeDefined();
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// extractLayerTrajectory Tests (PURE - testable without browser)
// ═══════════════════════════════════════════════════════════════════════════

// extractLayerTrajectory is already imported at the top of this file

describe("extractLayerTrajectory", () => {
  const createTestLayer = (id: string, visible = true, inPoint = 0, outPoint = 100): Layer => ({
    id,
    name: `Layer ${id}`,
    type: "solid",
    visible,
    locked: false,
    isolate: false,
    threeD: false,
    motionBlur: false,
    startFrame: inPoint,
    endFrame: outPoint,
    inPoint,
    outPoint,
    blendMode: "normal",
    opacity: createAnimatableProperty("opacity", 100, "number"),
    transform: createDefaultTransform(),
    effects: [],
    properties: [],
    parentId: null,
    data: { color: "#ff0000", width: 1920, height: 1080 },
  });

  const mockGetPosition = (layer: Layer, frame: number) => ({
    x: frame * 10,
    y: frame * 5,
  });

  it("should extract trajectory points for each frame", () => {
    const layer = createTestLayer("test-1");
    const result = extractLayerTrajectory(layer, 0, 10, mockGetPosition);
    
    expect(result.points).toHaveLength(11); // 0-10 inclusive
    expect(result.points[0]).toEqual({ frame: 0, x: 0, y: 0 });
    expect(result.points[5]).toEqual({ frame: 5, x: 50, y: 25 });
    expect(result.points[10]).toEqual({ frame: 10, x: 100, y: 50 });
  });

  it("should set visibility based on layer in/out points", () => {
    const layer = createTestLayer("test-2", true, 5, 15);
    const result = extractLayerTrajectory(layer, 0, 20, mockGetPosition);
    
    // Frames 0-4 should be invisible (before inPoint)
    expect(result.visibility[0]).toBe(false);
    expect(result.visibility[4]).toBe(false);
    
    // Frames 5-15 should be visible (in range)
    expect(result.visibility[5]).toBe(true);
    expect(result.visibility[10]).toBe(true);
    expect(result.visibility[15]).toBe(true);
    
    // Frames 16-20 should be invisible (after outPoint)
    expect(result.visibility[16]).toBe(false);
    expect(result.visibility[20]).toBe(false);
  });

  it("should respect layer visibility flag", () => {
    const layer = createTestLayer("test-3", false, 0, 100); // hidden layer
    const result = extractLayerTrajectory(layer, 0, 10, mockGetPosition);
    
    // All frames should be invisible because layer is hidden
    result.visibility.forEach((vis) => {
      expect(vis).toBe(false);
    });
  });

  it("should handle single frame range", () => {
    const layer = createTestLayer("test-4");
    const result = extractLayerTrajectory(layer, 5, 5, mockGetPosition);
    
    expect(result.points).toHaveLength(1);
    expect(result.points[0]).toEqual({ frame: 5, x: 50, y: 25 });
  });

  it("should handle empty range", () => {
    const layer = createTestLayer("test-5");
    const result = extractLayerTrajectory(layer, 10, 5, mockGetPosition); // end < start
    
    expect(result.points).toHaveLength(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// BROWSER-ONLY TESTS (Canvas API)
// ═══════════════════════════════════════════════════════════════════════════
//
// The following browser-dependent functionality is tested in E2E:
//
// Location: /ui/e2e/export/model-export.spec.ts
//
// Covered:
// - exportTTMLayer (E2E lines 22-99)
//   - export layer with TTM metadata
//   - include bounding box when provided
// - generateMotionMask (E2E lines 101-211)
//   - generate binary mask from layer motion
//   - respect brush size
//   - create continuous path between points
// - generateCombinedMotionMask (E2E lines 213-297)
//   - combine multiple layer masks
//   - handle overlapping trajectories
//   - handle empty trajectories
// - imageDataToBase64 (E2E lines 299-438)
//   - convert ImageData to base64 PNG
//   - preserve image dimensions
//   - preserve pixel colors
//   - handle transparent pixels
//
// Run E2E tests with: bunx playwright test model-export.spec.ts

// ═══════════════════════════════════════════════════════════════════════════
// exportForModel Tests
// ═══════════════════════════════════════════════════════════════════════════

describe("exportForModel", () => {
  it("should export camera-comfyui format", async () => {
    const options = {
      target: "camera-comfyui" as const,
      layers: [],
      cameras: [{
        id: "cam1",
        name: "Camera",
        type: "one-node" as const,
        position: { x: 0, y: 0, z: 500 },
        pointOfInterest: { x: 0, y: 0, z: 0 },
        orientation: { x: 0, y: 0, z: 0 },
        xRotation: 0,
        yRotation: 0,
        zRotation: 0,
        zoom: 1,
        focalLength: 50,
        angleOfView: 39.6,
        filmSize: 36,
        measureFilmSize: "horizontal" as const,
        depthOfField: {
          enabled: false,
          focusDistance: 100,
          aperture: 2.8,
          fStop: 2.8,
          blurLevel: 100,
          lockToZoom: false,
        },
        iris: {
          shape: 0,
          rotation: 0,
          roundness: 1,
          aspectRatio: 1,
          diffractionFringe: 0,
        },
        highlight: {
          gain: 0,
          threshold: 0,
          saturation: 0,
        },
        autoOrient: "off" as const,
        nearClip: 0.1,
        farClip: 10000,
      }],
      compWidth: 1920,
      compHeight: 1080,
      fps: 30,
      startFrame: 0,
      endFrame: 30,
      getPositionAtFrame: (_layer: Layer, _frame: number) => ({ x: 0, y: 0 }),
      getLayerBounds: (_layer: Layer, _frame: number) => ({ x: 0, y: 0, width: 100, height: 100 }),
    };

    const result = await exportForModel(options);

    expect(result.success).toBe(true);
    expect(result.target).toBe("camera-comfyui");
    expect(result.data).toBeDefined();
    expect(result.files).toBeDefined();
    expect(result.files!.length).toBeGreaterThan(0);
    expect(result.files![0].name).toBe("camera_trajectory.json");
  });

  it("should export wan-move format with trajectories", async () => {
    const mockLayer: Layer = {
      id: "layer-1",
      name: "Test Layer",
      type: "solid",
      visible: true,
      locked: false,
      isolate: false,
      threeD: false,
      motionBlur: false,
      blendMode: "normal",
      opacity: createAnimatableProperty("opacity", 1, "number"),
      transform: {
        position: createAnimatableProperty("position", { x: 100, y: 100 }, "position"),
        scale: createAnimatableProperty("scale", { x: 1, y: 1 }, "position"),
        rotation: createAnimatableProperty("rotation", 0, "number"),
        origin: createAnimatableProperty("origin", { x: 0, y: 0 }, "position"),
      },
      effects: [],
      properties: [],
      masks: [],
      startFrame: 0,
      endFrame: 10,
      inPoint: 0,
      outPoint: 10,
      parentId: null,
      data: null,
    };

    const getPositionAtFrame = (_layer: Layer, frame: number) => ({
      x: 100 + frame * 10,
      y: 100 + frame * 5,
    });

    const options: UnifiedExportOptions = {
      target: "wan-move",
      layers: [mockLayer],
      cameras: [],
      compWidth: 1920,
      compHeight: 1080,
      fps: 30,
      startFrame: 0,
      endFrame: 10,
      getPositionAtFrame,
      getLayerBounds: (_layer: Layer, _frame: number) => ({ x: 0, y: 0, width: 100, height: 100 }),
    };

    const result = await exportForModel(options);

    expect(result.success).toBe(true);
    expect(result.target).toBe("wan-move");
  });

  it("should handle valid target correctly", async () => {
    // Test with valid ModelTarget - function validates target internally
    const options: UnifiedExportOptions = {
      target: "wan-move", // Valid ModelTarget
      layers: [],
      cameras: [],
      compWidth: 1920,
      compHeight: 1080,
      fps: 30,
      startFrame: 0,
      endFrame: 30,
      getPositionAtFrame: (_layer: Layer, _frame: number) => ({ x: 0, y: 0 }),
      getLayerBounds: (_layer: Layer, _frame: number) => ({ x: 0, y: 0, width: 100, height: 100 }),
    };

    const result = await exportForModel(options);
    expect(result.success).toBe(true);
    expect(result.target).toBe("wan-move");
  });
});
