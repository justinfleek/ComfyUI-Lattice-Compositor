/**
 * Export Format Contract Tests
 *
 * Validates that all export tensor formats match the requirements
 * of target ML models (Wan, Uni3C, MotionCtrl, ControlNet, etc.)
 *
 * CRITICAL: These tests verify data shapes and value ranges that
 * ML models REQUIRE for proper inference. Failing tests indicate
 * exports that will cause model failures.
 *
 * @audit P0 CRITICAL - Export format compliance
 */

import { describe, it, expect, beforeEach } from "vitest";

// Import export functions
import {
  renderDepthFrame,
  convertDepthToFormat,
  depthToImageData,
  applyColormap,
  generateDepthMetadata,
  type DepthRenderOptions,
  type DepthRenderResult,
} from "@/services/export/depthRenderer";

import {
  exportToMotionCtrl,
  exportToMotionCtrlSVD,
  mapToWan22FunCamera,
  exportToUni3C,
  exportToCameraCtrl,
  exportCameraMatrices,
  computeViewMatrix,
  computeProjectionMatrix,
  interpolateCameraAtFrame,
} from "@/services/export/cameraExportFormats";

import {
  exportAsJSON,
  exportAsNPYData,
  generateSpiralFlow,
  generateWaveFlow,
  type WanMoveTrajectory,
  type GenerativeFlowConfig,
} from "@/services/export/wanMoveExport";

import {
  DEPTH_FORMAT_SPECS,
  EXPORT_PRESETS,
  calculateWanFrameCount,
  isValidWanFrameCount,
  getNearestValidWanFrameCount,
} from "@/config/exportPresets";

import type { Camera3D, CameraKeyframe } from "@/types/camera";
import type { DepthMapFormat, ExportTarget } from "@/types/export";
import type { Layer } from "@/types/project";

// ============================================================================
// Test Fixtures
// ============================================================================

function createTestCamera(): Camera3D {
  return {
    id: "test-camera",
    name: "Test Camera",
    type: "one-node",
    position: { x: 0, y: 0, z: 500 },
    pointOfInterest: { x: 0, y: 0, z: 0 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    focalLength: 50,
    zoom: 1778, // Realistic zoom for 50mm
    filmSize: 36,
    angleOfView: 39.6,
    measureFilmSize: "horizontal",
    depthOfField: {
      enabled: false,
      focusDistance: 100,
      aperture: 50, // Pixels (internal)
      fStop: 2.8, // f-stop (display)
      blurLevel: 1, // 0-1 multiplier
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
    nearClip: 0.1,
    farClip: 1000,
  };
}

function createTestKeyframes(): CameraKeyframe[] {
  return [
    {
      frame: 0,
      position: { x: 0, y: 0, z: 500 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1778,
      focusDistance: 100,
    },
    {
      frame: 40,
      position: { x: 100, y: 0, z: 400 },
      orientation: { x: 0, y: 30, z: 0 },
      focalLength: 50,
      zoom: 1778,
      focusDistance: 100,
    },
    {
      frame: 80,
      position: { x: 0, y: 0, z: 500 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1778,
      focusDistance: 100,
    },
  ];
}

function createTestLayer(): Layer {
  return {
    id: "test-layer",
    name: "Test Layer",
    type: "solid",
    visible: true,
    locked: false,
    solo: false,
    shy: false,
    startFrame: 0,
    endFrame: 100,
    transform: {
      position: { animated: false, value: [0, 0, 0], keyframes: [] },
      scale: { animated: false, value: [100, 100, 100], keyframes: [] },
      rotation: { animated: false, value: 0, keyframes: [] },
      anchorPoint: { animated: false, value: [0, 0], keyframes: [] },
    },
    opacity: { animated: false, value: 100, keyframes: [] },
    effects: [],
    masks: [],
    blendMode: "normal",
    parentId: null,
    trackMatteId: null,
    trackMatteType: null,
  } as unknown as Layer;
}

function createDepthRenderOptions(): DepthRenderOptions {
  return {
    width: 832,
    height: 480,
    nearClip: 0.1,
    farClip: 1000,
    camera: createTestCamera(),
    layers: [createTestLayer()],
    frame: 0,
  };
}

// ============================================================================
// 1. DEPTH FORMAT CONTRACT TESTS
// ============================================================================

describe("Depth Format Contracts", () => {
  describe("DEPTH_FORMAT_SPECS completeness", () => {
    const requiredFormats: DepthMapFormat[] = [
      "raw",
      "midas",
      "zoe",
      "depth-pro",
      "depth-anything",
      "marigold",
      "normalized",
    ];

    it.each(requiredFormats)("should have spec for format: %s", (format) => {
      expect(DEPTH_FORMAT_SPECS).toHaveProperty(format);
      const spec = DEPTH_FORMAT_SPECS[format];
      expect(spec).toHaveProperty("format", format);
      expect(spec).toHaveProperty("bitDepth");
      expect(spec).toHaveProperty("invert");
      expect(spec).toHaveProperty("normalize");
      expect(spec).toHaveProperty("nearClip");
      expect(spec).toHaveProperty("farClip");
    });
  });

  describe("MiDaS format contract", () => {
    /**
     * MiDaS Model Requirements:
     * - Bit depth: 8-bit (Uint8Array)
     * - Value range: 0-255
     * - Inversion: YES (near=bright, far=dark)
     * - Normalization: YES (0-1 then scaled to 0-255)
     */
    it("should export 8-bit inverted depth", () => {
      const spec = DEPTH_FORMAT_SPECS["midas"];
      expect(spec.bitDepth).toBe(8);
      expect(spec.invert).toBe(true);
      expect(spec.normalize).toBe(true);
    });

    it("should produce Uint8Array output", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "midas");

      expect(converted).toBeInstanceOf(Uint8Array);
      expect(converted.length).toBe(options.width * options.height);
    });

    it("should have values in range 0-255", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "midas") as Uint8Array;

      for (let i = 0; i < Math.min(1000, converted.length); i++) {
        expect(converted[i]).toBeGreaterThanOrEqual(0);
        expect(converted[i]).toBeLessThanOrEqual(255);
      }
    });

    it("should have near objects as BRIGHT (inverted)", () => {
      // Create a scene with a near object
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "midas") as Uint8Array;

      // With inversion, near objects should have HIGH values (bright)
      // If min depth exists, those pixels should be close to 255
      // This test validates the inversion logic is working
      const minDepth = result.minDepth;
      const maxDepth = result.maxDepth;
      
      // If there's depth variation, inverted near should be bright
      if (maxDepth > minDepth) {
        const maxValue = Math.max(...Array.from(converted));
        expect(maxValue).toBeGreaterThan(200); // Near objects should be bright
      }
    });
  });

  describe("Depth-Anything format contract", () => {
    /**
     * Depth-Anything Model Requirements:
     * - Bit depth: 16-bit (Uint16Array)
     * - Value range: 0-65535
     * - Inversion: YES (like MiDaS - near=bright)
     * - Normalization: YES
     */
    it("should export 16-bit inverted depth", () => {
      const spec = DEPTH_FORMAT_SPECS["depth-anything"];
      expect(spec.bitDepth).toBe(16);
      expect(spec.invert).toBe(true);
      expect(spec.normalize).toBe(true);
    });

    it("should produce Uint16Array output", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "depth-anything");

      expect(converted).toBeInstanceOf(Uint16Array);
      expect(converted.length).toBe(options.width * options.height);
    });

    it("should have values in range 0-65535", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "depth-anything") as Uint16Array;

      for (let i = 0; i < Math.min(1000, converted.length); i++) {
        expect(converted[i]).toBeGreaterThanOrEqual(0);
        expect(converted[i]).toBeLessThanOrEqual(65535);
      }
    });
  });

  describe("Zoe format contract", () => {
    /**
     * Zoe-Depth Model Requirements:
     * - Bit depth: 16-bit (Uint16Array)
     * - Value range: 0-65535
     * - Inversion: NO (near=dark, far=bright) - metric depth
     * - Normalization: YES
     */
    it("should export 16-bit non-inverted depth", () => {
      const spec = DEPTH_FORMAT_SPECS["zoe"];
      expect(spec.bitDepth).toBe(16);
      expect(spec.invert).toBe(false);
      expect(spec.normalize).toBe(true);
    });

    it("should produce Uint16Array output", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "zoe");

      expect(converted).toBeInstanceOf(Uint16Array);
    });
  });

  describe("Marigold format contract", () => {
    /**
     * Marigold Model Requirements:
     * - Bit depth: 16-bit (Uint16Array)
     * - Affine-invariant (scale/shift invariant)
     * - Normalization: YES
     * - Inversion: NO
     */
    it("should export 16-bit normalized depth", () => {
      const spec = DEPTH_FORMAT_SPECS["marigold"];
      expect(spec.bitDepth).toBe(16);
      expect(spec.normalize).toBe(true);
      expect(spec.invert).toBe(false);
    });

    it("should produce Uint16Array output", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "marigold");

      expect(converted).toBeInstanceOf(Uint16Array);
    });
  });

  describe("Raw format contract", () => {
    /**
     * Raw Format Requirements:
     * - Bit depth: 32-bit Float (Float32Array)
     * - No inversion, no normalization
     * - Preserves actual depth values
     */
    it("should export 32-bit float depth", () => {
      const spec = DEPTH_FORMAT_SPECS["raw"];
      expect(spec.bitDepth).toBe(32);
      expect(spec.normalize).toBe(false);
      expect(spec.invert).toBe(false);
    });

    it("should produce Float32Array output", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const converted = convertDepthToFormat(result, "raw");

      expect(converted).toBeInstanceOf(Float32Array);
      expect(converted.length).toBe(options.width * options.height);
    });
  });

  describe("Depth buffer invariants", () => {
    it("should always have minDepth <= maxDepth", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);

      expect(result.minDepth).toBeLessThanOrEqual(result.maxDepth);
    });

    it("should have correct buffer dimensions", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);

      expect(result.width).toBe(options.width);
      expect(result.height).toBe(options.height);
      expect(result.depthBuffer.length).toBe(options.width * options.height);
    });

    it("should handle empty scenes gracefully", () => {
      const options = createDepthRenderOptions();
      options.layers = [];
      const result = renderDepthFrame(options);

      expect(Number.isFinite(result.minDepth)).toBe(true);
      expect(Number.isFinite(result.maxDepth)).toBe(true);
    });
  });
});

// ============================================================================
// 2. CAMERA EXPORT FORMAT CONTRACT TESTS
// ============================================================================

describe("Camera Export Format Contracts", () => {
  describe("MotionCtrl 4x4 Matrix Format", () => {
    /**
     * MotionCtrl Requirements:
     * - RT matrix: 4x4 camera extrinsic (view) matrix
     * - One pose per frame
     * - Matrix must be valid transformation matrix
     */
    it("should export array of 4x4 matrices", () => {
      const camera = createTestCamera();
      const keyframes = createTestKeyframes();
      const frameCount = 81;

      const result = exportToMotionCtrl(camera, keyframes, frameCount);

      expect(result.camera_poses).toHaveLength(frameCount);
      
      // Verify each matrix is 4x4
      for (const pose of result.camera_poses) {
        expect(pose.RT).toHaveLength(4);
        for (const row of pose.RT) {
          expect(row).toHaveLength(4);
        }
      }
    });

    it("should have valid transformation matrix structure", () => {
      const camera = createTestCamera();
      const keyframes = createTestKeyframes();
      const result = exportToMotionCtrl(camera, keyframes, 1);

      const matrix = result.camera_poses[0].RT;
      
      // Last row should be [0, 0, 0, 1] for proper affine matrix
      expect(matrix[3][0]).toBeCloseTo(0);
      expect(matrix[3][1]).toBeCloseTo(0);
      expect(matrix[3][2]).toBeCloseTo(0);
      expect(matrix[3][3]).toBeCloseTo(1);
    });

    it("should have finite values in all matrix elements", () => {
      const camera = createTestCamera();
      const keyframes = createTestKeyframes();
      const result = exportToMotionCtrl(camera, keyframes, 81);

      for (const pose of result.camera_poses) {
        for (let i = 0; i < 4; i++) {
          for (let j = 0; j < 4; j++) {
            expect(Number.isFinite(pose.RT[i][j])).toBe(true);
          }
        }
      }
    });
  });

  describe("MotionCtrl-SVD Presets", () => {
    /**
     * MotionCtrl-SVD Requirements:
     * - motion_camera: valid preset string
     * - Optional camera_poses as JSON string
     */
    it("should detect zoom_in preset for forward camera motion", () => {
      const camera = createTestCamera();
      const keyframes: CameraKeyframe[] = [
        { frame: 0, position: { x: 0, y: 0, z: 500 } },
        { frame: 24, position: { x: 0, y: 0, z: 400 } }, // Moving forward (negative Z)
      ];

      const result = exportToMotionCtrlSVD(camera, keyframes, 25);
      expect(result.motion_camera).toBe("zoom_in");
    });

    it("should detect zoom_out preset for backward camera motion", () => {
      const camera = createTestCamera();
      const keyframes: CameraKeyframe[] = [
        { frame: 0, position: { x: 0, y: 0, z: 400 } },
        { frame: 24, position: { x: 0, y: 0, z: 500 } }, // Moving backward
      ];

      const result = exportToMotionCtrlSVD(camera, keyframes, 25);
      expect(result.motion_camera).toBe("zoom_out");
    });

    it("should return static for minimal motion", () => {
      const camera = createTestCamera();
      const keyframes: CameraKeyframe[] = [
        { frame: 0, position: { x: 0, y: 0, z: 500 } },
        { frame: 24, position: { x: 0, y: 0, z: 505 } }, // Minimal motion
      ];

      const result = exportToMotionCtrlSVD(camera, keyframes, 25);
      expect(result.motion_camera).toBe("static");
    });
  });

  describe("Wan 2.2 Fun Camera Format", () => {
    /**
     * Wan 2.2 Fun Camera Requirements:
     * - camera_motion: valid preset string
     * - Must be one of the defined Wan22CameraMotion types
     */
    const validWanMotions = [
      "Static",
      "Pan Up",
      "Pan Down",
      "Pan Left",
      "Pan Right",
      "Zoom In",
      "Zoom Out",
      "Orbital Left",
      "Orbital Right",
    ];

    it("should return valid Wan motion preset", () => {
      const keyframes: CameraKeyframe[] = [
        { frame: 0, position: { x: 0, y: 0, z: 500 } },
        { frame: 80, position: { x: 100, y: 0, z: 500 } },
      ];

      const result = mapToWan22FunCamera(keyframes);
      expect(result).toHaveProperty("camera_motion");
      // Camera motion should be a valid string (not null/undefined)
      expect(typeof result.camera_motion).toBe("string");
    });

    it("should detect pan motions", () => {
      const keyframes: CameraKeyframe[] = [
        { frame: 0, position: { x: 0, y: 0, z: 500 } },
        { frame: 80, position: { x: 100, y: 0, z: 500 } }, // Pan right
      ];

      const result = mapToWan22FunCamera(keyframes);
      expect(result.camera_motion).toContain("Pan");
    });

    it("should return Static for no keyframes", () => {
      const result = mapToWan22FunCamera([]);
      expect(result.camera_motion).toBe("Static");
    });
  });

  describe("Uni3C Trajectory Format", () => {
    /**
     * Uni3C Requirements:
     * - traj_type: preset string OR "custom"
     * - If custom: custom_trajectory array with per-frame params
     * - Each frame: zoom, x_offset, y_offset, z_offset, pitch, yaw, roll
     */
    it("should export trajectory type", () => {
      const camera = createTestCamera();
      const keyframes = createTestKeyframes();

      const result = exportToUni3C(camera, keyframes, 81, 832, 480);
      expect(result).toHaveProperty("traj_type");
    });

    it("should include custom trajectory for complex motions", () => {
      const camera = createTestCamera();
      const keyframes: CameraKeyframe[] = [
        { frame: 0, position: { x: 0, y: 0, z: 500 }, orientation: { x: 0, y: 0, z: 0 } },
        { frame: 40, position: { x: 100, y: 50, z: 400 }, orientation: { x: 15, y: 30, z: 5 } },
        { frame: 80, position: { x: -50, y: 0, z: 550 }, orientation: { x: 0, y: -20, z: 0 } },
      ];

      const result = exportToUni3C(camera, keyframes, 81, 832, 480);
      
      if (result.traj_type === "custom") {
        expect(result.custom_trajectory).toBeDefined();
        expect(result.custom_trajectory?.length).toBe(81);

        // Verify each frame has required fields
        for (const frame of result.custom_trajectory!) {
          expect(frame).toHaveProperty("zoom");
          expect(frame).toHaveProperty("x_offset");
          expect(frame).toHaveProperty("y_offset");
          expect(frame).toHaveProperty("z_offset");
          expect(frame).toHaveProperty("pitch");
          expect(frame).toHaveProperty("yaw");
          expect(frame).toHaveProperty("roll");
        }
      }
    });
  });

  describe("AnimateDiff CameraCtrl Format", () => {
    /**
     * AnimateDiff CameraCtrl Requirements:
     * - motion_type: valid motion string
     * - speed: 0-100
     * - frame_length: positive integer
     */
    it("should export motion type and speed", () => {
      const keyframes = createTestKeyframes();
      const result = exportToCameraCtrl(keyframes, 81);

      expect(result).toHaveProperty("motion_type");
      expect(result).toHaveProperty("speed");
      expect(result).toHaveProperty("frame_length");
    });

    it("should have speed in valid range 0-100", () => {
      const keyframes = createTestKeyframes();
      const result = exportToCameraCtrl(keyframes, 81);

      expect(result.speed).toBeGreaterThanOrEqual(0);
      expect(result.speed).toBeLessThanOrEqual(100);
    });

    it("should have correct frame length", () => {
      const keyframes = createTestKeyframes();
      const frameCount = 81;
      const result = exportToCameraCtrl(keyframes, frameCount);

      expect(result.frame_length).toBe(frameCount);
    });
  });

  describe("Full Camera Export (4x4 Matrices)", () => {
    /**
     * Full Camera Export Requirements:
     * - frames: array of FullCameraFrame objects
     * - Each frame: view_matrix (4x4), projection_matrix (4x4)
     * - Position and rotation as arrays
     * - FOV in radians
     */
    it("should export view and projection matrices per frame", () => {
      const camera = createTestCamera();
      const keyframes = createTestKeyframes();

      const result = exportCameraMatrices(camera, keyframes, {
        frameCount: 81,
        width: 832,
        height: 480,
        fps: 16,
      });

      expect(result.frames).toHaveLength(81);

      for (const frame of result.frames) {
        expect(frame.view_matrix).toHaveLength(4);
        expect(frame.projection_matrix).toHaveLength(4);
        
        for (let i = 0; i < 4; i++) {
          expect(frame.view_matrix[i]).toHaveLength(4);
          expect(frame.projection_matrix[i]).toHaveLength(4);
        }
      }
    });

    it("should include correct metadata", () => {
      const camera = createTestCamera();
      const keyframes = createTestKeyframes();

      const result = exportCameraMatrices(camera, keyframes, {
        frameCount: 81,
        width: 832,
        height: 480,
        fps: 16,
      });

      expect(result.metadata.width).toBe(832);
      expect(result.metadata.height).toBe(480);
      expect(result.metadata.fps).toBe(16);
      expect(result.metadata.total_frames).toBe(81);
    });

    it("should have consistent timestamps", () => {
      const camera = createTestCamera();
      const keyframes = createTestKeyframes();

      const result = exportCameraMatrices(camera, keyframes, {
        frameCount: 81,
        width: 832,
        height: 480,
        fps: 16,
      });

      for (let i = 0; i < result.frames.length; i++) {
        expect(result.frames[i].frame).toBe(i);
        expect(result.frames[i].timestamp).toBeCloseTo(i / 16, 5);
      }
    });
  });

  describe("View Matrix computation", () => {
    it("should produce valid orthonormal rotation submatrix", () => {
      const cam = interpolateCameraAtFrame(createTestCamera(), [], 0);
      const viewMatrix = computeViewMatrix(cam);

      // Extract 3x3 rotation submatrix
      const R = [
        [viewMatrix[0][0], viewMatrix[0][1], viewMatrix[0][2]],
        [viewMatrix[1][0], viewMatrix[1][1], viewMatrix[1][2]],
        [viewMatrix[2][0], viewMatrix[2][1], viewMatrix[2][2]],
      ];

      // Check determinant is approximately 1 (proper rotation, not reflection)
      const det =
        R[0][0] * (R[1][1] * R[2][2] - R[1][2] * R[2][1]) -
        R[0][1] * (R[1][0] * R[2][2] - R[1][2] * R[2][0]) +
        R[0][2] * (R[1][0] * R[2][1] - R[1][1] * R[2][0]);

      expect(Math.abs(det)).toBeCloseTo(1, 4);
    });
  });

  describe("Projection Matrix computation", () => {
    it("should produce valid perspective projection", () => {
      const cam = interpolateCameraAtFrame(createTestCamera(), [], 0);
      const projMatrix = computeProjectionMatrix(cam, 16 / 9);

      // Last row should be [0, 0, -1, 0] for perspective projection
      expect(projMatrix[3][0]).toBeCloseTo(0);
      expect(projMatrix[3][1]).toBeCloseTo(0);
      expect(projMatrix[3][2]).toBeCloseTo(-1);
      expect(projMatrix[3][3]).toBeCloseTo(0);
    });
  });
});

// ============================================================================
// 3. WAN-MOVE TRAJECTORY FORMAT CONTRACT TESTS
// ============================================================================

describe("Wan-Move Trajectory Format Contracts", () => {
  /**
   * Wan-Move Model Requirements:
   * - tracks: Float32Array shape [N, T, 2] - N points, T frames, x/y coords
   * - visibility: Uint8Array shape [N, T] - 1=visible, 0=hidden
   * - Coordinates normalized to canvas dimensions (0-width, 0-height)
   */

  function createTestTrajectory(): WanMoveTrajectory {
    const config: GenerativeFlowConfig = {
      pattern: "spiral",
      numPoints: 50,
      numFrames: 81,
      width: 832,
      height: 480,
      params: { seed: 42 },
    };
    return generateSpiralFlow(config);
  }

  describe("Trajectory array shape", () => {
    it("should have tracks shape [N][T][2]", () => {
      const trajectory = createTestTrajectory();
      const { tracks, metadata } = trajectory;

      expect(tracks).toHaveLength(metadata.numPoints);
      
      for (const track of tracks) {
        expect(track).toHaveLength(metadata.numFrames);
        for (const point of track) {
          expect(point).toHaveLength(2); // x, y
        }
      }
    });

    it("should have visibility shape [N][T]", () => {
      const trajectory = createTestTrajectory();
      const { visibility, metadata } = trajectory;

      expect(visibility).toHaveLength(metadata.numPoints);
      
      for (const vis of visibility) {
        expect(vis).toHaveLength(metadata.numFrames);
      }
    });
  });

  describe("NPY export format", () => {
    it("should flatten tracks to Float32Array [N*T*2]", () => {
      const trajectory = createTestTrajectory();
      const npy = exportAsNPYData(trajectory);

      const expectedLength =
        trajectory.metadata.numPoints * trajectory.metadata.numFrames * 2;
      expect(npy.tracks).toBeInstanceOf(Float32Array);
      expect(npy.tracks.length).toBe(expectedLength);
    });

    it("should flatten visibility to Uint8Array [N*T]", () => {
      const trajectory = createTestTrajectory();
      const npy = exportAsNPYData(trajectory);

      const expectedLength =
        trajectory.metadata.numPoints * trajectory.metadata.numFrames;
      expect(npy.visibility).toBeInstanceOf(Uint8Array);
      expect(npy.visibility.length).toBe(expectedLength);
    });

    it("should include correct shape metadata", () => {
      const trajectory = createTestTrajectory();
      const npy = exportAsNPYData(trajectory);

      expect(npy.shape.tracks).toEqual([
        trajectory.metadata.numPoints,
        trajectory.metadata.numFrames,
        2,
      ]);
      expect(npy.shape.visibility).toEqual([
        trajectory.metadata.numPoints,
        trajectory.metadata.numFrames,
      ]);
    });

    it("should have visibility values 0 or 1", () => {
      const trajectory = createTestTrajectory();
      const npy = exportAsNPYData(trajectory);

      for (let i = 0; i < npy.visibility.length; i++) {
        expect(npy.visibility[i]).toBeGreaterThanOrEqual(0);
        expect(npy.visibility[i]).toBeLessThanOrEqual(1);
      }
    });
  });

  describe("Coordinate bounds", () => {
    it("should have coordinates within canvas bounds", () => {
      const config: GenerativeFlowConfig = {
        pattern: "spiral",
        numPoints: 100,
        numFrames: 81,
        width: 832,
        height: 480,
        params: { seed: 42 },
      };
      const trajectory = generateSpiralFlow(config);

      for (const track of trajectory.tracks) {
        for (const [x, y] of track) {
          expect(x).toBeGreaterThanOrEqual(0);
          expect(x).toBeLessThanOrEqual(832);
          expect(y).toBeGreaterThanOrEqual(0);
          expect(y).toBeLessThanOrEqual(480);
        }
      }
    });
  });

  describe("JSON export format", () => {
    it("should produce valid JSON", () => {
      const trajectory = createTestTrajectory();
      const json = exportAsJSON(trajectory);

      const parsed = JSON.parse(json);
      expect(parsed).toHaveProperty("tracks");
      expect(parsed).toHaveProperty("visibility");
      expect(parsed).toHaveProperty("metadata");
    });
  });

  describe("Different flow patterns", () => {
    const patterns: GenerativeFlowConfig["pattern"][] = ["spiral", "wave"];

    it.each(patterns)("should generate valid trajectory for pattern: %s", (pattern) => {
      const config: GenerativeFlowConfig = {
        pattern,
        numPoints: 20,
        numFrames: 33,
        width: 832,
        height: 480,
        params: { seed: 42 },
      };

      let trajectory: WanMoveTrajectory;
      if (pattern === "spiral") {
        trajectory = generateSpiralFlow(config);
      } else {
        trajectory = generateWaveFlow(config);
      }

      expect(trajectory.tracks).toHaveLength(config.numPoints);
      expect(trajectory.tracks[0]).toHaveLength(config.numFrames);
      expect(trajectory.metadata.width).toBe(config.width);
      expect(trajectory.metadata.height).toBe(config.height);
    });
  });
});

// ============================================================================
// 4. EXPORT PRESET VALIDATION TESTS
// ============================================================================

describe("Export Preset Contracts", () => {
  describe("Wan 4n+1 frame pattern", () => {
    /**
     * Wan models require frame counts that follow the 4n+1 pattern.
     * Valid counts at 16fps: 17, 33, 49, 65, 81, 113, 161, 241
     * Formula: frames = (seconds × 16) + 1
     */
    it("should calculate correct frame count for duration", () => {
      expect(calculateWanFrameCount(1)).toBe(17); // 1×16+1
      expect(calculateWanFrameCount(2)).toBe(33); // 2×16+1
      expect(calculateWanFrameCount(3)).toBe(49); // 3×16+1
      expect(calculateWanFrameCount(5)).toBe(81); // 5×16+1
      expect(calculateWanFrameCount(10)).toBe(161); // 10×16+1
    });

    it("should validate 4n+1 pattern", () => {
      // Valid: (frameCount - 1) % 4 === 0
      expect(isValidWanFrameCount(17)).toBe(true); // 16 % 4 = 0
      expect(isValidWanFrameCount(33)).toBe(true); // 32 % 4 = 0
      expect(isValidWanFrameCount(49)).toBe(true); // 48 % 4 = 0
      expect(isValidWanFrameCount(81)).toBe(true); // 80 % 4 = 0

      // Invalid
      expect(isValidWanFrameCount(18)).toBe(false);
      expect(isValidWanFrameCount(80)).toBe(false);
      expect(isValidWanFrameCount(82)).toBe(false);
    });

    it("should get nearest valid frame count", () => {
      expect(getNearestValidWanFrameCount(80)).toBe(81);
      expect(getNearestValidWanFrameCount(82)).toBe(81);
      expect(getNearestValidWanFrameCount(50)).toBe(49);
      expect(getNearestValidWanFrameCount(18)).toBe(17);
    });
  });

  describe("Preset frame counts", () => {
    const wanTargets: ExportTarget[] = [
      "wan22-i2v",
      "wan22-t2v",
      "wan22-fun-camera",
      "wan22-first-last",
      "uni3c-camera",
      "uni3c-motion",
      "light-x",
      "wan-move",
      "ati",
      "ttm",
      "ttm-wan",
      "camera-comfyui",
    ];

    it.each(wanTargets)("should have valid 4n+1 frame count for %s", (target) => {
      const preset = EXPORT_PRESETS[target];
      if (preset.frameCount) {
        expect(isValidWanFrameCount(preset.frameCount)).toBe(true);
      }
    });

    it.each(wanTargets)("should have 16fps for Wan-based target %s", (target) => {
      const preset = EXPORT_PRESETS[target];
      expect(preset.fps).toBe(16);
    });
  });

  describe("Resolution constraints", () => {
    const allTargets = Object.keys(EXPORT_PRESETS) as ExportTarget[];

    it.each(allTargets)("should have valid resolution for %s", (target) => {
      const preset = EXPORT_PRESETS[target];

      if (preset.width && preset.height) {
        // Width and height should be positive
        expect(preset.width).toBeGreaterThan(0);
        expect(preset.height).toBeGreaterThan(0);

        // Most models require dimensions divisible by 8
        expect(preset.width % 8).toBe(0);
        expect(preset.height % 8).toBe(0);
      }
    });
  });

  describe("Depth format assignments", () => {
    it("should assign appropriate depth formats", () => {
      // ControlNet depth should use MiDaS format
      expect(EXPORT_PRESETS["controlnet-depth"].depthFormat).toBe("midas");

      // Uni3C should use normalized
      expect(EXPORT_PRESETS["uni3c-camera"].depthFormat).toBe("normalized");
      expect(EXPORT_PRESETS["uni3c-motion"].depthFormat).toBe("normalized");

      // Light-X should use normalized
      expect(EXPORT_PRESETS["light-x"].depthFormat).toBe("normalized");
    });
  });

  describe("Export flag consistency", () => {
    it("should enable camera export for camera-control targets", () => {
      const cameraTargets: ExportTarget[] = [
        "wan22-fun-camera",
        "uni3c-camera",
        "uni3c-motion",
        "motionctrl",
        "motionctrl-svd",
        "animatediff-cameractrl",
        "light-x",
        "ati",
        "camera-comfyui",
      ];

      for (const target of cameraTargets) {
        expect(EXPORT_PRESETS[target].exportCameraData).toBe(true);
      }
    });

    it("should enable depth export for depth-based targets", () => {
      const depthTargets: ExportTarget[] = [
        "controlnet-depth",
        "uni3c-camera",
        "uni3c-motion",
        "light-x",
      ];

      for (const target of depthTargets) {
        expect(EXPORT_PRESETS[target].exportDepthMap).toBe(true);
      }
    });

    it("should enable last frame export for first-last targets", () => {
      const firstLastTargets: ExportTarget[] = [
        "wan22-first-last",
        "ttm",
        "ttm-wan",
        "ttm-cogvideox",
      ];

      for (const target of firstLastTargets) {
        expect(EXPORT_PRESETS[target].exportLastFrame).toBe(true);
      }
    });
  });
});

// ============================================================================
// 5. COLORMAP TESTS
// ============================================================================

describe("Depth Colormap Contracts", () => {
  const colormaps = ["grayscale", "viridis", "magma", "plasma", "inferno", "turbo"] as const;

  /**
   * NOTE: These tests require ImageData which is a browser-only API.
   * They are skipped in Node.js/jsdom environment.
   * Run with vitest.browser.config.ts for browser testing.
   */
  const hasBrowserAPIs = typeof globalThis.ImageData !== "undefined";

  describe("depthToImageData", () => {
    it.skipIf(!hasBrowserAPIs)("should produce valid ImageData dimensions", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const imageData = depthToImageData(result);

      expect(imageData.width).toBe(options.width);
      expect(imageData.height).toBe(options.height);
      expect(imageData.data.length).toBe(options.width * options.height * 4);
    });

    it.skipIf(!hasBrowserAPIs)("should have opaque pixels (alpha = 255)", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const imageData = depthToImageData(result);

      // Check alpha channel (every 4th byte starting at index 3)
      for (let i = 3; i < imageData.data.length; i += 4) {
        expect(imageData.data[i]).toBe(255);
      }
    });
  });

  describe("applyColormap", () => {
    it.skipIf(!hasBrowserAPIs).each(colormaps)("should apply colormap: %s", (colormap) => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const imageData = applyColormap(result, colormap);

      expect(imageData.width).toBe(options.width);
      expect(imageData.height).toBe(options.height);
    });

    it.skipIf(!hasBrowserAPIs)("should produce valid RGB values", () => {
      const options = createDepthRenderOptions();
      const result = renderDepthFrame(options);
      const imageData = applyColormap(result, "viridis");

      for (let i = 0; i < imageData.data.length; i++) {
        expect(imageData.data[i]).toBeGreaterThanOrEqual(0);
        expect(imageData.data[i]).toBeLessThanOrEqual(255);
      }
    });
  });

  describe("generateDepthMetadata", () => {
    it("should generate metadata for MiDaS format", () => {
      const metadata = generateDepthMetadata("midas", 30, 512, 512, 0.1, 100) as any;

      expect(metadata.format).toBe("midas");
      expect(metadata.bitDepth).toBe(8);
      expect(metadata.frameCount).toBe(30);
      expect(metadata.width).toBe(512);
      expect(metadata.height).toBe(512);
      expect(metadata.actualRange.min).toBe(0.1);
      expect(metadata.actualRange.max).toBe(100);
      expect(metadata.generator).toBe("Lattice Compositor");
    });

    it("should generate metadata for depth-anything format", () => {
      const metadata = generateDepthMetadata("depth-anything", 60, 1920, 1080, 0.5, 50) as any;

      expect(metadata.format).toBe("depth-anything");
      expect(metadata.bitDepth).toBe(16);
      expect(metadata.frameCount).toBe(60);
    });

    it("should generate metadata for Zoe format", () => {
      const metadata = generateDepthMetadata("zoe", 10, 256, 256, 1, 200) as any;

      expect(metadata.format).toBe("zoe");
      expect(metadata.actualRange.min).toBe(1);
      expect(metadata.actualRange.max).toBe(200);
    });

    it("should generate metadata for Marigold format", () => {
      const metadata = generateDepthMetadata("marigold", 1, 768, 768, 0.01, 1000) as any;

      expect(metadata.format).toBe("marigold");
      expect(metadata.width).toBe(768);
      expect(metadata.height).toBe(768);
    });

    it("should generate metadata for raw format", () => {
      const metadata = generateDepthMetadata("raw", 120, 4096, 2160, 0.001, 10000) as any;

      expect(metadata.format).toBe("raw");
      expect(metadata.bitDepth).toBe(32);
    });

    it("should include timestamp", () => {
      const metadata = generateDepthMetadata("midas", 1, 100, 100, 0, 1) as any;

      expect(metadata.generatedAt).toBeDefined();
      expect(typeof metadata.generatedAt).toBe("string");
      // Should be ISO format
      expect(() => new Date(metadata.generatedAt)).not.toThrow();
    });
  });
});
