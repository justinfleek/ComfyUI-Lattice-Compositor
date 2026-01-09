/**
 * Camera Export Formats Tests - FULL COVERAGE
 *
 * Tests all camera export functions for various AI video generation formats.
 *
 * @audit P0 CRITICAL - Camera format compliance for AI models
 */

import { describe, it, expect } from "vitest";
import {
  interpolateCameraAtFrame,
  computeViewMatrix,
  computeProjectionMatrix,
  exportToMotionCtrl,
  exportToMotionCtrlSVD,
  detectMotionCtrlSVDPreset,
  mapToWan22FunCamera,
  exportToUni3C,
  detectCameraCtrlMotionType,
  exportToCameraCtrl,
  exportCameraMatrices,
  exportCameraForTarget,
  analyzeCameraMotion,
  detectUni3CTrajectoryType,
} from "@/services/export/cameraExportFormats";
import type { Camera3D, CameraKeyframe } from "@/types/camera";

// ============================================================================
// Test Fixtures
// ============================================================================

function createTestCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  const base: Camera3D = {
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
    filmSize: 36,
    zoom: 1778, // Realistic zoom for 50mm
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
    nearClip: 1,
    farClip: 10000,
  };
  return { ...base, ...overrides };
}

function createKeyframe(
  frame: number,
  overrides: Partial<CameraKeyframe> = {}
): CameraKeyframe {
  return {
    frame,
    temporalInterpolation: "linear",
    ...overrides,
  };
}

// ============================================================================
// interpolateCameraAtFrame Tests
// ============================================================================

describe("interpolateCameraAtFrame", () => {
  it("should return camera defaults when no keyframes", () => {
    const camera = createTestCamera({
      position: { x: 100, y: 200, z: 300 },
      orientation: { x: 10, y: 20, z: 30 },
    });

    const result = interpolateCameraAtFrame(camera, [], 10);

    expect(result.position).toEqual({ x: 100, y: 200, z: 300 });
    expect(result.rotation).toEqual({ x: 10, y: 20, z: 30 });
    expect(result.focalLength).toBe(50);
  });

  it("should return keyframe values at exact frame", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { position: { x: 100, y: 100, z: 100 } }),
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 10);

    expect(result.position).toEqual({ x: 100, y: 100, z: 100 });
  });

  it("should interpolate between keyframes", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { position: { x: 100, y: 100, z: 100 } }),
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 5);

    expect(result.position.x).toBeCloseTo(50);
    expect(result.position.y).toBeCloseTo(50);
    expect(result.position.z).toBeCloseTo(50);
  });

  it("should interpolate focal length", () => {
    const camera = createTestCamera({ focalLength: 50 });
    const keyframes = [
      createKeyframe(0, { focalLength: 35 }),
      createKeyframe(10, { focalLength: 85 }),
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 5);

    expect(result.focalLength).toBeCloseTo(60);
  });

  it("should handle angle wrapping for rotation", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(0, { orientation: { x: 0, y: 350, z: 0 } }),
      createKeyframe(10, { orientation: { x: 0, y: 10, z: 0 } }),
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 5);

    // Should interpolate through 360 (350 -> 360 -> 10)
    // At midpoint, should be at 0 or 360
    expect(result.rotation.y).toBeCloseTo(360, 0); // Allow variance
  });

  it("should use camera defaults for missing keyframe properties", () => {
    const camera = createTestCamera({
      focalLength: 50,
      zoom: 1.5,
    });
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { position: { x: 100, y: 100, z: 100 } }),
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 5);

    expect(result.focalLength).toBe(50);
    expect(result.zoom).toBe(1.5);
  });

  it("should handle single keyframe", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(5, { position: { x: 50, y: 50, z: 50 } }),
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 10);

    expect(result.position).toEqual({ x: 50, y: 50, z: 50 });
  });
});

// ============================================================================
// computeViewMatrix Tests
// ============================================================================

describe("computeViewMatrix", () => {
  it("should return 4x4 matrix", () => {
    const cam = {
      position: { x: 0, y: 0, z: 500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeViewMatrix(cam);

    expect(matrix.length).toBe(4);
    expect(matrix[0].length).toBe(4);
    expect(matrix[1].length).toBe(4);
    expect(matrix[2].length).toBe(4);
    expect(matrix[3].length).toBe(4);
  });

  it("should have identity rotation for zero angles", () => {
    const cam = {
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeViewMatrix(cam);

    // Top-left 3x3 should be identity for no rotation
    expect(matrix[0][0]).toBeCloseTo(1);
    expect(matrix[1][1]).toBeCloseTo(1);
    expect(matrix[2][2]).toBeCloseTo(1);
  });

  it("should include translation in last column", () => {
    const cam = {
      position: { x: 100, y: 200, z: 300 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeViewMatrix(cam);

    // Translation is negative of position for view matrix
    expect(matrix[0][3]).toBeCloseTo(-100);
    expect(matrix[1][3]).toBeCloseTo(-200);
    expect(matrix[2][3]).toBeCloseTo(-300);
  });

  it("should have [0,0,0,1] as last row", () => {
    const cam = {
      position: { x: 100, y: 200, z: 300 },
      rotation: { x: 45, y: 30, z: 15 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeViewMatrix(cam);

    expect(matrix[3]).toEqual([0, 0, 0, 1]);
  });
});

// ============================================================================
// computeProjectionMatrix Tests
// ============================================================================

describe("computeProjectionMatrix", () => {
  it("should return 4x4 matrix", () => {
    const cam = {
      position: { x: 0, y: 0, z: 500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeProjectionMatrix(cam, 16 / 9);

    expect(matrix.length).toBe(4);
    expect(matrix[0].length).toBe(4);
  });

  it("should scale by aspect ratio", () => {
    const cam = {
      position: { x: 0, y: 0, z: 500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix16x9 = computeProjectionMatrix(cam, 16 / 9);
    const matrix4x3 = computeProjectionMatrix(cam, 4 / 3);

    // Different aspect ratios should produce different X scaling
    expect(matrix16x9[0][0]).not.toBeCloseTo(matrix4x3[0][0]);
  });

  it("should have -1 in [3][2] for perspective divide", () => {
    const cam = {
      position: { x: 0, y: 0, z: 500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeProjectionMatrix(cam, 16 / 9);

    expect(matrix[3][2]).toBe(-1);
  });

  it("should respect near/far clip planes", () => {
    const cam = {
      position: { x: 0, y: 0, z: 500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix1 = computeProjectionMatrix(cam, 16 / 9, 0.1, 100);
    const matrix2 = computeProjectionMatrix(cam, 16 / 9, 10, 10000);

    // Different clip planes should produce different depth values
    // Use larger difference in near/far to ensure noticeable difference
    expect(matrix1[2][3]).not.toBeCloseTo(matrix2[2][3]);
  });
});

// ============================================================================
// detectMotionCtrlSVDPreset Tests
// ============================================================================

describe("detectMotionCtrlSVDPreset", () => {
  it("should return static for no keyframes", () => {
    const result = detectMotionCtrlSVDPreset([]);
    expect(result).toBe("static");
  });

  it("should return static for single keyframe", () => {
    const result = detectMotionCtrlSVDPreset([createKeyframe(0)]);
    expect(result).toBe("static");
  });

  it("should detect zoom_in for negative Z movement", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 400 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("zoom_in");
  });

  it("should detect zoom_out for positive Z movement", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 400 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 600 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("zoom_out");
  });

  it("should detect pan_left for negative X movement", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 100, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: -100, y: 0, z: 500 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("pan_left");
  });

  it("should detect pan_right for positive X movement", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: -100, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 100, y: 0, z: 500 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("pan_right");
  });

  it("should detect rotate_cw for positive Y rotation", () => {
    const keyframes = [
      createKeyframe(0, { orientation: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { orientation: { x: 0, y: 45, z: 0 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("rotate_cw");
  });

  it("should detect rotate_ccw for negative Y rotation", () => {
    const keyframes = [
      createKeyframe(0, { orientation: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { orientation: { x: 0, y: -45, z: 0 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("rotate_ccw");
  });
});

// ============================================================================
// exportToMotionCtrl Tests
// ============================================================================

describe("exportToMotionCtrl", () => {
  it("should return camera_poses array", () => {
    const camera = createTestCamera();
    const keyframes = [createKeyframe(0), createKeyframe(10)];

    const result = exportToMotionCtrl(camera, keyframes, 10);

    expect(result.camera_poses).toBeDefined();
    expect(result.camera_poses.length).toBe(10);
  });

  it("should include RT matrix for each frame", () => {
    const camera = createTestCamera();
    const keyframes = [createKeyframe(0)];

    const result = exportToMotionCtrl(camera, keyframes, 5);

    for (const pose of result.camera_poses) {
      expect(pose.RT).toBeDefined();
      expect(pose.RT.length).toBe(4);
      expect(pose.RT[0].length).toBe(4);
    }
  });
});

// ============================================================================
// exportToMotionCtrlSVD Tests
// ============================================================================

describe("exportToMotionCtrlSVD", () => {
  it("should return motion_camera preset for simple motion", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 400 } }),
    ];

    const result = exportToMotionCtrlSVD(camera, keyframes, 10);

    expect(result.motion_camera).toBe("zoom_in");
  });

  it("should include full poses for complex motion", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(5, { position: { x: 100, y: 50, z: 450 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 400 } }),
    ];

    const result = exportToMotionCtrlSVD(camera, keyframes, 10);

    expect(result.camera_poses).toBeDefined();
  });
});

// ============================================================================
// mapToWan22FunCamera Tests
// ============================================================================

describe("mapToWan22FunCamera", () => {
  it("should return Static for no keyframes", () => {
    const result = mapToWan22FunCamera([]);
    expect(result.camera_motion).toBe("Static");
  });

  it("should detect Zoom In motion", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 300 } }),
    ];

    const result = mapToWan22FunCamera(keyframes);
    expect(result.camera_motion).toBe("Zoom In");
  });

  it("should detect Zoom Out motion", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 300 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 500 } }),
    ];

    const result = mapToWan22FunCamera(keyframes);
    expect(result.camera_motion).toBe("Zoom Out");
  });
});

// ============================================================================
// exportToUni3C Tests
// ============================================================================

describe("exportToUni3C", () => {
  it("should return trajectory data", () => {
    const camera = createTestCamera();
    const keyframes = [createKeyframe(0), createKeyframe(10)];

    const result = exportToUni3C(camera, keyframes, 10, 1920, 1080);

    expect(result.traj_type).toBeDefined();
  });

  it("should include custom trajectory for animated camera with pan+zoom", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 200, y: 100, z: 300 } }), // Significant pan + zoom
    ];

    const result = exportToUni3C(camera, keyframes, 10, 1920, 1080);

    // Complex motion triggers custom trajectory
    if (result.traj_type === "custom") {
      expect(result.custom_trajectory).toBeDefined();
      expect(result.custom_trajectory!.length).toBe(10);
    }
  });

  it("should have trajectory frame objects with expected properties", () => {
    const camera = createTestCamera();
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 200, y: 100, z: 300 } }),
    ];

    const result = exportToUni3C(camera, keyframes, 10, 1920, 1080);

    if (result.custom_trajectory && result.custom_trajectory.length > 0) {
      const frame = result.custom_trajectory[0];
      expect(frame).toHaveProperty("zoom");
      expect(frame).toHaveProperty("x_offset");
      expect(frame).toHaveProperty("y_offset");
    }
  });
});

// ============================================================================
// detectCameraCtrlMotionType Tests
// ============================================================================

describe("detectCameraCtrlMotionType", () => {
  it("should return Static for no motion", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 500 } }),
    ];

    const result = detectCameraCtrlMotionType(keyframes);
    expect(result).toBe("Static");
  });

  it("should detect Move Forward", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 300 } }),
    ];

    const result = detectCameraCtrlMotionType(keyframes);
    expect(result).toBe("Move Forward");
  });

  it("should detect Move Backward", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 300 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 500 } }),
    ];

    const result = detectCameraCtrlMotionType(keyframes);
    expect(result).toBe("Move Backward");
  });

  it("should detect Move Left", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 100, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: -100, y: 0, z: 500 } }),
    ];

    const result = detectCameraCtrlMotionType(keyframes);
    expect(result).toBe("Move Left");
  });

  it("should detect Move Right", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: -100, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 100, y: 0, z: 500 } }),
    ];

    const result = detectCameraCtrlMotionType(keyframes);
    expect(result).toBe("Move Right");
  });

  it("should detect Rotate Right", () => {
    const keyframes = [
      createKeyframe(0, { orientation: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { orientation: { x: 0, y: 45, z: 0 } }),
    ];

    const result = detectCameraCtrlMotionType(keyframes);
    expect(result).toBe("Rotate Right");
  });
});

// ============================================================================
// exportToCameraCtrl Tests
// ============================================================================

describe("exportToCameraCtrl", () => {
  it("should return motion type and speed", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 300 } }),
    ];

    const result = exportToCameraCtrl(keyframes, 10);

    expect(result.motion_type).toBeDefined();
    expect(result.speed).toBeDefined();
    expect(result.frame_length).toBe(10);
  });

  it("should calculate speed based on motion magnitude", () => {
    const smallMotion = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 480 } }),
    ];

    const largeMotion = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 100 } }),
    ];

    const smallResult = exportToCameraCtrl(smallMotion, 10);
    const largeResult = exportToCameraCtrl(largeMotion, 10);

    expect(largeResult.speed).toBeGreaterThan(smallResult.speed);
  });
});

// ============================================================================
// exportCameraMatrices Tests
// ============================================================================

describe("exportCameraMatrices", () => {
  it("should return frames and metadata", () => {
    const camera = createTestCamera();
    const keyframes = [createKeyframe(0)];

    const result = exportCameraMatrices(camera, keyframes, {
      frameCount: 10,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    expect(result.frames).toBeDefined();
    expect(result.frames.length).toBe(10);
    expect(result.metadata).toBeDefined();
  });

  it("should include view and projection matrices per frame", () => {
    const camera = createTestCamera();
    const keyframes = [createKeyframe(0)];

    const result = exportCameraMatrices(camera, keyframes, {
      frameCount: 5,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    for (const frame of result.frames) {
      expect(frame.view_matrix.length).toBe(4);
      expect(frame.projection_matrix.length).toBe(4);
      expect(frame.position.length).toBe(3);
      expect(frame.rotation.length).toBe(3);
    }
  });

  it("should include correct timestamps", () => {
    const camera = createTestCamera();
    const keyframes = [createKeyframe(0)];

    const result = exportCameraMatrices(camera, keyframes, {
      frameCount: 5,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    expect(result.frames[0].timestamp).toBeCloseTo(0);
    expect(result.frames[1].timestamp).toBeCloseTo(1 / 24);
    expect(result.frames[2].timestamp).toBeCloseTo(2 / 24);
  });

  it("should include metadata fields", () => {
    const camera = createTestCamera();
    const keyframes = [createKeyframe(0)];

    const result = exportCameraMatrices(camera, keyframes, {
      frameCount: 10,
      width: 1920,
      height: 1080,
      fps: 30,
    });

    expect(result.metadata.width).toBe(1920);
    expect(result.metadata.height).toBe(1080);
    expect(result.metadata.fps).toBe(30);
    expect(result.metadata.total_frames).toBe(10);
  });
});

// ============================================================================
// exportCameraForTarget Tests
// ============================================================================

describe("exportCameraForTarget", () => {
  const camera = createTestCamera();
  const keyframes = [
    createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
    createKeyframe(10, { position: { x: 100, y: 0, z: 400 } }),
  ];

  it("should route to MotionCtrl format", () => {
    const result = exportCameraForTarget(
      "motionctrl",
      camera,
      keyframes,
      10
    ) as any;

    expect(result.camera_poses).toBeDefined();
  });

  it("should route to MotionCtrl-SVD format", () => {
    const result = exportCameraForTarget(
      "motionctrl-svd",
      camera,
      keyframes,
      10
    ) as any;

    expect(result.motion_camera).toBeDefined();
  });

  it("should route to Wan22 Fun Camera format", () => {
    const result = exportCameraForTarget(
      "wan22-fun-camera",
      camera,
      keyframes,
      10
    ) as any;

    expect(result.camera_motion).toBeDefined();
  });

  it("should route to Uni3C format", () => {
    const result = exportCameraForTarget(
      "uni3c-camera",
      camera,
      keyframes,
      10,
      1920,
      1080
    ) as any;

    expect(result.traj_type).toBeDefined();
  });

  it("should route to AnimateDiff CameraCtrl format", () => {
    const result = exportCameraForTarget(
      "animatediff-cameractrl",
      camera,
      keyframes,
      10
    ) as any;

    expect(result.motion_type).toBeDefined();
    expect(result.speed).toBeDefined();
  });

  it("should use full matrices for unknown targets", () => {
    const result = exportCameraForTarget(
      "unknown-target" as any,
      camera,
      keyframes,
      10,
      1920,
      1080,
      24
    ) as any;

    expect(result.frames).toBeDefined();
    expect(result.metadata).toBeDefined();
  });
});

// ============================================================================
// Determinism Tests
// ============================================================================

describe("Determinism", () => {
  it("should produce identical output for identical input", () => {
    const camera = createTestCamera({
      position: { x: 100, y: 200, z: 300 },
      orientation: { x: 15, y: 30, z: 45 },
    });
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 100, y: 50, z: 400 } }),
    ];

    const result1 = exportCameraMatrices(camera, keyframes, {
      frameCount: 10,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    const result2 = exportCameraMatrices(camera, keyframes, {
      frameCount: 10,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
  });
});

// ============================================================================
// analyzeCameraMotion Tests
// ============================================================================

describe("analyzeCameraMotion", () => {
  it("should return all false for no keyframes", () => {
    const result = analyzeCameraMotion([]);

    expect(result.hasPan).toBe(false);
    expect(result.hasZoom).toBe(false);
    expect(result.hasOrbit).toBe(false);
    expect(result.hasRotation).toBe(false);
  });

  it("should return all false for single keyframe", () => {
    const result = analyzeCameraMotion([createKeyframe(0)]);

    expect(result.hasPan).toBe(false);
    expect(result.hasZoom).toBe(false);
  });

  it("should detect pan left", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 100, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: -100, y: 0, z: 500 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasPan).toBe(true);
    expect(result.panDirection).toBe("left");
  });

  it("should detect pan right", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: -100, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 100, y: 0, z: 500 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasPan).toBe(true);
    expect(result.panDirection).toBe("right");
  });

  it("should detect pan up", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 100, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: -100, z: 500 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasPan).toBe(true);
    expect(result.panDirection).toBe("up");
  });

  it("should detect pan down", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: -100, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 100, z: 500 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasPan).toBe(true);
    expect(result.panDirection).toBe("down");
  });

  it("should detect zoom in", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 300 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasZoom).toBe(true);
    expect(result.zoomDirection).toBe("in");
  });

  it("should detect zoom out", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 300 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 500 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasZoom).toBe(true);
    expect(result.zoomDirection).toBe("out");
  });

  it("should detect rotation", () => {
    const keyframes = [
      createKeyframe(0, { orientation: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { orientation: { x: 0, y: 45, z: 0 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasRotation).toBe(true);
    expect(result.rotationMagnitude).toBe(45);
  });

  it("should calculate pan magnitude", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 100, y: 0, z: 500 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.panMagnitude).toBe(100);
  });

  it("should calculate zoom magnitude", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 300 } }),
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.zoomMagnitude).toBe(200);
  });
});

// ============================================================================
// detectUni3CTrajectoryType Tests
// ============================================================================

describe("detectUni3CTrajectoryType", () => {
  it("should return free1 for no motion", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: 500 } }),
    ];

    const result = detectUni3CTrajectoryType(keyframes);

    expect(result).toBe("free1");
  });

  it("should return orbit for large rotation with position change", () => {
    const keyframes = [
      createKeyframe(0, { 
        position: { x: -100, y: 0, z: 500 },
        orientation: { x: 0, y: 0, z: 0 },
      }),
      createKeyframe(10, { 
        position: { x: 100, y: 0, z: 500 },
        orientation: { x: 0, y: 90, z: 0 },
      }),
    ];

    const result = detectUni3CTrajectoryType(keyframes);

    expect(result).toBe("orbit");
  });

  it("should return custom for complex motion", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: 500 } }),
      createKeyframe(10, { position: { x: 200, y: 100, z: 300 } }),
    ];

    const result = detectUni3CTrajectoryType(keyframes);

    expect(result).toBe("custom");
  });
});
