/**
 * Camera Export Formats Adversarial Tests
 *
 * Tests designed to BREAK the camera export system and verify it fails gracefully.
 * Focus areas:
 * - Matrix computation with invalid inputs
 * - Interpolation edge cases
 * - Projection matrix validation
 * - Format conversion edge cases
 *
 * @module CameraExportFormatsAdversarialTests
 */

import { describe, expect, it, vi } from "vitest";

import {
  analyzeCameraMotion,
  computeProjectionMatrix,
  computeViewMatrix,
  detectMotionCtrlSVDPreset,
  exportCameraForTarget,
  exportCameraMatrices,
  exportToCameraCtrl,
  exportToMotionCtrl,
  exportToUni3C,
  interpolateCameraAtFrame,
  mapToWan22FunCamera,
} from "@/services/export/cameraExportFormats";
import type { Camera3D, CameraKeyframe } from "@/types/camera";

// ============================================================================
// Test Fixtures
// ============================================================================

function createValidCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  return {
    id: "test-camera",
    name: "Test Camera",
    type: "perspective",
    position: { x: 0, y: 0, z: -500 },
    orientation: { x: 0, y: 0, z: 0 },
    xRotation: 0,
    yRotation: 0,
    zRotation: 0,
    focalLength: 50,
    angleOfView: 39.6,
    zoom: 1,
    nearClip: 1,
    farClip: 10000,
    filmSize: 36,
    depthOfField: {
      enabled: false,
      focusDistance: 100,
      aperture: 2.8,
      bladeCount: 6,
    },
    ...overrides,
  } as Camera3D;
}

function createKeyframe(
  frame: number,
  overrides: Partial<CameraKeyframe> = {},
): CameraKeyframe {
  return {
    frame,
    position: { x: 0, y: 0, z: -500 },
    orientation: { x: 0, y: 0, z: 0 },
    focalLength: 50,
    zoom: 1,
    focusDistance: 100,
    ...overrides,
  };
}

// ============================================================================
// CRITICAL: View Matrix Computation
// ============================================================================

describe("CRITICAL: computeViewMatrix - Invalid Rotation Values", () => {
  it("should handle NaN rotation values", () => {
    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: NaN, y: NaN, z: NaN },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    // Should not throw - uses safe defaults
    const matrix = computeViewMatrix(cam);

    expect(matrix).toBeDefined();
    expect(matrix.length).toBe(4);
    expect(matrix[0].length).toBe(4);

    // Matrix should still be valid (no NaN in output)
    for (const row of matrix) {
      for (const val of row) {
        expect(Number.isFinite(val)).toBe(true);
      }
    }
  });

  it("should handle Infinity position values", () => {
    const cam = {
      position: { x: Infinity, y: -Infinity, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeViewMatrix(cam);

    // Matrix will have Infinity in translation - that's expected
    // The important thing is it doesn't crash
    expect(matrix).toBeDefined();
    expect(matrix.length).toBe(4);
  });

  it("should handle extreme rotation values (multiple rotations)", () => {
    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: 720, y: 1080, z: 3600 }, // Multiple full rotations
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeViewMatrix(cam);

    // Should still produce valid rotation matrix (periodic)
    for (const row of matrix) {
      for (const val of row) {
        expect(Number.isFinite(val)).toBe(true);
      }
    }
  });

  it("should produce orthonormal rotation part", () => {
    const cam = {
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 30, y: 45, z: 15 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeViewMatrix(cam);

    // Extract 3x3 rotation part
    const R = [
      [matrix[0][0], matrix[0][1], matrix[0][2]],
      [matrix[1][0], matrix[1][1], matrix[1][2]],
      [matrix[2][0], matrix[2][1], matrix[2][2]],
    ];

    // Check orthonormality: R * R^T should be identity (within tolerance)
    for (let i = 0; i < 3; i++) {
      for (let j = 0; j < 3; j++) {
        let sum = 0;
        for (let k = 0; k < 3; k++) {
          sum += R[i][k] * R[j][k];
        }
        const expected = i === j ? 1 : 0;
        expect(Math.abs(sum - expected)).toBeLessThan(0.0001);
      }
    }
  });
});

// ============================================================================
// CRITICAL: Projection Matrix Validation
// ============================================================================

describe("CRITICAL: computeProjectionMatrix - Invalid Aspect Ratio", () => {
  it("should throw for zero aspect ratio", () => {
    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    expect(() => {
      computeProjectionMatrix(cam, 0);
    }).toThrow(/aspect.*0|invalid/i);
  });

  it("should throw for negative aspect ratio", () => {
    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    expect(() => {
      computeProjectionMatrix(cam, -1.78);
    }).toThrow(/aspect.*-1.78|invalid/i);
  });

  it("should throw for NaN aspect ratio", () => {
    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    expect(() => {
      computeProjectionMatrix(cam, NaN);
    }).toThrow(/aspect.*NaN|invalid/i);
  });

  it("should use fallback for invalid nearClip", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeProjectionMatrix(cam, 1.78, -1, 1000);

    expect(matrix).toBeDefined();
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });

  it("should use fallback when farClip <= nearClip", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeProjectionMatrix(cam, 1.78, 100, 50);

    expect(matrix).toBeDefined();
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });

  it("should handle NaN focalLength with fallback", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const cam = {
      position: { x: 0, y: 0, z: -500 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: NaN,
      zoom: 1,
      focusDistance: 100,
    };

    const matrix = computeProjectionMatrix(cam, 1.78);

    expect(matrix).toBeDefined();
    // Should not have NaN in output
    for (const row of matrix) {
      for (const val of row) {
        expect(Number.isFinite(val)).toBe(true);
      }
    }
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });
});

// ============================================================================
// HIGH: Camera Interpolation Edge Cases
// ============================================================================

describe("HIGH: interpolateCameraAtFrame - Empty/Missing Keyframes", () => {
  it("should return camera defaults for empty keyframes array", () => {
    const camera = createValidCamera();
    const result = interpolateCameraAtFrame(camera, [], 10);

    expect(result.position).toEqual(camera.position);
    expect(result.rotation).toEqual(camera.orientation);
    expect(result.focalLength).toBe(camera.focalLength);
  });

  it("should return camera defaults for null keyframes", () => {
    const camera = createValidCamera();
    const result = interpolateCameraAtFrame(camera, null as any, 10);

    expect(result.position).toEqual(camera.position);
  });

  it("should handle single keyframe", () => {
    const camera = createValidCamera();
    const keyframes = [
      createKeyframe(5, { position: { x: 100, y: 0, z: -500 } }),
    ];

    // Before keyframe
    const before = interpolateCameraAtFrame(camera, keyframes, 0);
    expect(before.position.x).toBe(100);

    // At keyframe
    const at = interpolateCameraAtFrame(camera, keyframes, 5);
    expect(at.position.x).toBe(100);

    // After keyframe
    const after = interpolateCameraAtFrame(camera, keyframes, 10);
    expect(after.position.x).toBe(100);
  });

  it("should handle keyframes without position", () => {
    const camera = createValidCamera({ position: { x: 50, y: 0, z: -500 } });
    const keyframes = [
      { frame: 0, orientation: { x: 0, y: 0, z: 0 } } as CameraKeyframe,
      { frame: 10, orientation: { x: 0, y: 45, z: 0 } } as CameraKeyframe,
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 5);

    // Position should fall back to camera default
    expect(result.position).toEqual(camera.position);
  });

  it("should interpolate angles correctly across 360 boundary", () => {
    const camera = createValidCamera();
    const keyframes = [
      createKeyframe(0, { orientation: { x: 0, y: 350, z: 0 } }),
      createKeyframe(10, { orientation: { x: 0, y: 10, z: 0 } }),
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 5);

    // Should take short path: 350 -> 360/0 -> 10 (20 degrees)
    // Midpoint should be 0 (or 360)
    expect(Math.abs(result.rotation.y)).toBeLessThan(5);
  });
});

describe("HIGH: interpolateCameraAtFrame - Division by Zero", () => {
  it("should handle keyframes at same frame", () => {
    const camera = createValidCamera();
    const keyframes = [
      createKeyframe(5, { position: { x: 0, y: 0, z: -500 } }),
      createKeyframe(5, { position: { x: 100, y: 0, z: -500 } }),
    ];

    // Should not divide by zero - use first keyframe
    const result = interpolateCameraAtFrame(camera, keyframes, 5);
    expect(Number.isFinite(result.position.x)).toBe(true);
  });
});

// ============================================================================
// HIGH: Motion Analysis
// ============================================================================

describe("HIGH: analyzeCameraMotion - Edge Cases", () => {
  it("should return no motion for empty keyframes", () => {
    const result = analyzeCameraMotion([]);

    expect(result.hasPan).toBe(false);
    expect(result.hasZoom).toBe(false);
    expect(result.hasOrbit).toBe(false);
    expect(result.hasRotation).toBe(false);
  });

  it("should return no motion for single keyframe", () => {
    const result = analyzeCameraMotion([createKeyframe(0)]);

    expect(result.hasPan).toBe(false);
    expect(result.hasZoom).toBe(false);
  });

  it("should handle keyframes with missing position/orientation", () => {
    const keyframes = [
      { frame: 0 } as CameraKeyframe,
      { frame: 10 } as CameraKeyframe,
    ];

    // Should not throw - uses defaults
    const result = analyzeCameraMotion(keyframes);
    expect(result.panMagnitude).toBe(0);
  });
});

// ============================================================================
// HIGH: MotionCtrl Export
// ============================================================================

describe("HIGH: exportToMotionCtrl - Frame Count Validation", () => {
  it("should return empty poses for zero frame count", () => {
    const camera = createValidCamera();
    const result = exportToMotionCtrl(camera, [], 0);

    expect(result.camera_poses).toEqual([]);
  });

  it("should handle negative frame count gracefully", () => {
    const camera = createValidCamera();
    const result = exportToMotionCtrl(camera, [], -10);

    expect(result.camera_poses).toEqual([]);
  });

  it("should export correct number of poses", () => {
    const camera = createValidCamera();
    const result = exportToMotionCtrl(camera, [], 24);

    expect(result.camera_poses.length).toBe(24);
  });
});

// ============================================================================
// HIGH: Uni3C Export (Deprecated but should still work)
// ============================================================================

describe("HIGH: exportToUni3C - Dimension Validation", () => {
  it("should warn about non-functional export", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});

    const camera = createValidCamera();
    exportToUni3C(camera, [], 10, 1920, 1080);

    expect(consoleWarn).toHaveBeenCalledWith(
      expect.stringContaining("non-functional"),
    );

    consoleWarn.mockRestore();
  });

  it("should handle zero dimensions in offset calculation", () => {
    const camera = createValidCamera();
    const keyframes = [
      createKeyframe(0),
      createKeyframe(10, { position: { x: 100, y: 100, z: -400 } }),
    ];

    // Should not crash with zero dimensions (would cause divide by zero)
    const result = exportToUni3C(camera, keyframes, 10, 0, 0);
    expect(result.traj_type).toBe("custom");
  });
});

// ============================================================================
// HIGH: exportCameraMatrices - Full Validation
// ============================================================================

describe("HIGH: exportCameraMatrices - Input Validation", () => {
  it("should throw for zero dimensions", () => {
    const camera = createValidCamera();

    expect(() => {
      exportCameraMatrices(camera, [], {
        frameCount: 10,
        width: 0,
        height: 0,
        fps: 24,
      });
    }).toThrow(/invalid.*dimensions|width.*height/i);
  });

  it("should throw for zero fps", () => {
    const camera = createValidCamera();

    expect(() => {
      exportCameraMatrices(camera, [], {
        frameCount: 10,
        width: 1920,
        height: 1080,
        fps: 0,
      });
    }).toThrow(/fps.*0|invalid/i);
  });

  it("should use fallback for NaN values", () => {
    const consoleWarn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const camera = createValidCamera();

    const result = exportCameraMatrices(camera, [], {
      frameCount: NaN,
      width: NaN,
      height: NaN,
      fps: NaN,
    });

    // Should use fallback values
    expect(result.metadata.width).toBe(1920);
    expect(result.metadata.height).toBe(1080);
    expect(result.metadata.fps).toBe(24);
    expect(consoleWarn).toHaveBeenCalled();

    consoleWarn.mockRestore();
  });

  it("should ensure frame count is at least 1", () => {
    const camera = createValidCamera();

    const result = exportCameraMatrices(camera, [], {
      frameCount: 0,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    expect(result.frames.length).toBeGreaterThanOrEqual(1);
  });

  it("should produce valid frame data with no NaN", () => {
    const camera = createValidCamera();
    const keyframes = [createKeyframe(0), createKeyframe(10)];

    const result = exportCameraMatrices(camera, keyframes, {
      frameCount: 11,
      width: 1920,
      height: 1080,
      fps: 24,
    });

    for (const frame of result.frames) {
      expect(Number.isFinite(frame.timestamp)).toBe(true);
      expect(Number.isFinite(frame.fov)).toBe(true);
      expect(Number.isFinite(frame.focal_length)).toBe(true);

      for (const val of frame.position) {
        expect(Number.isFinite(val)).toBe(true);
      }
      for (const val of frame.rotation) {
        expect(Number.isFinite(val)).toBe(true);
      }
    }
  });
});

// ============================================================================
// MEDIUM: Format-Specific Exports
// ============================================================================

describe("MEDIUM: detectMotionCtrlSVDPreset - Motion Detection", () => {
  it("should detect static for no keyframes", () => {
    const result = detectMotionCtrlSVDPreset([]);
    expect(result).toBe("static");
  });

  it("should detect static for single keyframe", () => {
    const result = detectMotionCtrlSVDPreset([createKeyframe(0)]);
    expect(result).toBe("static");
  });

  it("should detect zoom_in for forward Z movement", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: -500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: -400 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("zoom_in");
  });

  it("should detect zoom_out for backward Z movement", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: -500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: -600 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("zoom_out");
  });

  it("should detect rotation", () => {
    const keyframes = [
      createKeyframe(0, { orientation: { x: 0, y: 0, z: 0 } }),
      createKeyframe(10, { orientation: { x: 0, y: 30, z: 0 } }),
    ];

    const result = detectMotionCtrlSVDPreset(keyframes);
    expect(result).toBe("rotate_cw");
  });
});

describe("MEDIUM: mapToWan22FunCamera - Preset Mapping", () => {
  it("should return Static for no motion", () => {
    const result = mapToWan22FunCamera([]);
    expect(result.camera_motion).toBe("Static");
  });

  it("should detect orbital motion", () => {
    const keyframes = [
      createKeyframe(0, {
        position: { x: 0, y: 0, z: -500 },
        orientation: { x: 0, y: 0, z: 0 },
      }),
      createKeyframe(10, {
        position: { x: 100, y: 0, z: -500 },
        orientation: { x: 0, y: 45, z: 0 },
      }),
    ];

    const result = mapToWan22FunCamera(keyframes);
    expect(result.camera_motion).toMatch(/Orbital/);
  });
});

// ============================================================================
// MEDIUM: CameraCtrl Export
// ============================================================================

describe("MEDIUM: exportToCameraCtrl - Motion Type Detection", () => {
  it("should return Static for no motion", () => {
    const result = exportToCameraCtrl([], 24);
    expect(result.motion_type).toBe("Static");
    expect(result.speed).toBe(0);
  });

  it("should calculate speed from motion magnitude", () => {
    const keyframes = [
      createKeyframe(0, { position: { x: 0, y: 0, z: -500 } }),
      createKeyframe(10, { position: { x: 0, y: 0, z: -200 } }), // Large zoom
    ];

    const result = exportToCameraCtrl(keyframes, 11);
    expect(result.speed).toBeGreaterThan(0);
    expect(result.speed).toBeLessThanOrEqual(100);
  });
});

// ============================================================================
// EDGE: exportCameraForTarget - Unknown Target
// ============================================================================

describe("EDGE: exportCameraForTarget - Target Routing", () => {
  it("should route to MotionCtrl for motionctrl target", () => {
    const camera = createValidCamera();
    const result = exportCameraForTarget("motionctrl", camera, [], 10);

    expect(result).toHaveProperty("camera_poses");
  });

  it("should route to full matrices for unknown target", () => {
    const camera = createValidCamera();
    const result = exportCameraForTarget(
      "unknown-target" as any,
      camera,
      [],
      10,
      1920,
      1080,
      24,
    );

    // Should fall through to exportCameraMatrices
    expect(result).toHaveProperty("frames");
    expect(result).toHaveProperty("metadata");
  });
});
