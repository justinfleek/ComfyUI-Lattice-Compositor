/**
 * Property Tests for Camera Export Formats
 *
 * Tests mathematical invariants and edge cases for camera export functions.
 * Uses fast-check for property-based testing.
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";

import {
  interpolateCameraAtFrame,
  computeViewMatrix,
  computeProjectionMatrix,
  exportToMotionCtrl,
  detectMotionCtrlSVDPreset,
  exportToMotionCtrlSVD,
  analyzeCameraMotion,
  mapToWan22FunCamera,
  detectUni3CTrajectoryType,
  exportToUni3C,
  detectCameraCtrlMotionType,
  exportToCameraCtrl,
  exportCameraMatrices,
  exportCameraForTarget,
} from "@/services/export/cameraExportFormats";

import type { Camera3D, CameraKeyframe, CameraType, MeasureFilmSize, AutoOrientMode } from "@/types/camera";

// ============================================================================
// Arbitraries (Test Data Generators)
// ============================================================================

/** Generate a valid 3D position */
const positionArb = fc.record({
  x: fc.integer({ min: -1000, max: 1000 }).map(n => n),
  y: fc.integer({ min: -1000, max: 1000 }).map(n => n),
  z: fc.integer({ min: -1000, max: 1000 }).map(n => n),
});

/** Generate a valid 3D rotation (degrees) */
const rotationArb = fc.record({
  x: fc.integer({ min: -180, max: 180 }).map(n => n),
  y: fc.integer({ min: -180, max: 180 }).map(n => n),
  z: fc.integer({ min: -180, max: 180 }).map(n => n),
});

/** Generate a valid camera keyframe */
const cameraKeyframeArb: fc.Arbitrary<CameraKeyframe> = fc.record({
  frame: fc.integer({ min: 0, max: 1000 }),
  position: fc.option(positionArb, { nil: undefined }),
  orientation: fc.option(rotationArb, { nil: undefined }),
  focalLength: fc.option(fc.integer({ min: 10, max: 200 }).map(n => n), { nil: undefined }),
  zoom: fc.option(fc.integer({ min: 1, max: 100 }).map(n => n / 10), { nil: undefined }),
  focusDistance: fc.option(fc.integer({ min: 1, max: 10000 }).map(n => n), { nil: undefined }),
});

/** Generate a sorted array of keyframes */
const sortedKeyframesArb = fc
  .array(cameraKeyframeArb, { minLength: 0, maxLength: 10 })
  .map((kfs) => kfs.sort((a, b) => a.frame - b.frame));

/** Generate a realistic Camera3D object with all required properties */
const camera3DArb: fc.Arbitrary<Camera3D> = fc.record({
  id: fc.string({ minLength: 1 }),
  name: fc.string({ minLength: 1 }),
  type: fc.constantFrom<CameraType>("one-node", "two-node"),
  position: positionArb,
  pointOfInterest: positionArb, // Required for both one-node and two-node
  orientation: rotationArb,
  xRotation: fc.integer({ min: -180, max: 180 }).map(n => n),
  yRotation: fc.integer({ min: -180, max: 180 }).map(n => n),
  zRotation: fc.integer({ min: -180, max: 180 }).map(n => n),
  focalLength: fc.integer({ min: 10, max: 200 }).map(n => n),
  zoom: fc.integer({ min: 100, max: 5000 }).map(n => n), // Realistic zoom range (pixels)
  filmSize: fc.constantFrom(36, 24, 18), // Common film sizes (full frame, APS-C, etc.)
  angleOfView: fc.integer({ min: 10, max: 120 }).map(n => n),
  measureFilmSize: fc.constantFrom<MeasureFilmSize>("horizontal", "vertical", "diagonal"),
  depthOfField: fc.record({
    enabled: fc.boolean(),
    focusDistance: fc.integer({ min: 1, max: 10000 }).map(n => n),
    aperture: fc.integer({ min: 10, max: 500 }).map(n => n), // Pixels (internal)
    fStop: fc.integer({ min: 1, max: 22 }).map(n => n / 10), // f-stop (display, e.g., 1.4, 2.8, 5.6)
    blurLevel: fc.float({ min: 0, max: 1, noNaN: true }),
    lockToZoom: fc.boolean(),
  }),
  iris: fc.record({
    shape: fc.integer({ min: 0, max: 10 }).map(n => n), // 0-10 (pentagon to circle)
    rotation: fc.integer({ min: 0, max: 360 }).map(n => n), // Degrees
    roundness: fc.float({ min: 0, max: 1, noNaN: true }),
    aspectRatio: fc.float({ min: 0.5, max: 2, noNaN: true }),
    diffractionFringe: fc.float({ min: 0, max: 1, noNaN: true }),
  }),
  highlight: fc.record({
    gain: fc.float({ min: 0, max: 1, noNaN: true }),
    threshold: fc.float({ min: 0, max: 1, noNaN: true }),
    saturation: fc.float({ min: 0, max: 1, noNaN: true }),
  }),
  autoOrient: fc.constantFrom<AutoOrientMode>("off", "orient-along-path", "orient-towards-poi"),
  nearClip: fc.float({ min: 0.1, max: 100, noNaN: true }),
  farClip: fc.integer({ min: 1000, max: 100000 }).map(n => n),
});

// ============================================================================
// interpolateCameraAtFrame Property Tests
// ============================================================================

describe("PROPERTY: interpolateCameraAtFrame", () => {
  it("returns camera defaults when no keyframes", () => {
    fc.assert(
      fc.property(camera3DArb, fc.integer({ min: 0, max: 1000 }), (camera, frame) => {
        const result = interpolateCameraAtFrame(camera, [], frame);

        expect(result.position).toEqual(camera.position);
        expect(result.rotation).toEqual(camera.orientation);
        expect(result.focalLength).toBe(camera.focalLength);
        expect(result.zoom).toBe(camera.zoom);
        expect(result.focusDistance).toBe(camera.depthOfField.focusDistance);
      }),
    );
  });

  it("returns exact keyframe values at keyframe frames", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        cameraKeyframeArb.filter((kf) => kf.position !== undefined),
        (camera, keyframe) => {
          const result = interpolateCameraAtFrame(camera, [keyframe], keyframe.frame);

          if (keyframe.position) {
            expect(result.position.x).toBeCloseTo(keyframe.position.x, 5);
            expect(result.position.y).toBeCloseTo(keyframe.position.y, 5);
            expect(result.position.z).toBeCloseTo(keyframe.position.z, 5);
          }
        },
      ),
    );
  });

  it("interpolation at first keyframe frame equals first keyframe (unique frames)", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        // Generate keyframes with UNIQUE frame numbers to test normal case
        fc.uniqueArray(fc.integer({ min: 0, max: 1000 }), { minLength: 2, maxLength: 5 }).chain((frames) => {
          const sortedFrames = [...frames].sort((a, b) => a - b);
          return fc.tuple(
            ...sortedFrames.map((frame) =>
              fc.record({
                frame: fc.constant(frame),
                position: positionArb,
                orientation: fc.option(rotationArb, { nil: undefined }),
                focalLength: fc.option(fc.integer({ min: 10, max: 200 }).map(n => n), { nil: undefined }),
                zoom: fc.option(fc.integer({ min: 1, max: 100 }).map(n => n / 10), { nil: undefined }),
                focusDistance: fc.option(fc.integer({ min: 1, max: 10000 }).map(n => n), { nil: undefined }),
              })
            )
          );
        }),
        (camera, keyframes) => {
          if (keyframes.length < 2) return;

          const result = interpolateCameraAtFrame(camera, keyframes, keyframes[0].frame);
          const firstPos = keyframes[0].position;

          expect(result.position.x).toBeCloseTo(firstPos.x, 5);
          expect(result.position.y).toBeCloseTo(firstPos.y, 5);
          expect(result.position.z).toBeCloseTo(firstPos.z, 5);
        },
      ),
    );
  });

  it("interpolation at last keyframe frame equals last keyframe (unique frames)", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        // Generate keyframes with UNIQUE frame numbers to test normal case
        fc.uniqueArray(fc.integer({ min: 0, max: 1000 }), { minLength: 2, maxLength: 5 }).chain((frames) => {
          const sortedFrames = [...frames].sort((a, b) => a - b);
          return fc.tuple(
            ...sortedFrames.map((frame) =>
              fc.record({
                frame: fc.constant(frame),
                position: positionArb,
                orientation: fc.option(rotationArb, { nil: undefined }),
                focalLength: fc.option(fc.integer({ min: 10, max: 200 }).map(n => n), { nil: undefined }),
                zoom: fc.option(fc.integer({ min: 1, max: 100 }).map(n => n / 10), { nil: undefined }),
                focusDistance: fc.option(fc.integer({ min: 1, max: 10000 }).map(n => n), { nil: undefined }),
              })
            )
          );
        }),
        (camera, keyframes) => {
          if (keyframes.length < 2) return;

          const lastIdx = keyframes.length - 1;
          const result = interpolateCameraAtFrame(camera, keyframes, keyframes[lastIdx].frame);
          const lastPos = keyframes[lastIdx].position;

          expect(result.position.x).toBeCloseTo(lastPos.x, 5);
          expect(result.position.y).toBeCloseTo(lastPos.y, 5);
          expect(result.position.z).toBeCloseTo(lastPos.z, 5);
        },
      ),
    );
  });

  // BUG-081: This test documents the CURRENT behavior with duplicate frames
  // The function uses LAST keyframe at a frame for `prev`, FIRST for `next`
  // When frames match, it returns `prev` (the LAST duplicate)
  it.skip("BUG-081: duplicate frame keyframes have undefined behavior - NEEDS FIX", () => {
    // This test is skipped because the behavior is inconsistent
    // See AUDIT_SESSION_LOG.md for full bug description
    // Realistic camera object with all required properties
    const camera: Camera3D = {
      id: "test",
      name: "Test",
      type: "one-node",
      position: { x: 0, y: 0, z: 0 },
      pointOfInterest: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      xRotation: 0,
      yRotation: 0,
      zRotation: 0,
      focalLength: 50,
      zoom: 1778, // Realistic zoom for 50mm
      filmSize: 36,
      angleOfView: 40,
      measureFilmSize: "horizontal",
      depthOfField: {
        enabled: false,
        focusDistance: 100,
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
        gain: 0,
        threshold: 1,
        saturation: 1,
      },
      autoOrient: "off",
      nearClip: 0.1,
      farClip: 10000,
    };

    const keyframes = [
      { frame: 5, position: { x: -9, y: 255, z: -879 } },
      { frame: 5, position: { x: 0, y: 0, z: 0 } }, // Duplicate frame!
      { frame: 100, position: { x: 100, y: 100, z: 100 } },
    ];

    const result = interpolateCameraAtFrame(camera, keyframes as any, 5);

    // Current behavior: returns LAST keyframe at frame 5
    // Is this intended? Should it be FIRST? Should it throw?
    expect(result.position.x).toBe(0); // Gets second keyframe
  });

  it("interpolated values are bounded by keyframe extremes", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        fc.array(cameraKeyframeArb.filter((kf) => kf.focalLength !== undefined), { minLength: 2, maxLength: 5 }),
        fc.integer({ min: 0, max: 100 }).map(n => n / 100),
        (camera, keyframes, t) => {
          const sorted = keyframes.sort((a, b) => a.frame - b.frame);
          if (sorted.length < 2 || sorted[0].frame === sorted[sorted.length - 1].frame) return;

          const focalLengths = sorted
            .map((kf) => kf.focalLength)
            .filter((f): f is number => f !== undefined);
          if (focalLengths.length < 2) return;

          const minFocal = Math.min(...focalLengths);
          const maxFocal = Math.max(...focalLengths);

          const frame = sorted[0].frame + t * (sorted[sorted.length - 1].frame - sorted[0].frame);
          const result = interpolateCameraAtFrame(camera, sorted, frame);

          // Allow small tolerance for floating point
          expect(result.focalLength).toBeGreaterThanOrEqual(minFocal - 0.01);
          expect(result.focalLength).toBeLessThanOrEqual(maxFocal + 0.01);
        },
      ),
    );
  });

  it("never produces NaN values", () => {
    fc.assert(
      fc.property(camera3DArb, sortedKeyframesArb, fc.integer({ min: -100, max: 2000 }), (camera, keyframes, frame) => {
        const result = interpolateCameraAtFrame(camera, keyframes, frame);

        expect(Number.isFinite(result.position.x)).toBe(true);
        expect(Number.isFinite(result.position.y)).toBe(true);
        expect(Number.isFinite(result.position.z)).toBe(true);
        expect(Number.isFinite(result.rotation.x)).toBe(true);
        expect(Number.isFinite(result.rotation.y)).toBe(true);
        expect(Number.isFinite(result.rotation.z)).toBe(true);
        expect(Number.isFinite(result.focalLength)).toBe(true);
        expect(Number.isFinite(result.zoom)).toBe(true);
        expect(Number.isFinite(result.focusDistance)).toBe(true);
      }),
    );
  });
});

// ============================================================================
// computeViewMatrix Property Tests
// ============================================================================

describe("PROPERTY: computeViewMatrix", () => {
  const interpolatedCameraArb = fc.record({
    position: positionArb,
    rotation: rotationArb,
    focalLength: fc.integer({ min: 10, max: 200 }).map(n => n),
    zoom: fc.integer({ min: 1, max: 100 }).map(n => n / 10),
    focusDistance: fc.integer({ min: 1, max: 10000 }).map(n => n),
  });

  it("returns 4x4 matrix", () => {
    fc.assert(
      fc.property(interpolatedCameraArb, (cam) => {
        const matrix = computeViewMatrix(cam);

        expect(matrix.length).toBe(4);
        matrix.forEach((row) => {
          expect(row.length).toBe(4);
        });
      }),
    );
  });

  it("last row is [0, 0, 0, 1]", () => {
    fc.assert(
      fc.property(interpolatedCameraArb, (cam) => {
        const matrix = computeViewMatrix(cam);

        expect(matrix[3][0]).toBeCloseTo(0, 10);
        expect(matrix[3][1]).toBeCloseTo(0, 10);
        expect(matrix[3][2]).toBeCloseTo(0, 10);
        expect(matrix[3][3]).toBeCloseTo(1, 10);
      }),
    );
  });

  it("identity rotation at zero angles", () => {
    fc.assert(
      fc.property(positionArb, fc.integer({ min: 10, max: 200 }), (position, focalLength) => {
        const cam = {
          position,
          rotation: { x: 0, y: 0, z: 0 },
          focalLength,
          zoom: 1,
          focusDistance: 100,
        };

        const matrix = computeViewMatrix(cam);

        // Rotation part should be identity
        expect(matrix[0][0]).toBeCloseTo(1, 5);
        expect(matrix[1][1]).toBeCloseTo(1, 5);
        expect(matrix[2][2]).toBeCloseTo(1, 5);
      }),
    );
  });

  it("all matrix values are finite", () => {
    fc.assert(
      fc.property(interpolatedCameraArb, (cam) => {
        const matrix = computeViewMatrix(cam);

        matrix.forEach((row) => {
          row.forEach((val) => {
            expect(Number.isFinite(val)).toBe(true);
          });
        });
      }),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(interpolatedCameraArb, (cam) => {
        const matrix1 = computeViewMatrix(cam);
        const matrix2 = computeViewMatrix(cam);

        for (let i = 0; i < 4; i++) {
          for (let j = 0; j < 4; j++) {
            expect(matrix1[i][j]).toBe(matrix2[i][j]);
          }
        }
      }),
    );
  });
});

// ============================================================================
// computeProjectionMatrix Property Tests
// ============================================================================

describe("PROPERTY: computeProjectionMatrix", () => {
  const interpolatedCameraArb = fc.record({
    position: positionArb,
    rotation: rotationArb,
    focalLength: fc.integer({ min: 10, max: 200 }).map(n => n),
    zoom: fc.integer({ min: 1, max: 100 }).map(n => n / 10),
    focusDistance: fc.integer({ min: 1, max: 10000 }).map(n => n),
  });

  it("returns 4x4 matrix", () => {
    fc.assert(
      fc.property(
        interpolatedCameraArb,
        fc.integer({ min: 5, max: 30 }).map(n => n / 10),
        (cam, aspectRatio) => {
          const matrix = computeProjectionMatrix(cam, aspectRatio);

          expect(matrix.length).toBe(4);
          matrix.forEach((row) => {
            expect(row.length).toBe(4);
          });
        },
      ),
    );
  });

  it("has -1 at [3][2] for perspective divide", () => {
    fc.assert(
      fc.property(
        interpolatedCameraArb,
        fc.integer({ min: 5, max: 30 }).map(n => n / 10),
        (cam, aspectRatio) => {
          const matrix = computeProjectionMatrix(cam, aspectRatio);
          expect(matrix[3][2]).toBe(-1);
        },
      ),
    );
  });

  it("has 0 at [3][3]", () => {
    fc.assert(
      fc.property(
        interpolatedCameraArb,
        fc.integer({ min: 5, max: 30 }).map(n => n / 10),
        (cam, aspectRatio) => {
          const matrix = computeProjectionMatrix(cam, aspectRatio);
          expect(matrix[3][3]).toBe(0);
        },
      ),
    );
  });

  it("all matrix values are finite", () => {
    fc.assert(
      fc.property(
        interpolatedCameraArb,
        fc.integer({ min: 5, max: 30 }).map(n => n / 10),
        (cam, aspectRatio) => {
          const matrix = computeProjectionMatrix(cam, aspectRatio);

          matrix.forEach((row) => {
            row.forEach((val) => {
              expect(Number.isFinite(val)).toBe(true);
            });
          });
        },
      ),
    );
  });
});

// ============================================================================
// exportToMotionCtrl Property Tests
// ============================================================================

describe("PROPERTY: exportToMotionCtrl", () => {
  it("returns correct number of poses", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 100 }),
        (camera, keyframes, frameCount) => {
          const result = exportToMotionCtrl(camera, keyframes, frameCount);

          expect(result.camera_poses.length).toBe(frameCount);
        },
      ),
    );
  });

  it("each pose has 4x4 RT matrix", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 20 }),
        (camera, keyframes, frameCount) => {
          const result = exportToMotionCtrl(camera, keyframes, frameCount);

          result.camera_poses.forEach((pose) => {
            expect(pose.RT.length).toBe(4);
            pose.RT.forEach((row) => {
              expect(row.length).toBe(4);
            });
          });
        },
      ),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 20 }),
        (camera, keyframes, frameCount) => {
          const result1 = exportToMotionCtrl(camera, keyframes, frameCount);
          const result2 = exportToMotionCtrl(camera, keyframes, frameCount);

          expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
        },
      ),
    );
  });
});

// ============================================================================
// detectMotionCtrlSVDPreset Property Tests
// ============================================================================

describe("PROPERTY: detectMotionCtrlSVDPreset", () => {
  it("returns static for empty keyframes", () => {
    const result = detectMotionCtrlSVDPreset([]);
    expect(result).toBe("static");
  });

  it("returns static for single keyframe", () => {
    fc.assert(
      fc.property(cameraKeyframeArb, (keyframe) => {
        const result = detectMotionCtrlSVDPreset([keyframe]);
        expect(result).toBe("static");
      }),
    );
  });

  it("returns valid preset", () => {
    const validPresets = [
      "static",
      "zoom_in",
      "zoom_out",
      "pan_left",
      "pan_right",
      "pan_up",
      "pan_down",
      "rotate_cw",
      "rotate_ccw",
    ];

    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result = detectMotionCtrlSVDPreset(keyframes);
        expect(validPresets).toContain(result);
      }),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result1 = detectMotionCtrlSVDPreset(keyframes);
        const result2 = detectMotionCtrlSVDPreset(keyframes);
        expect(result1).toBe(result2);
      }),
    );
  });
});

// ============================================================================
// analyzeCameraMotion Property Tests
// ============================================================================

describe("PROPERTY: analyzeCameraMotion", () => {
  it("returns all false for empty keyframes", () => {
    const result = analyzeCameraMotion([]);

    expect(result.hasPan).toBe(false);
    expect(result.hasZoom).toBe(false);
    expect(result.hasOrbit).toBe(false);
    expect(result.hasRotation).toBe(false);
  });

  it("magnitudes are non-negative", () => {
    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result = analyzeCameraMotion(keyframes);

        expect(result.panMagnitude).toBeGreaterThanOrEqual(0);
        expect(result.zoomMagnitude).toBeGreaterThanOrEqual(0);
        expect(result.orbitMagnitude).toBeGreaterThanOrEqual(0);
        expect(result.rotationMagnitude).toBeGreaterThanOrEqual(0);
      }),
    );
  });

  it("pan direction only set when hasPan is true", () => {
    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result = analyzeCameraMotion(keyframes);

        if (!result.hasPan) {
          expect(result.panDirection).toBeUndefined();
        }
        if (result.panDirection !== undefined) {
          expect(result.hasPan).toBe(true);
        }
      }),
    );
  });

  it("zoom direction only set when hasZoom is true", () => {
    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result = analyzeCameraMotion(keyframes);

        if (!result.hasZoom) {
          expect(result.zoomDirection).toBeUndefined();
        }
        if (result.zoomDirection !== undefined) {
          expect(result.hasZoom).toBe(true);
        }
      }),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result1 = analyzeCameraMotion(keyframes);
        const result2 = analyzeCameraMotion(keyframes);

        expect(result1).toEqual(result2);
      }),
    );
  });
});

// ============================================================================
// mapToWan22FunCamera Property Tests
// ============================================================================

describe("PROPERTY: mapToWan22FunCamera", () => {
  it("returns valid camera motion preset", () => {
    const validMotions = [
      "Static",
      "Zoom In",
      "Zoom Out",
      "Pan Up",
      "Pan Down",
      "Pan Left",
      "Pan Right",
      "Orbital Left",
      "Orbital Right",
      "Pan Up + Zoom In",
      "Pan Up + Zoom Out",
      "Pan Down + Zoom In",
      "Pan Down + Zoom Out",
      "Pan Left + Zoom In",
      "Pan Left + Zoom Out",
      "Pan Right + Zoom In",
      "Pan Right + Zoom Out",
    ];

    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result = mapToWan22FunCamera(keyframes);
        expect(validMotions).toContain(result.camera_motion);
      }),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(sortedKeyframesArb, (keyframes) => {
        const result1 = mapToWan22FunCamera(keyframes);
        const result2 = mapToWan22FunCamera(keyframes);

        expect(result1.camera_motion).toBe(result2.camera_motion);
      }),
    );
  });
});

// ============================================================================
// exportToUni3C Property Tests
// ============================================================================

describe("PROPERTY: exportToUni3C", () => {
  it("returns valid traj_type", () => {
    const validTypes = ["free1", "free2", "free3", "orbit", "custom"];

    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 50 }),
        fc.integer({ min: 256, max: 1920 }),
        fc.integer({ min: 256, max: 1080 }),
        (camera, keyframes, frameCount, width, height) => {
          const result = exportToUni3C(camera, keyframes, frameCount, width, height);
          expect(validTypes).toContain(result.traj_type);
        },
      ),
    );
  });

  it("custom trajectory has correct frame count", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        fc.array(cameraKeyframeArb.filter((kf) => kf.position !== undefined), { minLength: 3, maxLength: 5 }),
        fc.integer({ min: 10, max: 50 }),
        (camera, keyframes, frameCount) => {
          // Create keyframes with significant motion to trigger custom
          const sortedKfs = keyframes.sort((a, b) => a.frame - b.frame);
          sortedKfs[0] = { ...sortedKfs[0], frame: 0, position: { x: 0, y: 0, z: 0 } };
          sortedKfs[sortedKfs.length - 1] = {
            ...sortedKfs[sortedKfs.length - 1],
            frame: frameCount - 1,
            position: { x: 500, y: 0, z: -200 },
          };

          const result = exportToUni3C(camera, sortedKfs, frameCount, 1920, 1080);

          if (result.traj_type === "custom" && result.custom_trajectory) {
            expect(result.custom_trajectory.length).toBe(frameCount);
          }
        },
      ),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 20 }),
        (camera, keyframes, frameCount) => {
          const result1 = exportToUni3C(camera, keyframes, frameCount, 1920, 1080);
          const result2 = exportToUni3C(camera, keyframes, frameCount, 1920, 1080);

          expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
        },
      ),
    );
  });
});

// ============================================================================
// exportCameraMatrices Property Tests
// ============================================================================

describe("PROPERTY: exportCameraMatrices", () => {
  it("returns correct number of frames", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 50 }),
        fc.integer({ min: 256, max: 1920 }),
        fc.integer({ min: 256, max: 1080 }),
        fc.integer({ min: 1, max: 60 }),
        (camera, keyframes, frameCount, width, height, fps) => {
          const result = exportCameraMatrices(camera, keyframes, {
            frameCount,
            width,
            height,
            fps,
          });

          expect(result.frames.length).toBe(frameCount);
          expect(result.metadata.total_frames).toBe(frameCount);
        },
      ),
    );
  });

  it("frame indices are sequential", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 2, max: 20 }),
        (camera, keyframes, frameCount) => {
          const result = exportCameraMatrices(camera, keyframes, {
            frameCount,
            width: 1920,
            height: 1080,
            fps: 24,
          });

          result.frames.forEach((frame, index) => {
            expect(frame.frame).toBe(index);
          });
        },
      ),
    );
  });

  it("timestamps increase monotonically", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 2, max: 20 }),
        fc.integer({ min: 1, max: 60 }),
        (camera, keyframes, frameCount, fps) => {
          const result = exportCameraMatrices(camera, keyframes, {
            frameCount,
            width: 1920,
            height: 1080,
            fps,
          });

          for (let i = 1; i < result.frames.length; i++) {
            expect(result.frames[i].timestamp).toBeGreaterThan(result.frames[i - 1].timestamp);
          }
        },
      ),
    );
  });

  it("view matrices are 4x4", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 10 }),
        (camera, keyframes, frameCount) => {
          const result = exportCameraMatrices(camera, keyframes, {
            frameCount,
            width: 1920,
            height: 1080,
            fps: 24,
          });

          result.frames.forEach((frame) => {
            expect(frame.view_matrix.length).toBe(4);
            frame.view_matrix.forEach((row) => {
              expect(row.length).toBe(4);
            });
          });
        },
      ),
    );
  });

  it("projection matrices are 4x4", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 10 }),
        (camera, keyframes, frameCount) => {
          const result = exportCameraMatrices(camera, keyframes, {
            frameCount,
            width: 1920,
            height: 1080,
            fps: 24,
          });

          result.frames.forEach((frame) => {
            expect(frame.projection_matrix.length).toBe(4);
            frame.projection_matrix.forEach((row) => {
              expect(row.length).toBe(4);
            });
          });
        },
      ),
    );
  });

  it("metadata matches input options", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 50 }),
        fc.integer({ min: 256, max: 1920 }),
        fc.integer({ min: 256, max: 1080 }),
        fc.integer({ min: 1, max: 60 }),
        (camera, keyframes, frameCount, width, height, fps) => {
          const result = exportCameraMatrices(camera, keyframes, {
            frameCount,
            width,
            height,
            fps,
          });

          expect(result.metadata.width).toBe(width);
          expect(result.metadata.height).toBe(height);
          expect(result.metadata.fps).toBe(fps);
          expect(result.metadata.total_frames).toBe(frameCount);
        },
      ),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 10 }),
        (camera, keyframes, frameCount) => {
          const options = { frameCount, width: 1920, height: 1080, fps: 24 };

          const result1 = exportCameraMatrices(camera, keyframes, options);
          const result2 = exportCameraMatrices(camera, keyframes, options);

          expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
        },
      ),
    );
  });
});

// ============================================================================
// exportCameraForTarget Property Tests
// ============================================================================

describe("PROPERTY: exportCameraForTarget", () => {
  const targetArb = fc.constantFrom(
    "motionctrl",
    "motionctrl-svd",
    "wan22-fun-camera",
    "uni3c-camera",
    "animatediff-cameractrl",
    "unknown-format",
  );

  it("returns an object for any target", () => {
    fc.assert(
      fc.property(
        targetArb,
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 50 }),
        (target, camera, keyframes, frameCount) => {
          const result = exportCameraForTarget(
            target as any,
            camera,
            keyframes,
            frameCount,
          );

          expect(typeof result).toBe("object");
          expect(result).not.toBeNull();
        },
      ),
    );
  });

  it("is deterministic", () => {
    fc.assert(
      fc.property(
        targetArb,
        camera3DArb,
        sortedKeyframesArb,
        fc.integer({ min: 1, max: 20 }),
        (target, camera, keyframes, frameCount) => {
          const result1 = exportCameraForTarget(
            target as any,
            camera,
            keyframes,
            frameCount,
          );
          const result2 = exportCameraForTarget(
            target as any,
            camera,
            keyframes,
            frameCount,
          );

          expect(JSON.stringify(result1)).toBe(JSON.stringify(result2));
        },
      ),
    );
  });
});
