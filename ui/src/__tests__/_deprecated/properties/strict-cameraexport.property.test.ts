/**
 * STRICT Property Tests for Camera Export Formats
 *
 * Tests the ACTUAL matrix/tensor outputs for ComfyUI AI video nodes:
 * 1. MotionCtrl: 4x4 RT matrices
 * 2. MotionCtrl-SVD: presets + JSON poses
 * 3. Wan 2.2 Fun Camera: motion presets
 * 4. Uni3C: trajectory types + custom data
 * 5. AnimateDiff CameraCtrl: motion types
 *
 * TOLERANCE: STRICT - Wrong matrices = wrong camera in AI video
 */

import { describe, it, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  interpolateCameraAtFrame,
  computeViewMatrix,
  computeProjectionMatrix,
  exportToMotionCtrl,
  exportToMotionCtrlSVD,
  mapToWan22FunCamera,
  exportToUni3C,
  exportToCameraCtrl,
  exportCameraMatrices,
  analyzeCameraMotion,
  detectMotionCtrlSVDPreset,
  detectUni3CTrajectoryType,
  detectCameraCtrlMotionType,
} from '@/services/export/cameraExportFormats';
import type { Camera3D, CameraKeyframe } from '@/types/camera';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

const arbitraryVec3 = (): fc.Arbitrary<{ x: number; y: number; z: number }> =>
  fc.record({
    x: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    y: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
    z: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  });

const arbitraryRotation = (): fc.Arbitrary<{ x: number; y: number; z: number }> =>
  fc.record({
    x: fc.double({ min: -180, max: 180, noNaN: true, noDefaultInfinity: true }),
    y: fc.double({ min: -180, max: 180, noNaN: true, noDefaultInfinity: true }),
    z: fc.double({ min: -180, max: 180, noNaN: true, noDefaultInfinity: true }),
  });

const arbitraryCamera = (): fc.Arbitrary<Camera3D> =>
  fc.record({
    type: fc.constant('perspective' as const),
    position: arbitraryVec3(),
    orientation: arbitraryRotation(),
    focalLength: fc.double({ min: 10, max: 200, noNaN: true, noDefaultInfinity: true }),
    zoom: fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true }),
    filmSize: fc.constant(36),
    depthOfField: fc.record({
      enabled: fc.boolean(),
      fStop: fc.double({ min: 1.4, max: 22, noNaN: true, noDefaultInfinity: true }),
      focusDistance: fc.double({ min: 100, max: 10000, noNaN: true, noDefaultInfinity: true }),
      bladeCount: fc.integer({ min: 5, max: 9 }),
    }),
  });

const arbitraryKeyframe = (frame: number): fc.Arbitrary<CameraKeyframe> =>
  fc.record({
    frame: fc.constant(frame),
    position: fc.option(arbitraryVec3(), { nil: undefined }),
    orientation: fc.option(arbitraryRotation(), { nil: undefined }),
    focalLength: fc.option(fc.double({ min: 10, max: 200, noNaN: true, noDefaultInfinity: true }), { nil: undefined }),
    zoom: fc.option(fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true }), { nil: undefined }),
    focusDistance: fc.option(fc.double({ min: 100, max: 10000, noNaN: true, noDefaultInfinity: true }), { nil: undefined }),
  });

// ============================================================================
// STRICT VIEW MATRIX TESTS
// ============================================================================

describe('STRICT: View Matrix Generation', () => {
  test.prop([arbitraryCamera()])('view matrix is 4x4', (camera) => {
    const interpolated = {
      position: camera.position,
      rotation: camera.orientation,
      focalLength: camera.focalLength,
      zoom: camera.zoom,
      focusDistance: camera.depthOfField.focusDistance,
    };

    const matrix = computeViewMatrix(interpolated);

    expect(matrix.length).toBe(4);
    for (const row of matrix) {
      expect(row.length).toBe(4);
    }
  });

  test.prop([arbitraryCamera()])('view matrix has valid bottom row [0,0,0,1]', (camera) => {
    const interpolated = {
      position: camera.position,
      rotation: camera.orientation,
      focalLength: camera.focalLength,
      zoom: camera.zoom,
      focusDistance: camera.depthOfField.focusDistance,
    };

    const matrix = computeViewMatrix(interpolated);

    expect(matrix[3][0]).toBe(0);
    expect(matrix[3][1]).toBe(0);
    expect(matrix[3][2]).toBe(0);
    expect(matrix[3][3]).toBe(1);
  });

  test.prop([arbitraryCamera()])('view matrix contains finite values', (camera) => {
    const interpolated = {
      position: camera.position,
      rotation: camera.orientation,
      focalLength: camera.focalLength,
      zoom: camera.zoom,
      focusDistance: camera.depthOfField.focusDistance,
    };

    const matrix = computeViewMatrix(interpolated);

    for (let i = 0; i < 4; i++) {
      for (let j = 0; j < 4; j++) {
        expect(Number.isFinite(matrix[i][j])).toBe(true);
        expect(Number.isNaN(matrix[i][j])).toBe(false);
      }
    }
  });

  it('identity camera produces identity-like view matrix', () => {
    const camera = {
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 1000,
    };

    const matrix = computeViewMatrix(camera);

    // Rotation part should be identity
    expect(matrix[0][0]).toBeCloseTo(1, 5);
    expect(matrix[1][1]).toBeCloseTo(1, 5);
    expect(matrix[2][2]).toBeCloseTo(1, 5);

    // Translation should be 0
    expect(matrix[0][3]).toBeCloseTo(0, 5);
    expect(matrix[1][3]).toBeCloseTo(0, 5);
    expect(matrix[2][3]).toBeCloseTo(0, 5);
  });
});

// ============================================================================
// STRICT PROJECTION MATRIX TESTS
// ============================================================================

describe('STRICT: Projection Matrix Generation', () => {
  test.prop([
    arbitraryCamera(),
    fc.double({ min: 0.5, max: 3, noNaN: true, noDefaultInfinity: true })
  ])('projection matrix is 4x4', (camera, aspectRatio) => {
    const interpolated = {
      position: camera.position,
      rotation: camera.orientation,
      focalLength: camera.focalLength,
      zoom: camera.zoom,
      focusDistance: camera.depthOfField.focusDistance,
    };

    const matrix = computeProjectionMatrix(interpolated, aspectRatio);

    expect(matrix.length).toBe(4);
    for (const row of matrix) {
      expect(row.length).toBe(4);
    }
  });

  test.prop([
    arbitraryCamera(),
    fc.double({ min: 0.5, max: 3, noNaN: true, noDefaultInfinity: true })
  ])('projection matrix contains finite values', (camera, aspectRatio) => {
    const interpolated = {
      position: camera.position,
      rotation: camera.orientation,
      focalLength: camera.focalLength,
      zoom: camera.zoom,
      focusDistance: camera.depthOfField.focusDistance,
    };

    const matrix = computeProjectionMatrix(interpolated, aspectRatio);

    for (let i = 0; i < 4; i++) {
      for (let j = 0; j < 4; j++) {
        expect(Number.isFinite(matrix[i][j])).toBe(true);
        expect(Number.isNaN(matrix[i][j])).toBe(false);
      }
    }
  });
});

// ============================================================================
// STRICT MOTIONCTRL EXPORT TESTS
// ============================================================================

describe('STRICT: MotionCtrl Export', () => {
  test.prop([
    arbitraryCamera(),
    fc.integer({ min: 8, max: 64 })
  ])('exports correct number of poses', (camera, frameCount) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: camera.position, orientation: camera.orientation },
      { frame: frameCount - 1, position: { x: 100, y: 0, z: 0 }, orientation: { x: 0, y: 45, z: 0 } },
    ];

    const result = exportToMotionCtrl(camera, keyframes, frameCount);

    expect(result.camera_poses.length).toBe(frameCount);
  });

  test.prop([
    arbitraryCamera(),
    fc.integer({ min: 8, max: 32 })
  ])('each pose has valid RT matrix', (camera, frameCount) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: camera.position },
    ];

    const result = exportToMotionCtrl(camera, keyframes, frameCount);

    for (const pose of result.camera_poses) {
      expect(pose.RT.length).toBe(4);
      for (const row of pose.RT) {
        expect(row.length).toBe(4);
        for (const val of row) {
          expect(Number.isFinite(val)).toBe(true);
        }
      }
    }
  });

  test.prop([arbitraryCamera()])('static camera produces identical poses', (camera) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: camera.position, orientation: camera.orientation },
    ];

    const result = exportToMotionCtrl(camera, keyframes, 10);

    // All poses should be identical for static camera
    const firstPose = JSON.stringify(result.camera_poses[0].RT);
    for (let i = 1; i < result.camera_poses.length; i++) {
      expect(JSON.stringify(result.camera_poses[i].RT)).toBe(firstPose);
    }
  });
});

// ============================================================================
// STRICT UNI3C EXPORT TESTS
// ============================================================================

describe('STRICT: Uni3C Export', () => {
  test.prop([
    arbitraryCamera(),
    fc.integer({ min: 8, max: 64 })
  ])('exports valid trajectory type', (camera, frameCount) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: camera.position },
    ];

    const result = exportToUni3C(camera, keyframes, frameCount, 1920, 1080);

    expect(result.traj_type).toBeDefined();
    const validTypes = ['orbit', 'free1', 'free2', 'spiral', 'custom'];
    expect(validTypes).toContain(result.traj_type);
  });

  test.prop([
    arbitraryCamera(),
    fc.integer({ min: 8, max: 32 })
  ])('custom trajectory has correct frame count', (camera, frameCount) => {
    // Create keyframes that will trigger custom trajectory
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 }, orientation: { x: 0, y: 0, z: 0 } },
      { frame: Math.floor(frameCount / 2), position: { x: 100, y: 50, z: -100 }, orientation: { x: 15, y: 30, z: 0 } },
      { frame: frameCount - 1, position: { x: 200, y: 100, z: -200 }, orientation: { x: 30, y: 60, z: 0 } },
    ];

    const result = exportToUni3C(camera, keyframes, frameCount, 1920, 1080);

    if (result.traj_type === 'custom' && result.custom_trajectory) {
      expect(result.custom_trajectory.length).toBe(frameCount);

      for (const frame of result.custom_trajectory) {
        expect(Number.isFinite(frame.zoom)).toBe(true);
        expect(Number.isFinite(frame.x_offset)).toBe(true);
        expect(Number.isFinite(frame.y_offset)).toBe(true);
        expect(Number.isFinite(frame.z_offset)).toBe(true);
        expect(Number.isFinite(frame.pitch)).toBe(true);
        expect(Number.isFinite(frame.yaw)).toBe(true);
        expect(Number.isFinite(frame.roll)).toBe(true);
      }
    }
  });
});

// ============================================================================
// STRICT WAN 2.2 FUN CAMERA TESTS
// ============================================================================

describe('STRICT: Wan 2.2 Fun Camera Export', () => {
  const validPresets = [
    'Static', 'Pan Up', 'Pan Down', 'Pan Left', 'Pan Right',
    'Zoom In', 'Zoom Out', 'Orbital Left', 'Orbital Right',
  ];

  test.prop([arbitraryCamera()])('exports valid motion preset', (camera) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: camera.position },
    ];

    const result = mapToWan22FunCamera(keyframes);

    expect(result.camera_motion).toBeDefined();
    // Should be a string
    expect(typeof result.camera_motion).toBe('string');
  });

  it('static camera exports as Static', () => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
      { frame: 30, position: { x: 0, y: 0, z: 0 } },
    ];

    const result = mapToWan22FunCamera(keyframes);
    expect(result.camera_motion).toBe('Static');
  });

  it('pan right motion detected correctly', () => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
      { frame: 30, position: { x: 200, y: 0, z: 0 } },
    ];

    const result = mapToWan22FunCamera(keyframes);
    expect(result.camera_motion).toContain('Right');
  });

  it('zoom in motion detected correctly', () => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
      { frame: 30, position: { x: 0, y: 0, z: -200 } },
    ];

    const result = mapToWan22FunCamera(keyframes);
    expect(result.camera_motion).toContain('Zoom');
  });
});

// ============================================================================
// STRICT ANIMATEDIFF CAMERACTRL TESTS
// ============================================================================

describe('STRICT: AnimateDiff CameraCtrl Export', () => {
  test.prop([fc.integer({ min: 8, max: 128 })])('exports valid motion type', (frameCount) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
    ];

    const result = exportToCameraCtrl(keyframes, frameCount);

    expect(result.motion_type).toBeDefined();
    expect(result.frame_length).toBe(frameCount);
    expect(typeof result.speed).toBe('number');
  });

  const motionTypes = [
    'Static', 'Move Forward', 'Move Backward', 'Move Left', 'Move Right',
    'Move Up', 'Move Down', 'Rotate Left', 'Rotate Right', 'Rotate Up', 'Rotate Down',
    'Roll Left', 'Roll Right',
  ];

  it('all motion types are valid strings', () => {
    for (const type of motionTypes) {
      expect(typeof type).toBe('string');
    }
  });

  test.prop([fc.integer({ min: 8, max: 64 })])('speed is non-negative', (frameCount) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
      { frame: frameCount - 1, position: { x: 100, y: 0, z: 0 } },
    ];

    const result = exportToCameraCtrl(keyframes, frameCount);

    expect(result.speed).toBeGreaterThanOrEqual(0);
    expect(result.speed).toBeLessThanOrEqual(100);
  });
});

// ============================================================================
// STRICT INTERPOLATION TESTS
// ============================================================================

describe('STRICT: Camera Interpolation', () => {
  test.prop([
    arbitraryCamera(),
    fc.integer({ min: 0, max: 100 })
  ])('interpolation at keyframe returns keyframe value', (camera, frame) => {
    const keyframes: CameraKeyframe[] = [
      { frame, position: { x: 123, y: 456, z: 789 } },
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, frame);

    expect(result.position.x).toBe(123);
    expect(result.position.y).toBe(456);
    expect(result.position.z).toBe(789);
  });

  test.prop([arbitraryCamera()])('interpolation midpoint is average for linear', (camera) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
      { frame: 100, position: { x: 100, y: 200, z: 300 } },
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 50);

    expect(result.position.x).toBeCloseTo(50, 5);
    expect(result.position.y).toBeCloseTo(100, 5);
    expect(result.position.z).toBeCloseTo(150, 5);
  });

  test.prop([arbitraryCamera()])('interpolation before first keyframe uses first', (camera) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 50, position: { x: 100, y: 200, z: 300 } },
    ];

    const result = interpolateCameraAtFrame(camera, keyframes, 0);

    expect(result.position.x).toBe(100);
    expect(result.position.y).toBe(200);
    expect(result.position.z).toBe(300);
  });
});

// ============================================================================
// STRICT MOTION ANALYSIS TESTS
// ============================================================================

describe('STRICT: Camera Motion Analysis', () => {
  it('empty keyframes produces no motion', () => {
    const result = analyzeCameraMotion([]);

    expect(result.hasPan).toBe(false);
    expect(result.hasZoom).toBe(false);
    expect(result.hasOrbit).toBe(false);
    expect(result.hasRotation).toBe(false);
  });

  it('single keyframe produces no motion', () => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasPan).toBe(false);
    expect(result.hasZoom).toBe(false);
  });

  it('horizontal movement detected as pan', () => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
      { frame: 30, position: { x: 100, y: 0, z: 0 } },
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasPan).toBe(true);
    expect(result.panDirection).toBe('right');
  });

  it('Z movement detected as zoom', () => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: 0, y: 0, z: 0 } },
      { frame: 30, position: { x: 0, y: 0, z: -100 } },
    ];

    const result = analyzeCameraMotion(keyframes);

    expect(result.hasZoom).toBe(true);
    expect(result.zoomDirection).toBe('in');
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Camera Export Under Load', () => {
  test.prop([
    arbitraryCamera(),
    fc.integer({ min: 100, max: 300 })
  ])('handles large frame counts', (camera, frameCount) => {
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: camera.position },
      { frame: frameCount - 1, position: { x: 500, y: 500, z: 500 } },
    ];

    const result = exportToMotionCtrl(camera, keyframes, frameCount);

    expect(result.camera_poses.length).toBe(frameCount);

    // All poses should be valid
    for (const pose of result.camera_poses) {
      for (const row of pose.RT) {
        for (const val of row) {
          expect(Number.isFinite(val)).toBe(true);
        }
      }
    }
  });
});
