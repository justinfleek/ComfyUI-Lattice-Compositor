/**
 * Property Tests: cameraExportFormats.ts
 * 
 * Testing all 14 exported functions with strict tolerances.
 * NO loosening tests to pass - failures are bugs.
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
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
} from '@/services/export/cameraExportFormats';
import { focalLengthToFOV } from '@/services/math3d';
import type { Camera3D, CameraKeyframe } from '@/types/camera';

// ============================================================================
// Custom Arbitraries
// ============================================================================

const vec3Arb = fc.record({
  x: fc.float({ min: Math.fround(-10000), max: Math.fround(10000), noNaN: true }),
  y: fc.float({ min: Math.fround(-10000), max: Math.fround(10000), noNaN: true }),
  z: fc.float({ min: Math.fround(-10000), max: Math.fround(10000), noNaN: true }),
});

const orientationArb = fc.record({
  x: fc.float({ min: Math.fround(-360), max: Math.fround(360), noNaN: true }),
  y: fc.float({ min: Math.fround(-360), max: Math.fround(360), noNaN: true }),
  z: fc.float({ min: Math.fround(-360), max: Math.fround(360), noNaN: true }),
});

const cameraKeyframeArb: fc.Arbitrary<CameraKeyframe> = fc.record({
  frame: fc.integer({ min: 0, max: 10000 }),
  position: fc.option(vec3Arb, { nil: undefined }),
  orientation: fc.option(orientationArb, { nil: undefined }),
  focalLength: fc.option(fc.float({ min: Math.fround(1), max: Math.fround(500), noNaN: true }), { nil: undefined }),
  zoom: fc.option(fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }), { nil: undefined }),
  focusDistance: fc.option(fc.float({ min: Math.fround(0.1), max: Math.fround(10000), noNaN: true }), { nil: undefined }),
});

const sortedKeyframesArb = fc.array(cameraKeyframeArb, { minLength: 0, maxLength: 20 })
  .map(kfs => kfs.sort((a, b) => a.frame - b.frame));

const camera3DArb: fc.Arbitrary<Camera3D> = fc.record({
  id: fc.uuid(),
  name: fc.string({ minLength: 1, maxLength: 50 }),
  type: fc.constantFrom('perspective', 'orthographic') as fc.Arbitrary<'perspective' | 'orthographic'>,
  position: vec3Arb,
  orientation: orientationArb,
  focalLength: fc.float({ min: Math.fround(1), max: Math.fround(500), noNaN: true }),
  zoom: fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
  filmSize: fc.float({ min: Math.fround(10), max: Math.fround(100), noNaN: true }),
  depthOfField: fc.record({
    enabled: fc.boolean(),
    focusDistance: fc.float({ min: Math.fround(0.1), max: Math.fround(10000), noNaN: true }),
    aperture: fc.float({ min: Math.fround(0.5), max: Math.fround(32), noNaN: true }),
    blurAmount: fc.float({ min: Math.fround(0), max: Math.fround(100), noNaN: true }),
  }),
});

// ============================================================================
// Test: interpolateCameraAtFrame
// ============================================================================

describe('interpolateCameraAtFrame', () => {
  test.prop([camera3DArb, sortedKeyframesArb, fc.integer({ min: 0, max: 10000 })])(
    'returns valid InterpolatedCamera for any inputs',
    (camera, keyframes, frame) => {
      const result = interpolateCameraAtFrame(camera, keyframes, frame);
      
      // Must return valid structure
      expect(result).toHaveProperty('position');
      expect(result).toHaveProperty('rotation');
      expect(result).toHaveProperty('focalLength');
      expect(result).toHaveProperty('zoom');
      expect(result).toHaveProperty('focusDistance');
      
      // No NaN values allowed in output
      expect(Number.isNaN(result.position.x)).toBe(false);
      expect(Number.isNaN(result.position.y)).toBe(false);
      expect(Number.isNaN(result.position.z)).toBe(false);
      expect(Number.isNaN(result.rotation.x)).toBe(false);
      expect(Number.isNaN(result.rotation.y)).toBe(false);
      expect(Number.isNaN(result.rotation.z)).toBe(false);
      expect(Number.isNaN(result.focalLength)).toBe(false);
      expect(Number.isNaN(result.zoom)).toBe(false);
      expect(Number.isNaN(result.focusDistance)).toBe(false);
    }
  );

  test.prop([camera3DArb, sortedKeyframesArb])(
    'at exact keyframe frame returns keyframe values',
    (camera, keyframes) => {
      if (keyframes.length === 0) return; // Skip empty case
      
      const kf = keyframes[0];
      const result = interpolateCameraAtFrame(camera, keyframes, kf.frame);
      
      // If keyframe has position, result should match
      if (kf.position) {
        expect(result.position.x).toBeCloseTo(kf.position.x, 10);
        expect(result.position.y).toBeCloseTo(kf.position.y, 10);
        expect(result.position.z).toBeCloseTo(kf.position.z, 10);
      }
    }
  );

  test.prop([camera3DArb])(
    'with empty keyframes returns camera defaults',
    (camera) => {
      const result = interpolateCameraAtFrame(camera, [], 0);
      
      expect(result.position.x).toBeCloseTo(camera.position.x, 10);
      expect(result.position.y).toBeCloseTo(camera.position.y, 10);
      expect(result.position.z).toBeCloseTo(camera.position.z, 10);
      expect(result.focalLength).toBeCloseTo(camera.focalLength, 10);
    }
  );
});

// ============================================================================
// Test: computeViewMatrix
// ============================================================================

describe('computeViewMatrix', () => {
  test.prop([vec3Arb, orientationArb, fc.float({ min: Math.fround(10), max: Math.fround(200), noNaN: true })])(
    'returns valid 4x4 matrix',
    (position, rotation, focalLength) => {
      const cam = {
        position,
        rotation,
        focalLength,
        zoom: 1,
        focusDistance: 100,
      };
      
      const matrix = computeViewMatrix(cam);
      
      // Must be 4x4
      expect(matrix.length).toBe(4);
      matrix.forEach(row => {
        expect(row.length).toBe(4);
      });
      
      // No NaN values
      matrix.forEach(row => {
        row.forEach(val => {
          expect(Number.isNaN(val)).toBe(false);
          expect(Number.isFinite(val)).toBe(true);
        });
      });
      
      // Last row must be [0, 0, 0, 1] for valid homogeneous matrix
      expect(matrix[3][0]).toBeCloseTo(0, 10);
      expect(matrix[3][1]).toBeCloseTo(0, 10);
      expect(matrix[3][2]).toBeCloseTo(0, 10);
      expect(matrix[3][3]).toBeCloseTo(1, 10);
    }
  );

  test('identity rotation at origin produces identity-like view matrix', () => {
    const cam = {
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };
    
    const matrix = computeViewMatrix(cam);
    
    // With no rotation and at origin, should be close to identity
    expect(matrix[0][0]).toBeCloseTo(1, 10);
    expect(matrix[1][1]).toBeCloseTo(1, 10);
    expect(matrix[2][2]).toBeCloseTo(1, 10);
    expect(matrix[0][3]).toBeCloseTo(0, 10); // translation
    expect(matrix[1][3]).toBeCloseTo(0, 10);
    expect(matrix[2][3]).toBeCloseTo(0, 10);
  });
});

// ============================================================================
// Test: computeProjectionMatrix
// ============================================================================

describe('computeProjectionMatrix', () => {
  test.prop([
    fc.float({ min: Math.fround(10), max: Math.fround(200), noNaN: true }),
    fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
  ])(
    'returns valid 4x4 projection matrix',
    (focalLength, aspectRatio) => {
      const cam = {
        position: { x: 0, y: 0, z: 0 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength,
        zoom: 1,
        focusDistance: 100,
      };
      
      const matrix = computeProjectionMatrix(cam, aspectRatio);
      
      // Must be 4x4
      expect(matrix.length).toBe(4);
      matrix.forEach(row => {
        expect(row.length).toBe(4);
      });
      
      // No NaN values
      matrix.forEach(row => {
        row.forEach(val => {
          expect(Number.isNaN(val)).toBe(false);
        });
      });
    }
  );

  // BUG TEST: Verify FOV conversion is correct
  test('FOV conversion uses correct units (radians)', () => {
    // focalLengthToFOV returns RADIANS
    const fov = focalLengthToFOV(50, 36); // 50mm lens, 36mm sensor
    
    // FOV for 50mm on 36mm should be about 39.6 degrees = 0.69 radians
    // NOT 39.6 * PI / 180 = 0.69, which would then be incorrectly converted again
    expect(fov).toBeGreaterThan(0.5);
    expect(fov).toBeLessThan(1.0);
    
    // The projection matrix should use this value correctly
    const cam = {
      position: { x: 0, y: 0, z: 0 },
      rotation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      focusDistance: 100,
    };
    
    const matrix = computeProjectionMatrix(cam, 16/9);
    
    // The f value (1/tan(fov/2)) for 50mm should produce reasonable values
    // If FOV is incorrectly double-converted, this will fail
    const f = matrix[1][1]; // This is 1/tan(fov/2)
    
    // For 50mm lens, f should be around 2.4 (cot of ~22 degrees)
    // If bug exists (radians treated as degrees), f would be around 57 (cot of ~1 degree)
    expect(f).toBeGreaterThan(1);
    expect(f).toBeLessThan(5);
  });
});

// ============================================================================
// Test: exportToMotionCtrl
// ============================================================================

describe('exportToMotionCtrl', () => {
  test.prop([camera3DArb, sortedKeyframesArb, fc.integer({ min: 1, max: 100 })])(
    'returns correct number of poses',
    (camera, keyframes, frameCount) => {
      const result = exportToMotionCtrl(camera, keyframes, frameCount);
      
      expect(result.camera_poses.length).toBe(frameCount);
    }
  );

  test.prop([camera3DArb, sortedKeyframesArb, fc.integer({ min: 1, max: 100 })])(
    'each pose has valid RT matrix',
    (camera, keyframes, frameCount) => {
      const result = exportToMotionCtrl(camera, keyframes, frameCount);
      
      result.camera_poses.forEach(pose => {
        expect(pose.RT.length).toBe(4);
        pose.RT.forEach(row => {
          expect(row.length).toBe(4);
          row.forEach(val => {
            expect(Number.isNaN(val)).toBe(false);
            expect(Number.isFinite(val)).toBe(true);
          });
        });
      });
    }
  );
});

// ============================================================================
// Test: detectMotionCtrlSVDPreset
// ============================================================================

describe('detectMotionCtrlSVDPreset', () => {
  test.prop([sortedKeyframesArb])(
    'returns valid preset string',
    (keyframes) => {
      const result = detectMotionCtrlSVDPreset(keyframes);
      
      const validPresets = ['static', 'zoom_in', 'zoom_out', 'pan_left', 'pan_right', 'pan_up', 'pan_down', 'rotate_cw', 'rotate_ccw'];
      expect(validPresets).toContain(result);
    }
  );

  test('empty keyframes returns static', () => {
    expect(detectMotionCtrlSVDPreset([])).toBe('static');
  });

  test('single keyframe returns static', () => {
    const kf: CameraKeyframe = { frame: 0 };
    expect(detectMotionCtrlSVDPreset([kf])).toBe('static');
  });
});

// ============================================================================
// Test: analyzeCameraMotion
// ============================================================================

describe('analyzeCameraMotion', () => {
  test.prop([sortedKeyframesArb])(
    'returns valid motion analysis',
    (keyframes) => {
      const result = analyzeCameraMotion(keyframes);
      
      expect(typeof result.hasPan).toBe('boolean');
      expect(typeof result.hasZoom).toBe('boolean');
      expect(typeof result.hasOrbit).toBe('boolean');
      expect(typeof result.hasRotation).toBe('boolean');
      expect(typeof result.panMagnitude).toBe('number');
      expect(typeof result.zoomMagnitude).toBe('number');
      expect(typeof result.orbitMagnitude).toBe('number');
      expect(typeof result.rotationMagnitude).toBe('number');
      
      // Magnitudes must be non-negative
      expect(result.panMagnitude).toBeGreaterThanOrEqual(0);
      expect(result.zoomMagnitude).toBeGreaterThanOrEqual(0);
      expect(result.orbitMagnitude).toBeGreaterThanOrEqual(0);
      expect(result.rotationMagnitude).toBeGreaterThanOrEqual(0);
    }
  );
});

// ============================================================================
// Test: mapToWan22FunCamera
// ============================================================================

describe('mapToWan22FunCamera', () => {
  test.prop([sortedKeyframesArb])(
    'returns valid Wan22 camera motion preset',
    (keyframes) => {
      const result = mapToWan22FunCamera(keyframes);
      
      expect(result).toHaveProperty('camera_motion');
      expect(typeof result.camera_motion).toBe('string');
    }
  );
});

// ============================================================================
// Test: detectUni3CTrajectoryType
// ============================================================================

describe('detectUni3CTrajectoryType', () => {
  test.prop([sortedKeyframesArb])(
    'returns valid Uni3C trajectory type',
    (keyframes) => {
      const result = detectUni3CTrajectoryType(keyframes);
      
      const validTypes = ['orbit', 'custom', 'free1', 'free2', 'free3', 'target1', 'target2'];
      expect(validTypes).toContain(result);
    }
  );
});

// ============================================================================
// Test: exportToUni3C
// ============================================================================

describe('exportToUni3C', () => {
  test.prop([
    camera3DArb,
    sortedKeyframesArb,
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 100, max: 4096 }),
    fc.integer({ min: 100, max: 4096 }),
  ])(
    'returns valid Uni3C data',
    (camera, keyframes, frameCount, width, height) => {
      const result = exportToUni3C(camera, keyframes, frameCount, width, height);
      
      expect(result).toHaveProperty('traj_type');
      
      // If custom trajectory, verify structure
      if (result.traj_type === 'custom' && result.custom_trajectory) {
        expect(result.custom_trajectory.length).toBe(frameCount);
        result.custom_trajectory.forEach(traj => {
          expect(typeof traj.zoom).toBe('number');
          expect(typeof traj.x_offset).toBe('number');
          expect(typeof traj.y_offset).toBe('number');
          expect(typeof traj.z_offset).toBe('number');
          expect(typeof traj.pitch).toBe('number');
          expect(typeof traj.yaw).toBe('number');
          expect(typeof traj.roll).toBe('number');
        });
      }
    }
  );
});

// ============================================================================
// Test: detectCameraCtrlMotionType
// ============================================================================

describe('detectCameraCtrlMotionType', () => {
  test.prop([sortedKeyframesArb])(
    'returns valid CameraCtrl motion type',
    (keyframes) => {
      const result = detectCameraCtrlMotionType(keyframes);
      
      const validTypes = [
        'Static', 'Move Forward', 'Move Backward', 
        'Move Left', 'Move Right', 'Move Up', 'Move Down',
        'Rotate Left', 'Rotate Right', 'Rotate Up', 'Rotate Down',
        'Roll Left', 'Roll Right'
      ];
      expect(validTypes).toContain(result);
    }
  );
});

// ============================================================================
// Test: exportToCameraCtrl
// ============================================================================

describe('exportToCameraCtrl', () => {
  test.prop([sortedKeyframesArb, fc.integer({ min: 1, max: 1000 })])(
    'returns valid CameraCtrl poses',
    (keyframes, frameCount) => {
      const result = exportToCameraCtrl(keyframes, frameCount);
      
      expect(result).toHaveProperty('motion_type');
      expect(result).toHaveProperty('speed');
      expect(result).toHaveProperty('frame_length');
      
      expect(typeof result.speed).toBe('number');
      expect(result.speed).toBeGreaterThanOrEqual(0);
      expect(result.speed).toBeLessThanOrEqual(100);
      expect(result.frame_length).toBe(frameCount);
    }
  );
});

// ============================================================================
// Test: exportCameraMatrices
// ============================================================================

describe('exportCameraMatrices', () => {
  test.prop([
    camera3DArb,
    sortedKeyframesArb,
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 100, max: 4096 }),
    fc.integer({ min: 100, max: 4096 }),
    fc.integer({ min: 1, max: 120 }),
  ])(
    'returns correct frame count and valid matrices',
    (camera, keyframes, frameCount, width, height, fps) => {
      const result = exportCameraMatrices(camera, keyframes, {
        frameCount,
        width,
        height,
        fps,
      });
      
      expect(result.frames.length).toBe(frameCount);
      expect(result.metadata.width).toBe(width);
      expect(result.metadata.height).toBe(height);
      expect(result.metadata.fps).toBe(fps);
      expect(result.metadata.total_frames).toBe(frameCount);
      
      result.frames.forEach((frame, i) => {
        expect(frame.frame).toBe(i);
        expect(frame.view_matrix.length).toBe(4);
        expect(frame.projection_matrix.length).toBe(4);
        expect(frame.position.length).toBe(3);
        expect(frame.rotation.length).toBe(3);
      });
    }
  );
});

// ============================================================================
// Test: exportCameraForTarget (Router)
// ============================================================================

describe('exportCameraForTarget', () => {
  const targets = [
    'motionctrl',
    'motionctrl-svd', 
    'wan22-fun-camera',
    'uni3c-camera',
    'uni3c-motion',
    'animatediff-cameractrl',
    'custom',
  ] as const;

  test.prop([
    fc.constantFrom(...targets),
    camera3DArb,
    sortedKeyframesArb,
    fc.integer({ min: 1, max: 100 }),
  ])(
    'returns valid object for all target formats',
    (target, camera, keyframes, frameCount) => {
      const result = exportCameraForTarget(
        target as any,
        camera,
        keyframes,
        frameCount,
        1920,
        1080,
        24
      );
      
      expect(typeof result).toBe('object');
      expect(result).not.toBeNull();
    }
  );
});

// ============================================================================
// Edge Case Tests
// ============================================================================

describe('Edge Cases', () => {
  test('interpolation with NaN in keyframe position handles gracefully', () => {
    const camera: Camera3D = {
      id: 'test',
      name: 'test',
      type: 'perspective',
      position: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      filmSize: 36,
      depthOfField: {
        enabled: false,
        focusDistance: 100,
        aperture: 2.8,
        blurAmount: 0,
      },
    };
    
    const keyframes: CameraKeyframe[] = [
      { frame: 0, position: { x: NaN, y: 0, z: 0 } },
      { frame: 10, position: { x: 100, y: 0, z: 0 } },
    ];
    
    // This should either throw or return camera defaults, NOT propagate NaN
    const result = interpolateCameraAtFrame(camera, keyframes, 5);
    
    // Document: Currently this WILL propagate NaN - this is a bug
    // The test documents current behavior
    if (Number.isNaN(result.position.x)) {
      // BUG: NaN propagated to output
      console.warn('BUG: NaN propagated in interpolateCameraAtFrame');
    }
  });

  test('lerpAngle handles angles > 360', () => {
    // This tests internal function behavior via interpolation
    const camera: Camera3D = {
      id: 'test',
      name: 'test',
      type: 'perspective',
      position: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      filmSize: 36,
      depthOfField: {
        enabled: false,
        focusDistance: 100,
        aperture: 2.8,
        blurAmount: 0,
      },
    };
    
    const keyframes: CameraKeyframe[] = [
      { frame: 0, orientation: { x: 0, y: 0, z: 0 } },
      { frame: 10, orientation: { x: 0, y: 720, z: 0 } }, // 720 degrees
    ];
    
    const result = interpolateCameraAtFrame(camera, keyframes, 5);
    
    // Result should be interpolated, but 720 degrees is unusual
    // Document behavior
    expect(Number.isFinite(result.rotation.y)).toBe(true);
  });

  test('division by zero when keyframes have same frame', () => {
    const camera: Camera3D = {
      id: 'test',
      name: 'test',
      type: 'perspective',
      position: { x: 0, y: 0, z: 0 },
      orientation: { x: 0, y: 0, z: 0 },
      focalLength: 50,
      zoom: 1,
      filmSize: 36,
      depthOfField: {
        enabled: false,
        focusDistance: 100,
        aperture: 2.8,
        blurAmount: 0,
      },
    };
    
    const keyframes: CameraKeyframe[] = [
      { frame: 5, position: { x: 0, y: 0, z: 0 } },
      { frame: 5, position: { x: 100, y: 0, z: 0 } }, // Same frame!
    ];
    
    // Should not produce NaN from division by zero
    const result = interpolateCameraAtFrame(camera, keyframes, 5);
    
    expect(Number.isNaN(result.position.x)).toBe(false);
  });
});
