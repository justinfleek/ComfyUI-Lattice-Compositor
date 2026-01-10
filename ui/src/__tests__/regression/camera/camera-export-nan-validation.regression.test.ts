/**
 * REGRESSION TEST: Camera Export NaN/Infinity Validation
 *
 * @fixed 2026-01-10
 * @file services/export/cameraExportFormats.ts
 * @rootCause Camera export functions could receive NaN rotation/position/focalLength values
 *            from corrupted keyframes or invalid interpolation, producing invalid matrices
 * @fix Added NaN guards with fallback values in computeViewMatrix and computeProjectionMatrix
 * @counterexample exportCameraMatrices with NaN keyframe values would produce NaN-filled matrices
 */

import { describe, test, expect } from 'vitest';
import {
  computeViewMatrix,
  computeProjectionMatrix,
  exportCameraMatrices,
  interpolateCameraAtFrame,
} from '@/services/export/cameraExportFormats';
import type { Camera3D, CameraKeyframe } from '@/types/camera';

function createTestCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  return {
    id: 'test-cam',
    name: 'Test Camera',
    type: 'two-node',
    position: { x: 0, y: 0, z: -1000 },
    pointOfInterest: { x: 0, y: 0, z: 0 },
    orientation: { x: 0, y: 0, z: 0 },
    focalLength: 50,
    filmSize: 36,
    zoom: 100,
    nearClip: 1,
    farClip: 10000,
    depthOfField: {
      enabled: false,
      focusDistance: 500,
      aperture: 2.8,
      focalLength: 50,
      bladeCount: 5,
    },
    ...overrides,
  } as Camera3D;
}

describe('Camera Export NaN Validation Regression', () => {
  describe('computeViewMatrix NaN guards', () => {
    /**
     * Original bug: NaN rotation values would produce NaN-filled view matrix
     * Fix: Guard against NaN, fallback to 0 for invalid rotation components
     */
    test('handles NaN rotation values with fallback', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: NaN, y: NaN, z: NaN },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      const matrix = computeViewMatrix(cam);

      // Matrix should be valid (no NaN values)
      for (const row of matrix) {
        for (const value of row) {
          expect(Number.isFinite(value)).toBe(true);
        }
      }
    });

    test('handles NaN position values with fallback', () => {
      const cam = {
        position: { x: NaN, y: NaN, z: NaN },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      const matrix = computeViewMatrix(cam);

      // Matrix should be valid (no NaN values)
      for (const row of matrix) {
        for (const value of row) {
          expect(Number.isFinite(value)).toBe(true);
        }
      }
    });

    test('handles mixed NaN and valid values', () => {
      const cam = {
        position: { x: 100, y: NaN, z: -500 },
        rotation: { x: NaN, y: 45, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      const matrix = computeViewMatrix(cam);

      // Matrix should be valid
      for (const row of matrix) {
        for (const value of row) {
          expect(Number.isFinite(value)).toBe(true);
        }
      }
    });

    test('handles Infinity position values', () => {
      const cam = {
        position: { x: Infinity, y: -Infinity, z: 0 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      const matrix = computeViewMatrix(cam);

      // Should fallback to 0 for invalid position
      for (const row of matrix) {
        for (const value of row) {
          expect(Number.isFinite(value)).toBe(true);
        }
      }
    });
  });

  describe('computeProjectionMatrix validation', () => {
    /**
     * Original bug: Invalid aspectRatio would produce broken projection
     * Fix: Validate aspectRatio is positive and finite
     */
    test('throws on zero aspectRatio', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      expect(() => computeProjectionMatrix(cam, 0)).toThrow('Invalid aspectRatio');
    });

    test('throws on negative aspectRatio', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      expect(() => computeProjectionMatrix(cam, -1)).toThrow('Invalid aspectRatio');
    });

    test('throws on NaN aspectRatio', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      expect(() => computeProjectionMatrix(cam, NaN)).toThrow('Invalid aspectRatio');
    });

    test('throws on Infinity aspectRatio', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      expect(() => computeProjectionMatrix(cam, Infinity)).toThrow('Invalid aspectRatio');
    });

    /**
     * Original bug: NaN focalLength would produce NaN in projection matrix
     * Fix: Fallback to 50mm standard lens for invalid focalLength
     */
    test('handles NaN focalLength with fallback to 50mm', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: NaN,
        zoom: 1,
        focusDistance: 500,
      };

      const matrix = computeProjectionMatrix(cam, 16 / 9);

      // Matrix should be valid
      for (const row of matrix) {
        for (const value of row) {
          expect(Number.isFinite(value)).toBe(true);
        }
      }
    });

    /**
     * Original bug: Invalid nearClip/farClip could cause divide by zero
     * Fix: Validate and provide safe defaults
     */
    test('handles invalid nearClip with fallback', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      const matrix = computeProjectionMatrix(cam, 16 / 9, NaN, 1000);

      for (const row of matrix) {
        for (const value of row) {
          expect(Number.isFinite(value)).toBe(true);
        }
      }
    });

    test('handles invalid farClip with fallback', () => {
      const cam = {
        position: { x: 0, y: 0, z: -1000 },
        rotation: { x: 0, y: 0, z: 0 },
        focalLength: 50,
        zoom: 1,
        focusDistance: 500,
      };

      const matrix = computeProjectionMatrix(cam, 16 / 9, 0.1, NaN);

      for (const row of matrix) {
        for (const value of row) {
          expect(Number.isFinite(value)).toBe(true);
        }
      }
    });
  });

  describe('exportCameraMatrices validation', () => {
    const camera = createTestCamera();
    const keyframes: CameraKeyframe[] = [];

    test('throws on invalid width', () => {
      expect(() => exportCameraMatrices(camera, keyframes, {
        frameCount: 24,
        width: 0,
        height: 1080,
        fps: 24,
      })).toThrow('Invalid dimensions');
    });

    test('throws on invalid height', () => {
      expect(() => exportCameraMatrices(camera, keyframes, {
        frameCount: 24,
        width: 1920,
        height: -1,
        fps: 24,
      })).toThrow('Invalid dimensions');
    });

    test('throws on NaN dimensions', () => {
      expect(() => exportCameraMatrices(camera, keyframes, {
        frameCount: 24,
        width: NaN,
        height: NaN,
        fps: 24,
      })).toThrow('Invalid dimensions');
    });

    test('throws on invalid fps', () => {
      expect(() => exportCameraMatrices(camera, keyframes, {
        frameCount: 24,
        width: 1920,
        height: 1080,
        fps: 0,
      })).toThrow('Invalid fps');
    });

    test('throws on NaN fps', () => {
      expect(() => exportCameraMatrices(camera, keyframes, {
        frameCount: 24,
        width: 1920,
        height: 1080,
        fps: NaN,
      })).toThrow('Invalid fps');
    });

    test('throws on invalid frameCount', () => {
      expect(() => exportCameraMatrices(camera, keyframes, {
        frameCount: -1,
        width: 1920,
        height: 1080,
        fps: 24,
      })).toThrow('Invalid frameCount');
    });

    test('produces valid export with valid inputs', () => {
      const result = exportCameraMatrices(camera, keyframes, {
        frameCount: 10,
        width: 1920,
        height: 1080,
        fps: 24,
      });

      expect(result.frames.length).toBe(10);
      expect(result.metadata.width).toBe(1920);
      expect(result.metadata.height).toBe(1080);
      expect(result.metadata.fps).toBe(24);

      // Verify all matrices are valid
      for (const frame of result.frames) {
        for (const row of frame.view_matrix) {
          for (const value of row) {
            expect(Number.isFinite(value)).toBe(true);
          }
        }
        for (const row of frame.projection_matrix) {
          for (const value of row) {
            expect(Number.isFinite(value)).toBe(true);
          }
        }
      }
    });
  });

  describe('interpolateCameraAtFrame with corrupted keyframes', () => {
    const camera = createTestCamera();

    test('handles keyframes with undefined position', () => {
      const keyframes: CameraKeyframe[] = [
        { frame: 0, position: undefined as any },
        { frame: 24, position: { x: 100, y: 100, z: -500 } },
      ];

      // Should not throw, should use camera defaults for missing values
      const result = interpolateCameraAtFrame(camera, keyframes, 12);
      expect(Number.isFinite(result.position.x)).toBe(true);
      expect(Number.isFinite(result.position.y)).toBe(true);
      expect(Number.isFinite(result.position.z)).toBe(true);
    });

    test('handles empty keyframes array', () => {
      const result = interpolateCameraAtFrame(camera, [], 12);

      // Should return camera defaults
      expect(result.position).toEqual(camera.position);
      expect(result.rotation).toEqual(camera.orientation);
    });

    test('handles frame before all keyframes', () => {
      const keyframes: CameraKeyframe[] = [
        { frame: 10, position: { x: 100, y: 0, z: -500 } },
      ];

      const result = interpolateCameraAtFrame(camera, keyframes, 5);
      expect(Number.isFinite(result.position.x)).toBe(true);
    });

    test('handles frame after all keyframes', () => {
      const keyframes: CameraKeyframe[] = [
        { frame: 10, position: { x: 100, y: 0, z: -500 } },
      ];

      const result = interpolateCameraAtFrame(camera, keyframes, 20);
      expect(Number.isFinite(result.position.x)).toBe(true);
    });
  });
});
