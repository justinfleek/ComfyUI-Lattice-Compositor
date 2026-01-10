/**
 * REGRESSION TEST: BUG - Dead Code Division by Zero Guards (4 bugs)
 * 
 * @fixed 2026-01-06
 * @file services/math3d.ts
 * @rootCause Four "dead code" functions had division by zero bugs: fovToFocalLength, zoomToFocalLength, focalLengthToZoom, quatToEuler
 * @fix Added guards to prevent division by zero in all four functions
 * @counterexample Various edge cases (fov=0, compWidth=0, filmSize=0, zero quaternion) produced Infinity/NaN
 */

import { describe, test, expect } from 'vitest';
import {
  fovToFocalLength,
  zoomToFocalLength,
  focalLengthToZoom,
  quatToEuler,
} from '@/services/math3d';
import type { Quat } from '@/services/math3d';

describe('BUG Regression: Dead Code Division by Zero Guards', () => {
  /**
   * BUG 1: fovToFocalLength - fov=0 or fov=PI causes division by zero
   */
  describe('fovToFocalLength division by zero', () => {
    test('original counterexample now passes - fov=0 returns sensorSize', () => {
      // Before fix: fov=0 would cause tan(0/2)=0, division by zero → Infinity
      // After fix: Returns sensorSize as default
      const result = fovToFocalLength(0, 36);
      
      expect(Number.isFinite(result)).toBe(true);
      expect(Number.isNaN(result)).toBe(false);
      expect(result).toBe(36); // Returns sensorSize as default
    });

    test('fov=PI returns sensorSize default', () => {
      const result = fovToFocalLength(Math.PI, 36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(36);
    });

    test('negative fov returns sensorSize default', () => {
      const result = fovToFocalLength(-0.5, 36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(36);
    });

    test('valid fov values work correctly', () => {
      const result = fovToFocalLength(Math.PI / 4, 36); // 45 degrees
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBeGreaterThan(0);
    });
  });

  /**
   * BUG 2: zoomToFocalLength - compWidth=0 causes division by zero
   */
  describe('zoomToFocalLength division by zero', () => {
    test('original counterexample now passes - compWidth=0 returns filmSize', () => {
      // Before fix: compWidth=0 would cause division by zero → Infinity
      // After fix: Returns filmSize as default
      const result = zoomToFocalLength(100, 0, 36);
      
      expect(Number.isFinite(result)).toBe(true);
      expect(Number.isNaN(result)).toBe(false);
      expect(result).toBe(36); // Returns filmSize as default
    });

    test('negative compWidth returns filmSize default', () => {
      const result = zoomToFocalLength(100, -1920, 36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(36);
    });

    test('valid compWidth values work correctly', () => {
      const result = zoomToFocalLength(100, 1920, 36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBeGreaterThan(0);
    });
  });

  /**
   * BUG 3: focalLengthToZoom - filmSize=0 causes division by zero
   */
  describe('focalLengthToZoom division by zero', () => {
    test('original counterexample now passes - filmSize=0 returns compWidth', () => {
      // Before fix: filmSize=0 would cause division by zero → Infinity
      // After fix: Returns compWidth as default
      const result = focalLengthToZoom(50, 1920, 0);
      
      expect(Number.isFinite(result)).toBe(true);
      expect(Number.isNaN(result)).toBe(false);
      expect(result).toBe(1920); // Returns compWidth as default
    });

    test('negative filmSize returns compWidth default', () => {
      const result = focalLengthToZoom(50, 1920, -36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(1920);
    });

    test('valid filmSize values work correctly', () => {
      const result = focalLengthToZoom(50, 1920, 36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBeGreaterThan(0);
    });
  });

  /**
   * BUG 4: quatToEuler - zero quaternion causes division by zero
   */
  describe('quatToEuler division by zero', () => {
    test('original counterexample now passes - zero quaternion returns identity', () => {
      // Before fix: Zero quaternion (length=0) would cause division by zero → NaN
      // After fix: Returns identity rotation (0, 0, 0)
      const zeroQuat: Quat = { x: 0, y: 0, z: 0, w: 0 };
      const result = quatToEuler(zeroQuat);
      
      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      expect(Number.isFinite(result.z)).toBe(true);
      expect(Number.isNaN(result.x)).toBe(false);
      expect(Number.isNaN(result.y)).toBe(false);
      expect(Number.isNaN(result.z)).toBe(false);
      
      // Should return identity rotation
      expect(result.x).toBe(0);
      expect(result.y).toBe(0);
      expect(result.z).toBe(0);
    });

    test('very small quaternion magnitude is handled', () => {
      const tinyQuat: Quat = { x: 0.0001, y: 0.0001, z: 0.0001, w: 0.0001 };
      const result = quatToEuler(tinyQuat);
      
      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      expect(Number.isFinite(result.z)).toBe(true);
    });

    test('valid quaternions work correctly', () => {
      const identityQuat: Quat = { x: 0, y: 0, z: 0, w: 1 };
      const result = quatToEuler(identityQuat);

      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      expect(Number.isFinite(result.z)).toBe(true);
      // Use toBeCloseTo to handle -0 vs 0 (JavaScript Object.is treats them as different)
      expect(result.x).toBeCloseTo(0);
      expect(result.y).toBeCloseTo(0);
      expect(result.z).toBeCloseTo(0);
    });
  });

  /**
   * Additional edge cases - all functions should handle edge cases gracefully
   */
  test('all functions return finite values for edge cases', () => {
    // fovToFocalLength edge cases
    expect(Number.isFinite(fovToFocalLength(0, 36))).toBe(true);
    expect(Number.isFinite(fovToFocalLength(Math.PI, 36))).toBe(true);
    expect(Number.isFinite(fovToFocalLength(-1, 36))).toBe(true);
    
    // zoomToFocalLength edge cases
    expect(Number.isFinite(zoomToFocalLength(100, 0, 36))).toBe(true);
    expect(Number.isFinite(zoomToFocalLength(100, -1920, 36))).toBe(true);
    
    // focalLengthToZoom edge cases
    expect(Number.isFinite(focalLengthToZoom(50, 1920, 0))).toBe(true);
    expect(Number.isFinite(focalLengthToZoom(50, 1920, -36))).toBe(true);
    
    // quatToEuler edge cases
    const zeroQuat: Quat = { x: 0, y: 0, z: 0, w: 0 };
    const result = quatToEuler(zeroQuat);
    expect(Number.isFinite(result.x)).toBe(true);
    expect(Number.isFinite(result.y)).toBe(true);
    expect(Number.isFinite(result.z)).toBe(true);
  });
});
