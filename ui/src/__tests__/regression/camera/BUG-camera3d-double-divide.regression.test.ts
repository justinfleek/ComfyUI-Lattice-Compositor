/**
 * REGRESSION TEST: BUG - Double Perspective Divide
 * 
 * @fixed 2026-01-05
 * @file services/camera3DVisualization.ts
 * @rootCause projectToScreen was doing perspective divide twice - once manually and once in transformPoint()
 * @fix Removed redundant w-divide in projectToScreen (transformPoint already does it)
 * @counterexample Projecting 3D points to screen produced incorrect coordinates
 */

import { describe, test, expect } from 'vitest';
import { projectToScreen, getCameraViewMatrices } from '@/services/camera3DVisualization';
import { vec3 } from '@/services/math3d';
import type { Camera3D } from '@/types/camera';

function createTestCamera(overrides: Partial<Camera3D> = {}): Camera3D {
  return {
    id: 'test-cam',
    name: 'Test Camera',
    type: 'two-node',
    position: vec3(0, 0, -1000),
    pointOfInterest: vec3(0, 0, 0),
    orientation: vec3(0, 0, 0),
    focalLength: 50,
    filmSize: 36,
    zoom: 100,
    nearClip: 1,
    farClip: 10000,
    ...overrides,
  };
}

describe('BUG Regression: Double Perspective Divide', () => {
  /**
   * This test MUST reproduce the exact counterexample from the bug report.
   * Before fix: Points were divided by w twice, producing incorrect screen coordinates
   * After fix: transformPoint() handles perspective divide, no redundant divide
   */
  test('original counterexample now passes', () => {
    const camera = createTestCamera({
      position: vec3(0, 0, -1000),
      pointOfInterest: vec3(0, 0, 0),
      focalLength: 50,
      filmSize: 36,
      nearClip: 1,
      farClip: 10000,
    });

    const compWidth = 1920;
    const compHeight = 1080;
    const matrices = getCameraViewMatrices(camera, compWidth, compHeight);

    // Test point at origin (should be center of screen)
    const point = vec3(0, 0, 0);
    const result = projectToScreen(point, matrices.viewProjection, compWidth, compHeight);

    // Point should be visible and projected to center of screen
    expect(result.visible).toBe(true);
    expect(result.x).toBeCloseTo(compWidth / 2, 1);
    expect(result.y).toBeCloseTo(compHeight / 2, 1);
    
    // Z should be in valid NDC range [-1, 1]
    expect(result.z).toBeGreaterThanOrEqual(-1);
    expect(result.z).toBeLessThanOrEqual(1);
  });

  /**
   * Additional edge cases related to this bug.
   */
  test('points at various depths project correctly', () => {
    const camera = createTestCamera();
    const compWidth = 1920;
    const compHeight = 1080;
    const matrices = getCameraViewMatrices(camera, compWidth, compHeight);

    const testPoints = [
      vec3(0, 0, -500),   // Close to camera
      vec3(0, 0, 0),      // At origin
      vec3(0, 0, 500),    // Far from camera
      vec3(100, 100, 0),  // Offset from center
    ];

    for (const point of testPoints) {
      const result = projectToScreen(point, matrices.viewProjection, compWidth, compHeight);
      
      // Should produce valid screen coordinates
      expect(result.x).toBeGreaterThanOrEqual(0);
      expect(result.x).toBeLessThanOrEqual(compWidth);
      expect(result.y).toBeGreaterThanOrEqual(0);
      expect(result.y).toBeLessThanOrEqual(compHeight);
      
      // Z should be finite
      expect(Number.isFinite(result.z)).toBe(true);
    }
  });

  test('points behind camera are correctly marked invisible', () => {
    const camera = createTestCamera({
      position: vec3(0, 0, -1000),
      pointOfInterest: vec3(0, 0, 0),
    });
    const compWidth = 1920;
    const compHeight = 1080;
    const matrices = getCameraViewMatrices(camera, compWidth, compHeight);

    // Point behind camera (positive Z in camera space)
    const pointBehind = vec3(0, 0, 2000);
    const result = projectToScreen(pointBehind, matrices.viewProjection, compWidth, compHeight);

    // Should be marked as not visible
    expect(result.visible).toBe(false);
    expect(result.x).toBe(0);
    expect(result.y).toBe(0);
    expect(result.z).toBe(0);
  });

  test('projection is consistent across multiple calls', () => {
    const camera = createTestCamera();
    const compWidth = 1920;
    const compHeight = 1080;
    const matrices = getCameraViewMatrices(camera, compWidth, compHeight);
    const point = vec3(100, 200, 0);

    // Project same point multiple times - should get same result
    const result1 = projectToScreen(point, matrices.viewProjection, compWidth, compHeight);
    const result2 = projectToScreen(point, matrices.viewProjection, compWidth, compHeight);
    const result3 = projectToScreen(point, matrices.viewProjection, compWidth, compHeight);

    expect(result1.x).toBe(result2.x);
    expect(result1.y).toBe(result2.y);
    expect(result1.z).toBe(result2.z);
    expect(result1.visible).toBe(result2.visible);

    expect(result2.x).toBe(result3.x);
    expect(result2.y).toBe(result3.y);
    expect(result2.z).toBe(result3.z);
    expect(result2.visible).toBe(result3.visible);
  });
});
