/**
 * Pose Export Browser Tests
 * 
 * Tests pose rendering in real browser with Canvas support.
 */

import { describe, expect, test } from 'vitest';
import {
  renderPoseFrame,
  createDefaultPoseExportConfig,
  type PoseExportConfig,
  type Pose,
} from '@/services/export/poseExport';

// ============================================================================
// HELPERS
// ============================================================================

function createTestPose(keypointCount: number = 18): Pose {
  return {
    id: `pose-${Math.random()}`,
    keypoints: Array(keypointCount).fill(null).map(() => ({
      x: Math.random(),
      y: Math.random(),
      confidence: Math.random(),
    })),
    format: keypointCount === 18 ? 'coco18' : 'openpose',
  };
}

// ============================================================================
// CANVAS RENDERING TESTS
// ============================================================================

describe('STRICT: Pose Canvas Rendering', () => {
  
  test('renderPoseFrame creates canvas with correct dimensions', () => {
    const config = createDefaultPoseExportConfig();
    const pose = createTestPose();
    
    const canvas = renderPoseFrame([pose], config);
    
    expect(canvas).toBeInstanceOf(HTMLCanvasElement);
    expect(canvas.width).toBe(config.width);
    expect(canvas.height).toBe(config.height);
  });

  test('renderPoseFrame with custom dimensions', () => {
    const config: PoseExportConfig = {
      ...createDefaultPoseExportConfig(),
      width: 1024,
      height: 768,
    };
    const pose = createTestPose();
    
    const canvas = renderPoseFrame([pose], config);
    
    expect(canvas.width).toBe(1024);
    expect(canvas.height).toBe(768);
  });

  test('renderPoseFrame fills background color', () => {
    const config: PoseExportConfig = {
      ...createDefaultPoseExportConfig(),
      width: 10,
      height: 10,
      backgroundColor: '#ff0000',
      showKeypoints: false,
      showBones: false,
    };
    
    const canvas = renderPoseFrame([], config);
    const ctx = canvas.getContext('2d')!;
    const pixel = ctx.getImageData(5, 5, 1, 1).data;
    
    // Should be red
    expect(pixel[0]).toBe(255);
    expect(pixel[1]).toBe(0);
    expect(pixel[2]).toBe(0);
  });

  test('renderPoseFrame handles empty pose array', () => {
    const config = createDefaultPoseExportConfig();
    
    const canvas = renderPoseFrame([], config);
    
    expect(canvas.width).toBe(config.width);
    expect(canvas.height).toBe(config.height);
  });

  test('renderPoseFrame handles multiple poses', () => {
    const config = createDefaultPoseExportConfig();
    const poses = [createTestPose(), createTestPose(), createTestPose()];
    
    const canvas = renderPoseFrame(poses, config);
    
    expect(canvas).toBeInstanceOf(HTMLCanvasElement);
  });

  test('renderPoseFrame respects showKeypoints=false', () => {
    const config: PoseExportConfig = {
      ...createDefaultPoseExportConfig(),
      showKeypoints: false,
      showBones: true,
    };
    const pose = createTestPose();
    
    // Should not throw
    const canvas = renderPoseFrame([pose], config);
    expect(canvas).toBeInstanceOf(HTMLCanvasElement);
  });

  test('renderPoseFrame respects showBones=false', () => {
    const config: PoseExportConfig = {
      ...createDefaultPoseExportConfig(),
      showKeypoints: true,
      showBones: false,
    };
    const pose = createTestPose();
    
    const canvas = renderPoseFrame([pose], config);
    expect(canvas).toBeInstanceOf(HTMLCanvasElement);
  });

  test('renderPoseFrame with useOpenPoseColors', () => {
    const config: PoseExportConfig = {
      ...createDefaultPoseExportConfig(),
      useOpenPoseColors: true,
    };
    const pose = createTestPose();
    
    const canvas = renderPoseFrame([pose], config);
    expect(canvas).toBeInstanceOf(HTMLCanvasElement);
  });

  test('DETERMINISM: same input produces same output', () => {
    const config = createDefaultPoseExportConfig();
    const pose: Pose = {
      id: 'determinism-test',
      keypoints: Array(18).fill(null).map((_, i) => ({
        x: i / 18,
        y: i / 18,
        confidence: 1.0,
      })),
      format: 'coco18',
    };
    
    const canvas1 = renderPoseFrame([pose], config);
    const canvas2 = renderPoseFrame([pose], config);
    
    const ctx1 = canvas1.getContext('2d')!;
    const ctx2 = canvas2.getContext('2d')!;
    const data1 = ctx1.getImageData(0, 0, canvas1.width, canvas1.height);
    const data2 = ctx2.getImageData(0, 0, canvas2.width, canvas2.height);
    
    // Compare all pixels
    for (let i = 0; i < data1.data.length; i++) {
      expect(data1.data[i]).toBe(data2.data[i]);
    }
  });
});
