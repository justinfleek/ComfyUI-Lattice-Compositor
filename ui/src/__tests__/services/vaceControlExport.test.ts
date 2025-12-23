/**
 * Tests for VACE Control Video Export
 */
import { describe, it, expect } from 'vitest';
import {
  PathFollower,
  VACEControlExporter,
  createPathFollower,
  createVACEExportConfig,
  calculateDurationForSpeed,
  calculateSpeed,
  splineLayerToPathFollower
} from '../../services/export/vaceControlExport';
import type { SplineControlPoint } from '@/types/project';

// Helper to create test control points
function createTestPath(): SplineControlPoint[] {
  return [
    { x: 100, y: 100, handleIn: null, handleOut: { x: 50, y: 0, z: 0 } },
    { x: 200, y: 100, handleIn: { x: -50, y: 0, z: 0 }, handleOut: { x: 50, y: 0, z: 0 } },
    { x: 300, y: 200, handleIn: { x: -50, y: 0, z: 0 }, handleOut: null }
  ];
}

describe('VACE Control Export - PathFollower', () => {
  describe('createPathFollower', () => {
    it('should create path follower with defaults', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints);

      expect(config.id).toBe('test');
      expect(config.shape).toBe('circle');
      expect(config.size).toEqual([20, 20]);
      expect(config.fillColor).toBe('#FFFFFF');
      expect(config.duration).toBe(60);
      expect(config.easing).toBe('ease-in-out');
      expect(config.alignToPath).toBe(true);
    });

    it('should accept custom options', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, {
        shape: 'square',
        size: [40, 40],
        duration: 120,
        easing: 'linear'
      });

      expect(config.shape).toBe('square');
      expect(config.size).toEqual([40, 40]);
      expect(config.duration).toBe(120);
      expect(config.easing).toBe('linear');
    });
  });

  describe('PathFollower class', () => {
    it('should calculate path length', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, { duration: 60 });
      const follower = new PathFollower(config);

      expect(follower.getPathLength()).toBeGreaterThan(0);
    });

    it('should calculate speed as length/duration', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, { duration: 60 });
      const follower = new PathFollower(config);

      const expectedSpeed = follower.getPathLength() / 60;
      expect(follower.getSpeed()).toBeCloseTo(expectedSpeed, 5);
    });

    it('should return not visible before startFrame', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, { startFrame: 10, duration: 60 });
      const follower = new PathFollower(config);

      const state = follower.getStateAtFrame(5);
      expect(state.visible).toBe(false);
    });

    it('should return visible during animation', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, { startFrame: 0, duration: 60 });
      const follower = new PathFollower(config);

      const state = follower.getStateAtFrame(30);
      expect(state.visible).toBe(true);
      expect(state.progress).toBeGreaterThan(0);
      expect(state.progress).toBeLessThan(1);
    });

    it('should progress to end of path at endFrame', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, { startFrame: 0, duration: 60 });
      const follower = new PathFollower(config);

      const state = follower.getStateAtFrame(60);
      expect(state.progress).toBeCloseTo(1, 2);
    });

    it('should handle looping', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, {
        startFrame: 0,
        duration: 30,
        loop: true,
        loopMode: 'restart'
      });
      const follower = new PathFollower(config);

      // Frame 45 should be equivalent to frame 15 (45 % 30 = 15)
      const state15 = follower.getStateAtFrame(15);
      const state45 = follower.getStateAtFrame(45);

      expect(state45.progress).toBeCloseTo(state15.progress, 2);
    });

    it('should handle pingpong looping', () => {
      const controlPoints = createTestPath();
      const config = createPathFollower('test', controlPoints, {
        startFrame: 0,
        duration: 30,
        loop: true,
        loopMode: 'pingpong'
      });
      const follower = new PathFollower(config);

      // In pingpong mode, frame 45 should go backward
      const state15 = follower.getStateAtFrame(15);
      const state45 = follower.getStateAtFrame(45);

      // 45 is in second half of cycle, should be going backward
      // position in cycle = 45 % 30 = 15, but direction reversed
      // so effective position = 30 - 15 = 15 from end
      expect(state45.visible).toBe(true);
    });
  });
});

describe('VACE Control Export - VACEControlExporter', () => {
  describe('renderFrame', () => {
    it('should render frame with correct dimensions', () => {
      const controlPoints = createTestPath();
      const pathFollower = createPathFollower('test', controlPoints);
      const config = createVACEExportConfig([pathFollower], {
        width: 512,
        height: 512,
        startFrame: 0,
        endFrame: 60
      });

      const exporter = new VACEControlExporter(config);
      const frame = exporter.renderFrame(30);

      expect(frame.canvas.width).toBe(512);
      expect(frame.canvas.height).toBe(512);
      expect(frame.frameNumber).toBe(30);
    });

    it('should track follower states', () => {
      const controlPoints = createTestPath();
      const pathFollower = createPathFollower('test', controlPoints);
      const config = createVACEExportConfig([pathFollower]);

      const exporter = new VACEControlExporter(config);
      const frame = exporter.renderFrame(30);

      expect(frame.states.has('test')).toBe(true);
      const state = frame.states.get('test')!;
      expect(state.visible).toBe(true);
    });

    it('should render black background by default', () => {
      const controlPoints = createTestPath();
      const pathFollower = createPathFollower('test', controlPoints);
      const config = createVACEExportConfig([pathFollower], {
        width: 100,
        height: 100
      });

      const exporter = new VACEControlExporter(config);
      const frame = exporter.renderFrame(30);
      const ctx = frame.canvas.getContext('2d')!;
      const imageData = ctx.getImageData(0, 0, 1, 1);

      // Background should be black (or near black)
      expect(imageData.data[0]).toBeLessThan(10); // R
      expect(imageData.data[1]).toBeLessThan(10); // G
      expect(imageData.data[2]).toBeLessThan(10); // B
    });
  });

  describe('renderAllFrames', () => {
    it('should generate correct number of frames', () => {
      const controlPoints = createTestPath();
      const pathFollower = createPathFollower('test', controlPoints);
      const config = createVACEExportConfig([pathFollower], {
        startFrame: 0,
        endFrame: 10
      });

      const exporter = new VACEControlExporter(config);
      const frames = [...exporter.renderAllFrames()];

      expect(frames.length).toBe(11); // 0 to 10 inclusive
    });
  });

  describe('getPathStats', () => {
    it('should return stats for all followers', () => {
      const controlPoints = createTestPath();
      const follower1 = createPathFollower('path1', controlPoints, { duration: 30 });
      const follower2 = createPathFollower('path2', controlPoints, { duration: 60 });
      const config = createVACEExportConfig([follower1, follower2]);

      const exporter = new VACEControlExporter(config);
      const stats = exporter.getPathStats();

      expect(stats.length).toBe(2);
      expect(stats[0].id).toBe('path1');
      expect(stats[0].duration).toBe(30);
      expect(stats[1].id).toBe('path2');
      expect(stats[1].duration).toBe(60);
    });
  });
});

describe('VACE Control Export - Utility Functions', () => {
  describe('calculateDurationForSpeed', () => {
    it('should calculate correct duration', () => {
      // Path length 100, speed 10 px/frame → duration 10 frames
      const duration = calculateDurationForSpeed(100, 10);
      expect(duration).toBe(10);
    });

    it('should round up fractional durations', () => {
      // Path length 100, speed 7 px/frame → 14.28... → 15 frames
      const duration = calculateDurationForSpeed(100, 7);
      expect(duration).toBe(15);
    });
  });

  describe('calculateSpeed', () => {
    it('should calculate correct speed', () => {
      // Path length 120, duration 60 frames → 2 px/frame
      const speed = calculateSpeed(120, 60);
      expect(speed).toBe(2);
    });
  });

  describe('splineLayerToPathFollower', () => {
    it('should convert spline layer data to path follower config', () => {
      const controlPoints = createTestPath();
      const config = splineLayerToPathFollower('layer1', controlPoints, false, 80);

      expect(config.id).toBe('layer1');
      expect(config.controlPoints).toBe(controlPoints);
      expect(config.closed).toBe(false);
      expect(config.duration).toBe(80);
    });
  });
});

describe('VACE Control Export - Shape Types', () => {
  it('should support all shape types without error', () => {
    const controlPoints = createTestPath();
    const shapes = ['circle', 'square', 'triangle', 'diamond', 'arrow'] as const;

    for (const shape of shapes) {
      const follower = createPathFollower('test', controlPoints, { shape });
      const config = createVACEExportConfig([follower], {
        width: 100,
        height: 100
      });

      const exporter = new VACEControlExporter(config);
      expect(() => exporter.renderFrame(30)).not.toThrow();
    }
  });
});

describe('VACE Control Export - Easing Functions', () => {
  it('should apply different easings correctly', () => {
    const controlPoints = createTestPath();
    const easings = ['linear', 'ease-in', 'ease-out', 'ease-in-out', 'ease-in-cubic', 'ease-out-cubic'] as const;

    const results: number[] = [];

    for (const easing of easings) {
      const config = createPathFollower('test', controlPoints, {
        startFrame: 0,
        duration: 100,
        easing
      });
      const follower = new PathFollower(config);
      const state = follower.getStateAtFrame(50); // Midpoint
      results.push(state.progress);
    }

    // Linear should be 0.5 at midpoint
    expect(results[0]).toBeCloseTo(0.5, 2);

    // Ease-in should be less than 0.5 at midpoint
    expect(results[1]).toBeLessThan(0.5);

    // Ease-out should be greater than 0.5 at midpoint
    expect(results[2]).toBeGreaterThan(0.5);
  });
});
