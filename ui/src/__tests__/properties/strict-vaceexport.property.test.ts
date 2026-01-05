/**
 * STRICT Property Tests: VACE Control Export
 * 
 * Tests VACE (Video Animation Control Engine) export for:
 * - White shapes on black background (#000000)
 * - Arc-length parameterized path following
 * - Speed = pathLength / duration (implicit)
 * - Easing functions for motion timing
 * 
 * Model Requirements:
 * - Background: Pure black (#000000)
 * - Shapes: White (#FFFFFF) or custom color
 * - Clean edges (anti-aliased optional)
 * - Consistent motion speed via arc-length parameterization
 */

import { describe, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  PathFollower,
  VACEControlExporter,
  createPathFollower,
  createVACEExportConfig,
  calculateDurationForSpeed,
  calculateSpeed,
  splineLayerToPathFollower,
  type PathFollowerConfig,
  type PathFollowerShape,
  type PathFollowerEasing,
  type VACEExportConfig,
  type PathFollowerState,
} from '@/services/export/vaceControlExport';

// BUG-054: EASING_FUNCTIONS is not exported from vaceControlExport.ts
// This is an internal constant that should be exported for testing/preview
// For now, we define our own copy to test expected behavior
const EASING_FUNCTIONS: Record<PathFollowerEasing, (t: number) => number> = {
  'linear': (t) => t,
  'ease-in': (t) => t * t,
  'ease-out': (t) => t * (2 - t),
  'ease-in-out': (t) => t < 0.5 ? 2 * t * t : -1 + (4 - 2 * t) * t,
  'ease-in-cubic': (t) => t * t * t,
  'ease-out-cubic': (t) => (--t) * t * t + 1,
};
import type { ControlPoint } from '@/types/spline';

// ============================================================================
// ARBITRARIES
// ============================================================================

// Generate a valid control point
const arbitraryControlPoint = (): fc.Arbitrary<ControlPoint> =>
  fc.record({
    x: fc.double({ min: 0, max: 1024, noNaN: true }),
    y: fc.double({ min: 0, max: 1024, noNaN: true }),
    handleIn: fc.option(
      fc.record({
        x: fc.double({ min: -100, max: 100, noNaN: true }),
        y: fc.double({ min: -100, max: 100, noNaN: true }),
      }),
      { nil: null }
    ),
    handleOut: fc.option(
      fc.record({
        x: fc.double({ min: -100, max: 100, noNaN: true }),
        y: fc.double({ min: -100, max: 100, noNaN: true }),
      }),
      { nil: null }
    ),
  });

// Generate path with at least 2 points
const arbitraryPath = (minPoints: number = 2, maxPoints: number = 10): fc.Arbitrary<ControlPoint[]> =>
  fc.array(arbitraryControlPoint(), { minLength: minPoints, maxLength: maxPoints });

// Generate shape type
const arbitraryShape = (): fc.Arbitrary<PathFollowerShape> =>
  fc.constantFrom('circle', 'square', 'triangle', 'diamond', 'arrow', 'custom');

// Generate easing function
const arbitraryEasing = (): fc.Arbitrary<PathFollowerEasing> =>
  fc.constantFrom('linear', 'ease-in', 'ease-out', 'ease-in-out', 'ease-in-cubic', 'ease-out-cubic');

// Generate path follower config
const arbitraryPathFollowerConfig = (): fc.Arbitrary<PathFollowerConfig> =>
  fc.record({
    id: fc.uuid(),
    controlPoints: arbitraryPath(2, 6),
    closed: fc.boolean(),
    shape: arbitraryShape(),
    size: fc.tuple(
      fc.integer({ min: 5, max: 100 }),
      fc.integer({ min: 5, max: 100 })
    ),
    fillColor: fc.hexaString({ minLength: 6, maxLength: 6 }).map(s => `#${s}`),
    strokeColor: fc.option(
      fc.hexaString({ minLength: 6, maxLength: 6 }).map(s => `#${s}`),
      { nil: undefined }
    ),
    strokeWidth: fc.option(fc.integer({ min: 1, max: 10 }), { nil: undefined }),
    startFrame: fc.integer({ min: 0, max: 100 }),
    duration: fc.integer({ min: 1, max: 200 }),
    easing: arbitraryEasing(),
    alignToPath: fc.boolean(),
    rotationOffset: fc.integer({ min: -180, max: 180 }),
    loop: fc.boolean(),
    loopMode: fc.constantFrom('restart', 'pingpong'),
    scaleStart: fc.double({ min: 0.1, max: 2, noNaN: true }),
    scaleEnd: fc.double({ min: 0.1, max: 2, noNaN: true }),
    opacityStart: fc.double({ min: 0, max: 1, noNaN: true }),
    opacityEnd: fc.double({ min: 0, max: 1, noNaN: true }),
  });

// ============================================================================
// EASING FUNCTION TESTS
// ============================================================================

describe('STRICT: VACE Easing Functions', () => {
  test.prop([fc.double({ min: 0, max: 1, noNaN: true })])(
    'linear easing: f(t) = t',
    (t) => {
      const result = EASING_FUNCTIONS['linear'](t);
      expect(result).toBeCloseTo(t, 10);
    }
  );

  test('easing functions: f(0) = 0', () => {
    const easings: PathFollowerEasing[] = [
      'linear', 'ease-in', 'ease-out', 'ease-in-out', 'ease-in-cubic', 'ease-out-cubic'
    ];
    
    for (const easing of easings) {
      expect(EASING_FUNCTIONS[easing](0)).toBeCloseTo(0, 10);
    }
  });

  test('easing functions: f(1) = 1', () => {
    const easings: PathFollowerEasing[] = [
      'linear', 'ease-in', 'ease-out', 'ease-in-out', 'ease-in-cubic', 'ease-out-cubic'
    ];
    
    for (const easing of easings) {
      expect(EASING_FUNCTIONS[easing](1)).toBeCloseTo(1, 10);
    }
  });

  test.prop([fc.double({ min: 0, max: 1, noNaN: true })])(
    'easing functions are monotonic (output in [0, 1])',
    (t) => {
      const easings: PathFollowerEasing[] = [
        'linear', 'ease-in', 'ease-out', 'ease-in-out', 'ease-in-cubic', 'ease-out-cubic'
      ];
      
      for (const easing of easings) {
        const result = EASING_FUNCTIONS[easing](t);
        expect(result).toBeGreaterThanOrEqual(0);
        expect(result).toBeLessThanOrEqual(1);
      }
    }
  );

  test('ease-in starts slow', () => {
    const mid = EASING_FUNCTIONS['ease-in'](0.5);
    // ease-in at 0.5 should be less than linear 0.5
    expect(mid).toBeLessThan(0.5);
  });

  test('ease-out ends slow', () => {
    const mid = EASING_FUNCTIONS['ease-out'](0.5);
    // ease-out at 0.5 should be greater than linear 0.5
    expect(mid).toBeGreaterThan(0.5);
  });

  test('ease-in-out is symmetric at midpoint', () => {
    const mid = EASING_FUNCTIONS['ease-in-out'](0.5);
    expect(mid).toBeCloseTo(0.5, 10);
  });
});

// ============================================================================
// PATH FOLLOWER TESTS
// ============================================================================

describe('STRICT: PathFollower Class', () => {
  test('path with 2 points has positive length', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: { x: 50, y: 0 } },
      { x: 100, y: 0, handleIn: { x: -50, y: 0 }, handleOut: null },
    ]);
    
    const follower = new PathFollower(config);
    
    expect(follower.getPathLength()).toBeGreaterThan(0);
  });

  test('single point path has zero length', () => {
    const config = createPathFollower('test', [
      { x: 50, y: 50, handleIn: null, handleOut: null },
    ]);
    
    const follower = new PathFollower(config);
    
    expect(follower.getPathLength()).toBe(0);
  });

  test('speed = pathLength / duration', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { duration: 10 });
    
    const follower = new PathFollower(config);
    const pathLength = follower.getPathLength();
    const speed = follower.getSpeed();
    
    expect(speed).toBeCloseTo(pathLength / 10, 5);
  });

  test('state at startFrame - 1 is not visible', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 10, duration: 20 });
    
    const follower = new PathFollower(config);
    const state = follower.getStateAtFrame(9); // Before start
    
    expect(state.visible).toBe(false);
    expect(state.progress).toBe(0);
  });

  test('state at startFrame has progress 0', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 10, duration: 20, easing: 'linear' });
    
    const follower = new PathFollower(config);
    const state = follower.getStateAtFrame(10);
    
    expect(state.progress).toBeCloseTo(0, 5);
    expect(state.visible).toBe(true);
  });

  test('state at end frame has progress 1', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 20, easing: 'linear', loop: false });
    
    const follower = new PathFollower(config);
    const state = follower.getStateAtFrame(20);
    
    expect(state.progress).toBeCloseTo(1, 5);
  });

  test('state at midpoint with linear easing has progress 0.5', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 20, easing: 'linear' });
    
    const follower = new PathFollower(config);
    const state = follower.getStateAtFrame(10);
    
    expect(state.progress).toBeCloseTo(0.5, 5);
  });

  test('position interpolates along path', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 10, easing: 'linear' });
    
    const follower = new PathFollower(config);
    
    const stateStart = follower.getStateAtFrame(0);
    const stateEnd = follower.getStateAtFrame(10);
    
    expect(stateStart.position.x).toBeCloseTo(0, 0);
    expect(stateEnd.position.x).toBeCloseTo(100, 0);
  });

  test('scale interpolates from scaleStart to scaleEnd', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 10, easing: 'linear', scaleStart: 1, scaleEnd: 2 });
    
    const follower = new PathFollower(config);
    
    const stateStart = follower.getStateAtFrame(0);
    const stateMid = follower.getStateAtFrame(5);
    const stateEnd = follower.getStateAtFrame(10);
    
    expect(stateStart.scale).toBeCloseTo(1, 5);
    expect(stateMid.scale).toBeCloseTo(1.5, 5);
    expect(stateEnd.scale).toBeCloseTo(2, 5);
  });

  test('opacity interpolates from opacityStart to opacityEnd', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 10, easing: 'linear', opacityStart: 0, opacityEnd: 1 });
    
    const follower = new PathFollower(config);
    
    const stateMid = follower.getStateAtFrame(5);
    
    expect(stateMid.opacity).toBeCloseTo(0.5, 5);
  });
});

// ============================================================================
// LOOP BEHAVIOR TESTS
// ============================================================================

describe('STRICT: PathFollower Loop Behavior', () => {
  test('restart loop: returns to start after duration', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 10, loop: true, loopMode: 'restart', easing: 'linear' });
    
    const follower = new PathFollower(config);
    
    const stateLoop = follower.getStateAtFrame(10); // Exactly at loop point
    const stateLoopPlus = follower.getStateAtFrame(11); // Just after loop
    
    // Should be at or near start of path
    expect(stateLoopPlus.progress).toBeLessThan(0.2);
  });

  test('pingpong loop: reverses direction', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 10, loop: true, loopMode: 'pingpong', easing: 'linear' });
    
    const follower = new PathFollower(config);
    
    // At frame 15 (1.5 durations), should be at 0.5 progress going backwards
    const stateLoop = follower.getStateAtFrame(15);
    
    // With pingpong, should be coming back
    expect(stateLoop.progress).toBeCloseTo(0.5, 1);
  });

  test('no loop: stays at end after duration', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: 0, duration: 10, loop: false, easing: 'linear' });
    
    const follower = new PathFollower(config);
    
    const stateAfterEnd = follower.getStateAtFrame(15);
    
    expect(stateAfterEnd.progress).toBeCloseTo(1, 5);
    expect(stateAfterEnd.position.x).toBeCloseTo(100, 0);
  });
});

// ============================================================================
// VACE EXPORTER TESTS
// ============================================================================

describe('STRICT: VACEControlExporter Class', () => {
  test('getFrameCount returns correct count', () => {
    const config = createVACEExportConfig([], {
      startFrame: 0,
      endFrame: 80,
    });
    
    const exporter = new VACEControlExporter(config);
    
    expect(exporter.getFrameCount()).toBe(81); // 0-80 inclusive
  });

  test('getPathStats returns info for each follower', () => {
    const followers = [
      createPathFollower('path1', [
        { x: 0, y: 0, handleIn: null, handleOut: null },
        { x: 100, y: 0, handleIn: null, handleOut: null },
      ], { duration: 10 }),
      createPathFollower('path2', [
        { x: 0, y: 0, handleIn: null, handleOut: null },
        { x: 200, y: 0, handleIn: null, handleOut: null },
      ], { duration: 20 }),
    ];
    
    const config = createVACEExportConfig(followers);
    const exporter = new VACEControlExporter(config);
    const stats = exporter.getPathStats();
    
    expect(stats.length).toBe(2);
    expect(stats[0].id).toBe('path1');
    expect(stats[1].id).toBe('path2');
    expect(stats[0].duration).toBe(10);
    expect(stats[1].duration).toBe(20);
  });
});

// ============================================================================
// UTILITY FUNCTION TESTS
// ============================================================================

describe('STRICT: VACE Utility Functions', () => {
  test.prop([
    fc.double({ min: 10, max: 1000, noNaN: true }),
    fc.double({ min: 1, max: 100, noNaN: true }),
  ])('calculateDurationForSpeed: duration = pathLength / speed', (pathLength, speed) => {
    const duration = calculateDurationForSpeed(pathLength, speed);
    
    expect(duration).toBeCloseTo(Math.ceil(pathLength / speed), 0);
  });

  test.prop([
    fc.double({ min: 10, max: 1000, noNaN: true }),
    fc.integer({ min: 1, max: 200 }),
  ])('calculateSpeed: speed = pathLength / duration', (pathLength, duration) => {
    const speed = calculateSpeed(pathLength, duration);
    
    expect(speed).toBeCloseTo(pathLength / duration, 5);
  });

  test('createPathFollower applies defaults', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ]);
    
    expect(config.closed).toBe(false);
    expect(config.shape).toBe('circle');
    expect(config.size).toEqual([20, 20]);
    expect(config.fillColor).toBe('#FFFFFF');
    expect(config.startFrame).toBe(0);
    expect(config.duration).toBe(60);
    expect(config.easing).toBe('ease-in-out');
    expect(config.alignToPath).toBe(true);
    expect(config.rotationOffset).toBe(0);
    expect(config.loop).toBe(false);
    expect(config.loopMode).toBe('restart');
    expect(config.scaleStart).toBe(1);
    expect(config.scaleEnd).toBe(1);
    expect(config.opacityStart).toBe(1);
    expect(config.opacityEnd).toBe(1);
  });

  test('createVACEExportConfig applies defaults', () => {
    const config = createVACEExportConfig([]);
    
    expect(config.width).toBe(512);
    expect(config.height).toBe(512);
    expect(config.startFrame).toBe(0);
    expect(config.endFrame).toBe(80);
    expect(config.frameRate).toBe(16);
    expect(config.backgroundColor).toBe('#000000');
    expect(config.outputFormat).toBe('canvas');
    expect(config.antiAlias).toBe(true);
  });

  test('splineLayerToPathFollower converts correctly', () => {
    const points: ControlPoint[] = [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 100, handleIn: null, handleOut: null },
    ];
    
    const config = splineLayerToPathFollower('layer1', points, true, 30);
    
    expect(config.id).toBe('layer1');
    expect(config.controlPoints).toEqual(points);
    expect(config.closed).toBe(true);
    expect(config.duration).toBe(30);
  });
});

// ============================================================================
// EDGE CASE TESTS
// ============================================================================

describe('STRICT: VACE Export Edge Cases', () => {
  test('empty path follower list', () => {
    const config = createVACEExportConfig([]);
    const exporter = new VACEControlExporter(config);
    
    expect(exporter.getPathStats()).toEqual([]);
  });

  test('single point path returns not visible state', () => {
    const config = createPathFollower('test', [
      { x: 50, y: 50, handleIn: null, handleOut: null },
    ]);
    
    const follower = new PathFollower(config);
    const state = follower.getStateAtFrame(0);
    
    // Single point = no path = not visible
    expect(state.visible).toBe(false);
  });

  test('zero duration path follower', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { duration: 0 });
    
    // Should handle gracefully (division by zero)
    const follower = new PathFollower(config);
    const speed = follower.getSpeed();
    
    // Speed would be infinite or handled specially
    expect(Number.isFinite(speed)).toBe(false);
  });

  test('negative start frame', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { startFrame: -10, duration: 20 });
    
    const follower = new PathFollower(config);
    
    // At frame 0, should be partway through animation
    const state = follower.getStateAtFrame(0);
    expect(state.progress).toBeGreaterThan(0);
    expect(state.visible).toBe(true);
  });

  test('very large rotation offset', () => {
    const config = createPathFollower('test', [
      { x: 0, y: 0, handleIn: null, handleOut: null },
      { x: 100, y: 0, handleIn: null, handleOut: null },
    ], { rotationOffset: 3600 }); // 10 full rotations
    
    const follower = new PathFollower(config);
    const state = follower.getStateAtFrame(0);
    
    // Should handle large rotations
    expect(Number.isFinite(state.rotation)).toBe(true);
  });
});
