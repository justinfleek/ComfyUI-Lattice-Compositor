/**
 * Animated Spline Tests
 *
 * Tests for the animated spline system including:
 * - Control point interpolation
 * - Scrub determinism
 * - Static to animated conversion
 * - Integration with MotionEngine
 */

import { describe, it, expect, beforeEach } from 'vitest';
import type {
  ControlPoint,
  AnimatableControlPoint,
  AnimatableProperty,
  Keyframe,
} from '@/types/project';
import {
  controlPointToAnimatable,
  animatableToControlPoint,
  createAnimatableProperty,
} from '@/types/project';
import { interpolateProperty } from '@/services/interpolation';

// ============================================================================
// TEST UTILITIES
// ============================================================================

function createKeyframe<T>(id: number, frame: number, value: T): Keyframe<T> {
  return {
    id: `kf-${id}`,
    frame,
    value,
    interpolation: 'linear',
    inHandle: { frame: 0, value: 0, enabled: false },
    outHandle: { frame: 0, value: 0, enabled: false },
    controlMode: 'smooth',
  };
}

function createStaticControlPoint(
  id: string,
  x: number,
  y: number,
  depth: number = 0
): ControlPoint {
  return {
    id,
    x,
    y,
    depth,
    handleIn: { x: -20, y: 0 },
    handleOut: { x: 20, y: 0 },
    type: 'smooth',
  };
}

function createAnimatedControlPoint(
  id: string,
  xKeyframes: Array<{ frame: number; value: number }>,
  yKeyframes: Array<{ frame: number; value: number }>
): AnimatableControlPoint {
  const xProp = createAnimatableProperty('x', xKeyframes[0].value, 'number');
  xProp.animated = true;
  xProp.keyframes = xKeyframes.map((kf, i) => createKeyframe(i, kf.frame, kf.value));

  const yProp = createAnimatableProperty('y', yKeyframes[0].value, 'number');
  yProp.animated = true;
  yProp.keyframes = yKeyframes.map((kf, i) => createKeyframe(i, kf.frame, kf.value));

  return {
    id,
    x: xProp,
    y: yProp,
    handleIn: null,
    handleOut: null,
    type: 'smooth',
  };
}

// ============================================================================
// CONVERSION TESTS
// ============================================================================

describe('Control Point Conversion', () => {
  describe('controlPointToAnimatable', () => {
    it('should convert static control point to animatable', () => {
      const static_ = createStaticControlPoint('cp1', 100, 200, 50);
      const animated = controlPointToAnimatable(static_);

      expect(animated.id).toBe('cp1');
      expect(animated.x.value).toBe(100);
      expect(animated.y.value).toBe(200);
      expect(animated.depth?.value).toBe(50);
      expect(animated.type).toBe('smooth');
    });

    it('should preserve handles when converting', () => {
      const static_ = createStaticControlPoint('cp1', 100, 200);
      const animated = controlPointToAnimatable(static_);

      expect(animated.handleIn?.x.value).toBe(-20);
      expect(animated.handleIn?.y.value).toBe(0);
      expect(animated.handleOut?.x.value).toBe(20);
      expect(animated.handleOut?.y.value).toBe(0);
    });

    it('should handle null handles', () => {
      const static_: ControlPoint = {
        id: 'cp1',
        x: 100,
        y: 200,
        handleIn: null,
        handleOut: null,
        type: 'corner',
      };
      const animated = controlPointToAnimatable(static_);

      expect(animated.handleIn).toBeNull();
      expect(animated.handleOut).toBeNull();
    });
  });

  describe('animatableToControlPoint', () => {
    it('should convert animatable back to static using current values', () => {
      const animated = createAnimatedControlPoint(
        'cp1',
        [{ frame: 0, value: 100 }, { frame: 80, value: 500 }],
        [{ frame: 0, value: 200 }, { frame: 80, value: 600 }]
      );

      const static_ = animatableToControlPoint(animated);

      expect(static_.id).toBe('cp1');
      expect(static_.x).toBe(100); // Uses default value
      expect(static_.y).toBe(200);
    });
  });
});

// ============================================================================
// INTERPOLATION TESTS
// ============================================================================

describe('Animated Control Point Interpolation', () => {
  it('should interpolate x coordinate linearly', () => {
    const animated = createAnimatedControlPoint(
      'cp1',
      [{ frame: 0, value: 0 }, { frame: 80, value: 800 }],
      [{ frame: 0, value: 0 }, { frame: 80, value: 400 }]
    );

    // Frame 0: x = 0
    expect(interpolateProperty(animated.x, 0)).toBe(0);

    // Frame 40 (midpoint): x = 400
    expect(interpolateProperty(animated.x, 40)).toBe(400);

    // Frame 80: x = 800
    expect(interpolateProperty(animated.x, 80)).toBe(800);
  });

  it('should interpolate y coordinate linearly', () => {
    const animated = createAnimatedControlPoint(
      'cp1',
      [{ frame: 0, value: 0 }, { frame: 80, value: 800 }],
      [{ frame: 0, value: 100 }, { frame: 80, value: 500 }]
    );

    // Frame 0: y = 100
    expect(interpolateProperty(animated.y, 0)).toBe(100);

    // Frame 40 (midpoint): y = 300
    expect(interpolateProperty(animated.y, 40)).toBe(300);

    // Frame 80: y = 500
    expect(interpolateProperty(animated.y, 80)).toBe(500);
  });

  it('should handle multiple keyframes', () => {
    const xProp = createAnimatableProperty('x', 0, 'number');
    xProp.animated = true;
    xProp.keyframes = [
      createKeyframe(0, 0, 0),
      createKeyframe(1, 20, 100),
      createKeyframe(2, 40, 200),
      createKeyframe(3, 60, 100),
      createKeyframe(4, 80, 0),
    ];

    expect(interpolateProperty(xProp, 0)).toBe(0);
    expect(interpolateProperty(xProp, 20)).toBe(100);
    expect(interpolateProperty(xProp, 40)).toBe(200);
    expect(interpolateProperty(xProp, 50)).toBe(150); // Midpoint 40-60
    expect(interpolateProperty(xProp, 60)).toBe(100);
    expect(interpolateProperty(xProp, 80)).toBe(0);
  });
});

// ============================================================================
// DETERMINISM TESTS
// ============================================================================

describe('Animated Spline Determinism', () => {
  let animatedPoints: AnimatableControlPoint[];

  beforeEach(() => {
    animatedPoints = [
      createAnimatedControlPoint(
        'cp0',
        [{ frame: 0, value: 0 }, { frame: 80, value: 400 }],
        [{ frame: 0, value: 0 }, { frame: 80, value: 200 }]
      ),
      createAnimatedControlPoint(
        'cp1',
        [{ frame: 0, value: 200 }, { frame: 80, value: 600 }],
        [{ frame: 0, value: 100 }, { frame: 80, value: 300 }]
      ),
      createAnimatedControlPoint(
        'cp2',
        [{ frame: 0, value: 400 }, { frame: 80, value: 800 }],
        [{ frame: 0, value: 0 }, { frame: 80, value: 200 }]
      ),
    ];
  });

  it('should produce identical results for same frame (direct evaluation)', () => {
    const frame = 40;

    // First evaluation
    const result1 = animatedPoints.map(cp => ({
      x: interpolateProperty(cp.x, frame),
      y: interpolateProperty(cp.y, frame),
    }));

    // Second evaluation (same frame)
    const result2 = animatedPoints.map(cp => ({
      x: interpolateProperty(cp.x, frame),
      y: interpolateProperty(cp.y, frame),
    }));

    expect(result1).toEqual(result2);
  });

  it('should produce identical results regardless of evaluation order', () => {
    const frame = 30;

    // Direct evaluation
    const directResult = animatedPoints.map(cp => ({
      x: interpolateProperty(cp.x, frame),
      y: interpolateProperty(cp.y, frame),
    }));

    // Evaluate other frames first
    for (let f = 0; f < 80; f++) {
      animatedPoints.forEach(cp => {
        interpolateProperty(cp.x, f);
        interpolateProperty(cp.y, f);
      });
    }

    // Re-evaluate frame 30
    const afterOthersResult = animatedPoints.map(cp => ({
      x: interpolateProperty(cp.x, frame),
      y: interpolateProperty(cp.y, frame),
    }));

    expect(afterOthersResult).toEqual(directResult);
  });

  it('should produce identical results with random access patterns', () => {
    const frames = [45, 10, 70, 25, 60, 5, 80, 35, 0, 50];
    const results = new Map<number, Array<{ x: number; y: number }>>();

    // First pass: random order
    for (const frame of frames) {
      results.set(
        frame,
        animatedPoints.map(cp => ({
          x: interpolateProperty(cp.x, frame),
          y: interpolateProperty(cp.y, frame),
        }))
      );
    }

    // Second pass: different random order
    const shuffled = [...frames].reverse();
    for (const frame of shuffled) {
      const newResult = animatedPoints.map(cp => ({
        x: interpolateProperty(cp.x, frame),
        y: interpolateProperty(cp.y, frame),
      }));

      expect(newResult).toEqual(results.get(frame));
    }
  });
});

// ============================================================================
// STATIC SPLINE BEHAVIOR
// ============================================================================

describe('Static Spline Behavior', () => {
  it('should return same values for non-animated property', () => {
    const staticProp = createAnimatableProperty('x', 100, 'number');
    staticProp.animated = false;

    expect(interpolateProperty(staticProp, 0)).toBe(100);
    expect(interpolateProperty(staticProp, 40)).toBe(100);
    expect(interpolateProperty(staticProp, 80)).toBe(100);
  });

  it('should return same values for empty keyframes', () => {
    const prop = createAnimatableProperty('x', 250, 'number');
    prop.animated = true;
    prop.keyframes = [];

    expect(interpolateProperty(prop, 0)).toBe(250);
    expect(interpolateProperty(prop, 40)).toBe(250);
    expect(interpolateProperty(prop, 80)).toBe(250);
  });
});

// ============================================================================
// EDGE CASES
// ============================================================================

describe('Edge Cases', () => {
  it('should handle frame before first keyframe', () => {
    const animated = createAnimatedControlPoint(
      'cp1',
      [{ frame: 20, value: 100 }, { frame: 80, value: 500 }],
      [{ frame: 20, value: 100 }, { frame: 80, value: 500 }]
    );

    // Frame 0 is before first keyframe (20), should return first keyframe value
    expect(interpolateProperty(animated.x, 0)).toBe(100);
    expect(interpolateProperty(animated.x, 10)).toBe(100);
    expect(interpolateProperty(animated.x, 20)).toBe(100);
  });

  it('should handle frame after last keyframe', () => {
    const animated = createAnimatedControlPoint(
      'cp1',
      [{ frame: 0, value: 100 }, { frame: 60, value: 500 }],
      [{ frame: 0, value: 100 }, { frame: 60, value: 500 }]
    );

    // Frame 80 is after last keyframe (60), should return last keyframe value
    expect(interpolateProperty(animated.x, 60)).toBe(500);
    expect(interpolateProperty(animated.x, 70)).toBe(500);
    expect(interpolateProperty(animated.x, 80)).toBe(500);
  });

  it('should handle single keyframe', () => {
    const xProp = createAnimatableProperty('x', 100, 'number');
    xProp.animated = true;
    xProp.keyframes = [createKeyframe(0, 40, 200)];

    // All frames should return the single keyframe value
    expect(interpolateProperty(xProp, 0)).toBe(200);
    expect(interpolateProperty(xProp, 40)).toBe(200);
    expect(interpolateProperty(xProp, 80)).toBe(200);
  });

  it('should handle negative depth values', () => {
    const static_ = createStaticControlPoint('cp1', 100, 200, -50);
    const animated = controlPointToAnimatable(static_);

    expect(animated.depth?.value).toBe(-50);
  });
});
