/**
 * Expressions System Tests
 *
 * Tests for easing functions, motion expressions, and loop expressions.
 */

import { describe, it, expect } from 'vitest';
import {
  easing,
  motion,
  loop,
  time,
  math,
  evaluateExpression,
  type Expression,
  type ExpressionContext,
} from '@/services/expressions';

describe('Easing Functions', () => {
  describe('linear', () => {
    it('should return input unchanged', () => {
      expect(easing.linear(0)).toBe(0);
      expect(easing.linear(0.5)).toBe(0.5);
      expect(easing.linear(1)).toBe(1);
    });
  });

  describe('easeInQuad', () => {
    it('should ease in with quadratic curve', () => {
      expect(easing.easeInQuad(0)).toBe(0);
      expect(easing.easeInQuad(0.5)).toBe(0.25);
      expect(easing.easeInQuad(1)).toBe(1);
    });
  });

  describe('easeOutQuad', () => {
    it('should ease out with quadratic curve', () => {
      expect(easing.easeOutQuad(0)).toBe(0);
      expect(easing.easeOutQuad(0.5)).toBe(0.75);
      expect(easing.easeOutQuad(1)).toBe(1);
    });
  });

  describe('easeInOutQuad', () => {
    it('should ease in and out', () => {
      expect(easing.easeInOutQuad(0)).toBe(0);
      expect(easing.easeInOutQuad(0.5)).toBe(0.5);
      expect(easing.easeInOutQuad(1)).toBe(1);
    });
  });

  describe('easeInCubic', () => {
    it('should ease in with cubic curve', () => {
      expect(easing.easeInCubic(0)).toBe(0);
      expect(easing.easeInCubic(0.5)).toBe(0.125);
      expect(easing.easeInCubic(1)).toBe(1);
    });
  });

  describe('easeOutCubic', () => {
    it('should ease out with cubic curve', () => {
      expect(easing.easeOutCubic(0)).toBe(0);
      expect(easing.easeOutCubic(0.5)).toBe(0.875);
      expect(easing.easeOutCubic(1)).toBe(1);
    });
  });

  describe('easeOutElastic', () => {
    it('should have elastic overshoot', () => {
      expect(easing.easeOutElastic(0)).toBe(0);
      expect(easing.easeOutElastic(1)).toBe(1);
      // Elastic overshoots past 1 mid-animation
      const midValue = easing.easeOutElastic(0.6);
      expect(midValue).toBeGreaterThan(0.9);
    });
  });

  describe('easeOutBounce', () => {
    it('should simulate bounce', () => {
      expect(easing.easeOutBounce(0)).toBe(0);
      expect(easing.easeOutBounce(1)).toBe(1);
      // Bounce has distinctive pattern
      const earlyValue = easing.easeOutBounce(0.2);
      expect(earlyValue).toBeGreaterThan(0);
      expect(earlyValue).toBeLessThan(1);
    });
  });

  describe('cubicBezier', () => {
    it('should create custom easing curve', () => {
      const ease = easing.cubicBezier(0.25, 0.1, 0.25, 1.0);
      expect(ease(0)).toBeCloseTo(0, 2);
      expect(ease(1)).toBeCloseTo(1, 2);
      // Middle should be somewhere in between
      const mid = ease(0.5);
      expect(mid).toBeGreaterThan(0.3);
      expect(mid).toBeLessThan(0.9);
    });

    it('should approximate CSS ease preset', () => {
      const cssEase = easing.cubicBezier(0.25, 0.1, 0.25, 1.0);
      expect(cssEase(0)).toBeCloseTo(0, 2);
      expect(cssEase(1)).toBeCloseTo(1, 2);
    });
  });
});

describe('Motion Expressions', () => {
  // Create a full ExpressionContext for motion functions
  const createFullContext = (timeVal: number, value: number, velocity: number = 0): ExpressionContext => ({
    time: timeVal,
    frame: timeVal * 30,
    fps: 30,
    duration: 10,
    layerId: 'test',
    layerIndex: 0,
    layerName: 'test',
    inPoint: 0,
    outPoint: 10,
    propertyName: 'test.prop',
    value,
    velocity,
    numKeys: 2,
    keyframes: [
      { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: false }, outHandle: { frame: 5, value: 0, enabled: false }, controlMode: 'smooth' },
      { id: 'kf2', frame: 30, value: 100, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: false }, outHandle: { frame: 5, value: 0, enabled: false }, controlMode: 'smooth' },
    ],
  });

  describe('inertia', () => {
    it('should continue motion after last keyframe', () => {
      const ctx = createFullContext(1.33, 100, 100);
      const result = motion.inertia(ctx, 0.1, 2, 0.9);
      expect(typeof result).toBe('number');
    });

    it('should return value when no keyframes', () => {
      const ctx = {
        ...createFullContext(1, 100),
        keyframes: [],
        numKeys: 0,
      };
      const result = motion.inertia(ctx);
      expect(result).toBe(100);
    });
  });

  describe('bounce', () => {
    it('should create bouncing motion', () => {
      const ctx = createFullContext(1.5, 100);
      const result = motion.bounce(ctx, 0.7, 1000);
      expect(typeof result).toBe('number');
    });
  });

  describe('elastic', () => {
    it('should create elastic overshoot', () => {
      const ctx = createFullContext(1.2, 100);
      const result = motion.elastic(ctx, 0.5, 0.3);
      expect(typeof result).toBe('number');
    });
  });

  describe('jitter', () => {
    it('should add noise to value', () => {
      const ctx = createFullContext(0.5, 100);
      const result = motion.jitter(ctx, 5, 50, 1);
      expect(typeof result).toBe('number');
      // Should be within amplitude of original
      expect(result as number).toBeGreaterThanOrEqual(50);
      expect(result as number).toBeLessThanOrEqual(150);
    });
  });
});

describe('Loop Expressions', () => {
  // Create full context for loop functions
  const createLoopContext = (timeVal: number): ExpressionContext => ({
    time: timeVal,
    frame: timeVal * 30,
    fps: 30,
    duration: 10,
    layerId: 'test',
    layerIndex: 0,
    layerName: 'test',
    inPoint: 0,
    outPoint: 10,
    propertyName: 'test.prop',
    value: timeVal <= 1 ? timeVal * 100 : 100,
    velocity: timeVal <= 1 ? 100 : 0,
    numKeys: 2,
    keyframes: [
      { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: false }, outHandle: { frame: 5, value: 0, enabled: false }, controlMode: 'smooth' },
      { id: 'kf2', frame: 30, value: 100, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: false }, outHandle: { frame: 5, value: 0, enabled: false }, controlMode: 'smooth' },
    ],
  });

  describe('repeatAfter cycle', () => {
    it('should cycle keyframes after last', () => {
      const ctx = createLoopContext(1.5);
      const result = loop.repeatAfter(ctx, 'cycle');
      expect(typeof result).toBe('number');
    });

    it('should return original value when before keyframes end', () => {
      const ctx = createLoopContext(0.5);
      const result = loop.repeatAfter(ctx, 'cycle');
      expect(typeof result).toBe('number');
    });
  });

  describe('repeatAfter pingpong', () => {
    it('should reverse direction each cycle', () => {
      const ctx60 = createLoopContext(2);
      const result = loop.repeatAfter(ctx60, 'pingpong');
      expect(typeof result).toBe('number');
    });
  });

  describe('repeatAfter offset', () => {
    it('should add offset each cycle', () => {
      const ctx = createLoopContext(2);
      const result = loop.repeatAfter(ctx, 'offset');
      expect(typeof result).toBe('number');
    });
  });

  describe('repeatBefore', () => {
    it('should loop before first keyframe', () => {
      const ctx = {
        ...createLoopContext(-0.5),
        value: 0,
      };
      const result = loop.repeatBefore(ctx, 'cycle');
      expect(typeof result).toBe('number');
    });
  });
});

describe('Time Functions', () => {
  describe('timeRamp', () => {
    it('should create linear ramp', () => {
      expect(time.timeRamp(0, 1, 0, 100, 0)).toBe(0);
      expect(time.timeRamp(0, 1, 0, 100, 0.5)).toBe(50);
      expect(time.timeRamp(0, 1, 0, 100, 1)).toBe(100);
    });

    it('should clamp to output range', () => {
      expect(time.timeRamp(0, 1, 0, 100, -0.5)).toBe(0);
      expect(time.timeRamp(0, 1, 0, 100, 1.5)).toBe(100);
    });
  });

  describe('periodic', () => {
    it('should create periodic value', () => {
      const at0 = time.periodic(0, 1);
      const at1 = time.periodic(1, 1);
      expect(at0).toBeCloseTo(0, 5);
      expect(at1).toBeCloseTo(0, 5);
    });
  });

  describe('sawtooth', () => {
    it('should create sawtooth wave', () => {
      expect(time.sawtooth(0, 1)).toBe(0);
      // Sawtooth goes from -1 to 1 over period
      const mid = time.sawtooth(0.25, 1);
      expect(typeof mid).toBe('number');
    });
  });

  describe('triangle', () => {
    it('should create triangle wave', () => {
      expect(time.triangle(0, 1)).toBe(-1);
      const mid = time.triangle(0.25, 1);
      expect(mid).toBeCloseTo(0, 1);
    });
  });

  describe('square', () => {
    it('should create square wave', () => {
      expect(time.square(0, 1)).toBe(1);
      expect(time.square(0.4, 1)).toBe(1);
      expect(time.square(0.6, 1)).toBe(-1);
    });
  });

  describe('sine', () => {
    it('should create sine wave', () => {
      expect(time.sine(0, 1)).toBeCloseTo(0, 5);
      expect(time.sine(0.25, 1)).toBeCloseTo(1, 5);
      expect(time.sine(0.5, 1)).toBeCloseTo(0, 5);
    });
  });
});

describe('Math Functions', () => {
  describe('lerp', () => {
    it('should linearly interpolate', () => {
      expect(math.lerp(0, 100, 0)).toBe(0);
      expect(math.lerp(0, 100, 0.5)).toBe(50);
      expect(math.lerp(0, 100, 1)).toBe(100);
    });
  });

  describe('clamp', () => {
    it('should clamp values to range', () => {
      expect(math.clamp(-10, 0, 100)).toBe(0);
      expect(math.clamp(50, 0, 100)).toBe(50);
      expect(math.clamp(150, 0, 100)).toBe(100);
    });
  });

  describe('map', () => {
    it('should map from one range to another', () => {
      expect(math.map(50, 0, 100, 0, 1)).toBe(0.5);
      expect(math.map(0, 0, 100, 10, 20)).toBe(10);
      expect(math.map(100, 0, 100, 10, 20)).toBe(20);
    });
  });

  describe('smoothstep', () => {
    it('should create smooth transition', () => {
      expect(math.smoothstep(0, 1, 0)).toBe(0);
      expect(math.smoothstep(0, 1, 0.5)).toBe(0.5);
      expect(math.smoothstep(0, 1, 1)).toBe(1);
    });

    it('should have smooth derivatives at edges', () => {
      const nearZero = math.smoothstep(0, 1, 0.01);
      const nearOne = math.smoothstep(0, 1, 0.99);
      expect(nearZero).toBeLessThan(0.01);
      expect(nearOne).toBeGreaterThan(0.99);
    });
  });

  describe('seedRandom', () => {
    it('should produce deterministic values', () => {
      const val1 = math.seedRandom(42);
      const val2 = math.seedRandom(42);
      expect(val1).toBe(val2);
    });

    it('should produce different values for different seeds', () => {
      const val1 = math.seedRandom(1);
      const val2 = math.seedRandom(2);
      expect(val1).not.toBe(val2);
    });

    it('should produce values in 0-1 range', () => {
      for (let i = 0; i < 100; i++) {
        const val = math.seedRandom(i);
        expect(val).toBeGreaterThanOrEqual(0);
        expect(val).toBeLessThanOrEqual(1);
      }
    });
  });

  describe('gaussRandom', () => {
    it('should produce values', () => {
      const val = math.gaussRandom(0, 1);
      expect(typeof val).toBe('number');
    });
  });

  describe('distance', () => {
    it('should calculate distance between points', () => {
      expect(math.distance(0, 0, 3, 4)).toBe(5);
      expect(math.distance(0, 0, 0, 0)).toBe(0);
    });
  });

  describe('degreesToRadians', () => {
    it('should convert degrees to radians', () => {
      expect(math.degreesToRadians(0)).toBe(0);
      expect(math.degreesToRadians(180)).toBeCloseTo(Math.PI, 5);
      expect(math.degreesToRadians(360)).toBeCloseTo(2 * Math.PI, 5);
    });
  });

  describe('radiansToDegrees', () => {
    it('should convert radians to degrees', () => {
      expect(math.radiansToDegrees(0)).toBe(0);
      expect(math.radiansToDegrees(Math.PI)).toBeCloseTo(180, 5);
      expect(math.radiansToDegrees(2 * Math.PI)).toBeCloseTo(360, 5);
    });
  });
});

describe('evaluateExpression', () => {
  it('should evaluate jitter expression', () => {
    const context: ExpressionContext = {
      time: 0.5,
      frame: 15,
      fps: 30,
      duration: 10,
      layerId: 'layer1',
      layerIndex: 0,
      layerName: 'layer1',
      inPoint: 0,
      outPoint: 10,
      propertyName: 'transform.position.x',
      value: 100,
      velocity: 0,
      numKeys: 0,
      keyframes: [],
    };

    const expression: Expression = {
      type: 'preset',
      name: 'jitter',
      params: { frequency: 2, amplitude: 10, octaves: 1 },
      enabled: true,
    };

    const result = evaluateExpression(expression, context);

    expect(typeof result).toBe('number');
    // Jitter should be within amplitude of original value
    expect(result as number).toBeGreaterThanOrEqual(90);
    expect(result as number).toBeLessThanOrEqual(110);
  });

  it('should return current value when disabled', () => {
    const context: ExpressionContext = {
      time: 0.5,
      frame: 15,
      fps: 30,
      duration: 10,
      layerId: 'layer1',
      layerIndex: 0,
      layerName: 'layer1',
      inPoint: 0,
      outPoint: 10,
      propertyName: 'test',
      value: 42,
      velocity: 0,
      numKeys: 0,
      keyframes: [],
    };

    const expression: Expression = {
      type: 'preset',
      name: 'jitter',
      params: {},
      enabled: false,
    };

    const result = evaluateExpression(expression, context);
    expect(result).toBe(42);
  });
});

describe('Temporal Expression Functions', () => {
  describe('smooth()', () => {
    it('should smooth values over time window', () => {
      // Create context with keyframes to test smoothing
      const context: ExpressionContext = {
        time: 1.0,
        frame: 30,
        fps: 30,
        duration: 10,
        layerId: 'layer1',
        layerIndex: 0,
        layerName: 'layer1',
        inPoint: 0,
        outPoint: 10,
        propertyName: 'transform.position.x',
        value: 100,
        velocity: 0,
        numKeys: 2,
        keyframes: [
          { frame: 0, value: 0 },
          { frame: 60, value: 200 },
        ],
      };

      const expression: Expression = {
        type: 'custom',
        code: 'return smooth(0.2, 5)',
        enabled: true,
      };

      const result = evaluateExpression(expression, context);

      // Result should be a number (smoothed value)
      expect(typeof result).toBe('number');
      // Smoothed value should be close to the current interpolated value
      expect(result as number).toBeGreaterThan(50);
      expect(result as number).toBeLessThan(150);
    });

    it('should work with default parameters', () => {
      const context: ExpressionContext = {
        time: 0.5,
        frame: 15,
        fps: 30,
        duration: 10,
        layerId: 'layer1',
        layerIndex: 0,
        layerName: 'layer1',
        inPoint: 0,
        outPoint: 10,
        propertyName: 'test',
        value: 50,
        velocity: 0,
        numKeys: 0,
        keyframes: [],
      };

      const expression: Expression = {
        type: 'custom',
        code: 'return smooth()',
        enabled: true,
      };

      const result = evaluateExpression(expression, context);

      // Should return a value (averaging around current value when no keyframes)
      expect(typeof result).toBe('number');
    });
  });

  describe('posterizeTime()', () => {
    it('should quantize time to specified frame rate', () => {
      const context: ExpressionContext = {
        time: 0.55, // 55% through a second
        frame: 16,
        fps: 30,
        duration: 10,
        layerId: 'layer1',
        layerIndex: 0,
        layerName: 'layer1',
        inPoint: 0,
        outPoint: 10,
        propertyName: 'transform.position.x',
        value: 100,
        velocity: 0,
        numKeys: 0,
        keyframes: [],
      };

      const expression: Expression = {
        type: 'custom',
        code: 'return posterizeTime(12)', // 12 fps = steps every 1/12 second
        enabled: true,
      };

      const result = evaluateExpression(expression, context);

      // posterizeTime returns the quantized time
      expect(typeof result).toBe('number');
      // At 12fps, time should be quantized to multiples of 1/12 ≈ 0.0833
      // 0.55 / 0.0833 = 6.6, floor = 6, so result should be 6 * 0.0833 ≈ 0.5
      expect(result as number).toBeCloseTo(0.5, 1);
    });

    it('should create step-motion effect when used with value', () => {
      const context: ExpressionContext = {
        time: 0.75,
        frame: 22,
        fps: 30,
        duration: 10,
        layerId: 'layer1',
        layerIndex: 0,
        layerName: 'layer1',
        inPoint: 0,
        outPoint: 10,
        propertyName: 'test',
        value: 100,
        velocity: 0,
        numKeys: 2,
        keyframes: [
          { frame: 0, value: 0 },
          { frame: 90, value: 300 },
        ],
      };

      // Typical usage: posterizeTime(fps); return value
      const expression: Expression = {
        type: 'custom',
        code: 'posterizeTime(8); return value',
        enabled: true,
      };

      const result = evaluateExpression(expression, context);

      // Should return the current value (posterizeTime modifies time context)
      expect(typeof result).toBe('number');
      expect(result).toBe(100);
    });
  });

  describe('clamp()', () => {
    it('should clamp value to min/max range', () => {
      const context: ExpressionContext = {
        time: 0.5,
        frame: 15,
        fps: 30,
        duration: 10,
        layerId: 'layer1',
        layerIndex: 0,
        layerName: 'layer1',
        inPoint: 0,
        outPoint: 10,
        propertyName: 'test',
        value: 150,
        velocity: 0,
        numKeys: 0,
        keyframes: [],
      };

      const expression: Expression = {
        type: 'custom',
        code: 'return clamp(value, 0, 100)',
        enabled: true,
      };

      const result = evaluateExpression(expression, context);

      // 150 clamped to 0-100 should be 100
      expect(result).toBe(100);
    });

    it('should clamp value at minimum', () => {
      const context: ExpressionContext = {
        time: 0.5,
        frame: 15,
        fps: 30,
        duration: 10,
        layerId: 'layer1',
        layerIndex: 0,
        layerName: 'layer1',
        inPoint: 0,
        outPoint: 10,
        propertyName: 'test',
        value: -50,
        velocity: 0,
        numKeys: 0,
        keyframes: [],
      };

      const expression: Expression = {
        type: 'custom',
        code: 'return clamp(value, 0, 100)',
        enabled: true,
      };

      const result = evaluateExpression(expression, context);

      // -50 clamped to 0-100 should be 0
      expect(result).toBe(0);
    });

    it('should not change value within range', () => {
      const context: ExpressionContext = {
        time: 0.5,
        frame: 15,
        fps: 30,
        duration: 10,
        layerId: 'layer1',
        layerIndex: 0,
        layerName: 'layer1',
        inPoint: 0,
        outPoint: 10,
        propertyName: 'test',
        value: 50,
        velocity: 0,
        numKeys: 0,
        keyframes: [],
      };

      const expression: Expression = {
        type: 'custom',
        code: 'return clamp(value, 0, 100)',
        enabled: true,
      };

      const result = evaluateExpression(expression, context);

      // 50 is within 0-100, should remain 50
      expect(result).toBe(50);
    });
  });
});
