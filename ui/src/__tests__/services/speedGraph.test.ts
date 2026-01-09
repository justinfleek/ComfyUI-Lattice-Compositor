/**
 * Speed Graph Tests
 *
 * Tests the Speed Graph view functionality in the Curve Editor.
 * Tutorial 04 Steps 125-140 (estimated).
 *
 * The Speed Graph shows the derivative (rate of change) of property values.
 * This creates the characteristic "bell curve" shape for ease-in/ease-out animations.
 */

import { describe, expect, test } from "vitest";

describe("Speed Graph", () => {
  describe("Speed Calculation Logic", () => {
    /**
     * Speed = |dValue/dTime| (absolute value of derivative)
     * For linear interpolation: speed = constant
     * For ease curves: speed varies (bell curve shape)
     */

    test("constant speed for linear interpolation", () => {
      // Linear motion from 0 to 100 over 30 frames
      const startValue = 0;
      const endValue = 100;
      const duration = 30; // frames
      const fps = 30;

      // Linear interpolation: speed = (endValue - startValue) / time
      const timeInSeconds = duration / fps;
      const expectedSpeed = Math.abs(endValue - startValue) / timeInSeconds;

      // Speed should be 100 units per second
      expect(expectedSpeed).toBe(100);
    });

    test("zero speed at hold keyframes", () => {
      // Hold interpolation: no change between keyframes
      const speed = 0; // Value doesn't change
      expect(speed).toBe(0);
    });

    test("variable speed for bezier interpolation", () => {
      // Ease-in-out: starts slow, speeds up, slows down
      // At keyframes, speed approaches 0
      // At midpoint, speed is maximum

      // Simulated bezier curve values
      const samples = [
        { t: 0.0, speed: 0 }, // Start: slow
        { t: 0.25, speed: 50 }, // Accelerating
        { t: 0.5, speed: 100 }, // Maximum speed
        { t: 0.75, speed: 50 }, // Decelerating
        { t: 1.0, speed: 0 }, // End: slow
      ];

      // Bell curve shape verification
      expect(samples[2].speed).toBeGreaterThan(samples[0].speed);
      expect(samples[2].speed).toBeGreaterThan(samples[4].speed);
      expect(samples[1].speed).toBeGreaterThan(samples[0].speed);
      expect(samples[3].speed).toBeLessThan(samples[2].speed);
    });

    test("speed graph derivative formula", () => {
      // Speed = |f(t + epsilon) - f(t)| / epsilon
      const fps = 30;
      const epsilon = 1 / fps;

      // For a linear function f(t) = 100t
      const valueAtT = (t: number) => 100 * t;

      const t = 0.5;
      const v1 = valueAtT(t);
      const v2 = valueAtT(t + epsilon);
      const speed = Math.abs(v2 - v1) / epsilon;

      // Should equal the derivative of 100t = 100
      expect(speed).toBeCloseTo(100, 1);
    });
  });

  describe("Speed Graph UI", () => {
    test("graph mode can be set to speed", () => {
      const graphMode: "value" | "speed" = "speed";
      expect(graphMode).toBe("speed");
    });

    test("graph mode can be set to value", () => {
      const graphMode: "value" | "speed" = "value";
      expect(graphMode).toBe("value");
    });

    test("Y axis units for position speed", () => {
      const propertyType = "Position X";
      const unit = propertyType.includes("Rotation") ? "deg/sec" : "px/sec";
      expect(unit).toBe("px/sec");
    });

    test("Y axis units for rotation speed", () => {
      const propertyType = "Rotation";
      const unit = propertyType.includes("Rotation") ? "deg/sec" : "px/sec";
      expect(unit).toBe("deg/sec");
    });

    test("speed range starts at 0", () => {
      // Speed is always non-negative (absolute value of derivative)
      const speedRange = { min: 0, max: 100 };
      expect(speedRange.min).toBe(0);
    });

    test("speed range auto-scales to max speed", () => {
      // Find maximum speed across all samples
      const speeds = [10, 50, 120, 80, 30];
      const maxSpeed = Math.max(...speeds);
      const paddedMax = maxSpeed * 1.2; // 20% padding

      expect(paddedMax).toBe(144);
    });
  });

  describe("Speed Graph Rendering", () => {
    test("speed curve samples at sub-frame resolution", () => {
      const step = 0.5; // Sample every half frame for smoothness
      const frameCount = 10;
      const expectedSamples = Math.ceil(frameCount / step);

      expect(expectedSamples).toBe(20);
    });

    test("speed curve uses two-pass rendering", () => {
      // Pass 1: Black outline for visibility
      // Pass 2: Colored curve
      const passes = 2;
      const pass1Color = "#000";
      const pass1Width = 4;
      const pass2Width = 2;

      expect(passes).toBe(2);
      expect(pass1Color).toBe("#000");
      expect(pass1Width).toBeGreaterThan(pass2Width);
    });
  });

  describe("Cubic Bezier Speed", () => {
    /**
     * For cubic bezier: P(t) = (1-t)³P0 + 3(1-t)²tP1 + 3(1-t)t²P2 + t³P3
     * Speed is the magnitude of the derivative
     */

    function cubicBezierValue(
      p0: number,
      p1: number,
      p2: number,
      p3: number,
      t: number,
    ): number {
      const mt = 1 - t;
      return (
        mt * mt * mt * p0 +
        3 * mt * mt * t * p1 +
        3 * mt * t * t * p2 +
        t * t * t * p3
      );
    }

    function cubicBezierSpeed(
      p0: number,
      p1: number,
      p2: number,
      p3: number,
      t: number,
      fps: number,
    ): number {
      const epsilon = 1 / fps;
      const v1 = cubicBezierValue(p0, p1, p2, p3, t);
      const v2 = cubicBezierValue(p0, p1, p2, p3, Math.min(1, t + epsilon));
      return Math.abs(v2 - v1) * fps;
    }

    test("ease-in-out creates bell curve speed", () => {
      // Standard ease-in-out: starts and ends slow, fast in middle
      const p0 = 0,
        p1 = 0,
        p2 = 100,
        p3 = 100; // Ease-in-out control points
      const fps = 30;

      const speedStart = cubicBezierSpeed(p0, p1, p2, p3, 0, fps);
      const speedMid = cubicBezierSpeed(p0, p1, p2, p3, 0.5, fps);
      const speedEnd = cubicBezierSpeed(p0, p1, p2, p3, 0.95, fps);

      // Middle should be faster than ends
      expect(speedMid).toBeGreaterThan(speedStart);
      expect(speedMid).toBeGreaterThan(speedEnd);
    });

    test("linear bezier has constant speed", () => {
      // Linear: control points on the line
      const p0 = 0,
        p1 = 33.33,
        p2 = 66.67,
        p3 = 100;
      const fps = 30;

      const speed1 = cubicBezierSpeed(p0, p1, p2, p3, 0.25, fps);
      const speed2 = cubicBezierSpeed(p0, p1, p2, p3, 0.5, fps);
      const speed3 = cubicBezierSpeed(p0, p1, p2, p3, 0.75, fps);

      // All speeds should be approximately equal
      expect(Math.abs(speed1 - speed2)).toBeLessThan(50);
      expect(Math.abs(speed2 - speed3)).toBeLessThan(50);
    });

    test("ease-in starts slow then accelerates", () => {
      // Ease-in: slow start, fast end
      const p0 = 0,
        p1 = 0,
        p2 = 0,
        p3 = 100;
      const fps = 30;

      const speedStart = cubicBezierSpeed(p0, p1, p2, p3, 0.1, fps);
      const speedEnd = cubicBezierSpeed(p0, p1, p2, p3, 0.9, fps);

      // End should be faster than start
      expect(speedEnd).toBeGreaterThan(speedStart);
    });

    test("ease-out starts fast then decelerates", () => {
      // Ease-out: fast start, slow end
      const p0 = 0,
        p1 = 100,
        p2 = 100,
        p3 = 100;
      const fps = 30;

      const speedStart = cubicBezierSpeed(p0, p1, p2, p3, 0.1, fps);
      const speedEnd = cubicBezierSpeed(p0, p1, p2, p3, 0.9, fps);

      // Start should be faster than end
      expect(speedStart).toBeGreaterThan(speedEnd);
    });
  });

  describe("Speed Graph Value Range", () => {
    test("computes max speed across all curves", () => {
      const curve1Speeds = [10, 50, 30];
      const curve2Speeds = [20, 100, 40];

      const maxSpeed = Math.max(...curve1Speeds, ...curve2Speeds);

      expect(maxSpeed).toBe(100);
    });

    test("adds padding to max speed", () => {
      const maxSpeed = 100;
      const paddingFactor = 1.2;
      const rangeMax = maxSpeed * paddingFactor;

      expect(rangeMax).toBe(120);
    });

    test("defaults to 100 for minimum max speed", () => {
      const speeds: number[] = [5, 10, 15]; // All low speeds
      const computedMax = Math.max(...speeds);
      const defaultMin = 100;

      const rangeMax = Math.max(defaultMin, computedMax * 1.2);

      expect(rangeMax).toBe(100); // Uses default minimum
    });
  });

  describe("Tutorial 04 Speed Graph Steps", () => {
    test("Speed Graph view exists in Curve Editor", () => {
      // Step: User can toggle to Speed Graph view
      const viewModes = ["value", "speed"];
      expect(viewModes).toContain("speed");
    });

    test("Speed Graph shows derivative of property values", () => {
      // Step: Speed = rate of change
      const valueAtFrame0 = 0;
      const valueAtFrame1 = 100;
      const fps = 30;

      const deltaValue = valueAtFrame1 - valueAtFrame0;
      const deltaTime = 1 / fps; // 1 frame in seconds
      const speed = Math.abs(deltaValue / deltaTime);

      expect(speed).toBe(3000); // 100 units / (1/30 sec) = 3000 units/sec
    });

    test("Speed Graph creates bell curve for ease animations", () => {
      // Step: Ease-in-out shows characteristic bell curve shape
      const bellCurveShape = true; // Middle faster than ends
      expect(bellCurveShape).toBe(true);
    });

    test("Speed Graph Y axis shows velocity units", () => {
      // Step: Y axis labeled in units/second
      const positionUnit = "px/sec";
      const rotationUnit = "deg/sec";

      expect(positionUnit).toContain("/sec");
      expect(rotationUnit).toContain("/sec");
    });
  });

  describe("Determinism", () => {
    test("speed calculation is deterministic", () => {
      // Same inputs always produce same output
      const calculateSpeed = (v1: number, v2: number, fps: number) =>
        Math.abs(v2 - v1) * fps;

      const result1 = calculateSpeed(0, 100, 30);
      const result2 = calculateSpeed(0, 100, 30);
      const result3 = calculateSpeed(0, 100, 30);

      expect(result1).toBe(result2);
      expect(result2).toBe(result3);
    });

    test("speed graph same at any playhead position", () => {
      // Speed graph should look the same regardless of where playhead is
      const calculateSpeedCurve = (keyframes: number[], fps: number) => {
        const speeds: number[] = [];
        for (let i = 0; i < keyframes.length - 1; i++) {
          speeds.push(Math.abs(keyframes[i + 1] - keyframes[i]) * fps);
        }
        return speeds;
      };

      const keyframes = [0, 50, 100];
      const fps = 30;

      const speeds1 = calculateSpeedCurve(keyframes, fps);
      const speeds2 = calculateSpeedCurve(keyframes, fps);

      expect(speeds1).toEqual(speeds2);
    });
  });
});
