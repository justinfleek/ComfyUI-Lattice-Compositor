/**
 * Property tests for ui/src/services/export/vaceControlExport.ts
 * Tests pure functions: createPathFollower, createVACEExportConfig,
 *                       calculateDurationForSpeed, calculateSpeed,
 *                       splineLayerToPathFollower
 * 
 * Audit: 2026-01-06
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  createPathFollower,
  createVACEExportConfig,
  calculateDurationForSpeed,
  calculateSpeed,
  splineLayerToPathFollower,
  type SplineControlPoint,
  type PathFollowerConfig,
} from "@/services/export/vaceControlExport";

// ============================================================
// ARBITRARIES
// ============================================================

const controlPointArb: fc.Arbitrary<SplineControlPoint> = fc.record({
  x: fc.double({ min: -1000, max: 1000, noNaN: true }),
  y: fc.double({ min: -1000, max: 1000, noNaN: true }),
  handleIn: fc.option(
    fc.record({
      x: fc.double({ min: -100, max: 100, noNaN: true }),
      y: fc.double({ min: -100, max: 100, noNaN: true }),
    }),
    { nil: undefined }
  ),
  handleOut: fc.option(
    fc.record({
      x: fc.double({ min: -100, max: 100, noNaN: true }),
      y: fc.double({ min: -100, max: 100, noNaN: true }),
    }),
    { nil: undefined }
  ),
});

const controlPointsArb = fc.array(controlPointArb, { minLength: 2, maxLength: 20 });

// Generate valid hex colors
const hexDigitArb = fc.constantFrom('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F');
const hexColorArb = fc.tuple(hexDigitArb, hexDigitArb, hexDigitArb, hexDigitArb, hexDigitArb, hexDigitArb)
  .map(digits => `#${digits.join('')}`);

const shapeArb = fc.constantFrom("circle", "square", "triangle", "diamond", "arrow") as fc.Arbitrary<PathFollowerConfig["shape"]>;

const easingArb = fc.constantFrom("linear", "ease-in", "ease-out", "ease-in-out") as fc.Arbitrary<PathFollowerConfig["easing"]>;

const loopModeArb = fc.constantFrom("restart", "pingpong", "continue") as fc.Arbitrary<NonNullable<PathFollowerConfig["loopMode"]>>;

// ============================================================
// createPathFollower TESTS
// ============================================================

describe("PROPERTY: createPathFollower", () => {
  it("returns PathFollowerConfig with all required properties", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        controlPointsArb,
        (id, controlPoints) => {
          const config = createPathFollower(id, controlPoints);
          
          expect(config).toHaveProperty("id");
          expect(config).toHaveProperty("controlPoints");
          expect(config).toHaveProperty("closed");
          expect(config).toHaveProperty("shape");
          expect(config).toHaveProperty("size");
          expect(config).toHaveProperty("fillColor");
          expect(config).toHaveProperty("startFrame");
          expect(config).toHaveProperty("duration");
          expect(config).toHaveProperty("easing");
          expect(config).toHaveProperty("alignToPath");
          expect(config).toHaveProperty("rotationOffset");
          expect(config).toHaveProperty("loop");
          expect(config).toHaveProperty("scaleStart");
          expect(config).toHaveProperty("scaleEnd");
          expect(config).toHaveProperty("opacityStart");
          expect(config).toHaveProperty("opacityEnd");
        }
      )
    );
  });

  it("id matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        controlPointsArb,
        (id, controlPoints) => {
          const config = createPathFollower(id, controlPoints);
          expect(config.id).toBe(id);
        }
      )
    );
  });

  it("controlPoints matches input", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        controlPointsArb,
        (id, controlPoints) => {
          const config = createPathFollower(id, controlPoints);
          expect(config.controlPoints).toBe(controlPoints);
        }
      )
    );
  });

  it("has sensible defaults", () => {
    const config = createPathFollower("test", [{ x: 0, y: 0 }, { x: 100, y: 100 }]);
    
    expect(config.closed).toBe(false);
    expect(config.shape).toBe("circle");
    expect(config.size).toEqual([20, 20]);
    expect(config.fillColor).toBe("#FFFFFF");
    expect(config.startFrame).toBe(0);
    expect(config.duration).toBe(60);
    expect(config.easing).toBe("ease-in-out");
    expect(config.alignToPath).toBe(true);
    expect(config.rotationOffset).toBe(0);
    expect(config.loop).toBe(false);
    expect(config.scaleStart).toBe(1);
    expect(config.scaleEnd).toBe(1);
    expect(config.opacityStart).toBe(1);
    expect(config.opacityEnd).toBe(1);
  });

  it("respects custom options", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        controlPointsArb,
        fc.boolean(),
        shapeArb,
        hexColorArb,
        fc.integer({ min: 0, max: 100 }),
        fc.integer({ min: 1, max: 1000 }),
        easingArb,
        (id, controlPoints, closed, shape, fillColor, startFrame, duration, easing) => {
          const config = createPathFollower(id, controlPoints, {
            closed,
            shape,
            fillColor,
            startFrame,
            duration,
            easing,
          });
          
          expect(config.closed).toBe(closed);
          expect(config.shape).toBe(shape);
          expect(config.fillColor).toBe(fillColor);
          expect(config.startFrame).toBe(startFrame);
          expect(config.duration).toBe(duration);
          expect(config.easing).toBe(easing);
        }
      )
    );
  });

  it("scale and opacity can be customized", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 0, max: 5, noNaN: true }),
        fc.double({ min: 0, max: 5, noNaN: true }),
        fc.double({ min: 0, max: 1, noNaN: true }),
        fc.double({ min: 0, max: 1, noNaN: true }),
        (scaleStart, scaleEnd, opacityStart, opacityEnd) => {
          const config = createPathFollower("test", [{ x: 0, y: 0 }, { x: 100, y: 100 }], {
            scaleStart,
            scaleEnd,
            opacityStart,
            opacityEnd,
          });
          
          expect(config.scaleStart).toBe(scaleStart);
          expect(config.scaleEnd).toBe(scaleEnd);
          expect(config.opacityStart).toBe(opacityStart);
          expect(config.opacityEnd).toBe(opacityEnd);
        }
      )
    );
  });
});

// ============================================================
// createVACEExportConfig TESTS
// ============================================================

describe("PROPERTY: createVACEExportConfig", () => {
  it("returns VACEExportConfig with all required properties", () => {
    const config = createVACEExportConfig([]);
    
    expect(config).toHaveProperty("width");
    expect(config).toHaveProperty("height");
    expect(config).toHaveProperty("startFrame");
    expect(config).toHaveProperty("endFrame");
    expect(config).toHaveProperty("frameRate");
    expect(config).toHaveProperty("backgroundColor");
    expect(config).toHaveProperty("pathFollowers");
    expect(config).toHaveProperty("outputFormat");
    expect(config).toHaveProperty("antiAlias");
  });

  it("has sensible defaults", () => {
    const config = createVACEExportConfig([]);
    
    expect(config.width).toBe(512);
    expect(config.height).toBe(512);
    expect(config.startFrame).toBe(0);
    expect(config.endFrame).toBe(80);
    expect(config.frameRate).toBe(16);
    expect(config.backgroundColor).toBe("#000000");
    expect(config.outputFormat).toBe("canvas");
    expect(config.antiAlias).toBe(true);
  });

  it("pathFollowers matches input", () => {
    const followers = [
      createPathFollower("a", [{ x: 0, y: 0 }, { x: 100, y: 100 }]),
      createPathFollower("b", [{ x: 50, y: 50 }, { x: 150, y: 150 }]),
    ];
    const config = createVACEExportConfig(followers);
    
    expect(config.pathFollowers).toBe(followers);
    expect(config.pathFollowers.length).toBe(2);
  });

  it("respects custom dimensions", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 4096 }),
        fc.integer({ min: 1, max: 4096 }),
        (width, height) => {
          const config = createVACEExportConfig([], { width, height });
          expect(config.width).toBe(width);
          expect(config.height).toBe(height);
        }
      )
    );
  });

  it("respects custom frame range", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 0, max: 100 }),
        fc.integer({ min: 1, max: 500 }),
        (startFrame, endFrame) => {
          const config = createVACEExportConfig([], { startFrame, endFrame });
          expect(config.startFrame).toBe(startFrame);
          expect(config.endFrame).toBe(endFrame);
        }
      )
    );
  });
});

// ============================================================
// calculateDurationForSpeed TESTS
// ============================================================

describe("PROPERTY: calculateDurationForSpeed", () => {
  it("returns positive integer for positive inputs", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 1, max: 10000, noNaN: true }),
        fc.double({ min: 0.1, max: 100, noNaN: true }),
        (pathLength, pixelsPerFrame) => {
          const duration = calculateDurationForSpeed(pathLength, pixelsPerFrame);
          expect(duration).toBeGreaterThan(0);
          expect(Number.isInteger(duration)).toBe(true);
        }
      )
    );
  });

  it("higher speed means shorter duration", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 100, max: 10000, noNaN: true }),
        fc.double({ min: 1, max: 50, noNaN: true }),
        fc.double({ min: 51, max: 100, noNaN: true }),
        (pathLength, slowSpeed, fastSpeed) => {
          const slowDuration = calculateDurationForSpeed(pathLength, slowSpeed);
          const fastDuration = calculateDurationForSpeed(pathLength, fastSpeed);
          expect(fastDuration).toBeLessThanOrEqual(slowDuration);
        }
      )
    );
  });

  it("longer path means longer duration at same speed", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 100, max: 5000, noNaN: true }),
        fc.double({ min: 5001, max: 10000, noNaN: true }),
        fc.double({ min: 1, max: 100, noNaN: true }),
        (shortPath, longPath, speed) => {
          const shortDuration = calculateDurationForSpeed(shortPath, speed);
          const longDuration = calculateDurationForSpeed(longPath, speed);
          expect(longDuration).toBeGreaterThanOrEqual(shortDuration);
        }
      )
    );
  });

  it("is approximately pathLength / pixelsPerFrame rounded up", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 1, max: 10000, noNaN: true }),
        fc.double({ min: 0.1, max: 100, noNaN: true }),
        (pathLength, pixelsPerFrame) => {
          const duration = calculateDurationForSpeed(pathLength, pixelsPerFrame);
          const expected = Math.ceil(pathLength / pixelsPerFrame);
          expect(duration).toBe(expected);
        }
      )
    );
  });
});

// ============================================================
// calculateSpeed TESTS
// ============================================================

describe("PROPERTY: calculateSpeed", () => {
  it("returns positive for positive inputs", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 1, max: 10000, noNaN: true }),
        fc.integer({ min: 1, max: 1000 }),
        (pathLength, durationFrames) => {
          const speed = calculateSpeed(pathLength, durationFrames);
          expect(speed).toBeGreaterThan(0);
        }
      )
    );
  });

  it("longer duration means slower speed", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 100, max: 10000, noNaN: true }),
        fc.integer({ min: 1, max: 50 }),
        fc.integer({ min: 51, max: 100 }),
        (pathLength, shortDuration, longDuration) => {
          const fastSpeed = calculateSpeed(pathLength, shortDuration);
          const slowSpeed = calculateSpeed(pathLength, longDuration);
          expect(slowSpeed).toBeLessThan(fastSpeed);
        }
      )
    );
  });

  it("is exactly pathLength / durationFrames", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 1, max: 10000, noNaN: true }),
        fc.integer({ min: 1, max: 1000 }),
        (pathLength, durationFrames) => {
          const speed = calculateSpeed(pathLength, durationFrames);
          expect(speed).toBeCloseTo(pathLength / durationFrames, 10);
        }
      )
    );
  });
});

// ============================================================
// calculateDurationForSpeed and calculateSpeed INVERSE TESTS
// ============================================================

describe("PROPERTY: Speed/Duration inverse relationship", () => {
  it("calculateSpeed(L, calculateDurationForSpeed(L, S)) ≈ S (within rounding)", () => {
    fc.assert(
      fc.property(
        fc.double({ min: 100, max: 10000, noNaN: true }),
        fc.double({ min: 1, max: 100, noNaN: true }),
        (pathLength, targetSpeed) => {
          const duration = calculateDurationForSpeed(pathLength, targetSpeed);
          const actualSpeed = calculateSpeed(pathLength, duration);
          
          // Since duration = ceil(pathLength / targetSpeed), duration >= pathLength / targetSpeed
          // Therefore actualSpeed = pathLength / duration <= targetSpeed
          expect(actualSpeed).toBeLessThanOrEqual(targetSpeed + 1e-10);
          
          // actualSpeed should be close to targetSpeed (within one frame's worth)
          // Min speed occurs when ceil adds almost a full frame
          const minExpectedSpeed = pathLength / (pathLength / targetSpeed + 1);
          expect(actualSpeed).toBeGreaterThanOrEqual(minExpectedSpeed - 1e-10);
        }
      )
    );
  });
});

// ============================================================
// splineLayerToPathFollower TESTS
// ============================================================

describe("PROPERTY: splineLayerToPathFollower", () => {
  it("returns PathFollowerConfig", () => {
    fc.assert(
      fc.property(
        fc.string({ minLength: 1, maxLength: 20 }),
        controlPointsArb,
        fc.boolean(),
        fc.integer({ min: 1, max: 1000 }),
        (layerId, controlPoints, closed, totalFrames) => {
          const config = splineLayerToPathFollower(
            layerId, 
            controlPoints, 
            closed, 
            totalFrames
          );
          
          expect(config.id).toBe(layerId);
          expect(config.controlPoints).toBe(controlPoints);
          expect(config.closed).toBe(closed);
          expect(config.duration).toBe(totalFrames);
        }
      )
    );
  });

  it("inherits defaults from createPathFollower", () => {
    const config = splineLayerToPathFollower(
      "test",
      [{ x: 0, y: 0 }, { x: 100, y: 100 }],
      false,
      60
    );
    
    expect(config.shape).toBe("circle");
    expect(config.fillColor).toBe("#FFFFFF");
    expect(config.easing).toBe("ease-in-out");
    expect(config.alignToPath).toBe(true);
  });

  it("respects custom options", () => {
    fc.assert(
      fc.property(
        shapeArb,
        hexColorArb,
        fc.double({ min: 0.1, max: 2, noNaN: true }),
        fc.double({ min: 0.1, max: 2, noNaN: true }),
        (shape, fillColor, scaleStart, scaleEnd) => {
          const config = splineLayerToPathFollower(
            "test",
            [{ x: 0, y: 0 }, { x: 100, y: 100 }],
            false,
            60,
            { shape, fillColor, scaleStart, scaleEnd }
          );
          
          expect(config.shape).toBe(shape);
          expect(config.fillColor).toBe(fillColor);
          expect(config.scaleStart).toBe(scaleStart);
          expect(config.scaleEnd).toBe(scaleEnd);
        }
      )
    );
  });
});
