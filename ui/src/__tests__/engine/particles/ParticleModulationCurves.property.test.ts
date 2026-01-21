/**
 * Property Tests for ParticleModulationCurves.ts
 *
 * Comprehensive fast-check property tests for:
 * - Curve evaluation
 * - Various curve types
 * - Color gradient sampling
 * - Texture generation
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import {
  ParticleModulationCurves,
  type CurvePoint,
  type ColorStop,
} from "@/engine/particles/ParticleModulationCurves";
import type { ModulationCurve } from "@/engine/particles/types";

// ============================================================================
// HELPERS
// ============================================================================

function createSeededRNG(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 1103515245 + 12345) & 0x7fffffff;
    return s / 0x7fffffff;
  };
}

// ============================================================================
// ARBITRARIES
// ============================================================================

const arbCurvePoint: fc.Arbitrary<CurvePoint> = fc.record({
  time: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
  value: fc.float({ min: Math.fround(0), max: Math.fround(2), noNaN: true }),
  inTangent: fc.option(fc.float({ min: Math.fround(-10), max: Math.fround(10), noNaN: true })),
  outTangent: fc.option(fc.float({ min: Math.fround(-10), max: Math.fround(10), noNaN: true })),
});

const arbConstantCurve: fc.Arbitrary<ModulationCurve> = fc.record({
  type: fc.constant("constant" as const),
  value: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(2), noNaN: true }),
    fc.constant(NaN),
  ),
});

const arbLinearCurve: fc.Arbitrary<ModulationCurve> = fc.record({
  type: fc.constant("linear" as const),
  start: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(2), noNaN: true }),
    fc.constant(NaN),
  ),
  end: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(2), noNaN: true }),
    fc.constant(NaN),
  ),
});

const arbCurveCurve: fc.Arbitrary<ModulationCurve> = fc
  .array(arbCurvePoint, { minLength: 0, maxLength: 5 })
  .map((points) => ({
    type: "curve" as const,
    points: points.sort((a, b) => a.time - b.time),
  }));

const arbRandomCurve: fc.Arbitrary<ModulationCurve> = fc.record({
  type: fc.constant("random" as const),
  min: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  max: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(2), noNaN: true }),
    fc.constant(NaN),
  ),
});

const arbModulationCurve: fc.Arbitrary<ModulationCurve> = fc.oneof(
  arbConstantCurve,
  arbLinearCurve,
  arbCurveCurve,
  arbRandomCurve,
);

const arbColorStop: fc.Arbitrary<ColorStop> = fc.record({
  time: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
  color: fc.tuple(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
  ) as fc.Arbitrary<[number, number, number, number]>,
});

// ============================================================================
// TESTS: Construction
// ============================================================================

describe("ParticleModulationCurves construction", () => {
  it("should handle any resolution value", () => {
    fc.assert(
      fc.property(
        fc.oneof(
          fc.integer({ min: 2, max: 1024 }),
          fc.constant(0),
          fc.constant(-10),
          fc.constant(NaN),
        ),
        (resolution) => {
          const curves = new ParticleModulationCurves(createSeededRNG(12345), resolution);
          expect(curves).toBeDefined();
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Constant Curve
// ============================================================================

describe("ParticleModulationCurves constant curve", () => {
  let curves: ParticleModulationCurves;

  beforeEach(() => {
    curves = new ParticleModulationCurves(createSeededRNG(12345));
  });

  it("should return constant value regardless of t", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(0), max: Math.fround(2), noNaN: true }),
        fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
        (value, t) => {
          const curve: ModulationCurve = { type: "constant", value };
          expect(curves.evaluateCurve(curve, t)).toBe(value);
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should default to 1 when value is NaN", () => {
    const curve: ModulationCurve = { type: "constant", value: NaN };
    expect(curves.evaluateCurve(curve, 0.5)).toBe(1);
  });
});

// ============================================================================
// TESTS: Linear Curve
// ============================================================================

describe("ParticleModulationCurves linear curve", () => {
  let curves: ParticleModulationCurves;

  beforeEach(() => {
    curves = new ParticleModulationCurves(createSeededRNG(12345));
  });

  it("should interpolate between start and end", () => {
    const curve: ModulationCurve = { type: "linear", start: 0, end: 1 };

    expect(curves.evaluateCurve(curve, 0)).toBe(0);
    expect(curves.evaluateCurve(curve, 0.5)).toBe(0.5);
    expect(curves.evaluateCurve(curve, 1)).toBe(1);
  });

  it("should handle NaN start/end", () => {
    const curve: ModulationCurve = { type: "linear", start: NaN, end: NaN };
    const result = curves.evaluateCurve(curve, 0.5);
    expect(Number.isFinite(result)).toBe(true);
    expect(result).toBe(1); // Both default to 1
  });
});

// ============================================================================
// TESTS: Curve Type
// ============================================================================

describe("ParticleModulationCurves curve type", () => {
  let curves: ParticleModulationCurves;

  beforeEach(() => {
    curves = new ParticleModulationCurves(createSeededRNG(12345));
  });

  it("should return 1 for empty points array", () => {
    const curve: ModulationCurve = { type: "curve", points: [] };
    expect(curves.evaluateCurve(curve, 0.5)).toBe(1);
  });

  it("should return single point value for single point", () => {
    const curve: ModulationCurve = {
      type: "curve",
      points: [{ time: 0.5, value: 0.7 }],
    };
    expect(curves.evaluateCurve(curve, 0)).toBe(0.7);
    expect(curves.evaluateCurve(curve, 0.5)).toBe(0.7);
    expect(curves.evaluateCurve(curve, 1)).toBe(0.7);
  });

  it("should handle same time for adjacent points", () => {
    const curve: ModulationCurve = {
      type: "curve",
      points: [
        { time: 0.5, value: 0.3 },
        { time: 0.5, value: 0.7 },
      ],
    };
    // Should not produce NaN/Infinity
    const result = curves.evaluateCurve(curve, 0.5);
    expect(Number.isFinite(result)).toBe(true);
  });

  it("should interpolate smoothly between points", () => {
    const curve: ModulationCurve = {
      type: "curve",
      points: [
        { time: 0, value: 0 },
        { time: 1, value: 1 },
      ],
    };

    // At endpoints
    expect(curves.evaluateCurve(curve, 0)).toBeCloseTo(0, 5);
    expect(curves.evaluateCurve(curve, 1)).toBeCloseTo(1, 5);

    // Midpoint should be somewhere in between
    const mid = curves.evaluateCurve(curve, 0.5);
    expect(mid).toBeGreaterThan(0);
    expect(mid).toBeLessThan(1);
  });
});

// ============================================================================
// TESTS: Random Curve
// ============================================================================

describe("ParticleModulationCurves random curve", () => {
  let curves: ParticleModulationCurves;

  beforeEach(() => {
    curves = new ParticleModulationCurves(createSeededRNG(12345));
  });

  it("should produce values within min/max range", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
        fc.float({ min: Math.fround(1), max: Math.fround(2), noNaN: true }),
        (min, max) => {
          const curve: ModulationCurve = { type: "random", min, max };
          const result = curves.evaluateCurve(curve, 0.5);
          expect(result).toBeGreaterThanOrEqual(min);
          expect(result).toBeLessThanOrEqual(max);
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should use randomOffset when provided", () => {
    const curve: ModulationCurve = { type: "random", min: 0, max: 1 };

    // With same offset, should get same result
    const r1 = curves.evaluateCurve(curve, 0, 0.5);
    const r2 = curves.evaluateCurve(curve, 0, 0.5);
    expect(r1).toBe(r2);
  });

  it("should handle NaN min/max", () => {
    const curve: ModulationCurve = { type: "random", min: NaN, max: NaN };
    const result = curves.evaluateCurve(curve, 0.5);
    expect(Number.isFinite(result)).toBe(true);
  });
});

// ============================================================================
// TESTS: Any Curve
// ============================================================================

describe("ParticleModulationCurves any curve", () => {
  it("should not produce NaN with any curve config", () => {
    fc.assert(
      fc.property(
        arbModulationCurve,
        fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
        fc.option(fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true })),
        (curve, t, randomOffset) => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          const curves = new ParticleModulationCurves(createSeededRNG(42));
          const randomOffsetValue = (randomOffset !== null && randomOffset !== undefined && typeof randomOffset === "number" && Number.isFinite(randomOffset)) ? randomOffset : undefined;
          const result = curves.evaluateCurve(curve, t, randomOffsetValue);
          expect(Number.isFinite(result)).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should return 1 for undefined curve", () => {
    const curves = new ParticleModulationCurves(createSeededRNG(12345));
    expect(curves.evaluateCurve(undefined, 0.5)).toBe(1);
  });
});

// ============================================================================
// TESTS: Color Gradient
// ============================================================================

describe("ParticleModulationCurves color gradient", () => {
  let curves: ParticleModulationCurves;

  beforeEach(() => {
    curves = new ParticleModulationCurves(createSeededRNG(12345));
  });

  it("should return white for empty stops", () => {
    const result = curves.sampleColorGradient([], 0.5);
    expect(result).toEqual([1, 1, 1, 1]);
  });

  it("should return single stop color", () => {
    const stops: ColorStop[] = [{ time: 0.5, color: [1, 0, 0, 1] }];
    const result = curves.sampleColorGradient(stops, 0.5);
    expect(result).toEqual([1, 0, 0, 1]);
  });

  it("should interpolate between stops", () => {
    const stops: ColorStop[] = [
      { time: 0, color: [0, 0, 0, 1] },
      { time: 1, color: [1, 1, 1, 1] },
    ];

    const result = curves.sampleColorGradient(stops, 0.5);
    expect(result[0]).toBeCloseTo(0.5, 1);
    expect(result[1]).toBeCloseTo(0.5, 1);
    expect(result[2]).toBeCloseTo(0.5, 1);
  });

  it("should handle same time for adjacent stops", () => {
    const stops: ColorStop[] = [
      { time: 0.5, color: [1, 0, 0, 1] },
      { time: 0.5, color: [0, 1, 0, 1] },
    ];

    // Should not produce NaN
    const result = curves.sampleColorGradient(stops, 0.5);
    expect(Number.isFinite(result[0])).toBe(true);
    expect(Number.isFinite(result[1])).toBe(true);
    expect(Number.isFinite(result[2])).toBe(true);
    expect(Number.isFinite(result[3])).toBe(true);
  });

  it("should not produce NaN with any stops", () => {
    fc.assert(
      fc.property(
        fc.array(arbColorStop, { minLength: 0, maxLength: 10 }),
        fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
        (stops, t) => {
          const result = curves.sampleColorGradient(stops, t);
          expect(Number.isFinite(result[0])).toBe(true);
          expect(Number.isFinite(result[1])).toBe(true);
          expect(Number.isFinite(result[2])).toBe(true);
          expect(Number.isFinite(result[3])).toBe(true);
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Texture Generation
// ============================================================================

describe("ParticleModulationCurves texture generation", () => {
  it("should create textures with any modulation config", () => {
    fc.assert(
      fc.property(
        fc.option(arbModulationCurve),
        fc.option(arbModulationCurve),
        fc.option(fc.array(arbColorStop, { minLength: 0, maxLength: 5 })),
        (sizeOverLifetime, opacityOverLifetime, colorOverLifetime) => {
          // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
          const curves = new ParticleModulationCurves(createSeededRNG(42), 64);
          const sizeOverLifetimeValue = (sizeOverLifetime !== null && sizeOverLifetime !== undefined) ? sizeOverLifetime : undefined;
          const opacityOverLifetimeValue = (opacityOverLifetime !== null && opacityOverLifetime !== undefined) ? opacityOverLifetime : undefined;
          const colorOverLifetimeValue = (colorOverLifetime !== null && colorOverLifetime !== undefined) ? colorOverLifetime : undefined;
          const textures = curves.createTextures({
            sizeOverLifetime: sizeOverLifetimeValue,
            opacityOverLifetime: opacityOverLifetimeValue,
            colorOverLifetime: colorOverLifetimeValue,
          });

          expect(textures.sizeOverLifetime).toBeDefined();
          expect(textures.opacityOverLifetime).toBeDefined();
          expect(textures.colorOverLifetime).toBeDefined();

          curves.disposeTextures(textures);
        },
      ),
      { numRuns: 30 },
    );
  });
});

// ============================================================================
// TESTS: Sample Curve
// ============================================================================

describe("ParticleModulationCurves.sampleCurve", () => {
  it("should fill array with 1 for undefined curve", () => {
    const curves = new ParticleModulationCurves(createSeededRNG(12345));
    const output = new Float32Array(10);
    curves.sampleCurve(undefined, output);

    for (let i = 0; i < output.length; i++) {
      expect(output[i]).toBe(1);
    }
  });

  it("should sample curve into array", () => {
    const curves = new ParticleModulationCurves(createSeededRNG(12345));
    const output = new Float32Array(10);
    const curve: ModulationCurve = { type: "linear", start: 0, end: 1 };

    curves.sampleCurve(curve, output);

    expect(output[0]).toBeCloseTo(0, 5);
    expect(output[9]).toBeCloseTo(1, 5);
  });
});
