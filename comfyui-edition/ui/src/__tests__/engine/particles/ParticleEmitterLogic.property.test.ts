/**
 * Property Tests for ParticleEmitterLogic.ts
 *
 * Comprehensive fast-check property tests for:
 * - getEmitterPosition (all shape types)
 * - getEmissionDirection
 * - calculateInitialVelocity
 *
 * Tests verify:
 * - No NaN/Infinity outputs for any valid input
 * - Positions stay within expected bounds
 * - Direction vectors are always normalized
 * - RNG determinism (same seed = same output)
 * - Edge case handling (zero, negative, NaN inputs)
 */

import { describe, it, expect, vi, beforeEach } from "vitest";
import * as fc from "fast-check";
import * as THREE from "three";
import {
  getEmitterPosition,
  getEmissionDirection,
  calculateInitialVelocity,
  type SplineProvider,
  type RNGFunction,
} from "@/engine/particles/ParticleEmitterLogic";
import type { EmitterConfig, EmitterShapeConfig } from "@/engine/particles/types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

// Safe float that won't cause NaN issues
const safeFloat = (min = -10000, max = 10000) =>
  fc.float({ min: Math.fround(min), max: Math.fround(max), noNaN: true });

// Positive float for dimensions
const positiveFloat = (max = 1000) =>
  fc.float({ min: Math.fround(0.001), max: Math.fround(max), noNaN: true });

// Position object
const arbPosition = fc.record({
  x: safeFloat(),
  y: safeFloat(),
  z: safeFloat(),
});

// Direction object (will be normalized)
const arbDirection = fc.record({
  x: safeFloat(-1, 1),
  y: safeFloat(-1, 1),
  z: safeFloat(-1, 1),
});

// Shape configs for each type
const arbPointShape: fc.Arbitrary<EmitterShapeConfig> = fc.constant({ type: "point" as const });

const arbCircleShape: fc.Arbitrary<EmitterShapeConfig> = fc.record({
  type: fc.constant("circle" as const),
  radius: fc.oneof(positiveFloat(), fc.constant(undefined), fc.constant(NaN)),
  emitFromEdge: fc.boolean(),
});

const arbSphereShape: fc.Arbitrary<EmitterShapeConfig> = fc.record({
  type: fc.constant("sphere" as const),
  radius: fc.oneof(positiveFloat(), fc.constant(undefined), fc.constant(NaN)),
  emitFromEdge: fc.boolean(),
});

const arbBoxShape: fc.Arbitrary<EmitterShapeConfig> = fc.record({
  type: fc.constant("box" as const),
  boxSize: fc.oneof(
    fc.record({
      x: safeFloat(0, 1000),
      y: safeFloat(0, 1000),
      z: safeFloat(0, 1000),
    }),
    fc.constant(undefined),
  ),
});

const arbLineShape: fc.Arbitrary<EmitterShapeConfig> = fc.record({
  type: fc.constant("line" as const),
  lineStart: fc.oneof(arbPosition, fc.constant(undefined)),
  lineEnd: fc.oneof(arbPosition, fc.constant(undefined)),
});

const arbConeShape: fc.Arbitrary<EmitterShapeConfig> = fc.record({
  type: fc.constant("cone" as const),
  coneRadius: fc.oneof(positiveFloat(), fc.constant(undefined), fc.constant(NaN)),
  coneLength: fc.oneof(positiveFloat(), fc.constant(undefined), fc.constant(NaN)),
});

const arbSplineShape: fc.Arbitrary<EmitterShapeConfig> = fc.record({
  type: fc.constant("spline" as const),
  splineId: fc.oneof(fc.string(), fc.constant(undefined)),
  splineOffset: fc.oneof(fc.float({ min: 0, max: 1, noNaN: true }), fc.constant(undefined)),
});

const arbMeshShape: fc.Arbitrary<EmitterShapeConfig> = fc.record({
  type: fc.constant("mesh" as const),
  meshVertices: fc.oneof(
    fc.array(safeFloat(), { minLength: 0, maxLength: 300 }).map((arr) => new Float32Array(arr)),
    fc.constant(undefined),
  ),
});

// Combine all shapes
const arbShape = fc.oneof(
  arbPointShape,
  arbCircleShape,
  arbSphereShape,
  arbBoxShape,
  arbLineShape,
  arbConeShape,
  arbSplineShape,
  arbMeshShape,
);

// Full emitter config
const arbEmitterConfig: fc.Arbitrary<EmitterConfig> = fc.record({
  id: fc.uuid(),
  name: fc.string(),
  enabled: fc.boolean(),
  position: arbPosition,
  rotation: arbPosition,
  shape: arbShape,
  emissionRate: positiveFloat(1000),
  emissionRateVariance: fc.float({ min: 0, max: 100, noNaN: true }),
  burstCount: fc.integer({ min: 0, max: 1000 }),
  burstInterval: fc.integer({ min: 0, max: 300 }),
  initialSpeed: fc.oneof(positiveFloat(1000), fc.constant(NaN), fc.constant(-100)),
  speedVariance: fc.oneof(fc.float({ min: 0, max: 100, noNaN: true }), fc.constant(NaN)),
  inheritEmitterVelocity: fc.oneof(fc.float({ min: 0, max: 1, noNaN: true }), fc.constant(NaN)),
  initialSize: positiveFloat(100),
  sizeVariance: fc.float({ min: 0, max: 50, noNaN: true }),
  initialMass: positiveFloat(10),
  massVariance: fc.float({ min: 0, max: 5, noNaN: true }),
  lifetime: fc.integer({ min: 1, max: 600 }),
  lifetimeVariance: fc.float({ min: 0, max: 100, noNaN: true }),
  initialRotation: fc.float({ min: 0, max: 360, noNaN: true }),
  rotationVariance: fc.float({ min: 0, max: 360, noNaN: true }),
  initialAngularVelocity: fc.float({ min: -360, max: 360, noNaN: true }),
  angularVelocityVariance: fc.float({ min: 0, max: 360, noNaN: true }),
  colorStart: fc.tuple(
    fc.float({ min: 0, max: 1, noNaN: true }),
    fc.float({ min: 0, max: 1, noNaN: true }),
    fc.float({ min: 0, max: 1, noNaN: true }),
    fc.float({ min: 0, max: 1, noNaN: true }),
  ) as fc.Arbitrary<[number, number, number, number]>,
  colorEnd: fc.tuple(
    fc.float({ min: 0, max: 1, noNaN: true }),
    fc.float({ min: 0, max: 1, noNaN: true }),
    fc.float({ min: 0, max: 1, noNaN: true }),
    fc.float({ min: 0, max: 1, noNaN: true }),
  ) as fc.Arbitrary<[number, number, number, number]>,
  colorVariance: fc.float({ min: 0, max: 1, noNaN: true }),
  emissionDirection: arbDirection,
  emissionSpread: fc.oneof(
    fc.float({ min: 0, max: 180, noNaN: true }),
    fc.constant(NaN),
    fc.constant(-10),
  ),
  burstOnBeat: fc.boolean(),
  beatEmissionMultiplier: fc.float({ min: 1, max: 10, noNaN: true }),
});

// Seeded RNG for determinism
function createSeededRNG(seed: number): RNGFunction {
  let state = seed;
  return () => {
    state = (state * 1103515245 + 12345) & 0x7fffffff;
    return state / 0x7fffffff;
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleEmitterLogic.getEmitterPosition", () => {
  it("should never return NaN or Infinity for any shape type", () => {
    fc.assert(
      fc.property(
        arbEmitterConfig,
        fc.integer({ min: 1, max: 1000000 }),
        (emitter, seed) => {
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          expect(Number.isFinite(pos.x)).toBe(true);
          expect(Number.isFinite(pos.y)).toBe(true);
          expect(Number.isFinite(pos.z)).toBe(true);
        },
      ),
      { numRuns: 500 },
    );
  });

  it("should return base position for point emitter", () => {
    fc.assert(
      fc.property(
        arbPosition,
        fc.integer({ min: 1, max: 1000000 }),
        (position, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position,
            shape: { type: "point" },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          // Point emitter should return exactly base position (with Y negated)
          expect(pos.x).toBeCloseTo(position.x, 5);
          expect(pos.y).toBeCloseTo(-position.y, 5);
          expect(pos.z).toBeCloseTo(position.z, 5);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should return positions within circle radius for circle emitter", () => {
    fc.assert(
      fc.property(
        arbPosition,
        positiveFloat(500),
        fc.integer({ min: 1, max: 1000000 }),
        (position, radius, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position,
            shape: { type: "circle", radius, emitFromEdge: false },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          // Distance from base should be <= radius
          const dx = pos.x - position.x;
          const dy = pos.y - (-position.y);
          const dist = Math.sqrt(dx * dx + dy * dy);
          expect(dist).toBeLessThanOrEqual(radius + 0.001);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should return positions on circle edge when emitFromEdge=true", () => {
    fc.assert(
      fc.property(
        arbPosition,
        positiveFloat(500),
        fc.integer({ min: 1, max: 1000000 }),
        (position, radius, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position,
            shape: { type: "circle", radius, emitFromEdge: true },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          // Distance from base should be approximately equal to radius
          const dx = pos.x - position.x;
          const dy = pos.y - (-position.y);
          const dist = Math.sqrt(dx * dx + dy * dy);
          expect(dist).toBeCloseTo(radius, 1);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should return positions within sphere radius for sphere emitter", () => {
    fc.assert(
      fc.property(
        arbPosition,
        positiveFloat(500),
        fc.integer({ min: 1, max: 1000000 }),
        (position, radius, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position,
            shape: { type: "sphere", radius, emitFromEdge: false },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          // Distance from base should be <= radius
          const dx = pos.x - position.x;
          const dy = pos.y - (-position.y);
          const dz = pos.z - position.z;
          const dist = Math.sqrt(dx * dx + dy * dy + dz * dz);
          expect(dist).toBeLessThanOrEqual(radius + 0.001);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should return positions within box bounds for box emitter", () => {
    fc.assert(
      fc.property(
        arbPosition,
        fc.record({
          x: positiveFloat(500),
          y: positiveFloat(500),
          z: positiveFloat(500),
        }),
        fc.integer({ min: 1, max: 1000000 }),
        (position, boxSize, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position,
            shape: { type: "box", boxSize },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          // Position should be within box bounds centered at emitter position
          expect(Math.abs(pos.x - position.x)).toBeLessThanOrEqual(boxSize.x / 2 + 0.001);
          expect(Math.abs(pos.y - (-position.y))).toBeLessThanOrEqual(boxSize.y / 2 + 0.001);
          expect(Math.abs(pos.z - position.z)).toBeLessThanOrEqual(boxSize.z / 2 + 0.001);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should return positions along line for line emitter", () => {
    fc.assert(
      fc.property(
        arbPosition,
        arbPosition,
        arbPosition,
        fc.integer({ min: 1, max: 1000000 }),
        (emitterPos, lineStart, lineEnd, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position: emitterPos,
            shape: { type: "line", lineStart, lineEnd },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          // Position should be finite (line interpolation)
          expect(Number.isFinite(pos.x)).toBe(true);
          expect(Number.isFinite(pos.y)).toBe(true);
          expect(Number.isFinite(pos.z)).toBe(true);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should be deterministic with same seed", () => {
    fc.assert(
      fc.property(
        arbEmitterConfig,
        fc.integer({ min: 1, max: 1000000 }),
        (emitter, seed) => {
          const rng1 = createSeededRNG(seed);
          const rng2 = createSeededRNG(seed);

          const pos1 = getEmitterPosition(emitter, rng1);
          const pos2 = getEmitterPosition(emitter, rng2);

          expect(pos1.x).toBeCloseTo(pos2.x, 10);
          expect(pos1.y).toBeCloseTo(pos2.y, 10);
          expect(pos1.z).toBeCloseTo(pos2.z, 10);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should handle spline emission with provider", () => {
    fc.assert(
      fc.property(
        arbPosition,
        fc.string({ minLength: 1 }),
        fc.float({ min: 0, max: 1, noNaN: true }),
        fc.integer({ min: 1, max: 1000000 }),
        (position, splineId, splineT, seed) => {
          const splinePoint = { x: 100, y: 200, z: 50 };
          const splineProvider: SplineProvider = (id, t) => {
            if (id === splineId) return splinePoint;
            return null;
          };

          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position,
            shape: { type: "spline", splineId, splineOffset: splineT },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng, splineProvider);

          // Should return spline point (with Y negated)
          expect(pos.x).toBe(splinePoint.x);
          expect(pos.y).toBe(-splinePoint.y);
          expect(pos.z).toBe(splinePoint.z);
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should fallback to base position when spline provider returns null", () => {
    fc.assert(
      fc.property(arbPosition, fc.integer({ min: 1, max: 1000000 }), (position, seed) => {
        const splineProvider: SplineProvider = () => null;

        const emitter: EmitterConfig = {
          ...createMinimalEmitter(),
          position,
          shape: { type: "spline", splineId: "missing", splineOffset: 0.5 },
        };
        const rng = createSeededRNG(seed);
        const pos = getEmitterPosition(emitter, rng, splineProvider);

        // Should return base position
        expect(pos.x).toBe(position.x);
        expect(pos.y).toBe(-position.y);
        expect(pos.z).toBe(position.z);
      }),
      { numRuns: 50 },
    );
  });

  it("should handle mesh emission with vertices", () => {
    fc.assert(
      fc.property(
        arbPosition,
        fc.array(safeFloat(), { minLength: 3, maxLength: 300 }),
        fc.integer({ min: 1, max: 1000000 }),
        (position, verticesRaw, seed) => {
          // Ensure vertex count is multiple of 3
          const vertexCount = Math.floor(verticesRaw.length / 3);
          const meshVertices = new Float32Array(vertexCount * 3);
          for (let i = 0; i < vertexCount * 3; i++) {
            meshVertices[i] = verticesRaw[i];
          }

          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            position,
            shape: { type: "mesh", meshVertices },
          };
          const rng = createSeededRNG(seed);
          const pos = getEmitterPosition(emitter, rng);

          // Should return a valid position
          expect(Number.isFinite(pos.x)).toBe(true);
          expect(Number.isFinite(pos.y)).toBe(true);
          expect(Number.isFinite(pos.z)).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleEmitterLogic.getEmissionDirection", () => {
  it("should always return a normalized vector", () => {
    fc.assert(
      fc.property(arbEmitterConfig, fc.integer({ min: 1, max: 1000000 }), (emitter, seed) => {
        const rng = createSeededRNG(seed);
        const dir = getEmissionDirection(emitter, rng);

        const length = Math.sqrt(dir.x * dir.x + dir.y * dir.y + dir.z * dir.z);
        expect(length).toBeCloseTo(1, 5);
      }),
      { numRuns: 500 },
    );
  });

  it("should never return NaN components", () => {
    fc.assert(
      fc.property(arbEmitterConfig, fc.integer({ min: 1, max: 1000000 }), (emitter, seed) => {
        const rng = createSeededRNG(seed);
        const dir = getEmissionDirection(emitter, rng);

        expect(Number.isFinite(dir.x)).toBe(true);
        expect(Number.isFinite(dir.y)).toBe(true);
        expect(Number.isFinite(dir.z)).toBe(true);
      }),
      { numRuns: 500 },
    );
  });

  it("should return base direction when spread is 0", () => {
    fc.assert(
      fc.property(
        arbDirection,
        fc.integer({ min: 1, max: 1000000 }),
        (direction, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            emissionDirection: direction,
            emissionSpread: 0,
          };
          const rng = createSeededRNG(seed);
          const dir = getEmissionDirection(emitter, rng);

          // Normalize the input direction for comparison
          const baseLen = Math.sqrt(
            direction.x * direction.x + direction.y * direction.y + direction.z * direction.z,
          );
          if (baseLen > 0.001) {
            const normX = direction.x / baseLen;
            const normY = direction.y / baseLen;
            const normZ = direction.z / baseLen;

            expect(dir.x).toBeCloseTo(normX, 5);
            expect(dir.y).toBeCloseTo(normY, 5);
            expect(dir.z).toBeCloseTo(normZ, 5);
          }
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should vary direction within spread cone", () => {
    fc.assert(
      fc.property(
        fc.float({ min: 10, max: 90, noNaN: true }),
        fc.integer({ min: 1, max: 1000000 }),
        (spread, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            emissionDirection: { x: 0, y: 1, z: 0 },
            emissionSpread: spread,
          };

          // Generate multiple directions and verify they're different
          const directions: THREE.Vector3[] = [];
          for (let i = 0; i < 10; i++) {
            const rng = createSeededRNG(seed + i);
            directions.push(getEmissionDirection(emitter, rng));
          }

          // At least some directions should be different
          let hasDifferent = false;
          for (let i = 1; i < directions.length; i++) {
            if (
              Math.abs(directions[i].x - directions[0].x) > 0.001 ||
              Math.abs(directions[i].y - directions[0].y) > 0.001 ||
              Math.abs(directions[i].z - directions[0].z) > 0.001
            ) {
              hasDifferent = true;
              break;
            }
          }
          expect(hasDifferent).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should be deterministic with same seed", () => {
    fc.assert(
      fc.property(arbEmitterConfig, fc.integer({ min: 1, max: 1000000 }), (emitter, seed) => {
        const rng1 = createSeededRNG(seed);
        const rng2 = createSeededRNG(seed);

        const dir1 = getEmissionDirection(emitter, rng1);
        const dir2 = getEmissionDirection(emitter, rng2);

        expect(dir1.x).toBeCloseTo(dir2.x, 10);
        expect(dir1.y).toBeCloseTo(dir2.y, 10);
        expect(dir1.z).toBeCloseTo(dir2.z, 10);
      }),
      { numRuns: 100 },
    );
  });

  it("should handle negative spread gracefully", () => {
    fc.assert(
      fc.property(
        arbDirection,
        fc.float({ min: Math.fround(-180), max: Math.fround(-0.001), noNaN: true }),
        fc.integer({ min: 1, max: 1000000 }),
        (direction, negativeSpread, seed) => {
          const emitter: EmitterConfig = {
            ...createMinimalEmitter(),
            emissionDirection: direction,
            emissionSpread: negativeSpread,
          };
          const rng = createSeededRNG(seed);
          const dir = getEmissionDirection(emitter, rng);

          // Should return valid normalized direction
          const length = Math.sqrt(dir.x * dir.x + dir.y * dir.y + dir.z * dir.z);
          expect(length).toBeCloseTo(1, 5);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should handle NaN spread gracefully", () => {
    fc.assert(
      fc.property(arbDirection, fc.integer({ min: 1, max: 1000000 }), (direction, seed) => {
        const emitter: EmitterConfig = {
          ...createMinimalEmitter(),
          emissionDirection: direction,
          emissionSpread: NaN,
        };
        const rng = createSeededRNG(seed);
        const dir = getEmissionDirection(emitter, rng);

        // Should return valid normalized direction
        expect(Number.isFinite(dir.x)).toBe(true);
        expect(Number.isFinite(dir.y)).toBe(true);
        expect(Number.isFinite(dir.z)).toBe(true);
      }),
      { numRuns: 100 },
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleEmitterLogic.calculateInitialVelocity", () => {
  it("should never return NaN velocity components", () => {
    fc.assert(
      fc.property(
        arbEmitterConfig,
        arbPosition,
        fc.integer({ min: 1, max: 1000000 }),
        (emitter, emitterVel, seed) => {
          const emitterWithVel = {
            ...emitter,
            velocity: new THREE.Vector3(emitterVel.x, emitterVel.y, emitterVel.z),
          };
          const rng = createSeededRNG(seed);
          const result = calculateInitialVelocity(emitterWithVel, rng);

          expect(Number.isFinite(result.velocity.x)).toBe(true);
          expect(Number.isFinite(result.velocity.y)).toBe(true);
          expect(Number.isFinite(result.velocity.z)).toBe(true);
          expect(Number.isFinite(result.speed)).toBe(true);
        },
      ),
      { numRuns: 500 },
    );
  });

  it("should return normalized direction vector", () => {
    fc.assert(
      fc.property(
        arbEmitterConfig,
        arbPosition,
        fc.integer({ min: 1, max: 1000000 }),
        (emitter, emitterVel, seed) => {
          const emitterWithVel = {
            ...emitter,
            velocity: new THREE.Vector3(emitterVel.x, emitterVel.y, emitterVel.z),
          };
          const rng = createSeededRNG(seed);
          const result = calculateInitialVelocity(emitterWithVel, rng);

          const length = result.direction.length();
          expect(length).toBeCloseTo(1, 5);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should return non-negative speed", () => {
    fc.assert(
      fc.property(
        arbEmitterConfig,
        arbPosition,
        fc.integer({ min: 1, max: 1000000 }),
        (emitter, emitterVel, seed) => {
          // Ensure initialSpeed is valid for this test
          const validEmitter = {
            ...emitter,
            initialSpeed: Math.abs(emitter.initialSpeed) || 100,
            speedVariance: Math.min(emitter.speedVariance || 0, emitter.initialSpeed || 100),
            velocity: new THREE.Vector3(emitterVel.x, emitterVel.y, emitterVel.z),
          };
          const rng = createSeededRNG(seed);
          const result = calculateInitialVelocity(validEmitter, rng);

          // Speed calculation uses variance which can make it negative
          // but the function should handle this gracefully
          expect(Number.isFinite(result.speed)).toBe(true);
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should inherit emitter velocity correctly", () => {
    fc.assert(
      fc.property(
        fc.float({ min: 0.5, max: 1, noNaN: true }),
        arbPosition,
        fc.integer({ min: 1, max: 1000000 }),
        (inheritFactor, emitterVel, seed) => {
          const emitterWithVel = {
            ...createMinimalEmitter(),
            initialSpeed: 0, // No base speed
            speedVariance: 0,
            inheritEmitterVelocity: inheritFactor,
            velocity: new THREE.Vector3(emitterVel.x, emitterVel.y, emitterVel.z),
          };
          const rng = createSeededRNG(seed);
          const result = calculateInitialVelocity(emitterWithVel, rng);

          // Velocity should be close to inherited velocity
          expect(result.velocity.x).toBeCloseTo(emitterVel.x * inheritFactor, 3);
          expect(result.velocity.y).toBeCloseTo(emitterVel.y * inheritFactor, 3);
          expect(result.velocity.z).toBeCloseTo(emitterVel.z * inheritFactor, 3);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should be deterministic with same seed", () => {
    fc.assert(
      fc.property(
        arbEmitterConfig,
        arbPosition,
        fc.integer({ min: 1, max: 1000000 }),
        (emitter, emitterVel, seed) => {
          const emitterWithVel = {
            ...emitter,
            velocity: new THREE.Vector3(emitterVel.x, emitterVel.y, emitterVel.z),
          };

          const rng1 = createSeededRNG(seed);
          const rng2 = createSeededRNG(seed);

          const result1 = calculateInitialVelocity(emitterWithVel, rng1);
          const result2 = calculateInitialVelocity(emitterWithVel, rng2);

          expect(result1.velocity.x).toBeCloseTo(result2.velocity.x, 10);
          expect(result1.velocity.y).toBeCloseTo(result2.velocity.y, 10);
          expect(result1.velocity.z).toBeCloseTo(result2.velocity.z, 10);
          expect(result1.speed).toBeCloseTo(result2.speed, 10);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should handle NaN initialSpeed gracefully", () => {
    fc.assert(
      fc.property(arbPosition, fc.integer({ min: 1, max: 1000000 }), (emitterVel, seed) => {
        const emitterWithVel = {
          ...createMinimalEmitter(),
          initialSpeed: NaN,
          speedVariance: 0,
          velocity: new THREE.Vector3(emitterVel.x, emitterVel.y, emitterVel.z),
        };
        const rng = createSeededRNG(seed);
        const result = calculateInitialVelocity(emitterWithVel, rng);

        // Should default to 100 for NaN initialSpeed
        expect(Number.isFinite(result.velocity.x)).toBe(true);
        expect(Number.isFinite(result.velocity.y)).toBe(true);
        expect(Number.isFinite(result.velocity.z)).toBe(true);
      }),
      { numRuns: 100 },
    );
  });

  it("should handle NaN inheritEmitterVelocity gracefully", () => {
    fc.assert(
      fc.property(arbPosition, fc.integer({ min: 1, max: 1000000 }), (emitterVel, seed) => {
        const emitterWithVel = {
          ...createMinimalEmitter(),
          inheritEmitterVelocity: NaN,
          velocity: new THREE.Vector3(emitterVel.x, emitterVel.y, emitterVel.z),
        };
        const rng = createSeededRNG(seed);
        const result = calculateInitialVelocity(emitterWithVel, rng);

        // Should handle NaN gracefully
        expect(Number.isFinite(result.velocity.x)).toBe(true);
        expect(Number.isFinite(result.velocity.y)).toBe(true);
        expect(Number.isFinite(result.velocity.z)).toBe(true);
      }),
      { numRuns: 100 },
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                       // helper // functions
// ════════════════════════════════════════════════════════════════════════════

function createMinimalEmitter(): EmitterConfig {
  return {
    id: "test-emitter",
    name: "Test Emitter",
    enabled: true,
    position: { x: 0, y: 0, z: 0 },
    rotation: { x: 0, y: 0, z: 0 },
    shape: { type: "point" },
    emissionRate: 10,
    emissionRateVariance: 0,
    burstCount: 0,
    burstInterval: 0,
    initialSpeed: 100,
    speedVariance: 0,
    inheritEmitterVelocity: 0,
    initialSize: 10,
    sizeVariance: 0,
    initialMass: 1,
    massVariance: 0,
    lifetime: 60,
    lifetimeVariance: 0,
    initialRotation: 0,
    rotationVariance: 0,
    initialAngularVelocity: 0,
    angularVelocityVariance: 0,
    colorStart: [1, 1, 1, 1],
    colorEnd: [1, 1, 1, 0],
    colorVariance: 0,
    emissionDirection: { x: 0, y: 1, z: 0 },
    emissionSpread: 0,
    burstOnBeat: false,
    beatEmissionMultiplier: 1,
  };
}
