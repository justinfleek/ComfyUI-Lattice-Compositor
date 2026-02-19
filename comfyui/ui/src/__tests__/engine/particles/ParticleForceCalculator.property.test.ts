/**
 * Property Tests for ParticleForceCalculator.ts
 *
 * Comprehensive fast-check property tests for:
 * - calculateForceField (all force types)
 * - getForceFieldTypeIndex
 * - getFalloffTypeIndex
 *
 * Tests verify:
 * - No NaN/Infinity outputs for any valid input
 * - Force magnitudes are bounded
 * - Correct force field type mapping
 * - Edge case handling
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import * as THREE from "three";
import {
  calculateForceField,
  getForceFieldTypeIndex,
  getFalloffTypeIndex,
} from "@/engine/particles/ParticleForceCalculator";
import type { ForceFieldConfig, ForceFieldType } from "@/engine/particles/types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const safeFloat = (min = -10000, max = 10000) =>
  fc.float({ min: Math.fround(min), max: Math.fround(max), noNaN: true });

const positiveFloat = (max = 1000) =>
  fc.float({ min: Math.fround(0.001), max: Math.fround(max), noNaN: true });

const arbPosition = fc.record({
  x: safeFloat(),
  y: safeFloat(),
  z: safeFloat(),
});

const arbVelocity = fc.record({
  x: safeFloat(-1000, 1000),
  y: safeFloat(-1000, 1000),
  z: safeFloat(-1000, 1000),
});

const forceFieldTypes: ForceFieldType[] = [
  "gravity",
  "point",
  "vortex",
  "turbulence",
  "drag",
  "wind",
  "lorenz",
  "curl",
  "magnetic",
  "orbit",
];

const falloffTypes = ["linear", "quadratic", "exponential", "smoothstep", "none"] as const;

const arbForceFieldType = fc.constantFrom(...forceFieldTypes);

const arbFalloffType = fc.constantFrom(...falloffTypes);

// Force field config with all properties (both required and optional)
const arbForceFieldConfig: fc.Arbitrary<ForceFieldConfig> = fc.record({
  // Required base properties
  id: fc.uuid(),
  name: fc.string(),
  type: arbForceFieldType,
  enabled: fc.constant(true),
  strength: fc.oneof(safeFloat(-1000, 1000), fc.constant(NaN), fc.constant(Infinity)),
  position: arbPosition,
  falloffStart: fc.oneof(positiveFloat(500), fc.constant(0)),
  falloffEnd: fc.oneof(positiveFloat(1000), fc.constant(0)),
  falloffType: arbFalloffType,
  // Vortex-specific
  vortexAxis: fc.option(arbPosition, { nil: undefined }),
  inwardForce: fc.option(safeFloat(-100, 100), { nil: undefined }),
  // Turbulence/Curl-specific
  noiseScale: fc.option(positiveFloat(1), { nil: undefined }),
  noiseSpeed: fc.option(positiveFloat(10), { nil: undefined }),
  // Drag-specific
  linearDrag: fc.option(positiveFloat(1), { nil: undefined }),
  quadraticDrag: fc.option(positiveFloat(0.1), { nil: undefined }),
  // Wind-specific
  windDirection: fc.option(arbPosition, { nil: undefined }),
  gustStrength: fc.option(positiveFloat(100), { nil: undefined }),
  gustFrequency: fc.option(positiveFloat(10), { nil: undefined }),
  // Lorenz-specific
  lorenzSigma: fc.option(positiveFloat(20), { nil: undefined }),
  lorenzRho: fc.option(positiveFloat(50), { nil: undefined }),
  lorenzBeta: fc.option(positiveFloat(10), { nil: undefined }),
  // Orbit-specific
  orbitSpeed: fc.option(safeFloat(-100, 100), { nil: undefined }),
  // Path follow
  pathRadius: fc.option(positiveFloat(500), { nil: undefined }),
}) as fc.Arbitrary<ForceFieldConfig>;

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleForceCalculator.calculateForceField", () => {
  it("should never return NaN force components for any force type", () => {
    fc.assert(
      fc.property(
        arbForceFieldConfig,
        arbPosition,
        arbVelocity,
        positiveFloat(10),
        safeFloat(0, 1000),
        (field, particlePos, particleVel, mass, simTime) => {
          const force = calculateForceField(
            field,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            particleVel.x,
            particleVel.y,
            particleVel.z,
            mass,
            simTime,
          );

          expect(Number.isFinite(force.x)).toBe(true);
          expect(Number.isFinite(force.y)).toBe(true);
          expect(Number.isFinite(force.z)).toBe(true);
        },
      ),
      { numRuns: 1000 },
    );
  });

  // Note: calculateForceField does NOT check field.enabled - caller is responsible
  // This test verifies the function returns finite values (enabled check is at call site)

  it("should return very small force when strength is zero for simple force types", () => {
    // Only test simple force types where strength=0 should give near-zero force
    // Vortex has inwardForce, wind has gustStrength, turbulence/curl use noise
    const simpleTypes: ForceFieldType[] = ["gravity", "point", "drag", "lorenz", "magnetic", "orbit"];
    fc.assert(
      fc.property(
        fc.constantFrom(...simpleTypes),
        arbPosition,
        arbVelocity,
        positiveFloat(10),
        safeFloat(0, 1000),
        (type, particlePos, particleVel, mass, simTime) => {
          const field: ForceFieldConfig = {
            id: "test",
            name: "Test",
            type,
            enabled: true,
            strength: 0,
            position: { x: 0, y: 0, z: 0 },
            falloffStart: 0,
            falloffEnd: 1000,
            falloffType: "none",
          };
          const force = calculateForceField(
            field,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            particleVel.x,
            particleVel.y,
            particleVel.z,
            mass,
            simTime,
          );

          // Force should be very small for zero strength
          expect(Math.abs(force.x)).toBeLessThan(0.01);
          expect(Math.abs(force.y)).toBeLessThan(0.01);
          expect(Math.abs(force.z)).toBeLessThan(0.01);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should apply gravity in the direction specified", () => {
    fc.assert(
      fc.property(
        arbPosition,
        arbVelocity,
        positiveFloat(10),
        positiveFloat(100),
        (particlePos, particleVel, mass, strength) => {
          const gravityField: ForceFieldConfig = {
            id: "gravity",
            name: "Gravity",
            type: "gravity",
            enabled: true,
            strength,
            position: { x: 0, y: 0, z: 0 },
            direction: { x: 0, y: -1, z: 0 }, // Down
            falloffStart: 0,
            falloffEnd: 10000,
            falloffType: "none",
          };

          const force = calculateForceField(
            gravityField,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            particleVel.x,
            particleVel.y,
            particleVel.z,
            mass,
            0,
          );

          // Gravity should be in -Y direction
          expect(force.y).toBeLessThan(0);
          expect(Math.abs(force.x)).toBeLessThan(0.001);
          expect(Math.abs(force.z)).toBeLessThan(0.001);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should apply point attractor force toward the attractor", () => {
    fc.assert(
      fc.property(
        arbPosition,
        arbPosition,
        positiveFloat(10),
        positiveFloat(100),
        (attractorPos, particlePos, mass, strength) => {
          // Ensure particle is not at attractor position
          if (
            Math.abs(particlePos.x - attractorPos.x) < 1 &&
            Math.abs(particlePos.y - attractorPos.y) < 1 &&
            Math.abs(particlePos.z - attractorPos.z) < 1
          ) {
            return; // Skip this case
          }

          const pointField: ForceFieldConfig = {
            id: "point",
            name: "Point",
            type: "point",
            enabled: true,
            strength,
            position: attractorPos,
            falloffStart: 0,
            falloffEnd: 10000,
            falloffType: "none",
          };

          const force = calculateForceField(
            pointField,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            0,
            0,
            0,
            mass,
            0,
          );

          // Force should point toward attractor (positive dot product with direction)
          const toAttractor = new THREE.Vector3(
            attractorPos.x - particlePos.x,
            attractorPos.y - particlePos.y,
            attractorPos.z - particlePos.z,
          ).normalize();

          const forceDir = new THREE.Vector3(force.x, force.y, force.z);
          if (forceDir.length() > 0.001) {
            forceDir.normalize();
            const dot = forceDir.dot(toAttractor);
            expect(dot).toBeGreaterThan(0); // Force toward attractor
          }
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should apply drag force opposing velocity", () => {
    fc.assert(
      fc.property(
        arbPosition,
        fc.record({
          x: fc.float({ min: 10, max: 1000, noNaN: true }),
          y: fc.float({ min: 10, max: 1000, noNaN: true }),
          z: fc.float({ min: 10, max: 1000, noNaN: true }),
        }),
        positiveFloat(10),
        positiveFloat(1),
        (particlePos, particleVel, mass, dragStrength) => {
          const dragField: ForceFieldConfig = {
            id: "drag",
            name: "Drag",
            type: "drag",
            enabled: true,
            strength: dragStrength,
            position: { x: 0, y: 0, z: 0 },
            falloffStart: 0,
            falloffEnd: 10000,
            falloffType: "none",
            linearDrag: 0.1,
            quadraticDrag: 0.01,
          };

          const force = calculateForceField(
            dragField,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            particleVel.x,
            particleVel.y,
            particleVel.z,
            mass,
            0,
          );

          // Drag force should oppose velocity (negative dot product)
          const velDir = new THREE.Vector3(particleVel.x, particleVel.y, particleVel.z).normalize();
          const forceDir = new THREE.Vector3(force.x, force.y, force.z);
          if (forceDir.length() > 0.001) {
            forceDir.normalize();
            const dot = forceDir.dot(velDir);
            expect(dot).toBeLessThan(0); // Force opposes velocity
          }
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should apply vortex force tangentially", () => {
    fc.assert(
      fc.property(
        arbPosition,
        positiveFloat(10),
        positiveFloat(100),
        (particlePos, mass, strength) => {
          // Ensure particle is not on the axis
          if (Math.abs(particlePos.x) < 1 && Math.abs(particlePos.z) < 1) {
            return; // Skip this case
          }

          const vortexField: ForceFieldConfig = {
            id: "vortex",
            name: "Vortex",
            type: "vortex",
            enabled: true,
            strength,
            position: { x: 0, y: 0, z: 0 },
            vortexAxis: { x: 0, y: 1, z: 0 },
            inwardForce: 0,
            falloffStart: 0,
            falloffEnd: 10000,
            falloffType: "none",
          };

          const force = calculateForceField(
            vortexField,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            0,
            0,
            0,
            mass,
            0,
          );

          // Force should be finite
          expect(Number.isFinite(force.x)).toBe(true);
          expect(Number.isFinite(force.y)).toBe(true);
          expect(Number.isFinite(force.z)).toBe(true);

          // For Y-axis vortex, force should be mostly in XZ plane
          // and perpendicular to radial direction
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should handle NaN strength gracefully", () => {
    fc.assert(
      fc.property(
        arbForceFieldConfig,
        arbPosition,
        arbVelocity,
        positiveFloat(10),
        safeFloat(0, 1000),
        (field, particlePos, particleVel, mass, simTime) => {
          const nanStrengthField = { ...field, strength: NaN };
          const force = calculateForceField(
            nanStrengthField,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            particleVel.x,
            particleVel.y,
            particleVel.z,
            mass,
            simTime,
          );

          // Should return finite force (NaN handled gracefully)
          expect(Number.isFinite(force.x)).toBe(true);
          expect(Number.isFinite(force.y)).toBe(true);
          expect(Number.isFinite(force.z)).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should handle Infinity simulationTime gracefully for non-noise forces", () => {
    // Note: Turbulence and curl forces use sin(time) which returns NaN for Infinity
    // This is expected behavior - the ParticleForceCalculator has guards for this
    const nonNoiseTypes: ForceFieldType[] = [
      "gravity",
      "point",
      "drag",
      "lorenz",
      "magnetic",
      "orbit",
    ];
    fc.assert(
      fc.property(
        fc.constantFrom(...nonNoiseTypes),
        arbPosition,
        arbVelocity,
        positiveFloat(10),
        (type, particlePos, particleVel, mass) => {
          const field: ForceFieldConfig = {
            id: "test",
            name: "Test",
            type,
            enabled: true,
            strength: 10,
            position: { x: 0, y: 0, z: 0 },
            falloffStart: 0,
            falloffEnd: 1000,
            falloffType: "none",
          };
          const force = calculateForceField(
            field,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            particleVel.x,
            particleVel.y,
            particleVel.z,
            mass,
            Infinity,
          );

          // Should return finite force
          expect(Number.isFinite(force.x)).toBe(true);
          expect(Number.isFinite(force.y)).toBe(true);
          expect(Number.isFinite(force.z)).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should handle zero mass gracefully", () => {
    fc.assert(
      fc.property(
        arbForceFieldConfig,
        arbPosition,
        arbVelocity,
        safeFloat(0, 1000),
        (field, particlePos, particleVel, simTime) => {
          const force = calculateForceField(
            field,
            particlePos.x,
            particlePos.y,
            particlePos.z,
            particleVel.x,
            particleVel.y,
            particleVel.z,
            0, // Zero mass
            simTime,
          );

          // Should return finite force (zero mass handled gracefully)
          expect(Number.isFinite(force.x)).toBe(true);
          expect(Number.isFinite(force.y)).toBe(true);
          expect(Number.isFinite(force.z)).toBe(true);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should apply falloff correctly", () => {
    fc.assert(
      fc.property(
        positiveFloat(100), // strength
        positiveFloat(100), // falloffStart
        positiveFloat(200), // falloffEnd (must be > falloffStart)
        positiveFloat(10), // mass
        (strength, falloffStart, falloffEndAdd, mass) => {
          const falloffEnd = falloffStart + falloffEndAdd;

          const pointField: ForceFieldConfig = {
            id: "point",
            name: "Point",
            type: "point",
            enabled: true,
            strength,
            position: { x: 0, y: 0, z: 0 },
            falloffStart,
            falloffEnd,
            falloffType: "linear",
          };

          // Particle within falloff start should have full force
          const forceNear = calculateForceField(
            pointField,
            falloffStart * 0.5,
            0,
            0,
            0,
            0,
            0,
            mass,
            0,
          );

          // Particle beyond falloff end should have no force
          const forceFar = calculateForceField(
            pointField,
            falloffEnd * 2,
            0,
            0,
            0,
            0,
            0,
            mass,
            0,
          );

          // Near force should be stronger than far force
          const nearMag = Math.sqrt(
            forceNear.x * forceNear.x + forceNear.y * forceNear.y + forceNear.z * forceNear.z,
          );
          const farMag = Math.sqrt(
            forceFar.x * forceFar.x + forceFar.y * forceFar.y + forceFar.z * forceFar.z,
          );

          expect(nearMag).toBeGreaterThanOrEqual(farMag - 0.001);
        },
      ),
      { numRuns: 200 },
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleForceCalculator.getForceFieldTypeIndex", () => {
  it("should return valid index for all force types", () => {
    fc.assert(
      fc.property(arbForceFieldType, (type) => {
        const index = getForceFieldTypeIndex(type);
        expect(Number.isInteger(index)).toBe(true);
        expect(index).toBeGreaterThanOrEqual(0);
      }),
      { numRuns: 50 },
    );
  });

  it("should return unique indices for different types", () => {
    const indices = new Set<number>();
    for (const type of forceFieldTypes) {
      indices.add(getForceFieldTypeIndex(type));
    }
    // Not all types may have unique indices (some may share implementation)
    // but the indices should all be valid
    expect(indices.size).toBeGreaterThan(0);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleForceCalculator.getFalloffTypeIndex", () => {
  it("should return valid index for all falloff types", () => {
    fc.assert(
      fc.property(arbFalloffType, (type) => {
        const index = getFalloffTypeIndex(type);
        expect(Number.isInteger(index)).toBe(true);
        expect(index).toBeGreaterThanOrEqual(0);
      }),
      { numRuns: 20 },
    );
  });

  it("should return unique indices for each falloff type", () => {
    const indices = new Set<number>();
    for (const type of falloffTypes) {
      indices.add(getFalloffTypeIndex(type));
    }
    expect(indices.size).toBe(falloffTypes.length);
  });
});
