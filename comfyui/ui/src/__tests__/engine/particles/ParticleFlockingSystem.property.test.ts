/**
 * Property Tests for ParticleFlockingSystem.ts
 *
 * Comprehensive fast-check property tests for:
 * - Construction
 * - Flocking behavior (separation, alignment, cohesion)
 * - Speed limiting
 * - NaN/Infinity handling
 * - Perception angle filtering
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import { ParticleFlockingSystem } from "@/engine/particles/ParticleFlockingSystem";
import { SpatialHashGrid } from "@/engine/particles/SpatialHashGrid";
import type { FlockingConfig } from "@/engine/particles/types";
import { PARTICLE_STRIDE } from "@/engine/particles/types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                  // helpers
// ═══════════════════════════════════════════════════════════════════════════

function createParticleBuffer(count: number): Float32Array {
  return new Float32Array(count * PARTICLE_STRIDE);
}

function initParticle(
  buffer: Float32Array,
  index: number,
  pos: { x: number; y: number; z: number },
  vel: { x: number; y: number; z: number } = { x: 0, y: 0, z: 0 },
  lifetime: number = 100,
): void {
  const offset = index * PARTICLE_STRIDE;
  buffer[offset + 0] = pos.x;
  buffer[offset + 1] = pos.y;
  buffer[offset + 2] = pos.z;
  buffer[offset + 3] = vel.x;
  buffer[offset + 4] = vel.y;
  buffer[offset + 5] = vel.z;
  buffer[offset + 6] = 0; // age
  buffer[offset + 7] = lifetime;
  buffer[offset + 8] = 1; // mass
  buffer[offset + 9] = 10; // size
  buffer[offset + 10] = 0; // rotation
  buffer[offset + 11] = 0; // angular velocity
  buffer[offset + 12] = 1; // r
  buffer[offset + 13] = 1; // g
  buffer[offset + 14] = 1; // b
  buffer[offset + 15] = 1; // a
}

function getVelocity(buffer: Float32Array, index: number): { x: number; y: number; z: number } {
  const offset = index * PARTICLE_STRIDE;
  return {
    x: buffer[offset + 3],
    y: buffer[offset + 4],
    z: buffer[offset + 5],
  };
}

function createDefaultConfig(): FlockingConfig {
  return {
    enabled: true,
    separationRadius: 50,
    alignmentRadius: 100,
    cohesionRadius: 150,
    separationWeight: 1.5,
    alignmentWeight: 1.0,
    cohesionWeight: 1.0,
    maxForce: 10,
    maxSpeed: 100,
    perceptionAngle: 360,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                              // arbitraries
// ═══════════════════════════════════════════════════════════════════════════

const safeFloat = (min = -10000, max = 10000) =>
  fc.float({ min: Math.fround(min), max: Math.fround(max), noNaN: true });

const positiveFloat = (max = 1000) =>
  fc.float({ min: Math.fround(0.01), max: Math.fround(max), noNaN: true });

const arbFlockingConfig: fc.Arbitrary<FlockingConfig> = fc.record({
  enabled: fc.boolean(),
  separationRadius: fc.oneof(positiveFloat(200), fc.constant(0), fc.constant(NaN)),
  alignmentRadius: fc.oneof(positiveFloat(200), fc.constant(0), fc.constant(NaN)),
  cohesionRadius: fc.oneof(positiveFloat(200), fc.constant(0), fc.constant(NaN)),
  separationWeight: fc.oneof(safeFloat(-10, 10), fc.constant(NaN)),
  alignmentWeight: fc.oneof(safeFloat(-10, 10), fc.constant(NaN)),
  cohesionWeight: fc.oneof(safeFloat(-10, 10), fc.constant(NaN)),
  maxForce: fc.oneof(positiveFloat(100), fc.constant(0), fc.constant(NaN)),
  maxSpeed: fc.oneof(positiveFloat(500), fc.constant(0), fc.constant(-10), fc.constant(NaN)),
  perceptionAngle: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(360), noNaN: true }),
    fc.constant(NaN),
  ),
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Construction
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleFlockingSystem construction", () => {
  it("should handle any maxParticles value", () => {
    fc.assert(
      fc.property(
        fc.oneof(
          fc.integer({ min: 1, max: 100000 }),
          fc.constant(0),
          fc.constant(-100),
          fc.constant(Infinity),
        ),
        arbFlockingConfig,
        (maxParticles, config) => {
          const system = new ParticleFlockingSystem(maxParticles, config);
          expect(system).toBeDefined();
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: applyFlocking
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleFlockingSystem.applyFlocking", () => {
  let system: ParticleFlockingSystem;
  let spatialHash: SpatialHashGrid;
  let buffer: Float32Array;

  beforeEach(() => {
    const config = createDefaultConfig();
    system = new ParticleFlockingSystem(10, config);
    spatialHash = new SpatialHashGrid({ cellSize: 100, maxParticles: 10 });
    system.setSpatialHash(spatialHash);
    buffer = createParticleBuffer(10);
  });

  it("should not modify dead particles", () => {
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 10, y: 0, z: 0 }, 0); // dead
    spatialHash.rebuild(buffer);

    system.applyFlocking(buffer, 0.016);

    // Velocity should be unchanged
    expect(getVelocity(buffer, 0)).toEqual({ x: 10, y: 0, z: 0 });
  });

  it("should not crash with NaN dt", () => {
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 10, y: 0, z: 0 });
    spatialHash.rebuild(buffer);

    expect(() => system.applyFlocking(buffer, NaN)).not.toThrow();

    // Should use default dt and produce finite results
    const vel = getVelocity(buffer, 0);
    expect(Number.isFinite(vel.x)).toBe(true);
    expect(Number.isFinite(vel.y)).toBe(true);
    expect(Number.isFinite(vel.z)).toBe(true);
  });

  it("should apply separation force when particles are close", () => {
    // Two particles very close together
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 10, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
    spatialHash.rebuild(buffer);

    system.applyFlocking(buffer, 0.1);

    // Particle 0 should be pushed away from particle 1 (negative x)
    const vel0 = getVelocity(buffer, 0);
    expect(vel0.x).toBeLessThan(0);
  });

  it("should limit velocity to maxSpeed", () => {
    const config = createDefaultConfig();
    config.maxSpeed = 10;
    system = new ParticleFlockingSystem(10, config);
    system.setSpatialHash(spatialHash);

    // Particle with high initial velocity
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 1000, y: 1000, z: 1000 });
    spatialHash.rebuild(buffer);

    system.applyFlocking(buffer, 0.016);

    const vel = getVelocity(buffer, 0);
    const speed = Math.sqrt(vel.x ** 2 + vel.y ** 2 + vel.z ** 2);
    expect(speed).toBeLessThanOrEqual(10.1); // Small tolerance for floating point
  });

  it("should not produce NaN with any config", () => {
    fc.assert(
      fc.property(arbFlockingConfig, (config) => {
        const sys = new ParticleFlockingSystem(10, config);
        const hash = new SpatialHashGrid({ cellSize: 100, maxParticles: 10 });
        sys.setSpatialHash(hash);

        const buf = createParticleBuffer(10);
        for (let i = 0; i < 5; i++) {
          initParticle(buf, i, { x: i * 20, y: 0, z: 0 }, { x: 10, y: 5, z: 0 });
        }
        hash.rebuild(buf);

        sys.applyFlocking(buf, 0.016);

        // All velocities should be finite
        for (let i = 0; i < 5; i++) {
          const vel = getVelocity(buf, i);
          expect(Number.isFinite(vel.x)).toBe(true);
          expect(Number.isFinite(vel.y)).toBe(true);
          expect(Number.isFinite(vel.z)).toBe(true);
        }
      }),
      { numRuns: 100 },
    );
  });

  it("should apply alignment force to match neighbor velocities", () => {
    const config = createDefaultConfig();
    config.separationWeight = 0;
    config.cohesionWeight = 0;
    config.alignmentWeight = 2;
    config.alignmentRadius = 200;
    system = new ParticleFlockingSystem(10, config);
    system.setSpatialHash(spatialHash);

    // Stationary particle near a moving particle
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 50, y: 0, z: 0 }, { x: 100, y: 0, z: 0 });
    spatialHash.rebuild(buffer);

    system.applyFlocking(buffer, 0.1);

    // Particle 0 should now have velocity in +x direction (matching neighbor)
    const vel0 = getVelocity(buffer, 0);
    expect(vel0.x).toBeGreaterThan(0);
  });

  it("should apply cohesion force toward group center", () => {
    const config = createDefaultConfig();
    config.separationWeight = 0;
    config.alignmentWeight = 0;
    config.cohesionWeight = 2;
    config.cohesionRadius = 200;
    system = new ParticleFlockingSystem(10, config);
    system.setSpatialHash(spatialHash);

    // Isolated particle far from group
    initParticle(buffer, 0, { x: -100, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 50, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 2, { x: 60, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
    spatialHash.rebuild(buffer);

    system.applyFlocking(buffer, 0.1);

    // Particle 0 should move toward group (+x direction)
    const vel0 = getVelocity(buffer, 0);
    expect(vel0.x).toBeGreaterThan(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Perception Angle
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleFlockingSystem perception angle", () => {
  it("should exclude neighbors outside field of view", () => {
    const config = createDefaultConfig();
    config.perceptionAngle = 90; // 45 degrees each side
    config.separationWeight = 1;
    config.alignmentWeight = 0;
    config.cohesionWeight = 0;
    const system = new ParticleFlockingSystem(10, config);
    const spatialHash = new SpatialHashGrid({ cellSize: 100, maxParticles: 10 });
    system.setSpatialHash(spatialHash);

    const buffer = createParticleBuffer(10);

    // Particle 0 moving in +x direction
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 10, y: 0, z: 0 });
    // Particle 1 BEHIND particle 0 (should be outside FOV)
    initParticle(buffer, 1, { x: -20, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
    spatialHash.rebuild(buffer);

    const vel0Before = { ...getVelocity(buffer, 0) };
    system.applyFlocking(buffer, 0.016);
    const vel0After = getVelocity(buffer, 0);

    // With 90 degree FOV, particle behind should not influence (no separation)
    // Velocity change should be minimal
    expect(Math.abs(vel0After.x - vel0Before.x)).toBeLessThan(0.1);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Accessors
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleFlockingSystem accessors", () => {
  it("should correctly toggle enabled state", () => {
    const config = createDefaultConfig();
    const system = new ParticleFlockingSystem(10, config);

    expect(system.isEnabled()).toBe(true);

    system.setEnabled(false);
    expect(system.isEnabled()).toBe(false);

    system.setEnabled(true);
    expect(system.isEnabled()).toBe(true);
  });

  it("should update config correctly", () => {
    const config = createDefaultConfig();
    const system = new ParticleFlockingSystem(10, config);

    system.updateConfig({ maxSpeed: 500, separationWeight: 3.0 });

    const updatedConfig = system.getConfig();
    expect(updatedConfig.maxSpeed).toBe(500);
    expect(updatedConfig.separationWeight).toBe(3.0);
    // Other values should be unchanged
    expect(updatedConfig.alignmentWeight).toBe(1.0);
  });

  it("should return a copy of config, not reference", () => {
    const config = createDefaultConfig();
    const system = new ParticleFlockingSystem(10, config);

    const retrieved = system.getConfig();
    retrieved.maxSpeed = 9999;

    // Original config should be unchanged
    expect(system.getConfig().maxSpeed).toBe(100);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: No spatial hash
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleFlockingSystem without spatial hash", () => {
  it("should not crash when spatial hash is not set", () => {
    const config = createDefaultConfig();
    const system = new ParticleFlockingSystem(10, config);

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });

    expect(() => system.applyFlocking(buffer, 0.016)).not.toThrow();
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Reset
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleFlockingSystem.reset", () => {
  it("should not crash on reset", () => {
    const config = createDefaultConfig();
    const system = new ParticleFlockingSystem(10, config);

    expect(() => system.reset()).not.toThrow();
  });
});
