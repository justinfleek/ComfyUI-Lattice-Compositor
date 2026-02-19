/**
 * Property Tests for ParticleCollisionSystem.ts
 *
 * Comprehensive fast-check property tests for:
 * - Boundary collision handling
 * - Particle-particle collisions
 * - Plane collisions
 * - Energy conservation
 *
 * Tests verify:
 * - No NaN/Infinity in particle buffers after collision
 * - Particles stay within bounds after collision
 * - Bounce behavior conserves energy (with damping)
 * - Kill behavior removes particles properly
 * - Wrap behavior wraps particles correctly
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import {
  ParticleCollisionSystem,
  type CollisionConfig,
  type BoundsBehavior,
} from "@/engine/particles/ParticleCollisionSystem";
import { PARTICLE_STRIDE } from "@/engine/particles/types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                              // arbitraries
// ═══════════════════════════════════════════════════════════════════════════

const safeFloat = (min = -10000, max = 10000) =>
  fc.float({ min: Math.fround(min), max: Math.fround(max), noNaN: true });

const positiveFloat = (max = 1000) =>
  fc.float({ min: Math.fround(0.001), max: Math.fround(max), noNaN: true });

const boundsBehaviors: BoundsBehavior[] = ["none", "kill", "bounce", "wrap", "clamp", "stick"];
const arbBoundsBehavior = fc.constantFrom(...boundsBehaviors);

const arbBounds = fc.record({
  min: fc.record({
    x: safeFloat(-1000, 0),
    y: safeFloat(-1000, 0),
    z: safeFloat(-1000, 0),
  }),
  max: fc.record({
    x: safeFloat(0, 1000),
    y: safeFloat(0, 1000),
    z: safeFloat(0, 1000),
  }),
});

const arbCollisionPlane = fc.record({
  id: fc.uuid(),
  enabled: fc.boolean(),
  point: fc.record({
    x: safeFloat(-500, 500),
    y: safeFloat(-500, 500),
    z: safeFloat(-500, 500),
  }),
  normal: fc.record({
    x: safeFloat(-1, 1),
    y: safeFloat(-1, 1),
    z: safeFloat(-1, 1),
  }),
  bounciness: fc.float({ min: 0, max: 1, noNaN: true }),
  friction: fc.float({ min: 0, max: 1, noNaN: true }),
});

const arbCollisionConfig: fc.Arbitrary<CollisionConfig> = fc.record({
  enabled: fc.constant(true),
  bounds: arbBounds,
  boundsBehavior: arbBoundsBehavior,
  bounceDamping: fc.float({ min: 0, max: 1, noNaN: true }),
  particleCollision: fc.boolean(),
  particleRadius: positiveFloat(20),
  collisionResponse: fc.float({ min: 0, max: 1, noNaN: true }),
  bounciness: fc.float({ min: 0, max: 1, noNaN: true }),
  friction: fc.float({ min: 0, max: 1, noNaN: true }),
  planes: fc.array(arbCollisionPlane, { minLength: 0, maxLength: 5 }),
});

// Create a particle buffer with specific particle count
function createParticleBuffer(count: number): Float32Array {
  return new Float32Array(count * PARTICLE_STRIDE);
}

// Initialize a particle at a specific index
function initParticle(
  buffer: Float32Array,
  index: number,
  pos: { x: number; y: number; z: number },
  vel: { x: number; y: number; z: number },
  lifetime: number = 100,
  mass: number = 1,
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
  buffer[offset + 8] = mass;
  buffer[offset + 9] = 10; // size
  buffer[offset + 10] = 0; // rotation
  buffer[offset + 11] = 0; // angular velocity
  buffer[offset + 12] = 1; // r
  buffer[offset + 13] = 1; // g
  buffer[offset + 14] = 1; // b
  buffer[offset + 15] = 1; // a
}

// Get particle position from buffer
function getParticlePos(buffer: Float32Array, index: number): { x: number; y: number; z: number } {
  const offset = index * PARTICLE_STRIDE;
  return {
    x: buffer[offset + 0],
    y: buffer[offset + 1],
    z: buffer[offset + 2],
  };
}

// Get particle velocity from buffer
function getParticleVel(buffer: Float32Array, index: number): { x: number; y: number; z: number } {
  const offset = index * PARTICLE_STRIDE;
  return {
    x: buffer[offset + 3],
    y: buffer[offset + 4],
    z: buffer[offset + 5],
  };
}

// Get particle lifetime from buffer
function getParticleLifetime(buffer: Float32Array, index: number): number {
  const offset = index * PARTICLE_STRIDE;
  return buffer[offset + 7];
}

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: ParticleCollisionSystem Construction
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleCollisionSystem construction", () => {
  it("should handle any valid maxParticles", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 100000 }),
        arbCollisionConfig,
        (maxParticles, config) => {
          const system = new ParticleCollisionSystem(maxParticles, config);
          expect(system).toBeDefined();
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should clamp invalid maxParticles", () => {
    fc.assert(
      fc.property(
        fc.oneof(
          fc.constant(0),
          fc.constant(-100),
          fc.constant(Infinity),
          fc.constant(NaN),
        ),
        arbCollisionConfig,
        (invalidMaxParticles, config) => {
          // Should not throw, should handle gracefully
          const system = new ParticleCollisionSystem(invalidMaxParticles, config);
          expect(system).toBeDefined();
        },
      ),
      { numRuns: 20 },
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Boundary Collisions
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleCollisionSystem boundary collisions", () => {
  it("should never produce NaN positions after collision", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 100 }),
        arbCollisionConfig,
        fc.array(
          fc.record({
            pos: fc.record({
              x: safeFloat(-2000, 2000),
              y: safeFloat(-2000, 2000),
              z: safeFloat(-2000, 2000),
            }),
            vel: fc.record({
              x: safeFloat(-500, 500),
              y: safeFloat(-500, 500),
              z: safeFloat(-500, 500),
            }),
          }),
          { minLength: 1, maxLength: 50 },
        ),
        (maxParticles, config, particles) => {
          const system = new ParticleCollisionSystem(
            Math.max(maxParticles, particles.length),
            config,
          );
          const buffer = createParticleBuffer(Math.max(maxParticles, particles.length));

          // Initialize particles
          particles.forEach((p, i) => {
            initParticle(buffer, i, p.pos, p.vel);
          });

          // Apply collisions
          system.update(buffer);

          // Verify no NaN
          for (let i = 0; i < particles.length; i++) {
            const pos = getParticlePos(buffer, i);
            const vel = getParticleVel(buffer, i);

            expect(Number.isFinite(pos.x)).toBe(true);
            expect(Number.isFinite(pos.y)).toBe(true);
            expect(Number.isFinite(pos.z)).toBe(true);
            expect(Number.isFinite(vel.x)).toBe(true);
            expect(Number.isFinite(vel.y)).toBe(true);
            expect(Number.isFinite(vel.z)).toBe(true);
          }
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should keep particles within bounds for 'clamp' behavior", () => {
    fc.assert(
      fc.property(
        arbBounds,
        fc.array(
          fc.record({
            pos: fc.record({
              x: safeFloat(-2000, 2000),
              y: safeFloat(-2000, 2000),
              z: safeFloat(-2000, 2000),
            }),
            vel: fc.record({
              x: safeFloat(-500, 500),
              y: safeFloat(-500, 500),
              z: safeFloat(-500, 500),
            }),
          }),
          { minLength: 1, maxLength: 20 },
        ),
        (bounds, particles) => {
          const config: CollisionConfig = {
            enabled: true,
            bounds,
            boundsBehavior: "clamp",
            bounceDamping: 0.5,
            particleCollision: false,
            particleRadius: 5,
            collisionResponse: 0.5,
            bounciness: 0.5,
            friction: 0.1,
            planes: [],
          };

          const system = new ParticleCollisionSystem(particles.length, config);
          const buffer = createParticleBuffer(particles.length);

          // Initialize particles
          particles.forEach((p, i) => {
            initParticle(buffer, i, p.pos, p.vel);
          });

          // Apply collisions
          system.update(buffer);

          // Verify particles are within bounds
          for (let i = 0; i < particles.length; i++) {
            const pos = getParticlePos(buffer, i);

            expect(pos.x).toBeGreaterThanOrEqual(bounds.min.x - 0.001);
            expect(pos.x).toBeLessThanOrEqual(bounds.max.x + 0.001);
            expect(pos.y).toBeGreaterThanOrEqual(bounds.min.y - 0.001);
            expect(pos.y).toBeLessThanOrEqual(bounds.max.y + 0.001);
            expect(pos.z).toBeGreaterThanOrEqual(bounds.min.z - 0.001);
            expect(pos.z).toBeLessThanOrEqual(bounds.max.z + 0.001);
          }
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should kill particles outside bounds for 'kill' behavior", () => {
    // Use fixed bounds to ensure valid test
    const bounds = {
      min: { x: -100, y: -100, z: -100 },
      max: { x: 100, y: 100, z: 100 },
    };

    fc.assert(
      fc.property(
        fc.array(
          fc.record({
            pos: fc.record({
              // Position far outside bounds
              x: fc.oneof(
                fc.float({ min: Math.fround(-500), max: Math.fround(-200), noNaN: true }),
                fc.float({ min: Math.fround(200), max: Math.fround(500), noNaN: true }),
              ),
              y: fc.float({ min: Math.fround(-50), max: Math.fround(50), noNaN: true }),
              z: fc.float({ min: Math.fround(-50), max: Math.fround(50), noNaN: true }),
            }),
            vel: fc.record({
              x: safeFloat(-100, 100),
              y: safeFloat(-100, 100),
              z: safeFloat(-100, 100),
            }),
          }),
          { minLength: 1, maxLength: 10 },
        ),
        (particles) => {
          const config: CollisionConfig = {
            enabled: true,
            bounds,
            boundsBehavior: "kill",
            bounceDamping: 0.5,
            particleCollision: false,
            particleRadius: 5,
            collisionResponse: 0.5,
            bounciness: 0.5,
            friction: 0.1,
            planes: [],
          };

          const system = new ParticleCollisionSystem(particles.length, config);
          const buffer = createParticleBuffer(particles.length);

          // Initialize particles outside bounds (in X)
          particles.forEach((p, i) => {
            initParticle(buffer, i, p.pos, p.vel, 100);
          });

          // Apply collisions
          system.update(buffer);

          // Verify all particles are killed (age >= lifetime)
          // The kill behavior sets age = lifetime to mark particle as dead
          for (let i = 0; i < particles.length; i++) {
            const offset = i * PARTICLE_STRIDE;
            const age = buffer[offset + 6];
            const lifetime = buffer[offset + 7];
            expect(age).toBeGreaterThanOrEqual(lifetime);
          }
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should wrap particles for 'wrap' behavior", () => {
    fc.assert(
      fc.property(
        fc.record({
          min: fc.record({
            x: fc.constant(-100),
            y: fc.constant(-100),
            z: fc.constant(-100),
          }),
          max: fc.record({
            x: fc.constant(100),
            y: fc.constant(100),
            z: fc.constant(100),
          }),
        }),
        fc.array(
          fc.record({
            pos: fc.record({
              x: fc.float({ min: Math.fround(-200), max: Math.fround(200), noNaN: true }),
              y: fc.float({ min: Math.fround(-200), max: Math.fround(200), noNaN: true }),
              z: fc.float({ min: Math.fround(-200), max: Math.fround(200), noNaN: true }),
            }),
            vel: fc.record({
              x: fc.constant(0),
              y: fc.constant(0),
              z: fc.constant(0),
            }),
          }),
          { minLength: 1, maxLength: 10 },
        ),
        (bounds, particles) => {
          const config: CollisionConfig = {
            enabled: true,
            bounds,
            boundsBehavior: "wrap",
            bounceDamping: 0.5,
            particleCollision: false,
            particleRadius: 5,
            collisionResponse: 0.5,
            bounciness: 0.5,
            friction: 0.1,
            planes: [],
          };

          const system = new ParticleCollisionSystem(particles.length, config);
          const buffer = createParticleBuffer(particles.length);

          // Initialize particles
          particles.forEach((p, i) => {
            initParticle(buffer, i, p.pos, p.vel);
          });

          // Apply collisions
          system.update(buffer);

          // Verify particles are within bounds (wrapped)
          for (let i = 0; i < particles.length; i++) {
            const pos = getParticlePos(buffer, i);

            expect(pos.x).toBeGreaterThanOrEqual(bounds.min.x - 0.001);
            expect(pos.x).toBeLessThanOrEqual(bounds.max.x + 0.001);
            expect(pos.y).toBeGreaterThanOrEqual(bounds.min.y - 0.001);
            expect(pos.y).toBeLessThanOrEqual(bounds.max.y + 0.001);
            expect(pos.z).toBeGreaterThanOrEqual(bounds.min.z - 0.001);
            expect(pos.z).toBeLessThanOrEqual(bounds.max.z + 0.001);
          }
        },
      ),
      { numRuns: 200 },
    );
  });

  it("should bounce particles for 'bounce' behavior", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(0.1), max: Math.fround(1), noNaN: true }),
        fc.float({ min: Math.fround(100), max: Math.fround(500), noNaN: true }),
        (bounceDamping, speed) => {
          const bounds = {
            min: { x: -100, y: -100, z: -100 },
            max: { x: 100, y: 100, z: 100 },
          };

          const config: CollisionConfig = {
            enabled: true,
            bounds,
            boundsBehavior: "bounce",
            bounceDamping,
            particleCollision: false,
            particleRadius: 5,
            collisionResponse: 0.5,
            bounciness: 0.5,
            friction: 0.1,
            planes: [],
          };

          const system = new ParticleCollisionSystem(1, config);
          const buffer = createParticleBuffer(1);

          // Particle moving toward wall
          initParticle(buffer, 0, { x: 110, y: 0, z: 0 }, { x: speed, y: 0, z: 0 });

          // Apply collisions
          system.update(buffer);

          const pos = getParticlePos(buffer, 0);
          const vel = getParticleVel(buffer, 0);

          // Position should be within bounds after bounce
          expect(pos.x).toBeLessThanOrEqual(bounds.max.x + 0.001);

          // Velocity should have reversed direction (negative X)
          expect(vel.x).toBeLessThan(0);
        },
      ),
      { numRuns: 100 },
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Particle-Particle Collisions
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleCollisionSystem particle-particle collisions", () => {
  it("should not produce NaN when particles collide", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(5), max: Math.fround(50), noNaN: true }),
        fc.float({ min: Math.fround(0.1), max: Math.fround(1), noNaN: true }),
        fc.integer({ min: 2, max: 20 }),
        (particleRadius, response, particleCount) => {
          const config: CollisionConfig = {
            enabled: true,
            bounds: {
              min: { x: -1000, y: -1000, z: -1000 },
              max: { x: 1000, y: 1000, z: 1000 },
            },
            boundsBehavior: "none",
            bounceDamping: 0.8,
            particleCollision: true,
            particleRadius,
            collisionResponse: response,
            bounciness: 0.5,
            friction: 0.1,
            planes: [],
          };

          const system = new ParticleCollisionSystem(particleCount, config);
          const buffer = createParticleBuffer(particleCount);

          // Create particles very close together to force collisions
          for (let i = 0; i < particleCount; i++) {
            initParticle(
              buffer,
              i,
              { x: i * particleRadius * 0.5, y: 0, z: 0 },
              { x: (i % 2 === 0 ? 1 : -1) * 50, y: 0, z: 0 },
            );
          }

          // Apply collisions multiple times
          for (let frame = 0; frame < 10; frame++) {
            system.update(buffer);
          }

          // Verify no NaN
          for (let i = 0; i < particleCount; i++) {
            const pos = getParticlePos(buffer, i);
            const vel = getParticleVel(buffer, i);

            expect(Number.isFinite(pos.x)).toBe(true);
            expect(Number.isFinite(pos.y)).toBe(true);
            expect(Number.isFinite(pos.z)).toBe(true);
            expect(Number.isFinite(vel.x)).toBe(true);
            expect(Number.isFinite(vel.y)).toBe(true);
            expect(Number.isFinite(vel.z)).toBe(true);
          }
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should separate overlapping particles", () => {
    const config: CollisionConfig = {
      enabled: true,
      bounds: {
        min: { x: -1000, y: -1000, z: -1000 },
        max: { x: 1000, y: 1000, z: 1000 },
      },
      boundsBehavior: "none",
      bounceDamping: 0.8,
      particleCollision: true,
      particleRadius: 10,
      collisionResponse: 1,
      bounciness: 0.5,
      friction: 0.1,
      planes: [],
    };

    fc.assert(
      fc.property(fc.float({ min: 1, max: 8, noNaN: true }), (separation) => {
        const system = new ParticleCollisionSystem(2, config);
        const buffer = createParticleBuffer(2);

        // Two particles very close together
        initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });
        initParticle(buffer, 1, { x: separation, y: 0, z: 0 }, { x: 0, y: 0, z: 0 });

        // Apply collisions
        system.update(buffer);

        const pos0 = getParticlePos(buffer, 0);
        const pos1 = getParticlePos(buffer, 1);

        // Particles should be pushed apart
        const dist = Math.sqrt(
          (pos1.x - pos0.x) ** 2 + (pos1.y - pos0.y) ** 2 + (pos1.z - pos0.z) ** 2,
        );

        // After collision response, particles should be at least as far apart as before
        // (or further if they were overlapping)
        expect(dist).toBeGreaterThanOrEqual(separation - 0.001);
      }),
      { numRuns: 50 },
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Plane Collisions
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleCollisionSystem plane collisions", () => {
  it("should bounce particles off planes", () => {
    // Simple deterministic test for plane bouncing
    const config: CollisionConfig = {
      enabled: true,
      bounds: {
        min: { x: -1000, y: -1000, z: -1000 },
        max: { x: 1000, y: 1000, z: 1000 },
      },
      boundsBehavior: "none",
      bounceDamping: 0.8,
      particleCollision: false,
      particleRadius: 5,
      collisionResponse: 0.5,
      bounciness: 0.5,
      friction: 0.1,
      planes: [
        {
          id: "floor-plane",
          enabled: true,
          point: { x: 0, y: 0, z: 0 },
          normal: { x: 0, y: 1, z: 0 }, // Floor at Y=0
          bounciness: 0.5,
          friction: 0.1,
        },
      ],
    };

    const system = new ParticleCollisionSystem(1, config);
    const buffer = createParticleBuffer(1);

    // Particle below floor, moving down
    initParticle(buffer, 0, { x: 0, y: -2, z: 0 }, { x: 0, y: -100, z: 0 });

    // Apply collisions
    system.update(buffer);

    const pos = getParticlePos(buffer, 0);
    const vel = getParticleVel(buffer, 0);

    // After bounce:
    // - velocity Y should be positive (bounced up)
    // - position Y should be at or above floor (pushed out by particleRadius)
    expect(vel.y).toBeGreaterThan(0);
    expect(pos.y).toBeGreaterThanOrEqual(0);
  });

  it("should handle zero-length normal gracefully", () => {
    const config: CollisionConfig = {
      enabled: true,
      bounds: {
        min: { x: -1000, y: -1000, z: -1000 },
        max: { x: 1000, y: 1000, z: 1000 },
      },
      boundsBehavior: "none",
      bounceDamping: 0.8,
      particleCollision: false,
      particleRadius: 5,
      collisionResponse: 0.5,
      bounciness: 0.5,
      friction: 0.1,
      planes: [
        {
          id: "zero-normal-plane",
          enabled: true,
          point: { x: 0, y: 0, z: 0 },
          normal: { x: 0, y: 0, z: 0 }, // Zero normal
          bounciness: 0.5,
          friction: 0.1,
        },
      ],
    };

    fc.assert(
      fc.property(
        fc.record({
          x: safeFloat(-100, 100),
          y: safeFloat(-100, 100),
          z: safeFloat(-100, 100),
        }),
        fc.record({
          x: safeFloat(-100, 100),
          y: safeFloat(-100, 100),
          z: safeFloat(-100, 100),
        }),
        (pos, vel) => {
          const system = new ParticleCollisionSystem(1, config);
          const buffer = createParticleBuffer(1);

          initParticle(buffer, 0, pos, vel);

          // Should not throw or produce NaN
          system.update(buffer);

          const newPos = getParticlePos(buffer, 0);
          const newVel = getParticleVel(buffer, 0);

          expect(Number.isFinite(newPos.x)).toBe(true);
          expect(Number.isFinite(newPos.y)).toBe(true);
          expect(Number.isFinite(newPos.z)).toBe(true);
          expect(Number.isFinite(newVel.x)).toBe(true);
          expect(Number.isFinite(newVel.y)).toBe(true);
          expect(Number.isFinite(newVel.z)).toBe(true);
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// TESTS: Energy Conservation
// ═══════════════════════════════════════════════════════════════════════════

describe("ParticleCollisionSystem energy conservation", () => {
  it("should reduce energy with damping", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(0.5), max: Math.fround(0.95), noNaN: true }),
        fc.float({ min: Math.fround(100), max: Math.fround(500), noNaN: true }),
        (damping, speed) => {
          const config: CollisionConfig = {
            enabled: true,
            bounds: {
              min: { x: -100, y: -100, z: -100 },
              max: { x: 100, y: 100, z: 100 },
            },
            boundsBehavior: "bounce",
            bounceDamping: damping,
            particleCollision: false,
            particleRadius: 5,
            collisionResponse: 0.5,
            bounciness: 0.5,
            friction: 0.1,
            planes: [],
          };

          const system = new ParticleCollisionSystem(1, config);
          const buffer = createParticleBuffer(1);

          // Particle moving fast toward wall
          initParticle(buffer, 0, { x: 90, y: 0, z: 0 }, { x: speed, y: 0, z: 0 });

          const velBefore = getParticleVel(buffer, 0);
          const energyBefore = velBefore.x ** 2 + velBefore.y ** 2 + velBefore.z ** 2;

          // Apply collision
          system.update(buffer);

          const velAfter = getParticleVel(buffer, 0);
          const energyAfter = velAfter.x ** 2 + velAfter.y ** 2 + velAfter.z ** 2;

          // Energy should decrease after bounce (damping)
          expect(energyAfter).toBeLessThanOrEqual(energyBefore + 0.001);
        },
      ),
      { numRuns: 100 },
    );
  });
});
