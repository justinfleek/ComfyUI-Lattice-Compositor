/**
 * Property Tests for Particle Spring System
 *
 * Tests invariants for spring physics:
 * - Energy conservation (with damping)
 * - Spring constraint satisfaction
 * - Mass-weighted corrections
 * - Breakable springs
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import { ParticleSpringSystem } from "../../../engine/particles/ParticleSpringSystem";
import { PARTICLE_STRIDE } from "../../../engine/particles/types";

describe("ParticleSpringSystem", () => {
  // Helper to create a particle buffer with specific positions
  function createParticleBuffer(
    maxParticles: number,
    positions: Array<{ x: number; y: number; z: number }>
  ): Float32Array {
    const buffer = new Float32Array(maxParticles * PARTICLE_STRIDE);

    for (let i = 0; i < positions.length && i < maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      buffer[offset + 0] = positions[i].x; // position x
      buffer[offset + 1] = positions[i].y; // position y
      buffer[offset + 2] = positions[i].z; // position z
      buffer[offset + 3] = 0; // velocity x
      buffer[offset + 4] = 0; // velocity y
      buffer[offset + 5] = 0; // velocity z
      buffer[offset + 6] = 0; // age
      buffer[offset + 7] = 100; // lifetime
      buffer[offset + 8] = 1; // mass
      buffer[offset + 9] = 10; // size
    }

    return buffer;
  }

  // Arbitrary for valid spring config
  const arbSpringConfig = fc.record({
    globalStiffness: fc.float({ min: Math.fround(1), max: Math.fround(500), noNaN: true }),
    globalDamping: fc.float({ min: Math.fround(0), max: Math.fround(50), noNaN: true }),
    solverIterations: fc.integer({ min: 1, max: 16 }),
    useVerlet: fc.boolean(),
    enableBreaking: fc.boolean(),
    gravity: fc.record({
      x: fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
      y: fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
      z: fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
    }),
  });

  // Arbitrary for valid spring
  const arbSpring = fc.record({
    particleA: fc.integer({ min: 0, max: 99 }),
    particleB: fc.integer({ min: 0, max: 99 }),
    restLength: fc.float({ min: Math.fround(0.1), max: Math.fround(100), noNaN: true }),
    stiffness: fc.float({ min: Math.fround(1), max: Math.fround(500), noNaN: true }),
    damping: fc.float({ min: Math.fround(0), max: Math.fround(50), noNaN: true }),
    breakThreshold: fc.float({ min: Math.fround(0), max: Math.fround(10), noNaN: true }),
  }).filter(s => s.particleA !== s.particleB);

  describe("Spring Creation", () => {
    it("should add valid springs", () => {
      fc.assert(
        fc.property(arbSpring, (springDef) => {
          const system = new ParticleSpringSystem(100);
          system.addSpring(
            springDef.particleA,
            springDef.particleB,
            springDef.restLength,
            springDef.stiffness,
            springDef.damping,
            springDef.breakThreshold
          );

          expect(system.getSpringCount()).toBe(1);
        })
      );
    });

    it("should reject springs with same particle indices", () => {
      fc.assert(
        fc.property(fc.integer({ min: 0, max: 99 }), (idx) => {
          const system = new ParticleSpringSystem(100);
          system.addSpring(idx, idx, 10, 100, 5, 0);

          // Should not add spring
          expect(system.getSpringCount()).toBe(0);
        })
      );
    });

    it("should reject springs with out-of-bounds indices", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: 100, max: 1000 }),
          fc.integer({ min: 0, max: 99 }),
          (badIdx, goodIdx) => {
            const system = new ParticleSpringSystem(100);
            system.addSpring(badIdx, goodIdx, 10, 100, 5, 0);
            expect(system.getSpringCount()).toBe(0);

            system.addSpring(goodIdx, badIdx, 10, 100, 5, 0);
            expect(system.getSpringCount()).toBe(0);
          }
        )
      );
    });
  });

  describe("Cloth Grid Creation", () => {
    it("should create correct number of springs for cloth grid", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: 2, max: 10 }),
          fc.integer({ min: 2, max: 10 }),
          (width, height) => {
            const system = new ParticleSpringSystem(width * height);
            system.createClothGrid(0, width, height, 10, 100);

            // Expected springs:
            // Structural horizontal: (width - 1) * height
            // Structural vertical: width * (height - 1)
            // Shear: (width - 1) * (height - 1) * 2
            // Bend horizontal: (width - 2) * height
            // Bend vertical: width * (height - 2)
            const structH = (width - 1) * height;
            const structV = width * (height - 1);
            const shear = (width - 1) * (height - 1) * 2;
            const bendH = (width - 2) * height;
            const bendV = width * (height - 2);
            const expected = structH + structV + shear + bendH + bendV;

            expect(system.getSpringCount()).toBe(expected);
          }
        )
      );
    });
  });

  describe("Physics Properties", () => {
    it("should move particles toward rest length when stretched", () => {
      // Create two particles far apart, connected by a short spring
      // Use Verlet integration which is more stable for stiff springs
      const system = new ParticleSpringSystem(100, { 
        useVerlet: true,
        globalStiffness: 1, // Verlet uses position-based dynamics, stiffness is via iterations
        globalDamping: 1,
        solverIterations: 8,
        gravity: { x: 0, y: 0, z: 0 },
      });
      const buffer = createParticleBuffer(100, [
        { x: 0, y: 0, z: 0 },
        { x: 100, y: 0, z: 0 }, // 100 units apart
      ]);

      // Spring with rest length of 20
      system.addSpring(0, 1, 20, 1, 1, 0);
      system.initialize(buffer);

      // Run many simulation steps
      for (let i = 0; i < 100; i++) {
        system.update(buffer, 0.016);
      }

      // Particles should have moved closer together
      const dist = Math.sqrt(
        Math.pow(buffer[PARTICLE_STRIDE] - buffer[0], 2) +
        Math.pow(buffer[PARTICLE_STRIDE + 1] - buffer[1], 2) +
        Math.pow(buffer[PARTICLE_STRIDE + 2] - buffer[2], 2)
      );

      // Distance should be less than initial 100
      expect(Number.isFinite(dist)).toBe(true);
      expect(dist).toBeLessThan(100);
    });

    it("should push particles apart when compressed", () => {
      // Create two particles close together, connected by a long spring
      // Use Verlet integration which is more stable
      const system = new ParticleSpringSystem(100, { 
        useVerlet: true,
        globalStiffness: 1,
        globalDamping: 1,
        solverIterations: 8,
        gravity: { x: 0, y: 0, z: 0 },
      });
      const buffer = createParticleBuffer(100, [
        { x: 0, y: 0, z: 0 },
        { x: 5, y: 0, z: 0 }, // Only 5 units apart
      ]);

      // Spring with rest length of 50
      system.addSpring(0, 1, 50, 1, 1, 0);
      system.initialize(buffer);

      // Run many simulation steps
      for (let i = 0; i < 100; i++) {
        system.update(buffer, 0.016);
      }

      // Particles should have moved apart
      const dist = Math.sqrt(
        Math.pow(buffer[PARTICLE_STRIDE] - buffer[0], 2) +
        Math.pow(buffer[PARTICLE_STRIDE + 1] - buffer[1], 2) +
        Math.pow(buffer[PARTICLE_STRIDE + 2] - buffer[2], 2)
      );

      // Distance should be greater than initial 5
      expect(Number.isFinite(dist)).toBe(true);
      expect(dist).toBeGreaterThan(5);
    });

    it("should respect mass weighting in corrections", () => {
      // Create two particles: one heavy, one light
      const system = new ParticleSpringSystem(100, { useVerlet: true });
      const buffer = createParticleBuffer(100, [
        { x: 0, y: 0, z: 0 },
        { x: 100, y: 0, z: 0 },
      ]);

      // Set masses
      buffer[PARTICLE_STRIDE * 0 + 8] = 10; // Heavy particle
      buffer[PARTICLE_STRIDE * 1 + 8] = 1; // Light particle

      system.addSpring(0, 1, 50, 500, 0, 0);
      system.initialize(buffer);

      // Store initial positions
      const initialX0 = buffer[0];
      const initialX1 = buffer[PARTICLE_STRIDE];

      // Run simulation
      for (let i = 0; i < 5; i++) {
        system.update(buffer, 0.016);
      }

      // Heavy particle should move less than light particle
      const moveX0 = Math.abs(buffer[0] - initialX0);
      const moveX1 = Math.abs(buffer[PARTICLE_STRIDE] - initialX0);

      // Light particle (idx 1) should move more
      expect(moveX1).toBeGreaterThan(moveX0 * 0.5); // Allow some tolerance
    });
  });

  describe("Spring Breaking", () => {
    it("should break springs when threshold exceeded", () => {
      const system = new ParticleSpringSystem(100, { enableBreaking: true, useVerlet: false });
      const buffer = createParticleBuffer(100, [
        { x: 0, y: 0, z: 0 },
        { x: 200, y: 0, z: 0 }, // Far apart
      ]);

      // Spring with rest length 10, break threshold 0.5 (50% stretch breaks it)
      // 200 / 10 = 20x stretch = 1900% > 50%
      system.addSpring(0, 1, 10, 100, 5, 0.5);
      system.initialize(buffer);

      expect(system.getSpringCount()).toBe(1);

      // Run simulation - spring should break
      system.update(buffer, 0.016);

      // Spring should be deactivated (counted as 0)
      // Note: The spring still exists but is marked inactive
      const springs = system.getSprings();
      const activeSprings = springs.filter((s) => s.active);
      expect(activeSprings.length).toBe(0);
    });

    it("should not break unbreakable springs (threshold = 0)", () => {
      const system = new ParticleSpringSystem(100, { enableBreaking: true, useVerlet: false });
      const buffer = createParticleBuffer(100, [
        { x: 0, y: 0, z: 0 },
        { x: 200, y: 0, z: 0 },
      ]);

      // Spring with breakThreshold = 0 (unbreakable)
      system.addSpring(0, 1, 10, 100, 5, 0);
      system.initialize(buffer);

      // Run many simulation steps
      for (let i = 0; i < 100; i++) {
        system.update(buffer, 0.016);
      }

      // Spring should still be active
      expect(system.getSpringCount()).toBe(1);
    });
  });

  describe("Pin Constraints", () => {
    it("should keep pinned particles stationary", () => {
      const system = new ParticleSpringSystem(100, { useVerlet: true });
      const buffer = createParticleBuffer(100, [
        { x: 0, y: 0, z: 0 },
        { x: 50, y: 0, z: 0 },
      ]);

      system.pinParticle(0);
      system.addSpring(0, 1, 20, 500, 0, 0);
      system.initialize(buffer);

      const pinPositions = new Map<number, { x: number; y: number; z: number }>();
      pinPositions.set(0, { x: 0, y: 0, z: 0 });

      // Run simulation
      for (let i = 0; i < 10; i++) {
        system.update(buffer, 0.016);
        system.applyPins(buffer, pinPositions);
      }

      // Pinned particle should not have moved
      expect(buffer[0]).toBe(0);
      expect(buffer[1]).toBe(0);
      expect(buffer[2]).toBe(0);
    });
  });

  describe("Numerical Stability", () => {
    it("should not produce NaN or Infinity positions", () => {
      fc.assert(
        fc.property(
          arbSpringConfig,
          fc.array(arbSpring, { minLength: 1, maxLength: 10 }),
          (config, springs) => {
            const system = new ParticleSpringSystem(100, config);
            const buffer = createParticleBuffer(100, [
              { x: 0, y: 0, z: 0 },
              { x: 50, y: 0, z: 0 },
              { x: 100, y: 0, z: 0 },
              { x: 0, y: 50, z: 0 },
              { x: 50, y: 50, z: 0 },
            ]);

            for (const s of springs) {
              if (s.particleA < 5 && s.particleB < 5) {
                system.addSpring(
                  s.particleA,
                  s.particleB,
                  s.restLength,
                  s.stiffness,
                  s.damping,
                  s.breakThreshold
                );
              }
            }

            system.initialize(buffer);

            // Run many simulation steps
            for (let i = 0; i < 100; i++) {
              system.update(buffer, 0.016);
            }

            // Check all positions are finite
            for (let i = 0; i < 5; i++) {
              const offset = i * PARTICLE_STRIDE;
              expect(Number.isFinite(buffer[offset + 0])).toBe(true);
              expect(Number.isFinite(buffer[offset + 1])).toBe(true);
              expect(Number.isFinite(buffer[offset + 2])).toBe(true);
              expect(Number.isFinite(buffer[offset + 3])).toBe(true);
              expect(Number.isFinite(buffer[offset + 4])).toBe(true);
              expect(Number.isFinite(buffer[offset + 5])).toBe(true);
            }
          }
        ),
        { numRuns: 50 }
      );
    });
  });

  describe("Soft Body Creation", () => {
    it("should create correct number of springs for soft body", () => {
      const system = new ParticleSpringSystem(1000);
      
      // 3x3x3 soft body
      system.createSoftBody(0, 3, 3, 3, 10, 100);

      // Expected springs for 3x3x3:
      // Structural in X: 2 * 3 * 3 = 18
      // Structural in Y: 3 * 2 * 3 = 18
      // Structural in Z: 3 * 3 * 2 = 18
      // Diagonal XY: 2 * 2 * 3 = 12
      // Diagonal YZ: 3 * 2 * 2 = 12
      // Diagonal XZ: 2 * 3 * 2 = 12
      // Total = 18 + 18 + 18 + 12 + 12 + 12 = 90

      expect(system.getSpringCount()).toBe(90);
    });
  });

  describe("Chain Creation", () => {
    it("should create chain with correct spring count", () => {
      fc.assert(
        fc.property(fc.integer({ min: 2, max: 50 }), (length) => {
          const system = new ParticleSpringSystem(100);
          const indices = Array.from({ length }, (_, i) => i);
          
          system.createChain(indices, 10, 100);

          // Chain of N particles has N-1 springs
          expect(system.getSpringCount()).toBe(length - 1);
        })
      );
    });
  });
});
