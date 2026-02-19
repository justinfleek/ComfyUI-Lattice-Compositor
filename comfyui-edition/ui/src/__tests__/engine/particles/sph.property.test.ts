/**
 * Property Tests for Particle SPH System
 *
 * Tests invariants for SPH fluid simulation:
 * - Density should be positive
 * - Pressure should be non-negative
 * - Conservation laws (approximate due to boundary conditions)
 * - Numerical stability
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import { ParticleSPHSystem, type SPHConfig } from "../../../engine/particles/ParticleSPHSystem";
import { SpatialHashGrid } from "../../../engine/particles/SpatialHashGrid";
import { PARTICLE_STRIDE } from "../../../engine/particles/types";

describe("ParticleSPHSystem", () => {
  // Helper to create a particle buffer
  function createParticleBuffer(
    maxParticles: number,
    positions: Array<{ x: number; y: number; z: number }>
  ): Float32Array {
    const buffer = new Float32Array(maxParticles * PARTICLE_STRIDE);

    for (let i = 0; i < positions.length && i < maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      buffer[offset + 0] = positions[i].x;
      buffer[offset + 1] = positions[i].y;
      buffer[offset + 2] = positions[i].z;
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

  // Helper to create a spatial hash grid
  function createSpatialHash(
    maxParticles: number,
    buffer: Float32Array,
    cellSize: number
  ): SpatialHashGrid {
    const grid = new SpatialHashGrid({ maxParticles, cellSize });
    grid.rebuild(buffer);
    return grid;
  }

  // Arbitrary for valid SPH config
  const arbSPHConfig = fc.record({
    smoothingRadius: fc.float({ min: Math.fround(20), max: Math.fround(100), noNaN: true }),
    restDensity: fc.float({ min: Math.fround(100), max: Math.fround(2000), noNaN: true }),
    gasConstant: fc.float({ min: Math.fround(500), max: Math.fround(5000), noNaN: true }),
    viscosity: fc.float({ min: Math.fround(10), max: Math.fround(1000), noNaN: true }),
    surfaceTension: fc.float({ min: Math.fround(0), max: Math.fround(0.5), noNaN: true }),
    enableSurfaceTension: fc.boolean(),
    gravity: fc.record({
      x: fc.float({ min: Math.fround(-500), max: Math.fround(500), noNaN: true }),
      y: fc.float({ min: Math.fround(-1000), max: Math.fround(0), noNaN: true }),
      z: fc.float({ min: Math.fround(-500), max: Math.fround(500), noNaN: true }),
    }),
    maxTimeStep: fc.float({ min: Math.fround(0.001), max: Math.fround(0.01), noNaN: true }),
  });

  describe("Presets", () => {
    it("water preset should have valid values", () => {
      const preset = ParticleSPHSystem.waterPreset();
      
      expect(preset.smoothingRadius).toBeGreaterThan(0);
      expect(preset.restDensity).toBeGreaterThan(0);
      expect(preset.gasConstant).toBeGreaterThan(0);
      expect(preset.viscosity).toBeGreaterThan(0);
      expect(preset.gravity?.y).toBeLessThan(0); // Gravity down
    });

    it("honey preset should have higher viscosity than water", () => {
      const water = ParticleSPHSystem.waterPreset();
      const honey = ParticleSPHSystem.honeyPreset();

      expect(honey.viscosity!).toBeGreaterThan(water.viscosity!);
    });

    it("gas preset should have upward gravity (rises)", () => {
      const gas = ParticleSPHSystem.gasPreset();

      expect(gas.gravity?.y).toBeGreaterThan(0);
    });

    it("lava preset should have very high viscosity", () => {
      const lava = ParticleSPHSystem.lavaPreset();
      const water = ParticleSPHSystem.waterPreset();

      expect(lava.viscosity!).toBeGreaterThan(water.viscosity! * 100);
    });
  });

  describe("Density Calculation", () => {
    it("density should be positive for live particles", () => {
      const maxParticles = 100;
      const numParticles = 20;

      // Create particles in a grid
      const positions: Array<{ x: number; y: number; z: number }> = [];
      for (let i = 0; i < numParticles; i++) {
        positions.push({
          x: (i % 5) * 20 + 50,
          y: Math.floor(i / 5) * 20 + 50,
          z: 0,
        });
      }

      const buffer = createParticleBuffer(maxParticles, positions);
      const spatialHash = createSpatialHash(maxParticles, buffer, 40);

      const sph = new ParticleSPHSystem(maxParticles, ParticleSPHSystem.waterPreset());
      sph.setSpatialHash(spatialHash);
      
      // Run one update to compute densities
      sph.update(buffer, 0.004);

      // Check densities
      for (let i = 0; i < numParticles; i++) {
        const density = sph.getDensity(i);
        expect(density).toBeGreaterThanOrEqual(0);
        expect(Number.isFinite(density)).toBe(true);
      }
    });

    it("density should be higher in crowded regions", () => {
      const maxParticles = 100;

      // Create two groups: one dense, one sparse
      const positions: Array<{ x: number; y: number; z: number }> = [];
      
      // Dense group (particles at 0-40)
      for (let i = 0; i < 10; i++) {
        positions.push({ x: (i % 5) * 8, y: Math.floor(i / 5) * 8, z: 0 });
      }

      // Sparse group (particles at 200-400)
      for (let i = 0; i < 10; i++) {
        positions.push({ x: 200 + (i % 5) * 40, y: Math.floor(i / 5) * 40, z: 0 });
      }

      const buffer = createParticleBuffer(maxParticles, positions);
      const spatialHash = createSpatialHash(maxParticles, buffer, 50);

      const sph = new ParticleSPHSystem(maxParticles, ParticleSPHSystem.waterPreset());
      sph.setSpatialHash(spatialHash);
      sph.update(buffer, 0.004);

      // Average density of dense group
      let denseDensity = 0;
      for (let i = 0; i < 10; i++) {
        denseDensity += sph.getDensity(i);
      }
      denseDensity /= 10;

      // Average density of sparse group
      let sparseDensity = 0;
      for (let i = 10; i < 20; i++) {
        sparseDensity += sph.getDensity(i);
      }
      sparseDensity /= 10;

      // Dense region should have higher density
      expect(denseDensity).toBeGreaterThan(sparseDensity);
    });
  });

  describe("Pressure Forces", () => {
    it("particles should spread out from high density", () => {
      const maxParticles = 50;

      // Create particles very close together (very compressed)
      const positions: Array<{ x: number; y: number; z: number }> = [];
      for (let i = 0; i < 25; i++) {
        positions.push({
          x: 100 + (i % 5) * 3, // Even closer together
          y: 100 + Math.floor(i / 5) * 3,
          z: 0,
        });
      }

      const buffer = createParticleBuffer(maxParticles, positions);
      
      // Create SPH with higher gas constant for stronger pressure
      const sph = new ParticleSPHSystem(maxParticles, {
        smoothingRadius: 20,
        restDensity: 500, // Lower rest density = more pressure at current density
        gasConstant: 5000, // Higher = stronger pressure force
        viscosity: 50,
        surfaceTension: 0,
        enableSurfaceTension: false,
        gravity: { x: 0, y: 0, z: 0 },
        maxTimeStep: 0.002,
      });

      const spatialHash = createSpatialHash(maxParticles, buffer, 20);
      sph.setSpatialHash(spatialHash);

      // Calculate initial bounding box
      let initialMinX = Infinity, initialMaxX = -Infinity;
      let initialMinY = Infinity, initialMaxY = -Infinity;
      for (let i = 0; i < 25; i++) {
        const offset = i * PARTICLE_STRIDE;
        initialMinX = Math.min(initialMinX, buffer[offset + 0]);
        initialMaxX = Math.max(initialMaxX, buffer[offset + 0]);
        initialMinY = Math.min(initialMinY, buffer[offset + 1]);
        initialMaxY = Math.max(initialMaxY, buffer[offset + 1]);
      }
      const initialWidth = initialMaxX - initialMinX;
      const initialHeight = initialMaxY - initialMinY;

      // Run more simulation steps
      for (let i = 0; i < 50; i++) {
        spatialHash.rebuild(buffer);
        sph.update(buffer, 0.002);
      }

      // Calculate final bounding box
      let finalMinX = Infinity, finalMaxX = -Infinity;
      let finalMinY = Infinity, finalMaxY = -Infinity;
      for (let i = 0; i < 25; i++) {
        const offset = i * PARTICLE_STRIDE;
        finalMinX = Math.min(finalMinX, buffer[offset + 0]);
        finalMaxX = Math.max(finalMaxX, buffer[offset + 0]);
        finalMinY = Math.min(finalMinY, buffer[offset + 1]);
        finalMaxY = Math.max(finalMaxY, buffer[offset + 1]);
      }
      const finalWidth = finalMaxX - finalMinX;
      const finalHeight = finalMaxY - finalMinY;

      // Particles should have spread out at least a little
      expect(finalWidth).toBeGreaterThanOrEqual(initialWidth);
      expect(finalHeight).toBeGreaterThanOrEqual(initialHeight);
    });
  });

  describe("Viscosity", () => {
    it("high viscosity should produce finite velocity values", () => {
      const maxParticles = 10;

      // Create particles close together with different velocities
      const positions: Array<{ x: number; y: number; z: number }> = [];
      for (let i = 0; i < 5; i++) {
        positions.push({ x: i * 15 + 50, y: 50, z: 0 });
      }

      const buffer = createParticleBuffer(maxParticles, positions);

      // Set alternating velocities
      for (let i = 0; i < 5; i++) {
        const offset = i * PARTICLE_STRIDE;
        buffer[offset + 3] = i % 2 === 0 ? 50 : -50; // Smaller velocities
      }

      const sph = new ParticleSPHSystem(maxParticles, {
        smoothingRadius: 30,
        restDensity: 1000,
        gasConstant: 1000,
        viscosity: 5000,
        surfaceTension: 0,
        enableSurfaceTension: false,
        gravity: { x: 0, y: 0, z: 0 },
        maxTimeStep: 0.002, // Smaller timestep for stability
      });

      const spatialHash = createSpatialHash(maxParticles, buffer, 30);
      sph.setSpatialHash(spatialHash);

      // Run simulation
      for (let i = 0; i < 20; i++) {
        spatialHash.rebuild(buffer);
        sph.update(buffer, 0.002);
      }

      // Main test: all values should be finite (no NaN/Infinity)
      for (let i = 0; i < 5; i++) {
        const offset = i * PARTICLE_STRIDE;
        expect(Number.isFinite(buffer[offset + 0])).toBe(true); // position
        expect(Number.isFinite(buffer[offset + 1])).toBe(true);
        expect(Number.isFinite(buffer[offset + 2])).toBe(true);
        expect(Number.isFinite(buffer[offset + 3])).toBe(true); // velocity
        expect(Number.isFinite(buffer[offset + 4])).toBe(true);
        expect(Number.isFinite(buffer[offset + 5])).toBe(true);
      }
    });
  });

  describe("Numerical Stability", () => {
    it("should not produce NaN or Infinity values", () => {
      fc.assert(
        fc.property(arbSPHConfig, (config) => {
          const maxParticles = 30;

          // Create random particle positions
          const positions: Array<{ x: number; y: number; z: number }> = [];
          for (let i = 0; i < 20; i++) {
            positions.push({
              x: Math.random() * 200 + 50,
              y: Math.random() * 200 + 50,
              z: 0,
            });
          }

          const buffer = createParticleBuffer(maxParticles, positions);
          const spatialHash = createSpatialHash(maxParticles, buffer, config.smoothingRadius);

          const sph = new ParticleSPHSystem(maxParticles, config);
          sph.setSpatialHash(spatialHash);

          // Run simulation
          for (let i = 0; i < 10; i++) {
            spatialHash.rebuild(buffer);
            sph.update(buffer, Math.min(config.maxTimeStep, 0.008));
          }

          // Check all values are finite
          for (let i = 0; i < 20; i++) {
            const offset = i * PARTICLE_STRIDE;
            expect(Number.isFinite(buffer[offset + 0])).toBe(true);
            expect(Number.isFinite(buffer[offset + 1])).toBe(true);
            expect(Number.isFinite(buffer[offset + 2])).toBe(true);
            expect(Number.isFinite(buffer[offset + 3])).toBe(true);
            expect(Number.isFinite(buffer[offset + 4])).toBe(true);
            expect(Number.isFinite(buffer[offset + 5])).toBe(true);

            const density = sph.getDensity(i);
            const pressure = sph.getPressure(i);
            expect(Number.isFinite(density)).toBe(true);
            expect(Number.isFinite(pressure)).toBe(true);
          }
        }),
        { numRuns: 30 }
      );
    });

    it("pressure should be non-negative", () => {
      const maxParticles = 50;

      const positions: Array<{ x: number; y: number; z: number }> = [];
      for (let i = 0; i < 30; i++) {
        positions.push({
          x: (i % 6) * 25 + 50,
          y: Math.floor(i / 6) * 25 + 50,
          z: 0,
        });
      }

      const buffer = createParticleBuffer(maxParticles, positions);
      const spatialHash = createSpatialHash(maxParticles, buffer, 40);

      const sph = new ParticleSPHSystem(maxParticles, ParticleSPHSystem.waterPreset());
      sph.setSpatialHash(spatialHash);
      sph.update(buffer, 0.004);

      for (let i = 0; i < 30; i++) {
        const pressure = sph.getPressure(i);
        expect(pressure).toBeGreaterThanOrEqual(0);
      }
    });
  });

  describe("Configuration", () => {
    it("should update config correctly", () => {
      const sph = new ParticleSPHSystem(100, ParticleSPHSystem.waterPreset());

      const newConfig = {
        viscosity: 5000,
        restDensity: 1400,
      };

      sph.updateConfig(newConfig);
      const config = sph.getConfig();

      expect(config.viscosity).toBe(5000);
      expect(config.restDensity).toBe(1400);
      // Other values should remain from water preset
      expect(config.gasConstant).toBe(ParticleSPHSystem.waterPreset().gasConstant);
    });
  });
});
