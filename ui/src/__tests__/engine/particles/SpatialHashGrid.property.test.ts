/**
 * Property Tests for SpatialHashGrid.ts
 *
 * Comprehensive fast-check property tests for:
 * - Spatial hash construction
 * - Neighbor queries
 * - Radius queries
 * - Edge case handling
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  SpatialHashGrid,
  type SpatialHashConfig,
} from "@/engine/particles/SpatialHashGrid";
import { PARTICLE_STRIDE } from "@/engine/particles/types";

// ============================================================================
// HELPERS
// ============================================================================

function createParticleBuffer(count: number): Float32Array {
  return new Float32Array(count * PARTICLE_STRIDE);
}

function initParticle(
  buffer: Float32Array,
  index: number,
  pos: { x: number; y: number; z: number },
  lifetime: number = 100,
): void {
  const offset = index * PARTICLE_STRIDE;
  buffer[offset + 0] = pos.x;
  buffer[offset + 1] = pos.y;
  buffer[offset + 2] = pos.z;
  buffer[offset + 3] = 0; // vx
  buffer[offset + 4] = 0; // vy
  buffer[offset + 5] = 0; // vz
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

// ============================================================================
// ARBITRARIES
// ============================================================================

const safeFloat = (min = -10000, max = 10000) =>
  fc.float({ min: Math.fround(min), max: Math.fround(max), noNaN: true });

const positiveFloat = (max = 1000) =>
  fc.float({ min: Math.fround(0.001), max: Math.fround(max), noNaN: true });

const arbPosition = fc.record({
  x: safeFloat(-1000, 1000),
  y: safeFloat(-1000, 1000),
  z: safeFloat(-1000, 1000),
});

const arbConfig: fc.Arbitrary<SpatialHashConfig> = fc.record({
  cellSize: fc.oneof(
    positiveFloat(100),
    fc.constant(0),
    fc.constant(-10),
    fc.constant(NaN),
  ),
  maxParticles: fc.oneof(
    fc.integer({ min: 1, max: 10000 }),
    fc.constant(0),
    fc.constant(-100),
    fc.constant(Infinity),
  ),
});

// ============================================================================
// TESTS: Construction
// ============================================================================

describe("SpatialHashGrid construction", () => {
  it("should handle any config values without crashing", () => {
    fc.assert(
      fc.property(arbConfig, (config) => {
        const grid = new SpatialHashGrid(config);
        expect(grid).toBeDefined();
        // CellSize should be positive
        expect(grid.getCellSize()).toBeGreaterThan(0);
      }),
      { numRuns: 100 },
    );
  });

  it("should default to 1 for invalid cellSize values", () => {
    // Only invalid values (0, negative, NaN) should default to 1
    fc.assert(
      fc.property(
        fc.oneof(
          fc.constant(0),
          fc.constant(-10),
          fc.constant(NaN),
          fc.float({ min: Math.fround(-100), max: Math.fround(0), noNaN: true }),
        ),
        (invalidCellSize) => {
          const grid = new SpatialHashGrid({ cellSize: invalidCellSize, maxParticles: 100 });
          expect(grid.getCellSize()).toBe(1);
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should accept any positive finite cellSize", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(0.001), max: Math.fround(1000), noNaN: true }),
        (validCellSize) => {
          const grid = new SpatialHashGrid({ cellSize: validCellSize, maxParticles: 100 });
          expect(grid.getCellSize()).toBe(validCellSize);
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Rebuild
// ============================================================================

describe("SpatialHashGrid.rebuild", () => {
  it("should correctly count alive particles", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 1, max: 100 }),
        fc.integer({ min: 0, max: 50 }),
        (aliveCount, deadCount) => {
          const total = aliveCount + deadCount;
          const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: total });
          const buffer = createParticleBuffer(total);

          // Initialize alive particles
          for (let i = 0; i < aliveCount; i++) {
            initParticle(buffer, i, { x: i * 10, y: 0, z: 0 }, 100);
          }

          // Initialize dead particles (lifetime = 0)
          for (let i = aliveCount; i < total; i++) {
            initParticle(buffer, i, { x: i * 10, y: 0, z: 0 }, 0);
          }

          grid.rebuild(buffer);

          expect(grid.getParticleCount()).toBe(aliveCount);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should skip particles with NaN positions", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 3 });
    const buffer = createParticleBuffer(3);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100);
    initParticle(buffer, 1, { x: NaN, y: 0, z: 0 }, 100);
    initParticle(buffer, 2, { x: 100, y: 0, z: 0 }, 100);

    grid.rebuild(buffer);

    // Only 2 particles should be in the grid (NaN position skipped)
    expect(grid.getParticleCount()).toBe(2);
  });

  it("should skip particles with Infinity positions", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 3 });
    const buffer = createParticleBuffer(3);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100);
    initParticle(buffer, 1, { x: Infinity, y: 0, z: 0 }, 100);
    initParticle(buffer, 2, { x: 100, y: 0, z: 0 }, 100);

    grid.rebuild(buffer);

    // Only 2 particles should be in the grid (Infinity position skipped)
    expect(grid.getParticleCount()).toBe(2);
  });

  it("should place particles in correct cells", () => {
    // Helper to normalize -0 to 0 for comparison (Math.floor(-0 / x) = -0)
    const normalize = (n: number) => (Object.is(n, -0) ? 0 : n);

    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(10), max: Math.fround(100), noNaN: true }),
        fc.array(arbPosition, { minLength: 1, maxLength: 20 }),
        (cellSize, positions) => {
          const grid = new SpatialHashGrid({ cellSize, maxParticles: positions.length });
          const buffer = createParticleBuffer(positions.length);

          positions.forEach((pos, i) => {
            initParticle(buffer, i, pos, 100);
          });

          grid.rebuild(buffer);

          // Verify each particle is in the correct cell
          positions.forEach((pos, i) => {
            const cellKey = grid.getParticleCell(i);
            if (cellKey) {
              const [cx, cy, cz] = cellKey.split(",").map(Number);
              expect(normalize(Math.floor(pos.x / cellSize))).toBe(normalize(cx));
              expect(normalize(Math.floor(pos.y / cellSize))).toBe(normalize(cy));
              expect(normalize(Math.floor(pos.z / cellSize))).toBe(normalize(cz));
            }
          });
        },
      ),
      { numRuns: 100 },
    );
  });
});

// ============================================================================
// TESTS: Neighbor Queries
// ============================================================================

describe("SpatialHashGrid.getNeighbors", () => {
  it("should return particle in same cell", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 1 });
    const buffer = createParticleBuffer(1);

    initParticle(buffer, 0, { x: 50, y: 50, z: 50 }, 100);
    grid.rebuild(buffer);

    const neighbors = [...grid.getNeighbors(50, 50, 50)];
    expect(neighbors).toContain(0);
  });

  it("should return particles in adjacent cells", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 2 });
    const buffer = createParticleBuffer(2);

    // Two particles in adjacent cells
    initParticle(buffer, 0, { x: 50, y: 50, z: 50 }, 100); // cell (0, 0, 0)
    initParticle(buffer, 1, { x: 150, y: 50, z: 50 }, 100); // cell (1, 0, 0)
    grid.rebuild(buffer);

    // Query from first particle should find second (adjacent)
    const neighbors = [...grid.getNeighbors(50, 50, 50)];
    expect(neighbors).toContain(0);
    expect(neighbors).toContain(1);
  });

  it("should not return particles in distant cells", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 2 });
    const buffer = createParticleBuffer(2);

    // Two particles far apart (more than 1 cell away)
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100); // cell (0, 0, 0)
    initParticle(buffer, 1, { x: 500, y: 0, z: 0 }, 100); // cell (5, 0, 0)
    grid.rebuild(buffer);

    // Query from first particle should NOT find second
    const neighbors = [...grid.getNeighbors(0, 0, 0)];
    expect(neighbors).toContain(0);
    expect(neighbors).not.toContain(1);
  });

  it("should handle NaN query positions gracefully", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 1 });
    const buffer = createParticleBuffer(1);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100);
    grid.rebuild(buffer);

    // NaN query should return empty (not crash or infinite loop)
    const neighbors = [...grid.getNeighbors(NaN, 0, 0)];
    expect(neighbors).toHaveLength(0);
  });

  it("should handle Infinity query positions gracefully", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 1 });
    const buffer = createParticleBuffer(1);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100);
    grid.rebuild(buffer);

    // Infinity query should return empty (not crash or infinite loop)
    const neighbors = [...grid.getNeighbors(Infinity, 0, 0)];
    expect(neighbors).toHaveLength(0);
  });
});

// ============================================================================
// TESTS: Radius Queries
// ============================================================================

describe("SpatialHashGrid.getNeighborsInRadius", () => {
  it("should return particles within radius", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 3 });
    const buffer = createParticleBuffer(3);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100);
    initParticle(buffer, 1, { x: 20, y: 0, z: 0 }, 100); // Within 50 radius
    initParticle(buffer, 2, { x: 100, y: 0, z: 0 }, 100); // Outside 50 radius
    grid.rebuild(buffer);

    const neighbors = grid.getNeighborsInRadius(0, 0, 0, 50, buffer);
    expect(neighbors).toContain(0);
    expect(neighbors).toContain(1);
    expect(neighbors).not.toContain(2);
  });

  it("should exclude self when specified", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 1 });
    const buffer = createParticleBuffer(1);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100);
    grid.rebuild(buffer);

    const neighbors = grid.getNeighborsInRadius(0, 0, 0, 100, buffer, 0);
    expect(neighbors).not.toContain(0);
  });

  it("should handle varying radii correctly", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(10), max: Math.fround(500), noNaN: true }),
        fc.float({ min: Math.fround(1), max: Math.fround(200), noNaN: true }),
        (distance, radius) => {
          const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 2 });
          const buffer = createParticleBuffer(2);

          initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, 100);
          initParticle(buffer, 1, { x: distance, y: 0, z: 0 }, 100);
          grid.rebuild(buffer);

          const neighbors = grid.getNeighborsInRadius(0, 0, 0, radius, buffer, 0);

          if (distance <= radius) {
            expect(neighbors).toContain(1);
          } else {
            expect(neighbors).not.toContain(1);
          }
        },
      ),
      { numRuns: 100 },
    );
  });
});

// ============================================================================
// TESTS: Statistics
// ============================================================================

describe("SpatialHashGrid statistics", () => {
  it("should correctly count cells", () => {
    fc.assert(
      fc.property(
        fc.float({ min: Math.fround(10), max: Math.fround(100), noNaN: true }),
        fc.array(arbPosition, { minLength: 1, maxLength: 50 }),
        (cellSize, positions) => {
          const grid = new SpatialHashGrid({ cellSize, maxParticles: positions.length });
          const buffer = createParticleBuffer(positions.length);

          positions.forEach((pos, i) => {
            initParticle(buffer, i, pos, 100);
          });

          grid.rebuild(buffer);

          // Cell count should be <= particle count (multiple particles can share a cell)
          expect(grid.getCellCount()).toBeLessThanOrEqual(positions.length);
          expect(grid.getCellCount()).toBeGreaterThanOrEqual(1);
        },
      ),
      { numRuns: 100 },
    );
  });

  it("should calculate average occupancy correctly", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 10 });
    const buffer = createParticleBuffer(10);

    // All particles in same cell
    for (let i = 0; i < 10; i++) {
      initParticle(buffer, i, { x: 0, y: 0, z: 0 }, 100);
    }
    grid.rebuild(buffer);

    expect(grid.getCellCount()).toBe(1);
    expect(grid.getAverageOccupancy()).toBe(10);
  });

  it("should return 0 occupancy for empty grid", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 10 });
    const buffer = createParticleBuffer(10);

    // No alive particles
    grid.rebuild(buffer);

    expect(grid.getCellCount()).toBe(0);
    expect(grid.getAverageOccupancy()).toBe(0);
  });
});

// ============================================================================
// TESTS: Clear
// ============================================================================

describe("SpatialHashGrid.clear", () => {
  it("should remove all data", () => {
    const grid = new SpatialHashGrid({ cellSize: 100, maxParticles: 10 });
    const buffer = createParticleBuffer(10);

    for (let i = 0; i < 10; i++) {
      initParticle(buffer, i, { x: i * 10, y: 0, z: 0 }, 100);
    }
    grid.rebuild(buffer);

    expect(grid.getParticleCount()).toBe(10);

    grid.clear();

    expect(grid.getParticleCount()).toBe(0);
    expect(grid.getCellCount()).toBe(0);
  });
});
