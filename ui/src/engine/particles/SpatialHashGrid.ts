/**
 * Spatial Hash Grid
 *
 * Efficient spatial partitioning for O(n) neighbor queries.
 * Shared between flocking and collision systems to avoid
 * duplicate hash construction each frame.
 *
 * Based on uniform grid spatial hashing:
 * - Particles are binned into cells based on position
 * - Neighbor queries check only adjacent cells (3x3x3 grid)
 * - Cell size should be >= max interaction radius
 */

import { PARTICLE_STRIDE } from "./types";

// ============================================================================
// TYPES
// ============================================================================

export interface CellKey {
  x: number;
  y: number;
  z: number;
}

export interface SpatialHashConfig {
  cellSize: number;
  maxParticles: number;
}

// ============================================================================
// SPATIAL HASH GRID CLASS
// ============================================================================

export class SpatialHashGrid {
  private readonly maxParticles: number;
  private cellSize: number;
  private cells: Map<string, number[]> = new Map();
  private particleCells: Map<number, string> = new Map(); // particle index -> cell key

  constructor(config: SpatialHashConfig) {
    // Validate maxParticles to prevent infinite loop
    this.maxParticles = Number.isFinite(config.maxParticles) && config.maxParticles > 0
      ? Math.min(Math.floor(config.maxParticles), 10_000_000)
      : 10000;
    // Validate cellSize to prevent division by zero (NaN check required - Math.max(1, NaN) = NaN)
    this.cellSize = Number.isFinite(config.cellSize) && config.cellSize > 0
      ? config.cellSize
      : 1;
  }

  // ============================================================================
  // HASH CONSTRUCTION
  // ============================================================================

  /**
   * Rebuild the spatial hash from particle buffer
   * Call this ONCE per frame before any neighbor queries
   * @param particleBuffer - The current particle data buffer
   */
  rebuild(particleBuffer: Float32Array): void {
    this.cells.clear();
    this.particleCells.clear();

    for (let i = 0; i < this.maxParticles; i++) {
      const offset = i * PARTICLE_STRIDE;
      const lifetime = particleBuffer[offset + 7];
      const age = particleBuffer[offset + 6];

      // Skip dead particles
      if (lifetime <= 0 || age >= lifetime) continue;

      const px = particleBuffer[offset + 0];
      const py = particleBuffer[offset + 1];
      const pz = particleBuffer[offset + 2];

      // Skip particles with invalid positions (NaN/Infinity)
      if (!Number.isFinite(px) || !Number.isFinite(py) || !Number.isFinite(pz)) {
        continue;
      }

      const cellX = Math.floor(px / this.cellSize);
      const cellY = Math.floor(py / this.cellSize);
      const cellZ = Math.floor(pz / this.cellSize);
      const key = `${cellX},${cellY},${cellZ}`;

      if (!this.cells.has(key)) {
        this.cells.set(key, []);
      }
      this.cells.get(key)?.push(i);
      this.particleCells.set(i, key);
    }
  }

  // ============================================================================
  // NEIGHBOR QUERIES
  // ============================================================================

  /**
   * Get all particle indices in a cell
   */
  getCell(key: string): number[] {
    return this.cells.get(key) ?? [];
  }

  /**
   * Get all particle indices in cells adjacent to a position (3x3x3 grid)
   * @param px - X position
   * @param py - Y position
   * @param pz - Z position
   * @returns Iterator over neighbor particle indices
   */
  *getNeighbors(px: number, py: number, pz: number): Generator<number> {
    // Guard against NaN/Infinity positions causing infinite loops
    if (!Number.isFinite(px) || !Number.isFinite(py) || !Number.isFinite(pz)) {
      return;
    }

    const cellX = Math.floor(px / this.cellSize);
    const cellY = Math.floor(py / this.cellSize);
    const cellZ = Math.floor(pz / this.cellSize);

    for (let cx = cellX - 1; cx <= cellX + 1; cx++) {
      for (let cy = cellY - 1; cy <= cellY + 1; cy++) {
        for (let cz = cellZ - 1; cz <= cellZ + 1; cz++) {
          const neighbors = this.cells.get(`${cx},${cy},${cz}`);
          if (neighbors) {
            for (const index of neighbors) {
              yield index;
            }
          }
        }
      }
    }
  }

  /**
   * Get all particle indices within a radius of a position
   * @param px - X position
   * @param py - Y position
   * @param pz - Z position
   * @param radius - Search radius
   * @param particleBuffer - The particle data buffer for position lookups
   * @param excludeIndex - Optional particle index to exclude (self)
   */
  getNeighborsInRadius(
    px: number,
    py: number,
    pz: number,
    radius: number,
    particleBuffer: Float32Array,
    excludeIndex?: number,
  ): number[] {
    const radiusSq = radius * radius;
    const result: number[] = [];

    for (const index of this.getNeighbors(px, py, pz)) {
      if (index === excludeIndex) continue;

      const offset = index * PARTICLE_STRIDE;
      const nx = particleBuffer[offset + 0];
      const ny = particleBuffer[offset + 1];
      const nz = particleBuffer[offset + 2];

      const dx = nx - px;
      const dy = ny - py;
      const dz = nz - pz;
      const distSq = dx * dx + dy * dy + dz * dz;

      if (distSq <= radiusSq) {
        result.push(index);
      }
    }

    return result;
  }

  /**
   * Iterate over all cells with their particle indices
   * Useful for operations that need to process all occupied cells
   */
  *iterateCells(): Generator<[string, number[]]> {
    for (const entry of this.cells.entries()) {
      yield entry;
    }
  }

  /**
   * Get the cell key for a particle index
   */
  getParticleCell(index: number): string | undefined {
    return this.particleCells.get(index);
  }

  // ============================================================================
  // CONFIGURATION
  // ============================================================================

  /**
   * Update cell size (requires rebuild)
   */
  setCellSize(size: number): void {
    // NaN check required - Math.max(1, NaN) = NaN
    this.cellSize = Number.isFinite(size) && size > 0 ? size : 1;
  }

  /**
   * Get current cell size
   */
  getCellSize(): number {
    return this.cellSize;
  }

  // ============================================================================
  // STATISTICS
  // ============================================================================

  /**
   * Get number of occupied cells
   */
  getCellCount(): number {
    return this.cells.size;
  }

  /**
   * Get number of particles in the hash
   */
  getParticleCount(): number {
    return this.particleCells.size;
  }

  /**
   * Get average particles per cell
   */
  getAverageOccupancy(): number {
    if (this.cells.size === 0) return 0;
    let total = 0;
    for (const particles of this.cells.values()) {
      total += particles.length;
    }
    return total / this.cells.size;
  }

  /**
   * Get the raw cells map (for direct iteration in performance-critical code)
   */
  getRawCells(): Map<string, number[]> {
    return this.cells;
  }

  // ============================================================================
  // CLEANUP
  // ============================================================================

  /**
   * Clear all data
   */
  clear(): void {
    this.cells.clear();
    this.particleCells.clear();
  }
}
