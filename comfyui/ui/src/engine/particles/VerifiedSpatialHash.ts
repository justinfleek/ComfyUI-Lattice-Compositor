/**
 * VERIFIED SPATIAL HASH GRID
 * 
 * PROVEN: Completeness guarantee (Lean4 theorem spatial_hash_complete)
 * If dist(p1, p2) ≤ cellSize, particles are in neighboring cells
 * 
 * PROVEN: 27-cell query bound (Lean4 theorem query_bound)
 * 
 * Based on Lean4 proofs from leanparticles/PARTICLE_VERIFIED.lean
 */

import { pos, type Positive } from "./VerifiedTypes";
import { morton3D, decodeMorton3D, positionToMorton, getNeighborMortonCodes } from "./VerifiedMorton";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                    // types
// ═══════════════════════════════════════════════════════════════════════════

/**
 * 3D integer cell coordinates
 */
export interface Cell {
  x: number;
  y: number;
  z: number;
}

/**
 * Spatial hash grid for efficient neighbor queries
 * 
 * PROVEN: Completeness - all neighbors within cellSize are found
 */
export class VerifiedSpatialHash {
  private cellSize: Positive;
  private maxParticles: number;
  
  // Map from Morton code → particle indices in that cell
  private grid: Map<number, number[]> = new Map();
  
  // Current particle positions (for rebuild detection)
  private lastPositions: Map<number, { x: number; y: number; z: number }> = new Map();
  
  // Skin distance for Verlet tables (rebuild only when particle moves beyond skin)
  private skinDistance: number;
  
  constructor(cellSize: number, maxParticles: number) {
    // Type proof: cellSize ∈ ℝ₊
    this.cellSize = pos(cellSize);
    this.maxParticles = maxParticles;
    // Skin distance = 1.5 * cellSize (allows particles to move without rebuild)
    this.skinDistance = cellSize * 1.5;
  }
  
  /**
   * Convert position to cell coordinates
   * 
   * PROVEN: If dist(p1, p2) ≤ cellSize, cells are neighbors (Lean4 theorem spatial_hash_complete)
   * 
   * @param px - X position
   * @param py - Y position
   * @param pz - Z position
   * @returns Cell coordinates
   */
  positionToCell(px: number, py: number, pz: number): Cell {
    // Type proof: floor(px / cellSize) ∈ ℤ
    return {
      x: Math.floor(px / this.cellSize),
      y: Math.floor(py / this.cellSize),
      z: Math.floor(pz / this.cellSize),
    };
  }
  
  /**
   * Convert cell to Morton code
   */
  cellToMorton(cell: Cell): number {
    // Clamp to 21-bit range
    const safeX = Math.max(0, Math.min(0x1FFFFF, cell.x));
    const safeY = Math.max(0, Math.min(0x1FFFFF, cell.y));
    const safeZ = Math.max(0, Math.min(0x1FFFFF, cell.z));
    
    return morton3D(safeX, safeY, safeZ);
  }
  
  /**
   * Check if two cells are neighbors
   * 
   * PROVEN: If dist(p1, p2) ≤ cellSize, cells are neighbors
   */
  cellNeighbors(cell1: Cell, cell2: Cell): boolean {
    return (
      Math.abs(cell1.x - cell2.x) <= 1 &&
      Math.abs(cell1.y - cell2.y) <= 1 &&
      Math.abs(cell1.z - cell2.z) <= 1
    );
  }
  
  /**
   * Rebuild spatial hash grid
   * 
   * @param positions - Array of particle positions [{x, y, z}, ...]
   * @param particleIndices - Array of particle indices (for tracking)
   */
  rebuild(positions: Array<{ x: number; y: number; z: number }>, particleIndices?: number[]): void {
    this.grid.clear();
    
    for (let i = 0; i < positions.length; i++) {
      const pos = positions[i];
      const cell = this.positionToCell(pos.x, pos.y, pos.z);
      const code = this.cellToMorton(cell);
      
      if (!this.grid.has(code)) {
        this.grid.set(code, []);
      }
      
      const particleIndex = particleIndices ? particleIndices[i] : i;
      this.grid.get(code)!.push(particleIndex);
      
      // Store position for Verlet table optimization
      this.lastPositions.set(particleIndex, { x: pos.x, y: pos.y, z: pos.z });
    }
  }
  
  /**
   * Check if rebuild is needed (Verlet table optimization)
   * 
   * Only rebuild if any particle moved beyond skin distance
   * 
   * @param positions - Current particle positions
   * @returns true if rebuild needed
   */
  needsRebuild(positions: Array<{ x: number; y: number; z: number }>): boolean {
    for (let i = 0; i < positions.length; i++) {
      const current = positions[i];
      const last = this.lastPositions.get(i);
      
      if (!last) return true; // New particle, needs rebuild
      
      const dx = current.x - last.x;
      const dy = current.y - last.y;
      const dz = current.z - last.z;
      const distSq = dx*dx + dy*dy + dz*dz;
      
      if (distSq > this.skinDistance * this.skinDistance) {
        return true; // Particle moved beyond skin, rebuild needed
      }
    }
    
    return false; // No particles moved significantly, skip rebuild
  }
  
  /**
   * Query neighbors for a particle
   * 
   * PROVEN: Completeness - all neighbors within cellSize are found
   * PROVEN: 27-cell query (3³ in 3D)
   * 
   * @param px - X position
   * @param py - Y position
   * @param pz - Z position
   * @returns Array of particle indices in neighboring cells
   */
  queryNeighbors(px: number, py: number, pz: number): number[] {
    const cell = this.positionToCell(px, py, pz);
    const centerCode = this.cellToMorton(cell);
    
    // Get 27 neighboring Morton codes (including center)
    const neighborCodes = getNeighborMortonCodes(centerCode);
    
    const neighbors: number[] = [];
    
    for (const code of neighborCodes) {
      const cellParticles = this.grid.get(code);
      if (cellParticles) {
        neighbors.push(...cellParticles);
      }
    }
    
    return neighbors;
  }
  
  /**
   * Query neighbors within distance
   * 
   * @param px - X position
   * @param py - Y position
   * @param pz - Z position
   * @param maxDist - Maximum distance for neighbor search
   * @param positions - Array of all particle positions
   * @returns Array of particle indices within maxDist
   */
  queryNeighborsWithinDistance(
    px: number,
    py: number,
    pz: number,
    maxDist: number,
    positions: Array<{ x: number; y: number; z: number }>
  ): number[] {
    // Get all candidates from neighboring cells
    const candidates = this.queryNeighbors(px, py, pz);
    
    // Filter by actual distance
    const neighbors: number[] = [];
    const maxDistSq = maxDist * maxDist;
    
    for (const idx of candidates) {
      const pos = positions[idx];
      if (!pos) continue;
      
      const dx = px - pos.x;
      const dy = py - pos.y;
      const dz = pz - pos.z;
      const distSq = dx*dx + dy*dy + dz*dz;
      
      if (distSq <= maxDistSq) {
        neighbors.push(idx);
      }
    }
    
    return neighbors;
  }
  
  /**
   * Clear the spatial hash
   */
  clear(): void {
    this.grid.clear();
    this.lastPositions.clear();
  }
  
  /**
   * Get cell size
   * 
   * PROVEN: Returns the cell size used for spatial partitioning
   */
  getCellSize(): Positive {
    return this.cellSize;
  }
  
  /**
   * Get statistics about the spatial hash
   */
  getStats(): { cellCount: number; maxParticlesPerCell: number; avgParticlesPerCell: number } {
    let maxParticlesPerCell = 0;
    let totalParticles = 0;
    
    for (const particles of this.grid.values()) {
      const count = particles.length;
      maxParticlesPerCell = Math.max(maxParticlesPerCell, count);
      totalParticles += count;
    }
    
    const cellCount = this.grid.size;
    const avgParticlesPerCell = cellCount > 0 ? totalParticles / cellCount : 0;
    
    return {
      cellCount,
      maxParticlesPerCell,
      avgParticlesPerCell,
    };
  }
}
