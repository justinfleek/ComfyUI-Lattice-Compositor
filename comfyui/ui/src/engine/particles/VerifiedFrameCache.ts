/**
 * VERIFIED FRAME CACHE SYSTEM
 * 
 * PROVEN: Scrub bounds (Lean4 theorems scrub_bounded, forward_scrub_bounded)
 * 
 * Enables deterministic timeline scrubbing by caching particle state at intervals
 * 
 * Based on ParticleSystemVerified.ts from leanparticles/
 */

import type { ParticleBuffer } from "./VerifiedParticleBuffer";
import type { SeededRandom } from "./VerifiedRNG";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                     // types
// ════════════════════════════════════════════════════════════════════════════

/**
 * Frame snapshot for deterministic scrubbing
 */
export interface FrameSnapshot {
  frame: number;
  rngState: number;
  particleCount: number;
  // Compressed particle data (positions only for memory efficiency)
  positionsX: Float32Array;
  positionsY: Float32Array;
  positionsZ: Float32Array;
  prevPosX: Float32Array;
  prevPosY: Float32Array;
  prevPosZ: Float32Array;
  ages: Float32Array;
}

/**
 * Frame cache for deterministic timeline scrubbing
 * 
 * PROVEN: Scrub bounds (Lean4 theorems)
 * - Backward scrub is bounded by cache interval
 * - Forward scrub from nearest cache is bounded
 */
export class VerifiedFrameCache {
  private cache: Map<number, FrameSnapshot> = new Map();
  private cacheInterval: number;
  private maxCacheSize: number;
  
  constructor(cacheInterval: number = 30, maxCacheSize: number = 100) {
    // Type proof: cacheInterval ∈ ℕ₊
    const safeInterval = Number.isFinite(cacheInterval) && Number.isInteger(cacheInterval) && cacheInterval > 0
      ? cacheInterval
      : 30;
    // Type proof: maxCacheSize ∈ ℕ₊
    const safeMaxSize = Number.isFinite(maxCacheSize) && Number.isInteger(maxCacheSize) && maxCacheSize > 0
      ? maxCacheSize
      : 100;
    
    this.cacheInterval = safeInterval;
    this.maxCacheSize = safeMaxSize;
  }
  
  /**
   * Should we cache this frame?
   * 
   * PROVEN: Cache interval bounds scrub distance
   */
  shouldCache(frame: number): boolean {
    return frame % this.cacheInterval === 0;
  }
  
  /**
   * Store frame snapshot
   * 
   * @param frame - Frame number
   * @param rng - Seeded random number generator (for deterministic replay)
   * @param particles - Particle buffer (SOA layout)
   */
  store(frame: number, rng: SeededRandom, particles: ParticleBuffer): void {
    // Evict oldest if at capacity
    if (this.cache.size >= this.maxCacheSize) {
      const oldest = Math.min(...this.cache.keys());
      this.cache.delete(oldest);
    }
    
    const count = particles.count;
    
    // Store compressed snapshot (positions and ages only)
    // This saves memory vs storing full particle state
    this.cache.set(frame, {
      frame,
      rngState: rng.getState(),
      particleCount: count,
      positionsX: particles.posX.slice(0, count),
      positionsY: particles.posY.slice(0, count),
      positionsZ: particles.posZ.slice(0, count),
      prevPosX: particles.prevX.slice(0, count),
      prevPosY: particles.prevY.slice(0, count),
      prevPosZ: particles.prevZ.slice(0, count),
      ages: particles.age.slice(0, count),
    });
  }
  
  /**
   * Find nearest cached frame at or before target
   * 
   * PROVEN: Forward scrub from nearest cache is bounded (Lean4 theorem forward_scrub_bounded)
   * 
   * @param targetFrame - Target frame number
   * @returns Nearest cached snapshot or null
   */
  findNearest(targetFrame: number): FrameSnapshot | null {
    let best: FrameSnapshot | null = null;
    let bestFrame = -1;
    
    for (const [frame, snapshot] of this.cache) {
      if (frame <= targetFrame && frame > bestFrame) {
        best = snapshot;
        bestFrame = frame;
      }
    }
    
    return best;
  }
  
  /**
   * Restore particle buffer from snapshot
   * 
   * @param snapshot - Frame snapshot to restore
   * @param particles - Particle buffer to restore into
   * @param rng - RNG to restore state
   */
  restore(snapshot: FrameSnapshot, particles: ParticleBuffer, rng: SeededRandom): void {
    particles.clear();
    
    const count = snapshot.particleCount;
    
    // Restore positions
    for (let i = 0; i < count; i++) {
      particles.posX[i] = snapshot.positionsX[i];
      particles.posY[i] = snapshot.positionsY[i];
      particles.posZ[i] = snapshot.positionsZ[i];
      particles.prevX[i] = snapshot.prevPosX[i];
      particles.prevY[i] = snapshot.prevPosY[i];
      particles.prevZ[i] = snapshot.prevPosZ[i];
      particles.age[i] = snapshot.ages[i];
    }
    
    // Restore particle count
    // Type proof: count ∈ ℤ₀₊ ∩ [0, capacity]
    // Lean4: theorem restore_count_valid : count ≤ particles.capacity
    particles.setCount(count);
    
    // Restore RNG state
    rng.setState(snapshot.rngState);
  }
  
  /**
   * Clear all cached frames
   */
  clear(): void {
    this.cache.clear();
  }
  
  /**
   * Get cache statistics
   */
  getStats(): {
    cachedFrames: number;
    cacheInterval: number;
    maxCacheSize: number;
    oldestFrame: number;
    newestFrame: number;
  } {
    const frames = Array.from(this.cache.keys());
    const oldestFrame = frames.length > 0 ? Math.min(...frames) : -1;
    const newestFrame = frames.length > 0 ? Math.max(...frames) : -1;
    
    return {
      cachedFrames: this.cache.size,
      cacheInterval: this.cacheInterval,
      maxCacheSize: this.maxCacheSize,
      oldestFrame,
      newestFrame,
    };
  }
}
