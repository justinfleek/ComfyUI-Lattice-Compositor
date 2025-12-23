/**
 * Particle Frame Cache System
 *
 * Handles frame-based caching for particle systems to enable
 * efficient timeline scrubbing. Stores particle state snapshots
 * at configurable intervals and supports version-based invalidation.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

import { PARTICLE_STRIDE } from './types';

// ============================================================================
// TYPES
// ============================================================================

export interface ParticleFrameCache {
  frame: number;
  version: number;
  particleBuffer: Float32Array;
  freeIndices: number[];
  particleCount: number;
  simulationTime: number;
  rngState: number;
  emitterAccumulators: Map<string, number>;
}

export interface CacheStats {
  cachedFrames: number;
  version: number;
  currentFrame: number;
  cacheInterval: number;
  maxCacheSize: number;
}

// ============================================================================
// PARTICLE FRAME CACHE CLASS
// ============================================================================

export class ParticleFrameCacheSystem {
  private frameCache: Map<number, ParticleFrameCache> = new Map();
  private cacheVersion: number = 0;
  private cacheInterval: number = 30;  // Cache every N frames
  private maxCacheSize: number = 100;
  private currentSimulatedFrame: number = -1;
  private readonly maxParticles: number;

  constructor(maxParticles: number, cacheInterval: number = 30, maxCacheSize: number = 100) {
    this.maxParticles = maxParticles;
    this.cacheInterval = cacheInterval;
    this.maxCacheSize = maxCacheSize;
  }

  // ============================================================================
  // CACHE MANAGEMENT
  // ============================================================================

  /**
   * Cache the current particle state for a specific frame
   * Called automatically every cacheInterval frames during step()
   */
  cacheState(
    frame: number,
    particleBuffer: Float32Array,
    freeIndices: number[],
    particleCount: number,
    simulationTime: number,
    rngState: number,
    emitters: Map<string, { accumulator: number }>
  ): void {
    // Don't cache if we've exceeded max size - remove oldest
    if (this.frameCache.size >= this.maxCacheSize) {
      const oldestFrame = Math.min(...this.frameCache.keys());
      this.frameCache.delete(oldestFrame);
    }

    // Save emitter accumulators
    const emitterAccumulators = new Map<string, number>();
    for (const [id, emitter] of emitters) {
      emitterAccumulators.set(id, emitter.accumulator);
    }

    this.frameCache.set(frame, {
      frame,
      version: this.cacheVersion,
      particleBuffer: new Float32Array(particleBuffer), // Deep copy
      freeIndices: [...freeIndices], // Copy array
      particleCount,
      simulationTime,
      rngState,
      emitterAccumulators,
    });
  }

  /**
   * Restore particle state from a cached frame
   * @returns The cached frame data if restore succeeded, null if cache miss or version mismatch
   */
  restoreFromCache(frame: number): ParticleFrameCache | null {
    const cached = this.frameCache.get(frame);
    if (!cached || cached.version !== this.cacheVersion) {
      return null;
    }
    return cached;
  }

  /**
   * Find the nearest cached frame at or before the target frame
   * @returns The nearest cached frame number, or -1 if no cache exists
   */
  findNearestCache(targetFrame: number): number {
    let nearestFrame = -1;
    for (const frame of this.frameCache.keys()) {
      const cached = this.frameCache.get(frame);
      if (cached && cached.version === this.cacheVersion && frame <= targetFrame && frame > nearestFrame) {
        nearestFrame = frame;
      }
    }
    return nearestFrame;
  }

  /**
   * Check if a frame should be cached based on interval
   */
  shouldCacheFrame(frame: number): boolean {
    return frame % this.cacheInterval === 0;
  }

  /**
   * Clear all cached frames
   */
  clearCache(): void {
    this.frameCache.clear();
    this.currentSimulatedFrame = -1;
  }

  /**
   * Invalidate the cache by incrementing version
   * Called when particle parameters change (emitter config, force fields, etc.)
   */
  invalidateCache(): void {
    this.cacheVersion++;
    // Don't clear the map - old entries will be ignored due to version mismatch
    // This is more memory efficient for frequent invalidations
    this.currentSimulatedFrame = -1;
  }

  // ============================================================================
  // FRAME TRACKING
  // ============================================================================

  /**
   * Get current simulated frame
   */
  getCurrentFrame(): number {
    return this.currentSimulatedFrame;
  }

  /**
   * Set current simulated frame
   */
  setCurrentFrame(frame: number): void {
    this.currentSimulatedFrame = frame;
  }

  /**
   * Check if we can continue from current position (forward scrubbing)
   */
  canContinueFrom(targetFrame: number): boolean {
    return (
      this.currentSimulatedFrame >= 0 &&
      this.currentSimulatedFrame < targetFrame &&
      targetFrame - this.currentSimulatedFrame <= this.cacheInterval * 2
    );
  }

  // ============================================================================
  // CONFIGURATION
  // ============================================================================

  /**
   * Set the cache interval (how often to cache frames)
   */
  setCacheInterval(interval: number): void {
    this.cacheInterval = Math.max(1, interval);
  }

  /**
   * Get cache interval
   */
  getCacheInterval(): number {
    return this.cacheInterval;
  }

  /**
   * Get cache version
   */
  getVersion(): number {
    return this.cacheVersion;
  }

  // ============================================================================
  // STATISTICS
  // ============================================================================

  /**
   * Get cache statistics for debugging/UI
   */
  getStats(): CacheStats {
    // Count valid cached frames
    let validCount = 0;
    for (const cached of this.frameCache.values()) {
      if (cached.version === this.cacheVersion) {
        validCount++;
      }
    }

    return {
      cachedFrames: validCount,
      version: this.cacheVersion,
      currentFrame: this.currentSimulatedFrame,
      cacheInterval: this.cacheInterval,
      maxCacheSize: this.maxCacheSize,
    };
  }
}
