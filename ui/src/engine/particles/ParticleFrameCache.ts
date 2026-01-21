/**
 * Particle Frame Cache System
 *
 * Handles frame-based caching for particle systems to enable
 * efficient timeline scrubbing. Stores particle state snapshots
 * at configurable intervals and supports version-based invalidation.
 *
 * Extracted from GPUParticleSystem.ts for modularity.
 */

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
  emitterBurstTimers: Map<string, number>; // Burst interval timers for determinism
  particleEmitters: Map<number, string>; // Tracks which emitter spawned each particle for sub-emitter filtering
  audioSmoothedValues: Map<number, number>; // Audio EMA filter history for deterministic playback
  particleInitialValues: Map<
    number,
    { size: number; opacity: number; randomOffset: number }
  >; // Initial size/opacity values and random offset for lifetime modulation
}

export interface CacheStats {
  cachedFrames: number;
  version: number;
  currentFrame: number;
  cacheInterval: number;
  maxCacheSize: number;
  memoryUsageMB: number;
  maxMemoryMB: number;
}

// Memory safety constants
const PARTICLE_STRIDE = 16; // floats per particle (imported value)
const BYTES_PER_FLOAT = 4;
const BYTES_PER_PARTICLE = PARTICLE_STRIDE * BYTES_PER_FLOAT; // 64 bytes
const MB = 1024 * 1024;

/**
 * Maximum memory budget for particle cache (in MB)
 * This prevents browser tab crashes on memory-constrained devices
 */
const DEFAULT_MAX_CACHE_MEMORY_MB = 256;

// ============================================================================
// PARTICLE FRAME CACHE CLASS
// ============================================================================

export class ParticleFrameCacheSystem {
  private frameCache: Map<number, ParticleFrameCache> = new Map();
  private cacheVersion: number = 0;
  private cacheInterval: number = 30; // Cache every N frames
  private maxCacheSize: number = 100;
  private currentSimulatedFrame: number = -1;

  /** Number of particles this cache is configured for */
  private readonly maxParticles: number;

  /** Memory per cached frame in bytes */
  private readonly bytesPerCache: number;

  /** Maximum memory budget in bytes */
  private readonly maxMemoryBytes: number;

  constructor(
    maxParticles: number,
    cacheInterval: number = 30,
    maxCacheSize: number = 100,
    maxMemoryMB: number = DEFAULT_MAX_CACHE_MEMORY_MB,
  ) {
    // Validate maxParticles
    this.maxParticles = Number.isFinite(maxParticles) && maxParticles > 0
      ? Math.floor(maxParticles)
      : 10000;
    // Validate cacheInterval to prevent modulo by zero
    this.cacheInterval = Math.max(1, cacheInterval);

    // Calculate memory per cache entry
    // Each cache stores: Float32Array + freeIndices array + Maps
    // Float32Array dominates: maxParticles * 64 bytes
    this.bytesPerCache = maxParticles * BYTES_PER_PARTICLE;
    this.maxMemoryBytes = maxMemoryMB * MB;

    // Calculate safe maxCacheSize based on memory budget
    // Ensure at least 10 caches for usable scrubbing
    const memorySafeCacheSize = Math.max(
      10,
      Math.floor(this.maxMemoryBytes / this.bytesPerCache),
    );

    // Use the smaller of requested size vs memory-safe size
    this.maxCacheSize = Math.min(maxCacheSize, memorySafeCacheSize);

    // Log if we had to reduce cache size due to memory constraints
    if (this.maxCacheSize < maxCacheSize) {
      console.warn(
        `ParticleFrameCache: Reduced maxCacheSize from ${maxCacheSize} to ${this.maxCacheSize} ` +
          `due to memory constraints (${maxParticles} particles × ${this.maxCacheSize} caches = ` +
          `${((this.maxCacheSize * this.bytesPerCache) / MB).toFixed(1)}MB)`,
      );
    }
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
    emitters: Map<string, { accumulator: number; burstTimer?: number }>,
    particleEmitters: Map<number, string>, // Particle-to-emitter tracking for sub-emitter filtering
    audioSmoothedValues: Map<number, number>, // Audio EMA filter history for deterministic audio
    particleInitialValues: Map<
      number,
      { size: number; opacity: number; randomOffset: number }
    >, // Initial values for lifetime modulation (prevents exponential decay)
  ): void {
    // Don't cache if we've exceeded max size - remove oldest
    if (this.frameCache.size >= this.maxCacheSize) {
      const oldestFrame = Math.min(...this.frameCache.keys());
      this.frameCache.delete(oldestFrame);
    }

    // Save emitter accumulators and burst timers
    const emitterAccumulators = new Map<string, number>();
    const emitterBurstTimers = new Map<string, number>();
    // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
    for (const [id, emitter] of emitters) {
      emitterAccumulators.set(id, emitter.accumulator);
      const burstTimer = (typeof emitter.burstTimer === "number" && Number.isFinite(emitter.burstTimer)) ? emitter.burstTimer : 0;
      emitterBurstTimers.set(id, burstTimer);
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
      emitterBurstTimers,
      particleEmitters: new Map(particleEmitters), // Deep copy to prevent cache mutation
      audioSmoothedValues: new Map(audioSmoothedValues), // Deep copy to isolate cached state
      particleInitialValues: new Map(particleInitialValues), // Deep copy for frame independence
    });
  }

  /**
   * Restore particle state from a cached frame
   * @returns The cached frame data if restore succeeded, null if cache miss or version mismatch
   */
  restoreFromCache(frame: number): ParticleFrameCache {
    const cached = this.frameCache.get(frame);
    if (!cached) {
      throw new Error(`[ParticleFrameCache] Cache miss: Frame ${frame} not found in particle cache`);
    }
    if (cached.version !== this.cacheVersion) {
      throw new Error(`[ParticleFrameCache] Cache version mismatch: Frame ${frame} has version ${cached.version}, expected ${this.cacheVersion}`);
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
      if (
        cached &&
        cached.version === this.cacheVersion &&
        frame <= targetFrame &&
        frame > nearestFrame
      ) {
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
      memoryUsageMB: (validCount * this.bytesPerCache) / MB,
      maxMemoryMB: this.maxMemoryBytes / MB,
    };
  }

  /**
   * Get estimated memory usage in bytes
   */
  getMemoryUsage(): number {
    let validCount = 0;
    for (const cached of this.frameCache.values()) {
      if (cached.version === this.cacheVersion) {
        validCount++;
      }
    }
    return validCount * this.bytesPerCache;
  }

  /**
   * Get memory budget remaining in bytes
   */
  getMemoryRemaining(): number {
    return this.maxMemoryBytes - this.getMemoryUsage();
  }
}
