/**
 * Property Tests for ParticleFrameCache.ts
 *
 * Comprehensive fast-check property tests for:
 * - Construction and memory management
 * - Cache storage and retrieval
 * - Version-based invalidation
 * - Frame finding
 * - Statistics
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";
import {
  ParticleFrameCacheSystem,
  type ParticleFrameCache,
} from "@/engine/particles/ParticleFrameCache";

// ============================================================================
// HELPERS
// ============================================================================

const PARTICLE_STRIDE = 16;

function createMockState(particleCount: number): {
  particleBuffer: Float32Array;
  freeIndices: number[];
  simulationTime: number;
  rngState: number;
  emitters: Map<string, { accumulator: number; burstTimer?: number }>;
  particleEmitters: Map<number, string>;
  audioSmoothedValues: Map<number, number>;
  particleInitialValues: Map<number, { size: number; opacity: number; randomOffset: number }>;
} {
  return {
    particleBuffer: new Float32Array(particleCount * PARTICLE_STRIDE),
    freeIndices: [],
    simulationTime: 0,
    rngState: 12345,
    emitters: new Map([["emitter1", { accumulator: 0.5, burstTimer: 0 }]]),
    particleEmitters: new Map(),
    audioSmoothedValues: new Map(),
    particleInitialValues: new Map(),
  };
}

// ============================================================================
// ARBITRARIES
// ============================================================================

const positiveInt = (max = 10000) => fc.integer({ min: 1, max });
const nonNegativeInt = (max = 1000) => fc.integer({ min: 0, max });

const arbConstructorParams = fc.record({
  maxParticles: fc.oneof(
    positiveInt(100000),
    fc.constant(0),
    fc.constant(-100),
    fc.constant(NaN),
    fc.constant(Infinity),
  ),
  cacheInterval: fc.oneof(
    positiveInt(120),
    fc.constant(0),
    fc.constant(-10),
  ),
  maxCacheSize: fc.oneof(
    positiveInt(200),
    fc.constant(0),
    fc.constant(-10),
  ),
  maxMemoryMB: fc.oneof(
    positiveInt(1024),
    fc.constant(0),
    fc.constant(-10),
  ),
});

// ============================================================================
// TESTS: Construction
// ============================================================================

describe("ParticleFrameCacheSystem construction", () => {
  it("should handle any constructor params without crashing", () => {
    fc.assert(
      fc.property(arbConstructorParams, (params) => {
        const cache = new ParticleFrameCacheSystem(
          params.maxParticles,
          params.cacheInterval,
          params.maxCacheSize,
          params.maxMemoryMB,
        );
        expect(cache).toBeDefined();
        expect(cache.getCacheInterval()).toBeGreaterThanOrEqual(1);
      }),
      { numRuns: 100 },
    );
  });

  it("should default to 1 for invalid cacheInterval", () => {
    fc.assert(
      fc.property(
        fc.oneof(fc.constant(0), fc.constant(-10)),
        (invalidInterval) => {
          const cache = new ParticleFrameCacheSystem(1000, invalidInterval);
          expect(cache.getCacheInterval()).toBe(1);
        },
      ),
      { numRuns: 20 },
    );
  });

  it("should limit maxCacheSize by memory budget", () => {
    // 1000 particles * 64 bytes = 64KB per cache
    // 1MB budget = ~16 caches max
    const cache = new ParticleFrameCacheSystem(1000, 30, 1000, 1);
    const stats = cache.getStats();
    expect(stats.maxCacheSize).toBeLessThanOrEqual(16);
    expect(stats.maxCacheSize).toBeGreaterThanOrEqual(10); // Minimum is 10
  });
});

// ============================================================================
// TESTS: Cache Operations
// ============================================================================

describe("ParticleFrameCacheSystem.cacheState", () => {
  it("should store and retrieve particle state", () => {
    fc.assert(
      fc.property(
        nonNegativeInt(100),
        positiveInt(100),
        (frame, particleCount) => {
          const cache = new ParticleFrameCacheSystem(1000);
          const state = createMockState(particleCount);

          cache.cacheState(
            frame,
            state.particleBuffer,
            state.freeIndices,
            particleCount,
            state.simulationTime,
            state.rngState,
            state.emitters,
            state.particleEmitters,
            state.audioSmoothedValues,
            state.particleInitialValues,
          );

          const restored = cache.restoreFromCache(frame);
          expect(restored).not.toBeNull();
          expect(restored!.frame).toBe(frame);
          expect(restored!.particleCount).toBe(particleCount);
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should deep copy particleBuffer to prevent mutations", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    const state = createMockState(10);

    // Set a recognizable value
    state.particleBuffer[0] = 42;

    cache.cacheState(
      0,
      state.particleBuffer,
      state.freeIndices,
      10,
      state.simulationTime,
      state.rngState,
      state.emitters,
      state.particleEmitters,
      state.audioSmoothedValues,
      state.particleInitialValues,
    );

    // Mutate original
    state.particleBuffer[0] = 999;

    // Cached version should still have 42
    const restored = cache.restoreFromCache(0);
    expect(restored!.particleBuffer[0]).toBe(42);
  });

  it("should evict oldest cache when maxCacheSize exceeded", () => {
    const cache = new ParticleFrameCacheSystem(100, 1, 3); // Max 3 caches
    const state = createMockState(10);

    // Cache frames 0, 10, 20, 30
    for (let frame = 0; frame <= 30; frame += 10) {
      cache.cacheState(
        frame,
        state.particleBuffer,
        state.freeIndices,
        10,
        frame,
        state.rngState,
        state.emitters,
        state.particleEmitters,
        state.audioSmoothedValues,
        state.particleInitialValues,
      );
    }

    // Frame 0 should have been evicted (oldest)
    expect(cache.restoreFromCache(0)).toBeNull();
    // Frame 30 should still exist
    expect(cache.restoreFromCache(30)).not.toBeNull();
  });
});

// ============================================================================
// TESTS: Version Invalidation
// ============================================================================

describe("ParticleFrameCacheSystem.invalidateCache", () => {
  it("should invalidate all cached frames", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    const state = createMockState(10);

    // Cache a frame
    cache.cacheState(
      0,
      state.particleBuffer,
      state.freeIndices,
      10,
      0,
      state.rngState,
      state.emitters,
      state.particleEmitters,
      state.audioSmoothedValues,
      state.particleInitialValues,
    );

    expect(cache.restoreFromCache(0)).not.toBeNull();

    // Invalidate
    cache.invalidateCache();

    // Should no longer be valid
    expect(cache.restoreFromCache(0)).toBeNull();
  });

  it("should increment version on each invalidation", () => {
    fc.assert(
      fc.property(positiveInt(10), (invalidationCount) => {
        const cache = new ParticleFrameCacheSystem(1000);
        const initialVersion = cache.getVersion();

        for (let i = 0; i < invalidationCount; i++) {
          cache.invalidateCache();
        }

        expect(cache.getVersion()).toBe(initialVersion + invalidationCount);
      }),
      { numRuns: 20 },
    );
  });
});

// ============================================================================
// TESTS: Frame Finding
// ============================================================================

describe("ParticleFrameCacheSystem.findNearestCache", () => {
  it("should find exact cached frame", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    const state = createMockState(10);

    cache.cacheState(
      30,
      state.particleBuffer,
      state.freeIndices,
      10,
      30,
      state.rngState,
      state.emitters,
      state.particleEmitters,
      state.audioSmoothedValues,
      state.particleInitialValues,
    );

    expect(cache.findNearestCache(30)).toBe(30);
  });

  it("should find nearest cache at or before target", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    const state = createMockState(10);

    // Cache frames 0, 30, 60
    for (const frame of [0, 30, 60]) {
      cache.cacheState(
        frame,
        state.particleBuffer,
        state.freeIndices,
        10,
        frame,
        state.rngState,
        state.emitters,
        state.particleEmitters,
        state.audioSmoothedValues,
        state.particleInitialValues,
      );
    }

    // Target 45 should return 30 (nearest before)
    expect(cache.findNearestCache(45)).toBe(30);

    // Target 60 should return 60 (exact)
    expect(cache.findNearestCache(60)).toBe(60);

    // Target 15 should return 0 (nearest before)
    expect(cache.findNearestCache(15)).toBe(0);
  });

  it("should return -1 if no valid cache exists", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    expect(cache.findNearestCache(100)).toBe(-1);
  });

  it("should return -1 if all caches are after target", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    const state = createMockState(10);

    cache.cacheState(
      100,
      state.particleBuffer,
      state.freeIndices,
      10,
      100,
      state.rngState,
      state.emitters,
      state.particleEmitters,
      state.audioSmoothedValues,
      state.particleInitialValues,
    );

    expect(cache.findNearestCache(50)).toBe(-1);
  });
});

// ============================================================================
// TESTS: shouldCacheFrame
// ============================================================================

describe("ParticleFrameCacheSystem.shouldCacheFrame", () => {
  it("should return true for frames at cacheInterval multiples", () => {
    fc.assert(
      fc.property(
        positiveInt(120),
        nonNegativeInt(100),
        (interval, multiplier) => {
          const cache = new ParticleFrameCacheSystem(1000, interval);
          const frame = interval * multiplier;
          expect(cache.shouldCacheFrame(frame)).toBe(true);
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should return false for frames NOT at cacheInterval multiples", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: 2, max: 120 }),
        fc.integer({ min: 1, max: 100 }),
        (interval, offset) => {
          const cache = new ParticleFrameCacheSystem(1000, interval);
          // Ensure offset is not a multiple of interval
          const safeOffset = offset % interval === 0 ? 1 : offset % interval;
          const frame = interval + safeOffset;
          expect(cache.shouldCacheFrame(frame)).toBe(false);
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Frame Tracking
// ============================================================================

describe("ParticleFrameCacheSystem frame tracking", () => {
  it("should track current frame", () => {
    fc.assert(
      fc.property(fc.integer({ min: -1, max: 1000 }), (frame) => {
        const cache = new ParticleFrameCacheSystem(1000);
        cache.setCurrentFrame(frame);
        expect(cache.getCurrentFrame()).toBe(frame);
      }),
      { numRuns: 50 },
    );
  });

  it("should reset current frame on clearCache", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    cache.setCurrentFrame(100);
    cache.clearCache();
    expect(cache.getCurrentFrame()).toBe(-1);
  });

  it("should reset current frame on invalidateCache", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    cache.setCurrentFrame(100);
    cache.invalidateCache();
    expect(cache.getCurrentFrame()).toBe(-1);
  });
});

// ============================================================================
// TESTS: canContinueFrom
// ============================================================================

describe("ParticleFrameCacheSystem.canContinueFrom", () => {
  it("should return false if currentFrame is -1", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    expect(cache.canContinueFrom(10)).toBe(false);
  });

  it("should return false if targetFrame is before currentFrame", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    cache.setCurrentFrame(50);
    expect(cache.canContinueFrom(30)).toBe(false);
  });

  it("should return true for forward scrubbing within threshold", () => {
    const cache = new ParticleFrameCacheSystem(1000, 30); // interval = 30
    cache.setCurrentFrame(50);
    // Within 60 frames (2 * interval)
    expect(cache.canContinueFrom(100)).toBe(true);
  });

  it("should return false for large forward jumps", () => {
    const cache = new ParticleFrameCacheSystem(1000, 30); // interval = 30
    cache.setCurrentFrame(50);
    // Beyond 60 frames (2 * interval)
    expect(cache.canContinueFrom(200)).toBe(false);
  });
});

// ============================================================================
// TESTS: Statistics
// ============================================================================

describe("ParticleFrameCacheSystem statistics", () => {
  it("should report correct memory usage", () => {
    const cache = new ParticleFrameCacheSystem(1000, 30, 100, 256);
    const state = createMockState(10);

    // Cache 3 frames
    for (const frame of [0, 30, 60]) {
      cache.cacheState(
        frame,
        state.particleBuffer,
        state.freeIndices,
        10,
        frame,
        state.rngState,
        state.emitters,
        state.particleEmitters,
        state.audioSmoothedValues,
        state.particleInitialValues,
      );
    }

    const stats = cache.getStats();
    expect(stats.cachedFrames).toBe(3);
    expect(stats.memoryUsageMB).toBeGreaterThan(0);
  });

  it("should exclude invalidated frames from stats", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    const state = createMockState(10);

    cache.cacheState(
      0,
      state.particleBuffer,
      state.freeIndices,
      10,
      0,
      state.rngState,
      state.emitters,
      state.particleEmitters,
      state.audioSmoothedValues,
      state.particleInitialValues,
    );

    expect(cache.getStats().cachedFrames).toBe(1);

    cache.invalidateCache();

    expect(cache.getStats().cachedFrames).toBe(0);
  });
});

// ============================================================================
// TESTS: clearCache
// ============================================================================

describe("ParticleFrameCacheSystem.clearCache", () => {
  it("should remove all cached frames", () => {
    const cache = new ParticleFrameCacheSystem(1000);
    const state = createMockState(10);

    for (const frame of [0, 30, 60]) {
      cache.cacheState(
        frame,
        state.particleBuffer,
        state.freeIndices,
        10,
        frame,
        state.rngState,
        state.emitters,
        state.particleEmitters,
        state.audioSmoothedValues,
        state.particleInitialValues,
      );
    }

    cache.clearCache();

    expect(cache.restoreFromCache(0)).toBeNull();
    expect(cache.restoreFromCache(30)).toBeNull();
    expect(cache.restoreFromCache(60)).toBeNull();
    expect(cache.getStats().cachedFrames).toBe(0);
  });
});
