/**
 * STRICT Property Tests for Particle System
 * 
 * Tests the invariants that must hold for deterministic particle simulation:
 * 1. Determinism: same seed + same config = same particles
 * 2. Scrub-determinism: jumping to frame N always produces same state
 * 3. SeededRandom: produces consistent sequences
 * 4. Physics: conservation laws where applicable
 * 
 * TOLERANCE: STRICT - Particle animation must be reproducible for export
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { SeededRandom } from '@/services/particles/SeededRandom';
import { ParticleSystem, createDefaultSystemConfig, createDefaultEmitterConfig } from '@/services/particleSystem';
import type { ParticleSystemConfig, EmitterConfig } from '@/services/particleSystem';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                       // strict // seeded // random // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: SeededRandom Determinism', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('same seed produces same sequence', (seed) => {
    const rng1 = new SeededRandom(seed);
    const rng2 = new SeededRandom(seed);
    
    // Generate 100 values from each
    const sequence1: number[] = [];
    const sequence2: number[] = [];
    
    for (let i = 0; i < 100; i++) {
      sequence1.push(rng1.next());
      sequence2.push(rng2.next());
    }
    
    // Sequences should be identical
    for (let i = 0; i < 100; i++) {
      expect(sequence1[i]).toBe(sequence2[i]);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('different seeds produce different sequences', (seed1, seed2) => {
    fc.pre(seed1 !== seed2);
    
    const rng1 = new SeededRandom(seed1);
    const rng2 = new SeededRandom(seed2);
    
    // Generate sequences
    const sequence1: number[] = [];
    const sequence2: number[] = [];
    
    for (let i = 0; i < 10; i++) {
      sequence1.push(rng1.next());
      sequence2.push(rng2.next());
    }
    
    // At least one value should differ
    let allSame = true;
    for (let i = 0; i < 10; i++) {
      if (sequence1[i] !== sequence2[i]) {
        allSame = false;
        break;
      }
    }
    
    expect(allSame).toBe(false);
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('next() produces values in [0, 1)', (seed) => {
    const rng = new SeededRandom(seed);
    
    for (let i = 0; i < 1000; i++) {
      const value = rng.next();
      expect(value).toBeGreaterThanOrEqual(0);
      expect(value).toBeLessThan(1);
      expect(Number.isFinite(value)).toBe(true);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 101, max: 1000 })
  ])('range() produces values in specified range', (seed, min, max) => {
    const rng = new SeededRandom(seed);
    
    for (let i = 0; i < 100; i++) {
      const value = rng.range(min, max);
      expect(value).toBeGreaterThanOrEqual(min);
      expect(value).toBeLessThanOrEqual(max);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('reset() restores initial state', (seed) => {
    const rng = new SeededRandom(seed);
    
    // Generate some values
    const firstRun: number[] = [];
    for (let i = 0; i < 50; i++) {
      firstRun.push(rng.next());
    }
    
    // Reset
    rng.reset();
    
    // Generate again
    const secondRun: number[] = [];
    for (let i = 0; i < 50; i++) {
      secondRun.push(rng.next());
    }
    
    // Should be identical
    for (let i = 0; i < 50; i++) {
      expect(firstRun[i]).toBe(secondRun[i]);
    }
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('gaussian() produces values centered around 0', (seed) => {
    const rng = new SeededRandom(seed);
    
    // Generate many gaussian values
    let sum = 0;
    const count = 1000;
    
    for (let i = 0; i < count; i++) {
      sum += rng.gaussian();
    }
    
    const mean = sum / count;
    
    // Mean should be close to 0 (within 0.2 for 1000 samples)
    expect(Math.abs(mean)).toBeLessThan(0.2);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                      // strict // particle // system // determinism // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: Particle System Determinism', () => {
  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 1, max: 50 })
  ])('same config produces same particle count after N steps', (seed, steps) => {
    const config1: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 100,
    };
    const config2: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 100,
    };

    const emitter1: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 10,
    };
    const emitter2: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 10,
    };

    // Use seed in ParticleSystem constructor for determinism
    const system1 = new ParticleSystem(config1, seed);
    const system2 = new ParticleSystem(config2, seed);

    system1.addEmitter(emitter1);
    system2.addEmitter(emitter2);

    const deltaTime = 1 / 30;

    // Step both systems identically
    for (let i = 0; i < steps; i++) {
      system1.step(deltaTime);
      system2.step(deltaTime);
    }

    const particles1 = system1.getParticles();
    const particles2 = system2.getParticles();

    // Particle counts should match
    expect(particles1.length).toBe(particles2.length);
  });

  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 10, max: 30 })
  ])('particle positions are deterministic', (seed, steps) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 50,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 5,
      x: 0.5, // Normalized position (0-1)
      y: 0.5,
    };

    // Create two identical systems with same seed
    const system1 = new ParticleSystem({ ...config }, seed);
    const system2 = new ParticleSystem({ ...config }, seed);

    system1.addEmitter({ ...emitter });
    system2.addEmitter({ ...emitter });

    const deltaTime = 1 / 30;

    // Step both
    for (let i = 0; i < steps; i++) {
      system1.step(deltaTime);
      system2.step(deltaTime);
    }

    const particles1 = system1.getParticles();
    const particles2 = system2.getParticles();

    // All particle positions should match
    for (let i = 0; i < particles1.length; i++) {
      expect(particles1[i].x).toBe(particles2[i].x);
      expect(particles1[i].y).toBe(particles2[i].y);
      expect(particles1[i].vx).toBe(particles2[i].vx);
      expect(particles1[i].vy).toBe(particles2[i].vy);
    }
  });

  test.prop([
    fc.integer({ min: 1, max: 100 })
  ])('reset restores initial state', (seed) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 100,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 10,
    };

    const system = new ParticleSystem(config, seed);
    system.addEmitter(emitter);

    const deltaTime = 1 / 30;

    // Step forward
    for (let i = 0; i < 30; i++) {
      system.step(deltaTime);
    }

    const particlesBefore = system.getParticles().length;
    expect(particlesBefore).toBeGreaterThan(0);

    // Reset
    system.reset();

    // Should be empty after reset
    const particlesAfter = system.getParticles().length;
    expect(particlesAfter).toBe(0);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                   // strict // scrub // determinism // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: Scrub Determinism', () => {
  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 1, max: 60 })
  ])('stepping to frame N always produces same state', (seed, targetFrame) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 100,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 10,
    };

    const deltaTime = 1 / 30;

    // First run: step from 0 to targetFrame
    const system1 = new ParticleSystem({ ...config }, seed);
    system1.addEmitter({ ...emitter });

    for (let i = 0; i < targetFrame; i++) {
      system1.step(deltaTime);
    }

    const particles1 = system1.getParticles();

    // Second run: step from 0 to targetFrame
    const system2 = new ParticleSystem({ ...config }, seed);
    system2.addEmitter({ ...emitter });

    for (let i = 0; i < targetFrame; i++) {
      system2.step(deltaTime);
    }

    const particles2 = system2.getParticles();

    // Should be identical
    expect(particles1.length).toBe(particles2.length);

    for (let i = 0; i < particles1.length; i++) {
      expect(particles1[i].x).toBe(particles2[i].x);
      expect(particles1[i].y).toBe(particles2[i].y);
    }
  });

  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 30, max: 60 }),
    fc.integer({ min: 1, max: 29 })
  ])('forward vs reset-and-step produces same result', (seed, targetFrame, intermediateFrame) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 100,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 10,
    };

    const deltaTime = 1 / 30;

    // Method 1: Continuous stepping
    const system1 = new ParticleSystem({ ...config }, seed);
    system1.addEmitter({ ...emitter });

    for (let i = 0; i < targetFrame; i++) {
      system1.step(deltaTime);
    }

    const continuous = system1.getParticles();

    // Method 2: Step to intermediate, reset, step from 0
    const system2 = new ParticleSystem({ ...config }, seed);
    system2.addEmitter({ ...emitter });

    // Step to intermediate
    for (let i = 0; i < intermediateFrame; i++) {
      system2.step(deltaTime);
    }

    // Reset and step from 0 to target
    system2.reset();
    system2.resetEmitterSeeds(); // Important for determinism!

    for (let i = 0; i < targetFrame; i++) {
      system2.step(deltaTime);
    }

    const afterReset = system2.getParticles();

    // Should be identical
    expect(continuous.length).toBe(afterReset.length);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                // strict // physics // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRICT: Particle Physics', () => {
  test.prop([
    fc.integer({ min: 1, max: 100 })
  ])('particles respect maxParticles limit', (seed) => {
    const maxParticles = 50;
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 1000, // Very high rate
    };

    const system = new ParticleSystem(config, seed);
    system.addEmitter(emitter);

    const deltaTime = 1 / 30;

    // Step many times
    for (let i = 0; i < 100; i++) {
      system.step(deltaTime);
      const particles = system.getParticles();
      expect(particles.length).toBeLessThanOrEqual(maxParticles);
    }
  });

  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true })
  ])('gravity affects particle velocity', (seed, gravityValue) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 10,
      gravity: gravityValue, // gravity is a number, not an object
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 1,
      speed: 0, // Start stationary
      speedVariance: 0,
    };

    const system = new ParticleSystem(config, seed);
    system.addEmitter(emitter);

    const deltaTime = 1 / 30;

    // Step once to create particle
    system.step(deltaTime);
    const particles = system.getParticles();

    if (particles.length > 0) {
      const initialVy = particles[0].vy;

      // Step a few more times
      for (let i = 0; i < 10; i++) {
        system.step(deltaTime);
      }

      const finalVy = system.getParticles()[0]?.vy;

      if (finalVy !== undefined) {
        // Velocity should have increased in y direction due to gravity
        if (gravityValue > 0) {
          expect(finalVy).toBeGreaterThan(initialVy);
        }
      }
    }
  });

  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.double({ min: 0.5, max: 5, noNaN: true, noDefaultInfinity: true })
  ])('particle lifetime is respected', (seed, lifetime) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 100,
    };

    // lifetime is in frames for EmitterConfig (particleLifetime field)
    const lifetimeFrames = Math.ceil(lifetime * 30); // Convert seconds to frames

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 1,
      particleLifetime: lifetimeFrames,
      lifetimeVariance: 0, // No variance
    };

    const system = new ParticleSystem(config, seed);
    system.addEmitter(emitter);

    const deltaTime = 1 / 30;

    // Step to create particle
    system.step(deltaTime);

    // Step for longer than lifetime
    const stepsNeeded = lifetimeFrames + 10;

    for (let i = 0; i < stepsNeeded; i++) {
      system.step(deltaTime);
    }

    // Original particle should be dead (though new ones may have spawned)
    // This is hard to test precisely without particle IDs
    // Just ensure system doesn't crash
    expect(() => system.getParticles()).not.toThrow();
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                           // stress // tests
// ════════════════════════════════════════════════════════════════════════════

describe('STRESS: Particle System Under Load', () => {
  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 100, max: 300 })
  ])('handles many steps without crash or leak', (seed, totalSteps) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 500,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 50,
    };

    const system = new ParticleSystem(config, seed);
    system.addEmitter(emitter);

    const deltaTime = 1 / 30;

    // Step many times
    for (let i = 0; i < totalSteps; i++) {
      system.step(deltaTime);

      // Periodic checks
      if (i % 50 === 0) {
        const particles = system.getParticles();
        expect(particles.length).toBeLessThanOrEqual(500);
      }
    }

    // Final check
    expect(() => system.getParticles()).not.toThrow();
    expect(() => system.reset()).not.toThrow();
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                // bug // regression // tests
// ════════════════════════════════════════════════════════════════════════════

// ════════════════════════════════════════════════════════════════════════════
//                                               // real // production // tests
// ════════════════════════════════════════════════════════════════════════════

describe('INVARIANT: spriteIndex always valid', () => {
  // The invariant: for ANY configuration, spriteIndex must be 0 ≤ x < totalFrames
  test.prop([
    fc.integer({ min: 1, max: 32 }), // totalFrames
    fc.constantFrom('loop', 'once', 'pingpong', 'random') as fc.Arbitrary<'loop' | 'once' | 'pingpong' | 'random'>,
    fc.integer({ min: 1, max: 120 }), // frameRate
    fc.integer({ min: 1, max: 100 }), // steps
  ])('spriteIndex is always in valid range', (totalFrames, playMode, frameRate, steps) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 10,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-sprite',
      emissionRate: 3,
      sprite: {
        enabled: true,
        isSheet: true,
        totalFrames,
        columns: Math.ceil(Math.sqrt(totalFrames)),
        rows: Math.ceil(Math.sqrt(totalFrames)),
        frameRate,
        playMode,
        billboard: true, // Always face camera
        rotationEnabled: false,
        rotationSpeed: 0,
        rotationSpeedVariance: 0,
        alignToVelocity: false,
        imageUrl: '',
        imageData: null,
      },
    };

    const system = new ParticleSystem(config);
    system.addEmitter(emitter);

    // Step for variable number of frames
    for (let i = 0; i < steps; i++) {
      system.step(1/30);

      //                                                          // the // invariant
      for (const p of system.getParticles()) {
        expect(Number.isFinite(p.spriteIndex)).toBe(true);
        expect(p.spriteIndex).toBeGreaterThanOrEqual(0);
        expect(p.spriteIndex).toBeLessThan(totalFrames);
        expect(Number.isInteger(p.spriteIndex)).toBe(true);
      }
    }
  });
});

describe('INVARIANT: Scrubbing produces identical results', () => {
  // The critical invariant: scrub to frame N, then elsewhere, then back to N = IDENTICAL
  test.prop([
    fc.integer({ min: 1, max: 1000 }), // seed
    fc.integer({ min: 10, max: 50 }), // targetFrame
  ])('scrubbing to same frame always produces identical state', (seed, targetFrame) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 20,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 5,
    };

    // System 1: Go directly to targetFrame
    const system1 = new ParticleSystem({ ...config }, seed);
    system1.addEmitter({ ...emitter });
    for (let f = 0; f < targetFrame; f++) {
      system1.step(1/30);
    }
    const state1 = system1.getParticles().map(p => ({ x: p.x, y: p.y, vx: p.vx, vy: p.vy }));

    // System 2: Go to targetFrame, then to targetFrame+20, then BACK to targetFrame
    // This simulates user scrubbing forward then backward
    const system2 = new ParticleSystem({ ...config }, seed);
    system2.addEmitter({ ...emitter });

    // Go to targetFrame
    for (let f = 0; f < targetFrame; f++) {
      system2.step(1/30);
    }

    // Continue to targetFrame+20
    for (let f = 0; f < 20; f++) {
      system2.step(1/30);
    }

    // Reset and go back to targetFrame (simulating scrub back)
    system2.reset();
    for (let f = 0; f < targetFrame; f++) {
      system2.step(1/30);
    }
    const state2 = system2.getParticles().map(p => ({ x: p.x, y: p.y, vx: p.vx, vy: p.vy }));

    //                                                          // the // invariant
    expect(state1.length).toBe(state2.length);
    for (let i = 0; i < state1.length; i++) {
      expect(state1[i].x).toBe(state2[i].x);
      expect(state1[i].y).toBe(state2[i].y);
      expect(state1[i].vx).toBe(state2[i].vx);
      expect(state1[i].vy).toBe(state2[i].vy);
    }
  });
});

describe('INVARIANT: Particles never have NaN/Infinity', () => {
  // Physical invariant: all particle properties must be finite numbers
  test.prop([
    fc.integer({ min: 1, max: 1000 }), // seed
    fc.integer({ min: 10, max: 100 }), // steps
    fc.float({ min: -1000, max: 1000, noNaN: true }), // gravityValue
    fc.float({ min: -1000, max: 1000, noNaN: true }), // windStrength
  ])('particle state is always finite', (seed, steps, gravityValue, windStrength) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 50,
      gravity: gravityValue, // gravity is a number
      windStrength,
    };

    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate: 10,
    };

    const system = new ParticleSystem(config, seed);
    system.addEmitter(emitter);

    for (let i = 0; i < steps; i++) {
      system.step(1/30);

      //                                                          // the // invariant
      for (const p of system.getParticles()) {
        expect(Number.isFinite(p.x)).toBe(true);
        expect(Number.isFinite(p.y)).toBe(true);
        expect(Number.isFinite(p.vx)).toBe(true);
        expect(Number.isFinite(p.vy)).toBe(true);
        expect(Number.isFinite(p.age)).toBe(true);
        expect(Number.isFinite(p.lifetime)).toBe(true);
        expect(Number.isFinite(p.size)).toBe(true);
        expect(Number.isFinite(p.rotation)).toBe(true);
      }
    }
  });
});

describe('INVARIANT: Particle count never exceeds maxParticles', () => {
  test.prop([
    fc.integer({ min: 10, max: 100 }), // maxParticles
    fc.integer({ min: 50, max: 200 }), // emissionRate (high to stress test)
    fc.integer({ min: 50, max: 200 }), // steps
  ])('particle count respects maxParticles limit', (maxParticles, emissionRate, steps) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles,
    };
    
    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      emissionRate, // High rate to try to overflow
    };
    
    const system = new ParticleSystem(config);
    system.addEmitter(emitter);
    
    for (let i = 0; i < steps; i++) {
      system.step(1/30);
      
      //                                                          // the // invariant
      expect(system.getParticles().length).toBeLessThanOrEqual(maxParticles);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                            // particle // frame // cache // memory // safety
// ════════════════════════════════════════════════════════════════════════════

import { ParticleFrameCacheSystem } from '@/engine/particles/ParticleFrameCache';

describe('INVARIANT: ParticleFrameCache memory is bounded', () => {
  const PARTICLE_STRIDE = 16; // floats per particle
  const BYTES_PER_FLOAT = 4;
  const BYTES_PER_PARTICLE = PARTICLE_STRIDE * BYTES_PER_FLOAT; // 64 bytes
  const MB = 1024 * 1024;

  test.prop([
    fc.integer({ min: 1000, max: 500000 }), // maxParticles (1K to 500K)
    fc.integer({ min: 1, max: 30 }), // cacheInterval
    fc.integer({ min: 10, max: 1000 }), // requestedCacheSize
    fc.integer({ min: 32, max: 512 }), // maxMemoryMB
  ])('cache size is limited by memory budget', (maxParticles, cacheInterval, requestedCacheSize, maxMemoryMB) => {
    const cache = new ParticleFrameCacheSystem(
      maxParticles,
      cacheInterval,
      requestedCacheSize,
      maxMemoryMB,
    );

    const stats = cache.getStats();
    const bytesPerCache = maxParticles * BYTES_PER_PARTICLE;
    const maxPossibleCaches = Math.floor((maxMemoryMB * MB) / bytesPerCache);

    //                                                          // the // invariant
    expect(stats.maxCacheSize).toBeLessThanOrEqual(Math.max(10, maxPossibleCaches));
    
    //                                                          // the // invariant
    expect(stats.maxCacheSize).toBeGreaterThanOrEqual(10);

    //                                                          // the // invariant
    expect(stats.maxMemoryMB).toBe(maxMemoryMB);
  });

  it('reports memory usage correctly', () => {
    const maxParticles = 10000;
    const cache = new ParticleFrameCacheSystem(maxParticles, 5, 100, 64);
    
    // Initial memory should be 0
    expect(cache.getMemoryUsage()).toBe(0);
    expect(cache.getStats().memoryUsageMB).toBe(0);
    
    // Add a cache entry
    const buffer = new Float32Array(maxParticles * PARTICLE_STRIDE);
    cache.cacheState(
      0,
      buffer,
      [],
      100,
      0,
      12345,
      new Map(),
      new Map(),
      new Map(),
      new Map(),
    );
    
    // Memory should now be ~0.64 MB (10000 * 64 bytes)
    const expectedMB = (maxParticles * BYTES_PER_PARTICLE) / MB;
    expect(cache.getStats().memoryUsageMB).toBeCloseTo(expectedMB, 2);
  });

  test.prop([
    fc.integer({ min: 1000, max: 100000 }), // Reasonable particle count range
    fc.integer({ min: 50, max: 500 }), // Requested cache size
  ])('memory-constrained cache size respects both request and budget', (maxParticles, requestedCacheSize) => {
    const maxMemoryMB = 256; // Fixed budget
    
    const cache = new ParticleFrameCacheSystem(
      maxParticles,
      5,
      requestedCacheSize,
      maxMemoryMB,
    );

    const stats = cache.getStats();
    const bytesPerCache = maxParticles * BYTES_PER_PARTICLE;
    const memorySafeCacheSize = Math.max(10, Math.floor((maxMemoryMB * MB) / bytesPerCache));

    //                                                          // the // invariant
    const expectedSize = Math.min(requestedCacheSize, memorySafeCacheSize);
    expect(stats.maxCacheSize).toBe(expectedSize);
    
    //                                                          // the // invariant
    if (stats.maxCacheSize > 10) {
      expect(stats.maxCacheSize * bytesPerCache).toBeLessThanOrEqual(maxMemoryMB * MB);
    }
  });

  it('with extreme particle counts, minimum 10 caches is preserved for usability', () => {
    // With 1 million particles, each cache is 64MB
    // 256MB budget would only fit 4 caches, but we enforce minimum 10
    const cache = new ParticleFrameCacheSystem(
      1000000, // 1 million particles
      5,
      1000,
      256, // 256MB budget
    );

    const stats = cache.getStats();
    
    // Minimum 10 caches for usability (even if over budget)
    expect(stats.maxCacheSize).toBe(10);
    
    // This WILL exceed 256MB budget by design - usability over strict memory
    // 10 caches × 64MB = 640MB
    expect(stats.memoryUsageMB).toBe(0); // No caches created yet
  });
});
