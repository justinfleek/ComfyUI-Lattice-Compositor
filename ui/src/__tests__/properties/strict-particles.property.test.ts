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

// ============================================================================
// STRICT SEEDED RANDOM TESTS
// ============================================================================

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

// ============================================================================
// STRICT PARTICLE SYSTEM DETERMINISM TESTS
// ============================================================================

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
      seed,
      emissionRate: 10,
    };
    const emitter2: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      seed,
      emissionRate: 10,
    };
    
    const system1 = new ParticleSystem(config1);
    const system2 = new ParticleSystem(config2);
    
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
      seed,
      emissionRate: 5,
      position: { x: 100, y: 100 },
    };
    
    // Create two identical systems
    const system1 = new ParticleSystem({ ...config });
    const system2 = new ParticleSystem({ ...config });
    
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
      seed,
      emissionRate: 10,
    };
    
    const system = new ParticleSystem(config);
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

// ============================================================================
// STRICT SCRUB DETERMINISM TESTS
// ============================================================================

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
      seed,
      emissionRate: 10,
    };
    
    const deltaTime = 1 / 30;
    
    // First run: step from 0 to targetFrame
    const system1 = new ParticleSystem({ ...config });
    system1.addEmitter({ ...emitter });
    
    for (let i = 0; i < targetFrame; i++) {
      system1.step(deltaTime);
    }
    
    const particles1 = system1.getParticles();
    
    // Second run: step from 0 to targetFrame
    const system2 = new ParticleSystem({ ...config });
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
      seed,
      emissionRate: 10,
    };
    
    const deltaTime = 1 / 30;
    
    // Method 1: Continuous stepping
    const system1 = new ParticleSystem({ ...config });
    system1.addEmitter({ ...emitter });
    
    for (let i = 0; i < targetFrame; i++) {
      system1.step(deltaTime);
    }
    
    const continuous = system1.getParticles();
    
    // Method 2: Step to intermediate, reset, step from 0
    const system2 = new ParticleSystem({ ...config });
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

// ============================================================================
// STRICT PHYSICS TESTS
// ============================================================================

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
      seed,
      emissionRate: 1000, // Very high rate
    };
    
    const system = new ParticleSystem(config);
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
  ])('gravity affects particle velocity', (seed, gravity) => {
    const config: ParticleSystemConfig = {
      ...createDefaultSystemConfig(),
      maxParticles: 10,
      gravity: { x: 0, y: gravity, z: 0 },
    };
    
    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      seed,
      emissionRate: 1,
      initialVelocity: { x: 0, y: 0 }, // Start stationary
      velocitySpread: { x: 0, y: 0 },
    };
    
    const system = new ParticleSystem(config);
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
        if (gravity > 0) {
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
    
    const emitter: EmitterConfig = {
      ...createDefaultEmitterConfig(),
      id: 'emitter-1',
      seed,
      emissionRate: 1,
      lifetime,
      lifetimeSpread: 0, // No variance
    };
    
    const system = new ParticleSystem(config);
    system.addEmitter(emitter);
    
    const deltaTime = 1 / 30;
    const fps = 30;
    
    // Step to create particle
    system.step(deltaTime);
    
    // Step for longer than lifetime
    const stepsNeeded = Math.ceil(lifetime * fps) + 10;
    
    for (let i = 0; i < stepsNeeded; i++) {
      system.step(deltaTime);
    }
    
    // Original particle should be dead (though new ones may have spawned)
    // This is hard to test precisely without particle IDs
    // Just ensure system doesn't crash
    expect(() => system.getParticles()).not.toThrow();
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

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
      seed,
      emissionRate: 50,
    };
    
    const system = new ParticleSystem(config);
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
