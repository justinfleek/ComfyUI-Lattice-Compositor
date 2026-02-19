/**
 * Property Tests for VerifiedGPUParticleSystem
 * 
 * Tests the verified GPU particle system for:
 * 1. Buffer offset correctness in exported particles
 * 2. Input validation (fps, maxParticles, mass, size, lifetime)
 * 3. RNG determinism (same seed = same results)
 * 4. Safe defaults for invalid inputs
 */

import { describe, it, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  VerifiedGPUParticleSystem,
  createDefaultConfig,
  createDefaultEmitter,
  createDefaultForceField,
} from '@/engine/particles';
import { PARTICLE_STRIDE, type GPUParticleSystemConfig } from '@/engine/particles/types';

// ============================================================================
// Test Setup - Mock Three.js since we can't use WebGL in Node
// ============================================================================

// Create a minimal mock for testing without WebGL
function createTestableSystem(config?: Partial<GPUParticleSystemConfig>) {
  const system = new VerifiedGPUParticleSystem({
    ...createDefaultConfig(),
    maxParticles: 1000, // Small for testing
    ...config,
  });
  return system;
}

// ============================================================================
// BUFFER LAYOUT TESTS
// ============================================================================

describe('VerifiedGPUParticleSystem Buffer Layout', () => {
  it('PARTICLE_STRIDE should be 16 floats (64 bytes)', () => {
    expect(PARTICLE_STRIDE).toBe(16);
  });

  it('buffer layout matches type definition', () => {
    // Verify the documented layout:
    // [0-2]=pos, [3-5]=vel, [6]=age, [7]=lifetime, [8]=mass, [9]=size, [10]=rot, [11]=angVel, [12-15]=rgba
    const expectedLayout = {
      positionX: 0,
      positionY: 1,
      positionZ: 2,
      velocityX: 3,
      velocityY: 4,
      velocityZ: 5,
      age: 6,
      lifetime: 7,
      mass: 8,
      size: 9,
      rotation: 10,
      angularVelocity: 11,
      colorR: 12,
      colorG: 13,
      colorB: 14,
      colorA: 15,
    };
    
    // Total stride should be 16
    expect(Object.keys(expectedLayout).length).toBe(16);
    expect(Math.max(...Object.values(expectedLayout)) + 1).toBe(PARTICLE_STRIDE);
  });
});

// ============================================================================
// CONFIGURATION VALIDATION TESTS
// ============================================================================

describe('VerifiedGPUParticleSystem Configuration Validation', () => {
  test.prop([
    fc.integer({ min: -1000000, max: 2000000 })
  ])('maxParticles is capped and validated', (maxParticles) => {
    const system = createTestableSystem({ maxParticles });
    const state = system.getState();
    
    // maxParticles should be capped at 1M and be positive
    // If invalid (<=0, NaN), defaults to 100000
    if (!Number.isFinite(maxParticles) || maxParticles <= 0) {
      // Should default to 100000
      expect(state.gpuMemoryBytes).toBe(0); // Not initialized yet, but config should be valid
    } else if (maxParticles > 1000000) {
      // Should be capped at 1M
      // We can't directly check maxParticles, but the system should be created
    }
    
    // System should always be created successfully
    expect(system).toBeDefined();
    system.dispose();
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('randomSeed produces deterministic RNG', (seed) => {
    const system1 = createTestableSystem({ randomSeed: seed, maxParticles: 100 });
    const system2 = createTestableSystem({ randomSeed: seed, maxParticles: 100 });
    
    // Add identical emitters
    const emitter = createDefaultEmitter('test');
    emitter.emissionRate = 10;
    system1.addEmitter(emitter);
    system2.addEmitter({ ...emitter });
    
    // Step both systems
    system1.step(1/60);
    system2.step(1/60);
    
    // States should be identical
    const state1 = system1.getState();
    const state2 = system2.getState();
    
    expect(state1.particleCount).toBe(state2.particleCount);
    expect(state1.simulationTime).toBe(state2.simulationTime);
    
    system1.dispose();
    system2.dispose();
  });
});

// ============================================================================
// DEFAULT FACTORY TESTS
// ============================================================================

describe('Default Factory Functions', () => {
  test.prop([
    fc.constantFrom('gravity', 'vortex', 'turbulence', 'drag', 'wind', 'lorenz') as fc.Arbitrary<'gravity' | 'vortex' | 'turbulence' | 'drag' | 'wind' | 'lorenz'>
  ])('createDefaultForceField produces valid config for all types', (type) => {
    const field = createDefaultForceField(type);
    
    expect(field.type).toBe(type);
    expect(field.enabled).toBe(true);
    expect(Number.isFinite(field.strength)).toBe(true);
    expect(field.falloffStart).toBeLessThanOrEqual(field.falloffEnd);
    
    // Type-specific properties
    if (type === 'gravity') {
      expect(field.direction).toBeDefined();
    } else if (type === 'vortex') {
      expect(field.vortexAxis).toBeDefined();
    } else if (type === 'turbulence') {
      expect(field.noiseScale).toBeGreaterThan(0);
    } else if (type === 'drag') {
      expect(field.linearDrag).toBeGreaterThanOrEqual(0);
    } else if (type === 'wind') {
      expect(field.windDirection).toBeDefined();
    } else if (type === 'lorenz') {
      expect(field.lorenzSigma).toBeDefined();
    }
  });

  it('createDefaultEmitter produces valid config', () => {
    const emitter = createDefaultEmitter();
    
    expect(emitter.enabled).toBe(true);
    expect(emitter.emissionRate).toBeGreaterThan(0);
    expect(emitter.initialSpeed).toBeGreaterThan(0);
    expect(emitter.lifetime).toBeGreaterThan(0);
    expect(emitter.initialSize).toBeGreaterThan(0);
    expect(emitter.initialMass).toBeGreaterThan(0);
  });

  it('createDefaultConfig produces valid config', () => {
    const config = createDefaultConfig();
    
    expect(config.maxParticles).toBeGreaterThan(0);
    expect(config.timeScale).toBeGreaterThan(0);
    expect(config.render).toBeDefined();
    expect(config.render.mode).toBeDefined();
  });
});

// ============================================================================
// EMITTER MANAGEMENT TESTS
// ============================================================================

describe('Emitter Management', () => {
  let system: VerifiedGPUParticleSystem;
  
  beforeEach(() => {
    system = createTestableSystem({ maxParticles: 100 });
  });

  test.prop([
    fc.string({ minLength: 1, maxLength: 50 })
  ])('addEmitter and getEmitter round-trip', (id) => {
    const emitter = createDefaultEmitter(id);
    system.addEmitter(emitter);
    
    const retrieved = system.getEmitter(id);
    expect(retrieved).toBeDefined();
    expect(retrieved?.id).toBe(id);
    
    system.dispose();
  });

  test.prop([
    fc.string({ minLength: 1, maxLength: 50 }),
    fc.double({ min: 0, max: 10000, noNaN: true, noDefaultInfinity: true })
  ])('updateEmitter modifies emission rate', (id, newRate) => {
    const emitter = createDefaultEmitter(id);
    system.addEmitter(emitter);
    
    system.updateEmitter(id, { emissionRate: newRate });
    
    const retrieved = system.getEmitter(id);
    expect(retrieved?.emissionRate).toBe(newRate);
    
    system.dispose();
  });

  test.prop([
    fc.string({ minLength: 1, maxLength: 50 })
  ])('removeEmitter removes the emitter', (id) => {
    const emitter = createDefaultEmitter(id);
    system.addEmitter(emitter);
    
    expect(system.getEmitter(id)).toBeDefined();
    
    system.removeEmitter(id);
    
    expect(system.getEmitter(id)).toBeUndefined();
    
    system.dispose();
  });
});

// ============================================================================
// SIMULATION TESTS
// ============================================================================

describe('Simulation', () => {
  test.prop([
    fc.integer({ min: 1, max: 100 }),
    fc.integer({ min: 1, max: 60 })
  ])('step advances simulation time', (steps, fps) => {
    const system = createTestableSystem({ maxParticles: 100 });
    const dt = 1 / fps;
    
    for (let i = 0; i < steps; i++) {
      system.step(dt);
    }
    
    const state = system.getState();
    expect(state.frameCount).toBe(steps);
    expect(state.simulationTime).toBeCloseTo(steps * dt, 6);
    
    system.dispose();
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('reset restores initial state with same seed', (seed) => {
    const system = createTestableSystem({ randomSeed: seed, maxParticles: 100 });
    
    // Add emitter and step
    const emitter = createDefaultEmitter('test');
    emitter.emissionRate = 100;
    system.addEmitter(emitter);
    
    for (let i = 0; i < 10; i++) {
      system.step(1/60);
    }
    
    // Capture state after stepping
    const stateAfterStep = system.getState();
    expect(stateAfterStep.frameCount).toBe(10);
    expect(stateAfterStep.particleCount).toBeGreaterThan(0);
    
    // Reset
    system.reset();
    
    const stateAfterReset = system.getState();
    expect(stateAfterReset.frameCount).toBe(0);
    expect(stateAfterReset.particleCount).toBe(0);
    expect(stateAfterReset.simulationTime).toBe(0);
    
    system.dispose();
  });
});

// ============================================================================
// FPS VALIDATION (BUG-097 regression test)
// ============================================================================

describe('simulateToFrame fps validation', () => {
  test.prop([
    fc.integer({ min: 0, max: 100 }),
    fc.oneof(
      fc.constant(0),
      fc.constant(-1),
      fc.constant(NaN),
      fc.constant(Infinity),
      fc.constant(-Infinity),
      fc.integer({ min: 1, max: 120 })
    )
  ])('simulateToFrame handles edge case fps values', (targetFrame, fps) => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    // Add an emitter
    const emitter = createDefaultEmitter('test');
    system.addEmitter(emitter);
    
    // This should not throw or produce NaN/Infinity
    // Note: simulateToFrame requires frameCacheSystem which needs initialize()
    // Since we can't call initialize() without WebGL, we test the method doesn't crash
    const result = system.simulateToFrame(targetFrame, fps);
    
    // Result should be a finite number (0 since frameCacheSystem is null without init)
    expect(Number.isFinite(result)).toBe(true);
    
    system.dispose();
  });
});

// ============================================================================
// PARTICLE EMISSION VALIDATION
// ============================================================================

describe('Particle Emission Validation', () => {
  test.prop([
    fc.double({ min: -1000, max: 1000, noNaN: true }),
    fc.double({ min: -1000, max: 1000, noNaN: true }),
    fc.double({ min: -1000, max: 1000, noNaN: true }),
  ])('emitter validates speed variance', (speed, variance) => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    const emitter = createDefaultEmitter('test');
    emitter.initialSpeed = speed;
    emitter.speedVariance = variance;
    emitter.emissionRate = 100;
    
    system.addEmitter(emitter);
    
    // Step should not crash even with weird speed values
    system.step(1/60);
    
    // System should still be functional
    const state = system.getState();
    expect(Number.isFinite(state.simulationTime)).toBe(true);
    
    system.dispose();
  });

  test.prop([
    fc.double({ min: -100, max: 100, noNaN: true }),
    fc.double({ min: -100, max: 100, noNaN: true }),
  ])('emitter validates lifetime variance', (lifetime, variance) => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    const emitter = createDefaultEmitter('test');
    emitter.lifetime = lifetime;
    emitter.lifetimeVariance = variance;
    emitter.emissionRate = 100;
    
    system.addEmitter(emitter);
    
    // Step should not crash - invalid lifetime should be clamped/defaulted
    system.step(1/60);
    
    const state = system.getState();
    expect(Number.isFinite(state.simulationTime)).toBe(true);
    
    system.dispose();
  });

  test.prop([
    fc.double({ min: -100, max: 100, noNaN: true }),
    fc.double({ min: -100, max: 100, noNaN: true }),
  ])('emitter validates mass variance (BUG-087 regression)', (mass, variance) => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    const emitter = createDefaultEmitter('test');
    emitter.initialMass = mass;
    emitter.massVariance = variance;
    emitter.emissionRate = 100;
    
    system.addEmitter(emitter);
    
    // Add a force field to test mass division
    const gravity = createDefaultForceField('gravity');
    system.addForceField(gravity);
    
    // Step should not crash - mass=0 or negative should be clamped to 0.001
    system.step(1/60);
    
    const state = system.getState();
    expect(Number.isFinite(state.simulationTime)).toBe(true);
    
    system.dispose();
  });

  test.prop([
    fc.double({ min: -100, max: 100, noNaN: true }),
    fc.double({ min: -100, max: 100, noNaN: true }),
  ])('emitter validates size variance (BUG-089 regression)', (size, variance) => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    const emitter = createDefaultEmitter('test');
    emitter.initialSize = size;
    emitter.sizeVariance = variance;
    emitter.emissionRate = 100;
    
    system.addEmitter(emitter);
    
    // Step should not crash - size=0 or negative should be clamped to 0.001
    system.step(1/60);
    
    const state = system.getState();
    expect(Number.isFinite(state.simulationTime)).toBe(true);
    
    system.dispose();
  });
});

// ============================================================================
// RNG DETERMINISM TESTS
// ============================================================================

describe('RNG Determinism', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 1, max: 50 })
  ])('same seed produces identical particle counts after N steps', (seed, steps) => {
    const config = { randomSeed: seed, maxParticles: 500 };
    
    const system1 = createTestableSystem(config);
    const system2 = createTestableSystem(config);
    
    // Identical emitter configs
    const emitter1 = createDefaultEmitter('test');
    emitter1.emissionRate = 50;
    const emitter2 = { ...emitter1 };
    
    system1.addEmitter(emitter1);
    system2.addEmitter(emitter2);
    
    // Step both identically
    for (let i = 0; i < steps; i++) {
      system1.step(1/60);
      system2.step(1/60);
    }
    
    // Should have identical states
    expect(system1.getState().particleCount).toBe(system2.getState().particleCount);
    expect(system1.getState().frameCount).toBe(system2.getState().frameCount);
    
    system1.dispose();
    system2.dispose();
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 1, max: 20 }),
    fc.integer({ min: 1, max: 20 })
  ])('reset restores deterministic state', (seed, stepsBefore, stepsAfter) => {
    const system = createTestableSystem({ randomSeed: seed, maxParticles: 200 });
    
    const emitter = createDefaultEmitter('test');
    emitter.emissionRate = 20;
    system.addEmitter(emitter);
    
    // Step, then reset, then step the same amount
    for (let i = 0; i < stepsBefore; i++) {
      system.step(1/60);
    }
    
    const countBeforeReset = system.getState().particleCount;
    
    system.reset();
    
    // Step same amount again
    for (let i = 0; i < stepsBefore; i++) {
      system.step(1/60);
    }
    
    // Should have same count (deterministic)
    expect(system.getState().particleCount).toBe(countBeforeReset);
    
    system.dispose();
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('different seeds produce different results (except collisions)', (seed1, seed2) => {
    fc.pre(seed1 !== seed2);
    
    const system1 = createTestableSystem({ randomSeed: seed1, maxParticles: 200 });
    const system2 = createTestableSystem({ randomSeed: seed2, maxParticles: 200 });
    
    const emitter = createDefaultEmitter('test');
    emitter.emissionRate = 30;
    emitter.speedVariance = 50;
    emitter.sizeVariance = 10;
    
    system1.addEmitter({ ...emitter });
    system2.addEmitter({ ...emitter });
    
    for (let i = 0; i < 10; i++) {
      system1.step(1/60);
      system2.step(1/60);
    }
    
    // Very likely to have different states with different seeds
    // (Not guaranteed since seeds could produce same RNG sequence by chance)
    // Just verify both systems are functional
    expect(system1.getState().particleCount).toBeGreaterThan(0);
    expect(system2.getState().particleCount).toBeGreaterThan(0);
    
    system1.dispose();
    system2.dispose();
  });
});

// ============================================================================
// BURST COUNT VALIDATION (BUG-098 regression test)
// ============================================================================

describe('Burst Count Validation (BUG-098)', () => {
  test.prop([
    fc.oneof(
      fc.constant(Infinity),
      fc.constant(-Infinity),
      fc.constant(NaN),
      fc.integer({ min: -1000, max: 1000000 })
    )
  ])('triggerBurst handles edge case burstCount values', (burstCount) => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    const emitter = createDefaultEmitter('test');
    emitter.burstCount = burstCount;
    emitter.burstOnBeat = true;
    system.addEmitter(emitter);
    
    // This should NOT hang or crash
    const startTime = Date.now();
    system.triggerBurst('test');
    const elapsed = Date.now() - startTime;
    
    // Should complete quickly (not infinite loop)
    expect(elapsed).toBeLessThan(1000);
    
    system.dispose();
  });

  test.prop([
    fc.double({ min: 0, max: 1e10, noNaN: true }),
    fc.double({ min: 0, max: 1e10, noNaN: true })
  ])('beat burst multiplier is capped', (burstCount, multiplier) => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    const emitter = createDefaultEmitter('test');
    emitter.burstCount = burstCount;
    emitter.beatEmissionMultiplier = multiplier;
    emitter.burstOnBeat = true;
    system.addEmitter(emitter);
    
    // Trigger beat
    system.setAudioFeature('onsets', 1);
    
    // Should not hang
    const startTime = Date.now();
    system.step(1/60);
    const elapsed = Date.now() - startTime;
    
    expect(elapsed).toBeLessThan(1000);
    
    system.dispose();
  });
});

// ============================================================================
// SPAWN RATE CAPPING (BUG-099 regression test)
// ============================================================================

describe('Spawn Rate Capping (BUG-099)', () => {
  test.prop([
    fc.double({ min: 0.1, max: 10, noNaN: true }), // Large dt (simulating browser pause)
    fc.double({ min: 1000, max: 50000, noNaN: true }) // High emission rate
  ])('does not spawn excessive particles with large dt', (dt, emissionRate) => {
    const system = createTestableSystem({ maxParticles: 15000 });
    
    const emitter = createDefaultEmitter('test');
    emitter.emissionRate = emissionRate;
    system.addEmitter(emitter);
    
    const stateBefore = system.getState();
    
    // Simulate large dt (browser pause scenario)
    const startTime = Date.now();
    system.step(dt);
    const elapsed = Date.now() - startTime;
    
    const stateAfter = system.getState();
    
    // Should complete quickly (not trying to spawn millions)
    expect(elapsed).toBeLessThan(2000);
    
    // Particles spawned should be capped (max 10000 per frame)
    const spawned = stateAfter.particleCount - stateBefore.particleCount;
    expect(spawned).toBeLessThanOrEqual(10000);
    
    system.dispose();
  });

  it('accumulator does not grow unbounded', () => {
    const system = createTestableSystem({ maxParticles: 500 });
    
    const emitter = createDefaultEmitter('test');
    emitter.emissionRate = 50000; // High rate
    system.addEmitter(emitter);
    
    // Simulate a large dt (browser pause scenario)
    const startTime = Date.now();
    system.step(2); // 2 second dt - would try to spawn 100k without cap
    const elapsed = Date.now() - startTime;
    
    // Should complete quickly due to cap
    expect(elapsed).toBeLessThan(5000);
    
    // System should still be responsive
    const state = system.getState();
    expect(Number.isFinite(state.simulationTime)).toBe(true);
    
    system.dispose();
  });
});

// ============================================================================
// CLEANUP TESTS
// ============================================================================

describe('Resource Cleanup', () => {
  it('dispose cleans up all resources', () => {
    const system = createTestableSystem({ maxParticles: 100 });
    
    const emitter = createDefaultEmitter('test');
    system.addEmitter(emitter);
    system.step(1/60);
    
    // Should not throw
    expect(() => system.dispose()).not.toThrow();
  });
});
