/**
 * Property Tests for ParticleSubEmitter.ts
 *
 * Comprehensive fast-check property tests for:
 * - Construction
 * - Sub-emitter management
 * - Death event processing
 * - Particle spawning
 * - Config validation
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import {
  ParticleSubEmitter,
  type DeathEvent,
} from "@/engine/particles/ParticleSubEmitter";
import type { SubEmitterConfig } from "@/engine/particles/types";
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
  vel: { x: number; y: number; z: number } = { x: 0, y: 0, z: 0 },
  color: [number, number, number, number] = [1, 1, 1, 1],
  lifetime: number = 100,
): void {
  const offset = index * PARTICLE_STRIDE;
  buffer[offset + 0] = pos.x;
  buffer[offset + 1] = pos.y;
  buffer[offset + 2] = pos.z;
  buffer[offset + 3] = vel.x;
  buffer[offset + 4] = vel.y;
  buffer[offset + 5] = vel.z;
  buffer[offset + 6] = 0; // age
  buffer[offset + 7] = lifetime;
  buffer[offset + 8] = 1; // mass
  buffer[offset + 9] = 10; // size
  buffer[offset + 10] = 0; // rotation
  buffer[offset + 11] = 0; // angular velocity
  buffer[offset + 12] = color[0];
  buffer[offset + 13] = color[1];
  buffer[offset + 14] = color[2];
  buffer[offset + 15] = color[3];
}

function createDefaultSubEmitterConfig(): SubEmitterConfig {
  return {
    id: "subemitter-1",
    trigger: "death",
    parentEmitterId: "*",
    triggerProbability: 1.0,
    emitCount: 5,
    emitCountVariance: 2,
    inheritVelocity: 0.3,
    inheritSize: 0.5,
    inheritColor: 0.5,
    inheritRotation: 0,
    overrides: {
      initialSpeed: 100,
      emissionSpread: 180,
      lifetime: 30,
      initialMass: 1,
      initialSize: 5,
      initialAngularVelocity: 0,
      colorStart: [1, 0.5, 0, 1],
    },
  };
}

function createSeededRNG(seed: number): () => number {
  let s = seed;
  return () => {
    s = (s * 1103515245 + 12345) & 0x7fffffff;
    return s / 0x7fffffff;
  };
}

// ============================================================================
// ARBITRARIES
// ============================================================================

const arbOverrides = fc.record({
  initialSpeed: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(500), noNaN: true }),
    fc.constant(NaN),
  ),
  emissionSpread: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(360), noNaN: true }),
    fc.constant(NaN),
  ),
  lifetime: fc.oneof(
    fc.float({ min: Math.fround(1), max: Math.fround(500), noNaN: true }),
    fc.constant(0),
    fc.constant(NaN),
  ),
  initialMass: fc.oneof(
    fc.float({ min: Math.fround(0.1), max: Math.fround(100), noNaN: true }),
    fc.constant(NaN),
  ),
  initialSize: fc.oneof(
    fc.float({ min: Math.fround(1), max: Math.fround(100), noNaN: true }),
    fc.constant(NaN),
  ),
  initialAngularVelocity: fc.oneof(
    fc.float({ min: Math.fround(-10), max: Math.fround(10), noNaN: true }),
    fc.constant(NaN),
  ),
  colorStart: fc.tuple(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
  ) as fc.Arbitrary<[number, number, number, number]>,
});

const arbSubEmitterConfig: fc.Arbitrary<SubEmitterConfig> = fc.record({
  id: fc.string({ minLength: 1, maxLength: 10 }),
  trigger: fc.constantFrom("death", "birth", "collision") as fc.Arbitrary<"death" | "birth" | "collision">,
  parentEmitterId: fc.oneof(fc.constant("*"), fc.string({ minLength: 1, maxLength: 10 })),
  triggerProbability: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
  emitCount: fc.oneof(
    fc.integer({ min: 1, max: 20 }),
    fc.constant(0),
    fc.constant(NaN),
    fc.constant(Infinity),
  ),
  emitCountVariance: fc.oneof(
    fc.integer({ min: 0, max: 10 }),
    fc.constant(NaN),
  ),
  inheritVelocity: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  inheritSize: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  inheritColor: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  inheritRotation: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  overrides: arbOverrides,
});

// ============================================================================
// TESTS: Construction
// ============================================================================

describe("ParticleSubEmitter construction", () => {
  it("should handle any maxParticles value", () => {
    fc.assert(
      fc.property(
        fc.oneof(
          fc.integer({ min: 1, max: 10000 }),
          fc.constant(0),
          fc.constant(-100),
          fc.constant(Infinity),
        ),
        fc.integer({ min: 1, max: 1000000 }),
        (maxParticles, seed) => {
          const rng = createSeededRNG(seed);
          const system = new ParticleSubEmitter(maxParticles, rng);
          expect(system).toBeDefined();
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Sub-emitter management
// ============================================================================

describe("ParticleSubEmitter management", () => {
  let system: ParticleSubEmitter;

  beforeEach(() => {
    system = new ParticleSubEmitter(100, createSeededRNG(12345));
  });

  it("should add and remove sub-emitters", () => {
    expect(system.hasSubEmitters()).toBe(false);

    const config = createDefaultSubEmitterConfig();
    system.addSubEmitter(config);
    expect(system.hasSubEmitters()).toBe(true);
    expect(system.getSubEmitters().has(config.id)).toBe(true);

    system.removeSubEmitter(config.id);
    expect(system.hasSubEmitters()).toBe(false);
  });

  it("should handle adding with any config", () => {
    fc.assert(
      fc.property(arbSubEmitterConfig, (config) => {
        expect(() => system.addSubEmitter(config)).not.toThrow();
        expect(system.getSubEmitters().has(config.id)).toBe(true);
      }),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Death event processing
// ============================================================================

describe("ParticleSubEmitter.processDeathEvents", () => {
  let system: ParticleSubEmitter;
  let buffer: Float32Array;
  let freeIndices: number[];

  beforeEach(() => {
    system = new ParticleSubEmitter(10, createSeededRNG(12345));
    buffer = createParticleBuffer(10);
    freeIndices = [2, 3, 4, 5, 6, 7, 8, 9]; // Indices 0, 1 are "used"
  });

  it("should return 0 when no sub-emitters configured", () => {
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    system.queueDeathEvent({ index: 0 });

    const spawned = system.processDeathEvents(buffer, freeIndices);
    expect(spawned).toBe(0);
  });

  it("should spawn sub-particles on death", () => {
    const config = createDefaultSubEmitterConfig();
    config.emitCount = 3;
    config.emitCountVariance = 0;
    config.triggerProbability = 1.0;
    system.addSubEmitter(config);

    initParticle(buffer, 0, { x: 100, y: 200, z: 300 });
    system.queueDeathEvent({ index: 0 });

    const spawned = system.processDeathEvents(buffer, freeIndices);
    expect(spawned).toBe(3);
    expect(freeIndices.length).toBe(5); // 8 - 3 = 5
  });

  it("should not spawn when freeIndices is empty", () => {
    const config = createDefaultSubEmitterConfig();
    system.addSubEmitter(config);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    system.queueDeathEvent({ index: 0 });

    const spawned = system.processDeathEvents(buffer, []); // No free indices
    expect(spawned).toBe(0);
  });

  it("should skip invalid death index", () => {
    const config = createDefaultSubEmitterConfig();
    system.addSubEmitter(config);

    // Queue event with invalid index
    system.queueDeathEvent({ index: -1 });
    system.queueDeathEvent({ index: NaN });
    system.queueDeathEvent({ index: 1000 }); // Out of bounds

    const spawned = system.processDeathEvents(buffer, freeIndices);
    expect(spawned).toBe(0);
  });

  it("should respect trigger probability", () => {
    const config = createDefaultSubEmitterConfig();
    config.triggerProbability = 0; // Never trigger
    system.addSubEmitter(config);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    system.queueDeathEvent({ index: 0 });

    const spawned = system.processDeathEvents(buffer, freeIndices);
    expect(spawned).toBe(0);
  });

  it("should filter by parentEmitterId", () => {
    const config = createDefaultSubEmitterConfig();
    config.parentEmitterId = "specific-emitter";
    system.addSubEmitter(config);

    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    // Death event with different emitterId
    system.queueDeathEvent({ index: 0, emitterId: "other-emitter" });

    const spawned = system.processDeathEvents(buffer, freeIndices);
    expect(spawned).toBe(0);
  });

  it("should not produce NaN with any config", () => {
    fc.assert(
      fc.property(arbSubEmitterConfig, (config) => {
        // Only test death trigger
        config.trigger = "death";
        config.parentEmitterId = "*";
        config.triggerProbability = 1.0;

        const sys = new ParticleSubEmitter(10, createSeededRNG(42));
        sys.addSubEmitter(config);

        const buf = createParticleBuffer(10);
        initParticle(buf, 0, { x: 100, y: 200, z: 300 }, { x: 10, y: 20, z: 30 });

        const free = [2, 3, 4, 5, 6, 7, 8, 9];
        sys.queueDeathEvent({ index: 0 });

        sys.processDeathEvents(buf, free);

        // Check spawned particles don't have NaN
        for (let i = 2; i < 10; i++) {
          const offset = i * PARTICLE_STRIDE;
          for (let j = 0; j < PARTICLE_STRIDE; j++) {
            const val = buf[offset + j];
            // Values should be either 0 (unused) or finite
            expect(Number.isFinite(val) || val === 0).toBe(true);
          }
        }
      }),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Particle inheritance
// ============================================================================

describe("ParticleSubEmitter inheritance", () => {
  it("should inherit position from parent", () => {
    const system = new ParticleSubEmitter(10, createSeededRNG(12345));
    const config = createDefaultSubEmitterConfig();
    config.emitCount = 1;
    config.emitCountVariance = 0;
    system.addSubEmitter(config);

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 100, y: 200, z: 300 });

    system.queueDeathEvent({ index: 0 });
    system.processDeathEvents(buffer, [2]);

    // Check sub-particle position
    const offset = 2 * PARTICLE_STRIDE;
    expect(buffer[offset + 0]).toBe(100);
    expect(buffer[offset + 1]).toBe(200);
    expect(buffer[offset + 2]).toBe(300);
  });

  it("should inherit velocity when configured", () => {
    const system = new ParticleSubEmitter(10, createSeededRNG(12345));
    const config = createDefaultSubEmitterConfig();
    config.emitCount = 1;
    config.emitCountVariance = 0;
    config.inheritVelocity = 1.0; // Full inheritance
    config.overrides.initialSpeed = 0; // No new speed
    system.addSubEmitter(config);

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 50, y: 100, z: 150 });

    system.queueDeathEvent({ index: 0 });
    system.processDeathEvents(buffer, [2]);

    // Sub-particle should have inherited velocity
    const offset = 2 * PARTICLE_STRIDE;
    expect(buffer[offset + 3]).toBe(50); // vx
    expect(buffer[offset + 4]).toBe(100); // vy
    expect(buffer[offset + 5]).toBe(150); // vz
  });

  it("should inherit color when configured", () => {
    const system = new ParticleSubEmitter(10, createSeededRNG(12345));
    const config = createDefaultSubEmitterConfig();
    config.emitCount = 1;
    config.emitCountVariance = 0;
    config.inheritColor = 1.0; // Full inheritance
    system.addSubEmitter(config);

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 }, { x: 0, y: 0, z: 0 }, [1, 0, 0, 1]);

    system.queueDeathEvent({ index: 0 });
    system.processDeathEvents(buffer, [2]);

    // Sub-particle should have inherited color
    const offset = 2 * PARTICLE_STRIDE;
    expect(buffer[offset + 12]).toBe(1); // r
    expect(buffer[offset + 13]).toBe(0); // g
    expect(buffer[offset + 14]).toBe(0); // b
  });
});

// ============================================================================
// TESTS: Accessors
// ============================================================================

describe("ParticleSubEmitter accessors", () => {
  it("should track pending event count", () => {
    const system = new ParticleSubEmitter(10, createSeededRNG(12345));

    expect(system.getPendingEventCount()).toBe(0);

    system.queueDeathEvent({ index: 0 });
    system.queueDeathEvent({ index: 1 });

    expect(system.getPendingEventCount()).toBe(2);
  });

  it("should call emit callback when provided", () => {
    const system = new ParticleSubEmitter(10, createSeededRNG(12345));
    const config = createDefaultSubEmitterConfig();
    config.emitCount = 2;
    config.emitCountVariance = 0;
    system.addSubEmitter(config);

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });

    const emits: Array<{ index: number; emitterId: string; isSubEmitter: boolean }> = [];
    system.setEmitCallback((event) => emits.push(event));

    system.queueDeathEvent({ index: 0 });
    system.processDeathEvents(buffer, [2, 3, 4, 5]);

    expect(emits.length).toBe(2);
    expect(emits[0].isSubEmitter).toBe(true);
    expect(emits[0].emitterId).toBe(config.id);
  });
});

// ============================================================================
// TESTS: Reset and Clear
// ============================================================================

describe("ParticleSubEmitter reset and clear", () => {
  it("should clear pending events on reset", () => {
    const system = new ParticleSubEmitter(10, createSeededRNG(12345));

    system.queueDeathEvent({ index: 0 });
    system.queueDeathEvent({ index: 1 });
    expect(system.getPendingEventCount()).toBe(2);

    system.reset();
    expect(system.getPendingEventCount()).toBe(0);
  });

  it("should clear everything on clear", () => {
    const system = new ParticleSubEmitter(10, createSeededRNG(12345));
    system.addSubEmitter(createDefaultSubEmitterConfig());
    system.queueDeathEvent({ index: 0 });

    system.clear();

    expect(system.hasSubEmitters()).toBe(false);
    expect(system.getPendingEventCount()).toBe(0);
  });
});
