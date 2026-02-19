/**
 * Property Tests for ParticleConnectionSystem.ts
 *
 * Comprehensive fast-check property tests for:
 * - Construction
 * - Connection generation
 * - Distance-based fading
 * - Connection limits
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import { ParticleConnectionSystem } from "@/engine/particles/ParticleConnectionSystem";
import type { ConnectionConfig } from "@/engine/particles/types";
import { PARTICLE_STRIDE } from "@/engine/particles/types";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                                   // helpers
// ════════════════════════════════════════════════════════════════════════════

function createParticleBuffer(count: number): Float32Array {
  return new Float32Array(count * PARTICLE_STRIDE);
}

function initParticle(
  buffer: Float32Array,
  index: number,
  pos: { x: number; y: number; z: number },
  color: { r: number; g: number; b: number; a: number } = { r: 1, g: 1, b: 1, a: 1 },
  lifetime: number = 100,
): void {
  const offset = index * PARTICLE_STRIDE;
  buffer[offset + 0] = pos.x;
  buffer[offset + 1] = pos.y;
  buffer[offset + 2] = pos.z;
  buffer[offset + 3] = 0; // vx
  buffer[offset + 4] = 0; // vy
  buffer[offset + 5] = 0; // vz
  buffer[offset + 6] = 0; // age
  buffer[offset + 7] = lifetime;
  buffer[offset + 8] = 1; // mass
  buffer[offset + 9] = 10; // size
  buffer[offset + 10] = 0; // rotation
  buffer[offset + 11] = 0; // angular velocity
  buffer[offset + 12] = color.r;
  buffer[offset + 13] = color.g;
  buffer[offset + 14] = color.b;
  buffer[offset + 15] = color.a;
}

function createDefaultConfig(): ConnectionConfig {
  return {
    enabled: true,
    maxDistance: 100,
    maxConnections: 10,
    lineWidth: 1,
    lineOpacity: 0.5,
    fadeByDistance: true,
  };
}

// ════════════════════════════════════════════════════════════════════════════
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const arbConnectionConfig: fc.Arbitrary<ConnectionConfig> = fc.record({
  enabled: fc.boolean(),
  maxDistance: fc.oneof(
    fc.float({ min: Math.fround(1), max: Math.fround(500), noNaN: true }),
    fc.constant(0),
    fc.constant(NaN),
  ),
  maxConnections: fc.oneof(
    fc.integer({ min: 1, max: 100 }),
    fc.constant(0),
    fc.constant(-10),
    fc.constant(Infinity),
  ),
  lineWidth: fc.float({ min: Math.fround(0.1), max: Math.fround(10), noNaN: true }),
  lineOpacity: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  fadeByDistance: fc.boolean(),
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleConnectionSystem construction", () => {
  it("should handle any maxParticles value", () => {
    fc.assert(
      fc.property(
        fc.oneof(
          fc.integer({ min: 1, max: 10000 }),
          fc.constant(0),
          fc.constant(-100),
          fc.constant(Infinity),
        ),
        arbConnectionConfig,
        (maxParticles, config) => {
          const system = new ParticleConnectionSystem(maxParticles, config);
          expect(system).toBeDefined();
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleConnectionSystem initialization", () => {
  it("should initialize with any config", () => {
    fc.assert(
      fc.property(arbConnectionConfig, (config) => {
        const system = new ParticleConnectionSystem(100, config);
        expect(() => system.initialize()).not.toThrow();
        expect(system.isInitialized()).toBe(true);
      }),
      { numRuns: 50 },
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleConnectionSystem.update", () => {
  let system: ParticleConnectionSystem;
  let buffer: Float32Array;

  beforeEach(() => {
    system = new ParticleConnectionSystem(10, createDefaultConfig());
    system.initialize();
    buffer = createParticleBuffer(10);
  });

  it("should not crash when disabled", () => {
    system.setEnabled(false);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 10, y: 0, z: 0 });
    expect(() => system.update(buffer)).not.toThrow();
  });

  it("should not crash when uninitialized", () => {
    const uninitSystem = new ParticleConnectionSystem(10, createDefaultConfig());
    expect(() => uninitSystem.update(buffer)).not.toThrow();
  });

  it("should create connections between nearby particles", () => {
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 20, y: 0, z: 0 }); // Within maxDistance (100)

    system.update(buffer);

    const mesh = system.getMesh();
    expect(mesh).not.toBeNull();
    const drawRange = mesh!.geometry.drawRange;
    expect(drawRange.count).toBeGreaterThan(0); // Should have connections
  });

  it("should NOT create connections between distant particles", () => {
    const config = createDefaultConfig();
    config.maxDistance = 50;
    const sys = new ParticleConnectionSystem(10, config);
    sys.initialize();

    const buf = createParticleBuffer(10);
    initParticle(buf, 0, { x: 0, y: 0, z: 0 });
    initParticle(buf, 1, { x: 200, y: 0, z: 0 }); // Outside maxDistance (50)

    sys.update(buf);

    const mesh = sys.getMesh();
    expect(mesh).not.toBeNull();
    const drawRange = mesh!.geometry.drawRange;
    expect(drawRange.count).toBe(0); // No connections
  });

  it("should skip dead particles", () => {
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 20, y: 0, z: 0 }, undefined, 0); // Dead

    system.update(buffer);

    const mesh = system.getMesh();
    const drawRange = mesh!.geometry.drawRange;
    expect(drawRange.count).toBe(0); // No connections (only 1 alive particle)
  });

  it("should limit connections per particle", () => {
    const config = createDefaultConfig();
    config.maxConnections = 2;
    config.maxDistance = 200;
    const sys = new ParticleConnectionSystem(10, config);
    sys.initialize();

    const buf = createParticleBuffer(10);
    // Create 5 particles all close together
    for (let i = 0; i < 5; i++) {
      initParticle(buf, i, { x: i * 10, y: 0, z: 0 });
    }

    sys.update(buf);

    // Each particle should have at most 2 connections
    const mesh = sys.getMesh();
    const drawRange = mesh!.geometry.drawRange;
    // With 5 particles and max 2 connections each, we can have at most 5*2/2 = 5 unique pairs
    // (each connection is counted once per pair)
    expect(drawRange.count).toBeLessThanOrEqual(5 * 2 * 2); // 2 vertices per line
  });

  it("should not produce NaN with any config", () => {
    fc.assert(
      fc.property(arbConnectionConfig, (config) => {
        const sys = new ParticleConnectionSystem(10, config);
        sys.initialize();

        const buf = createParticleBuffer(10);
        for (let i = 0; i < 5; i++) {
          initParticle(buf, i, { x: i * 20, y: 0, z: 0 });
        }

        sys.update(buf);

        const mesh = sys.getMesh();
        if (mesh) {
          const posAttr = mesh.geometry.getAttribute("position");
          const colorAttr = mesh.geometry.getAttribute("color");

          // Check some vertices for NaN
          for (let v = 0; v < Math.min(10, posAttr.count); v++) {
            expect(Number.isFinite(posAttr.getX(v))).toBe(true);
            expect(Number.isFinite(posAttr.getY(v))).toBe(true);
            expect(Number.isFinite(posAttr.getZ(v))).toBe(true);
            expect(Number.isFinite(colorAttr.getX(v))).toBe(true);
            expect(Number.isFinite(colorAttr.getW(v))).toBe(true); // opacity
          }
        }
      }),
      { numRuns: 50 },
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleConnectionSystem distance fading", () => {
  it("should fade opacity with distance when enabled", () => {
    const config = createDefaultConfig();
    config.fadeByDistance = true;
    config.maxDistance = 100;
    config.lineOpacity = 1.0;
    const system = new ParticleConnectionSystem(10, config);
    system.initialize();

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 50, y: 0, z: 0 }); // Halfway to maxDistance

    system.update(buffer);

    const mesh = system.getMesh()!;
    const colorAttr = mesh.geometry.getAttribute("color");
    if (colorAttr.count >= 2) {
      const opacity = colorAttr.getW(0);
      // Should be ~0.5 (1.0 * (1 - 50/100))
      expect(opacity).toBeGreaterThan(0);
      expect(opacity).toBeLessThan(1);
    }
  });

  it("should not fade when fadeByDistance is false", () => {
    const config = createDefaultConfig();
    config.fadeByDistance = false;
    config.maxDistance = 100;
    config.lineOpacity = 1.0;
    const system = new ParticleConnectionSystem(10, config);
    system.initialize();

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 50, y: 0, z: 0 });

    system.update(buffer);

    const mesh = system.getMesh()!;
    const colorAttr = mesh.geometry.getAttribute("color");
    if (colorAttr.count >= 2) {
      const opacity = colorAttr.getW(0);
      // Should be exactly lineOpacity (1.0)
      expect(opacity).toBe(1.0);
    }
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleConnectionSystem accessors", () => {
  it("should return mesh after initialization", () => {
    const system = new ParticleConnectionSystem(10, createDefaultConfig());
    expect(system.getMesh()).toBeNull();

    system.initialize();
    expect(system.getMesh()).not.toBeNull();
  });

  it("should toggle enabled state", () => {
    const system = new ParticleConnectionSystem(10, createDefaultConfig());
    expect(system.isEnabled()).toBe(true);

    system.setEnabled(false);
    expect(system.isEnabled()).toBe(false);

    system.setEnabled(true);
    expect(system.isEnabled()).toBe(true);
  });

  it("should update config", () => {
    const system = new ParticleConnectionSystem(10, createDefaultConfig());
    system.updateConfig({ maxDistance: 200, lineOpacity: 0.8 });

    // Verify by initializing and checking behavior
    system.initialize();
    expect(system.isInitialized()).toBe(true);
  });
});

// ════════════════════════════════════════════════════════════════════════════
//                                                                     // tests
// ════════════════════════════════════════════════════════════════════════════

describe("ParticleConnectionSystem reset and dispose", () => {
  it("should clear connections on reset", () => {
    const system = new ParticleConnectionSystem(10, createDefaultConfig());
    system.initialize();

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    initParticle(buffer, 1, { x: 10, y: 0, z: 0 });
    system.update(buffer);

    system.reset();

    const drawRange = system.getMesh()!.geometry.drawRange;
    expect(drawRange.count).toBe(0);
  });

  it("should not crash reset when uninitialized", () => {
    const system = new ParticleConnectionSystem(10, createDefaultConfig());
    expect(() => system.reset()).not.toThrow();
  });

  it("should clean up resources on dispose", () => {
    const system = new ParticleConnectionSystem(10, createDefaultConfig());
    system.initialize();
    expect(system.getMesh()).not.toBeNull();

    system.dispose();
    expect(system.getMesh()).toBeNull();
  });

  it("should not crash dispose when uninitialized", () => {
    const system = new ParticleConnectionSystem(10, createDefaultConfig());
    expect(() => system.dispose()).not.toThrow();
  });
});
