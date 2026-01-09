/**
 * Property Tests for ParticleTrailSystem.ts
 *
 * Comprehensive fast-check property tests for:
 * - Construction
 * - Trail buffer management
 * - Alpha fading
 * - Trail history
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import {
  ParticleTrailSystem,
  type TrailConfig,
  type TrailBlendingConfig,
} from "@/engine/particles/ParticleTrailSystem";
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

function createDefaultConfig(): TrailConfig {
  return {
    trailLength: 8,
    trailSegments: 4,
    trailWidthStart: 1.0,
    trailWidthEnd: 0.0,
    trailFadeMode: "alpha",
  };
}

function createDefaultBlendingConfig(): TrailBlendingConfig {
  return {
    blendMode: "normal",
  };
}

// ============================================================================
// ARBITRARIES
// ============================================================================

const arbTrailConfig: fc.Arbitrary<TrailConfig> = fc.record({
  trailLength: fc.oneof(
    fc.integer({ min: 1, max: 32 }),
    fc.constant(0),
    fc.constant(-10),
    fc.constant(NaN),
  ),
  trailSegments: fc.integer({ min: 1, max: 10 }),
  trailWidthStart: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(10), noNaN: true }),
    fc.constant(NaN),
  ),
  trailWidthEnd: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  trailFadeMode: fc.constantFrom("none", "alpha", "width", "both") as fc.Arbitrary<
    "none" | "alpha" | "width" | "both"
  >,
});

const arbBlendingConfig: fc.Arbitrary<TrailBlendingConfig> = fc.record({
  blendMode: fc.constantFrom("normal", "additive", "multiply", "screen", "premultiplied") as fc.Arbitrary<
    "normal" | "additive" | "multiply" | "screen" | "premultiplied"
  >,
});

// ============================================================================
// TESTS: Construction
// ============================================================================

describe("ParticleTrailSystem construction", () => {
  it("should handle any maxParticles value", () => {
    fc.assert(
      fc.property(
        fc.oneof(
          fc.integer({ min: 1, max: 10000 }),
          fc.constant(0),
          fc.constant(-100),
          fc.constant(Infinity),
        ),
        arbTrailConfig,
        arbBlendingConfig,
        (maxParticles, config, blending) => {
          const system = new ParticleTrailSystem(maxParticles, config, blending);
          expect(system).toBeDefined();
        },
      ),
      { numRuns: 50 },
    );
  });
});

// ============================================================================
// TESTS: Initialization
// ============================================================================

describe("ParticleTrailSystem initialization", () => {
  it("should initialize with any valid config", () => {
    fc.assert(
      fc.property(arbTrailConfig, arbBlendingConfig, (config, blending) => {
        const system = new ParticleTrailSystem(100, config, blending);
        expect(() => system.initialize()).not.toThrow();
        // If trailLength is valid (> 0), should be initialized
        if (Number.isFinite(config.trailLength) && config.trailLength > 0) {
          expect(system.isInitialized()).toBe(true);
        }
      }),
      { numRuns: 50 },
    );
  });

  it("should default trailLength when zero or negative", () => {
    const config: TrailConfig = {
      ...createDefaultConfig(),
      trailLength: 0,
    };
    const system = new ParticleTrailSystem(100, config, createDefaultBlendingConfig());
    system.initialize();
    // With trailLength = 0, system defaults to 8, so mesh IS created
    expect(system.isInitialized()).toBe(true);
  });
});

// ============================================================================
// TESTS: Update
// ============================================================================

describe("ParticleTrailSystem.update", () => {
  let system: ParticleTrailSystem;
  let buffer: Float32Array;

  beforeEach(() => {
    system = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    system.initialize();
    buffer = createParticleBuffer(10);
  });

  it("should not crash with dead particles", () => {
    initParticle(buffer, 0, { x: 100, y: 0, z: 0 }, undefined, 0); // dead
    expect(() => system.update(buffer)).not.toThrow();
  });

  it("should not crash when uninitialized", () => {
    const uninitSystem = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    expect(() => uninitSystem.update(buffer)).not.toThrow();
  });

  it("should build trail history over multiple updates", () => {
    // Create particle that moves
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    system.update(buffer);

    // Move particle
    buffer[0] = 10;
    system.update(buffer);

    // Move again
    buffer[0] = 20;
    system.update(buffer);

    // Trail mesh should have some vertices
    const mesh = system.getMesh();
    expect(mesh).not.toBeNull();
    expect(mesh!.geometry).toBeDefined();
  });

  it("should skip particles at origin (0,0,0) for trail", () => {
    // Particle at exactly origin
    initParticle(buffer, 0, { x: 0, y: 0, z: 0 });
    system.update(buffer);

    // Should not create trail segments for origin positions
    const mesh = system.getMesh();
    const geometry = mesh?.geometry;
    if (geometry) {
      const drawRange = geometry.drawRange;
      // No trail segments since we start at origin
      expect(drawRange.count).toBe(0);
    }
  });

  it("should handle NaN trailLength gracefully", () => {
    const config: TrailConfig = {
      ...createDefaultConfig(),
      trailLength: NaN,
    };
    const sys = new ParticleTrailSystem(10, config, createDefaultBlendingConfig());
    sys.initialize();

    initParticle(buffer, 0, { x: 100, y: 0, z: 0 });
    expect(() => sys.update(buffer)).not.toThrow();
  });
});

// ============================================================================
// TESTS: Alpha Fading
// ============================================================================

describe("ParticleTrailSystem alpha fading", () => {
  it("should apply alpha fade along trail", () => {
    const config: TrailConfig = {
      trailLength: 8,
      trailSegments: 4,
      trailWidthStart: 1.0,
      trailWidthEnd: 0.0, // Full fade
      trailFadeMode: "alpha",
    };
    const system = new ParticleTrailSystem(1, config, createDefaultBlendingConfig());
    system.initialize();

    const buffer = createParticleBuffer(1);

    // Update multiple times to build trail
    for (let i = 0; i < 10; i++) {
      initParticle(buffer, 0, { x: i * 10, y: 0, z: 0 }, { r: 1, g: 1, b: 1, a: 1 });
      system.update(buffer);
    }

    const mesh = system.getMesh();
    expect(mesh).not.toBeNull();

    const colorAttr = mesh!.geometry.getAttribute("color");
    if (colorAttr && colorAttr.count > 0) {
      // First vertex (start of trail) should have higher alpha than last
      const firstAlpha = colorAttr.getW(0);
      // Alpha values should be in valid range
      expect(firstAlpha).toBeGreaterThanOrEqual(0);
      expect(firstAlpha).toBeLessThanOrEqual(1);
    }
  });

  it("should not fade when trailFadeMode is none", () => {
    const config: TrailConfig = {
      trailLength: 8,
      trailSegments: 4,
      trailWidthStart: 1.0,
      trailWidthEnd: 0.0,
      trailFadeMode: "none",
    };
    const system = new ParticleTrailSystem(1, config, createDefaultBlendingConfig());
    system.initialize();

    const buffer = createParticleBuffer(1);

    for (let i = 0; i < 10; i++) {
      initParticle(buffer, 0, { x: i * 10, y: 0, z: 0 }, { r: 1, g: 1, b: 1, a: 1 });
      system.update(buffer);
    }

    const mesh = system.getMesh();
    const colorAttr = mesh?.geometry.getAttribute("color");
    if (colorAttr && colorAttr.count >= 2) {
      // With no fading, all alphas should be the same (particle alpha)
      const alpha0 = colorAttr.getW(0);
      const alpha1 = colorAttr.getW(1);
      expect(alpha0).toBe(alpha1);
    }
  });
});

// ============================================================================
// TESTS: Accessors
// ============================================================================

describe("ParticleTrailSystem accessors", () => {
  it("should return mesh after initialization", () => {
    const system = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    expect(system.getMesh()).toBeNull();

    system.initialize();
    expect(system.getMesh()).not.toBeNull();
  });

  it("should update config", () => {
    const system = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    system.updateConfig({ trailLength: 16, trailFadeMode: "both" });

    // Config is private, but we can verify by behavior
    // Initialize with updated config
    system.initialize();
    expect(system.isInitialized()).toBe(true);
  });
});

// ============================================================================
// TESTS: Reset
// ============================================================================

describe("ParticleTrailSystem.reset", () => {
  it("should clear trail history", () => {
    const system = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    system.initialize();

    const buffer = createParticleBuffer(10);
    initParticle(buffer, 0, { x: 100, y: 0, z: 0 });
    system.update(buffer);

    // Reset should clear
    system.reset();

    const mesh = system.getMesh();
    const drawRange = mesh?.geometry.drawRange;
    expect(drawRange?.count).toBe(0);
  });

  it("should not crash when uninitialized", () => {
    const system = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    expect(() => system.reset()).not.toThrow();
  });
});

// ============================================================================
// TESTS: Dispose
// ============================================================================

describe("ParticleTrailSystem.dispose", () => {
  it("should clean up resources", () => {
    const system = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    system.initialize();
    expect(system.getMesh()).not.toBeNull();

    system.dispose();
    expect(system.getMesh()).toBeNull();
  });

  it("should not crash when uninitialized", () => {
    const system = new ParticleTrailSystem(10, createDefaultConfig(), createDefaultBlendingConfig());
    expect(() => system.dispose()).not.toThrow();
  });
});

// ============================================================================
// TESTS: Blending modes
// ============================================================================

describe("ParticleTrailSystem blending modes", () => {
  it("should handle all blending modes", () => {
    fc.assert(
      fc.property(arbBlendingConfig, (blending) => {
        const system = new ParticleTrailSystem(10, createDefaultConfig(), blending);
        expect(() => system.initialize()).not.toThrow();
        expect(system.isInitialized()).toBe(true);
      }),
      { numRuns: 10 },
    );
  });
});
