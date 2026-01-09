/**
 * Property Tests for ParticleAudioReactive.ts
 *
 * Comprehensive fast-check property tests for:
 * - Audio feature storage
 * - Binding management
 * - Modulation calculations
 * - Smoothing
 * - Trigger modes
 */

import { describe, it, expect, beforeEach } from "vitest";
import * as fc from "fast-check";
import { ParticleAudioReactive } from "@/engine/particles/ParticleAudioReactive";
import type {
  AudioBinding,
  AudioFeature,
  EmitterConfig,
  ForceFieldConfig,
} from "@/engine/particles/types";

// ============================================================================
// HELPERS
// ============================================================================

function createDefaultBinding(): AudioBinding {
  return {
    feature: "bass",
    target: "emitter",
    targetId: "emitter-1",
    parameter: "emissionRate",
    min: 0,
    max: 1,
    outputMin: 10,
    outputMax: 100,
    smoothing: 0.5,
    curve: "linear",
    triggerMode: "continuous",
  };
}

function createEmitterMap(): Map<
  string,
  EmitterConfig & { accumulator: number; velocity: unknown }
> {
  const emitter = {
    id: "emitter-1",
    enabled: true,
    position: { x: 0, y: 0, z: 0 },
    rotation: { x: 0, y: 0, z: 0 },
    scale: { x: 1, y: 1, z: 1 },
    emissionRate: 50,
    lifetime: 100,
    lifetimeVariance: 0,
    initialSpeed: 100,
    speedVariance: 0,
    emissionSpread: 45,
    shape: "point" as const,
    accumulator: 0,
    velocity: null,
  } as EmitterConfig & { accumulator: number; velocity: unknown };

  return new Map([["emitter-1", emitter]]);
}

function createForceFieldMap(): Map<string, ForceFieldConfig> {
  const field: ForceFieldConfig = {
    id: "field-1",
    type: "point",
    enabled: true,
    position: { x: 0, y: 0, z: 0 },
    strength: 100,
    falloffStart: 0,
    falloffEnd: 100,
    falloffType: "linear",
  };

  return new Map([["field-1", field]]);
}

// ============================================================================
// ARBITRARIES
// ============================================================================

const arbAudioFeature: fc.Arbitrary<AudioFeature> = fc.constantFrom(
  "bass",
  "mid",
  "treble",
  "rms",
  "onsets",
  "spectralCentroid",
);

const arbBinding: fc.Arbitrary<AudioBinding> = fc.record({
  feature: arbAudioFeature,
  target: fc.constantFrom("emitter", "forceField") as fc.Arbitrary<"emitter" | "forceField">,
  targetId: fc.string({ minLength: 1, maxLength: 10 }),
  parameter: fc.string({ minLength: 1, maxLength: 20 }),
  min: fc.oneof(
    fc.float({ min: Math.fround(-10), max: Math.fround(10), noNaN: true }),
    fc.constant(NaN),
  ),
  max: fc.oneof(
    fc.float({ min: Math.fround(-10), max: Math.fround(10), noNaN: true }),
    fc.constant(NaN),
  ),
  outputMin: fc.oneof(
    fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
    fc.constant(NaN),
  ),
  outputMax: fc.oneof(
    fc.float({ min: Math.fround(-1000), max: Math.fround(1000), noNaN: true }),
    fc.constant(NaN),
  ),
  smoothing: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
    fc.constant(-0.5),
    fc.constant(1.5),
  ),
  curve: fc.constantFrom("linear", "exponential", "logarithmic", "step") as fc.Arbitrary<
    "linear" | "exponential" | "logarithmic" | "step"
  >,
  triggerMode: fc.constantFrom("continuous", "onThreshold", "onBeat") as fc.Arbitrary<
    "continuous" | "onThreshold" | "onBeat"
  >,
  threshold: fc.oneof(
    fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
    fc.constant(NaN),
  ),
  stepCount: fc.integer({ min: 1, max: 20 }),
});

// ============================================================================
// TESTS: Audio Features
// ============================================================================

describe("ParticleAudioReactive audio features", () => {
  let system: ParticleAudioReactive;

  beforeEach(() => {
    system = new ParticleAudioReactive();
  });

  it("should store and retrieve audio features", () => {
    fc.assert(
      fc.property(
        arbAudioFeature,
        fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
        (feature, value) => {
          system.setFeature(feature, value);
          expect(system.getFeature(feature)).toBe(value);
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should return 0 for unset features", () => {
    fc.assert(
      fc.property(arbAudioFeature, (feature) => {
        expect(system.getFeature(feature)).toBe(0);
      }),
      { numRuns: 20 },
    );
  });

  it("should return all features as a map", () => {
    system.setFeature("bass", 0.5);
    system.setFeature("mid", 0.7);

    const features = system.getFeatures();
    expect(features.get("bass")).toBe(0.5);
    expect(features.get("mid")).toBe(0.7);
  });
});

// ============================================================================
// TESTS: Bindings
// ============================================================================

describe("ParticleAudioReactive bindings", () => {
  let system: ParticleAudioReactive;

  beforeEach(() => {
    system = new ParticleAudioReactive();
  });

  it("should store and retrieve bindings", () => {
    fc.assert(
      fc.property(fc.array(arbBinding, { minLength: 0, maxLength: 10 }), (bindings) => {
        system.setBindings(bindings);
        expect(system.getBindings()).toBe(bindings);
      }),
      { numRuns: 20 },
    );
  });
});

// ============================================================================
// TESTS: Modulation
// ============================================================================

describe("ParticleAudioReactive.applyModulation", () => {
  let system: ParticleAudioReactive;

  beforeEach(() => {
    system = new ParticleAudioReactive();
  });

  it("should modify emitter parameter based on audio", () => {
    const binding = createDefaultBinding();
    system.setBindings([binding]);
    system.setFeature("bass", 1.0); // Max value

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    system.applyModulation(emitters, forceFields);

    // With bass=1.0, output should be outputMax=100
    const emitter = emitters.get("emitter-1");
    expect(emitter?.emissionRate).toBe(100);
  });

  it("should apply smoothing correctly", () => {
    const binding = createDefaultBinding();
    binding.smoothing = 0.5; // 50% smoothing
    system.setBindings([binding]);

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    // First frame: bass = 1.0
    system.setFeature("bass", 1.0);
    system.applyModulation(emitters, forceFields);
    const firstValue = emitters.get("emitter-1")?.emissionRate;

    // Second frame: bass = 0.0
    system.setFeature("bass", 0.0);
    system.applyModulation(emitters, forceFields);
    const secondValue = emitters.get("emitter-1")?.emissionRate;

    // With smoothing, second value should be between 0 and first value
    expect(secondValue).toBeGreaterThan(10); // outputMin
    expect(secondValue).toBeLessThan(firstValue!);
  });

  it("should not produce NaN with any binding config", () => {
    fc.assert(
      fc.property(
        fc.array(arbBinding, { minLength: 1, maxLength: 5 }),
        fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
        (bindings, featureValue) => {
          const sys = new ParticleAudioReactive();
          sys.setBindings(bindings);

          // Set all features to same value
          for (const binding of bindings) {
            sys.setFeature(binding.feature, featureValue);
          }

          const emitters = createEmitterMap();
          const forceFields = createForceFieldMap();

          // Add targets for all bindings
          for (const binding of bindings) {
            if (binding.target === "emitter" && !emitters.has(binding.targetId)) {
              emitters.set(binding.targetId, {
                ...emitters.get("emitter-1")!,
                id: binding.targetId,
              });
            }
            if (binding.target === "forceField" && !forceFields.has(binding.targetId)) {
              forceFields.set(binding.targetId, {
                ...forceFields.get("field-1")!,
                id: binding.targetId,
              });
            }
          }

          expect(() => sys.applyModulation(emitters, forceFields)).not.toThrow();

          // Check no NaN values in emitters
          for (const emitter of emitters.values()) {
            for (const [key, value] of Object.entries(emitter)) {
              if (typeof value === "number") {
                expect(Number.isFinite(value)).toBe(true);
              }
            }
          }
        },
      ),
      { numRuns: 50 },
    );
  });

  it("should handle min === max gracefully", () => {
    const binding = createDefaultBinding();
    binding.min = 0.5;
    binding.max = 0.5; // Same value
    system.setBindings([binding]);
    system.setFeature("bass", 0.5);

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    expect(() => system.applyModulation(emitters, forceFields)).not.toThrow();
  });
});

// ============================================================================
// TESTS: Trigger Modes
// ============================================================================

describe("ParticleAudioReactive trigger modes", () => {
  let system: ParticleAudioReactive;

  beforeEach(() => {
    system = new ParticleAudioReactive();
  });

  it("should only apply onThreshold when above threshold", () => {
    const binding = createDefaultBinding();
    binding.triggerMode = "onThreshold";
    binding.threshold = 0.5;
    system.setBindings([binding]);

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    // Below threshold
    system.setFeature("bass", 0.3);
    system.applyModulation(emitters, forceFields);
    expect(emitters.get("emitter-1")?.emissionRate).toBe(50); // Unchanged

    // Above threshold
    system.setFeature("bass", 0.7);
    system.applyModulation(emitters, forceFields);
    expect(emitters.get("emitter-1")?.emissionRate).not.toBe(50); // Changed
  });

  it("should only apply onBeat when beat is detected", () => {
    const binding = createDefaultBinding();
    binding.triggerMode = "onBeat";
    system.setBindings([binding]);

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    // No beat
    system.setFeature("bass", 1.0);
    system.applyModulation(emitters, forceFields);
    expect(emitters.get("emitter-1")?.emissionRate).toBe(50); // Unchanged

    // With beat (onsets = 1)
    system.setFeature("onsets", 1.0);
    system.applyModulation(emitters, forceFields);
    expect(emitters.get("emitter-1")?.emissionRate).not.toBe(50); // Changed
  });
});

// ============================================================================
// TESTS: Curves
// ============================================================================

describe("ParticleAudioReactive curves", () => {
  let system: ParticleAudioReactive;

  beforeEach(() => {
    system = new ParticleAudioReactive();
  });

  it("should apply exponential curve", () => {
    const binding = createDefaultBinding();
    binding.curve = "exponential";
    binding.smoothing = 0;
    system.setBindings([binding]);

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    // At t=0.5, exponential gives t^2 = 0.25
    system.setFeature("bass", 0.5);
    system.applyModulation(emitters, forceFields);

    const expected = 10 + 0.25 * (100 - 10); // outputMin + t^2 * range
    expect(emitters.get("emitter-1")?.emissionRate).toBeCloseTo(expected, 1);
  });

  it("should apply logarithmic curve", () => {
    const binding = createDefaultBinding();
    binding.curve = "logarithmic";
    binding.smoothing = 0;
    system.setBindings([binding]);

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    // At t=0.25, logarithmic gives sqrt(t) = 0.5
    system.setFeature("bass", 0.25);
    system.applyModulation(emitters, forceFields);

    const expected = 10 + 0.5 * (100 - 10);
    expect(emitters.get("emitter-1")?.emissionRate).toBeCloseTo(expected, 1);
  });

  it("should apply step curve", () => {
    const binding = createDefaultBinding();
    binding.curve = "step";
    binding.stepCount = 4;
    binding.smoothing = 0;
    system.setBindings([binding]);

    const emitters = createEmitterMap();
    const forceFields = createForceFieldMap();

    // At t=0.3, with 4 steps: floor(0.3*4)/4 = 1/4 = 0.25
    system.setFeature("bass", 0.3);
    system.applyModulation(emitters, forceFields);

    const expected = 10 + 0.25 * (100 - 10);
    expect(emitters.get("emitter-1")?.emissionRate).toBeCloseTo(expected, 1);
  });
});

// ============================================================================
// TESTS: getModulation
// ============================================================================

describe("ParticleAudioReactive.getModulation", () => {
  let system: ParticleAudioReactive;

  beforeEach(() => {
    system = new ParticleAudioReactive();
  });

  it("should return modulation value for bound parameter", () => {
    const binding = createDefaultBinding();
    system.setBindings([binding]);
    system.setFeature("bass", 0.5);

    const modulation = system.getModulation("emitter", "emitter-1", "emissionRate");
    expect(modulation).toBeDefined();
    expect(modulation).toBeCloseTo(55, 0); // 10 + 0.5 * 90
  });

  it("should return undefined for unbound parameter", () => {
    const binding = createDefaultBinding();
    system.setBindings([binding]);

    const modulation = system.getModulation("emitter", "emitter-1", "nonexistent");
    expect(modulation).toBeUndefined();
  });

  it("should handle NaN in binding range", () => {
    const binding = createDefaultBinding();
    binding.min = NaN;
    binding.max = NaN;
    system.setBindings([binding]);
    system.setFeature("bass", 0.5);

    const modulation = system.getModulation("emitter", "emitter-1", "emissionRate");
    expect(modulation).toBeDefined();
    expect(Number.isFinite(modulation)).toBe(true);
  });
});

// ============================================================================
// TESTS: Reset and Clear
// ============================================================================

describe("ParticleAudioReactive reset and clear", () => {
  it("should clear smoothed values on reset", () => {
    const system = new ParticleAudioReactive();
    const binding = createDefaultBinding();
    binding.smoothing = 0.9;
    system.setBindings([binding]);

    // Apply modulation to create smoothed values
    system.setFeature("bass", 1.0);
    system.applyModulation(createEmitterMap(), createForceFieldMap());

    expect(system.getSmoothedAudioValues().size).toBeGreaterThan(0);

    system.reset();
    expect(system.getSmoothedAudioValues().size).toBe(0);
  });

  it("should clear everything on clear", () => {
    const system = new ParticleAudioReactive();
    system.setBindings([createDefaultBinding()]);
    system.setFeature("bass", 0.5);
    system.applyModulation(createEmitterMap(), createForceFieldMap());

    system.clear();

    expect(system.getBindings()).toHaveLength(0);
    expect(system.getFeatures().size).toBe(0);
    expect(system.getSmoothedAudioValues().size).toBe(0);
  });
});

// ============================================================================
// TESTS: Smoothed Values Save/Restore
// ============================================================================

describe("ParticleAudioReactive smoothed values", () => {
  it("should get and set smoothed values for caching", () => {
    const system = new ParticleAudioReactive();
    const binding = createDefaultBinding();
    binding.smoothing = 0.5;
    system.setBindings([binding]);

    system.setFeature("bass", 1.0);
    system.applyModulation(createEmitterMap(), createForceFieldMap());

    const cached = system.getSmoothedAudioValues();
    expect(cached.size).toBeGreaterThan(0);

    // Create new system and restore
    const newSystem = new ParticleAudioReactive();
    newSystem.setSmoothedAudioValues(cached);

    expect(newSystem.getSmoothedAudioValues().size).toBe(cached.size);
  });
});
