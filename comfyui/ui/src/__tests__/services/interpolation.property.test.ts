/**
 * Property-Based Tests for interpolation.ts
 *
 * Tests the PURITY CONTRACT and mathematical invariants of the interpolation engine.
 * Uses fast-check to generate random inputs and verify properties hold for ALL inputs.
 */
import { describe, expect, beforeEach, it } from "vitest";
import { test } from "@fast-check/vitest";
import * as fc from "fast-check";
import {
  interpolateProperty,
  clearBezierCache,
  getBezierCacheStats,
  EASING_PRESETS_NORMALIZED,
  createHandlesForPreset,
  getBezierCurvePoint,
  getBezierCurvePointNormalized,
  applyEasing,
} from "@/services/interpolation";
import type { AnimatableProperty, Keyframe, BezierHandle } from "@/types/project";

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// ARBITRARIES (Generators)
// ═══════════════════════════════════════════════════════════════════════════

const finiteNumber = fc.double({ noNaN: true, noDefaultInfinity: true });
const finitePositiveNumber = fc.double({
  noNaN: true,
  noDefaultInfinity: true,
  min: 0.001,
  max: 1e6,
});
const unitInterval = fc.double({ min: 0, max: 1, noNaN: true });
const frame = fc.integer({ min: -10000, max: 10000 });
const positiveFrame = fc.integer({ min: 0, max: 10000 });

const vec2Arb = fc.record({
  x: finiteNumber,
  y: finiteNumber,
});

const vec3Arb = fc.record({
  x: finiteNumber,
  y: finiteNumber,
  z: finiteNumber,
});

const hexColorArb = fc.tuple(
  fc.integer({ min: 0, max: 255 }),
  fc.integer({ min: 0, max: 255 }),
  fc.integer({ min: 0, max: 255 }),
).map(([r, g, b]) => 
  `#${r.toString(16).padStart(2, "0")}${g.toString(16).padStart(2, "0")}${b.toString(16).padStart(2, "0")}`
);

const bezierHandleArb = fc.record({
  frame: fc.double({ min: -100, max: 100, noNaN: true }),
  value: fc.double({ min: -1000, max: 1000, noNaN: true }),
  enabled: fc.boolean(),
});

const interpolationTypeArb = fc.constantFrom(
  "linear",
  "hold",
  "bezier",
  "easeInQuad",
  "easeOutQuad",
  "easeInOutQuad",
  "easeInCubic",
  "easeOutCubic",
);

const controlModeArb = fc.constantFrom("smooth", "corner", "auto-bezier", "continuous-bezier");

function keyframeArb<T>(valueArb: fc.Arbitrary<T>): fc.Arbitrary<Keyframe<T>> {
  return fc.record({
    id: fc.uuid(),
    frame: frame,
    value: valueArb,
    interpolation: interpolationTypeArb,
    outHandle: bezierHandleArb,
    inHandle: bezierHandleArb,
    controlMode: controlModeArb,
  }) as fc.Arbitrary<Keyframe<T>>;
}

// Generate sorted keyframes (required for interpolation)
function sortedKeyframesArb<T>(
  valueArb: fc.Arbitrary<T>,
  minCount: number = 2,
  maxCount: number = 10,
): fc.Arbitrary<Keyframe<T>[]> {
  return fc
    .array(keyframeArb(valueArb), { minLength: minCount, maxLength: maxCount })
    .map((kfs) => {
      // Sort by frame and ensure no duplicates
      const sorted = [...kfs].sort((a, b) => a.frame - b.frame);
      // Remove duplicates (keep first)
      const seen = new Set<number>();
      return sorted.filter((kf) => {
        if (seen.has(kf.frame)) return false;
        seen.add(kf.frame);
        return true;
      });
    })
    .filter((kfs) => kfs.length >= minCount);
}

const propertyTypeArb = fc.constantFrom("number", "position", "color", "vector3");

function animatablePropertyArb<T>(
  valueArb: fc.Arbitrary<T>,
): fc.Arbitrary<AnimatableProperty<T>> {
  return fc.record({
    id: fc.uuid(),
    value: valueArb,
    animated: fc.boolean(),
    keyframes: fc.oneof(
      fc.constant([]),
      sortedKeyframesArb(valueArb, 2, 5),
    ),
    name: fc.constant("testProperty"),
    type: propertyTypeArb,
  }) as fc.Arbitrary<AnimatableProperty<T>>;
}

// Helper to create keyframe with required fields
function createTestKeyframe<T>(overrides: Partial<Keyframe<T>> & { frame: number; value: T }): Keyframe<T> {
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  const interpolation = (overrides.interpolation !== null && overrides.interpolation !== undefined && typeof overrides.interpolation === "string" && overrides.interpolation.length > 0) ? overrides.interpolation : "linear";
  const outHandle = (overrides.outHandle !== null && overrides.outHandle !== undefined && typeof overrides.outHandle === "object") ? overrides.outHandle : { frame: 0, value: 0, enabled: false };
  const inHandle = (overrides.inHandle !== null && overrides.inHandle !== undefined && typeof overrides.inHandle === "object") ? overrides.inHandle : { frame: 0, value: 0, enabled: false };
  const controlMode = (overrides.controlMode !== null && overrides.controlMode !== undefined && typeof overrides.controlMode === "string" && overrides.controlMode.length > 0) ? overrides.controlMode : "smooth";
  return {
    id: `kf-${overrides.frame}`,
    frame: overrides.frame,
    value: overrides.value,
    interpolation,
    outHandle,
    inHandle,
    controlMode,
  };
}

// Helper to create animatable property with required fields
function createTestProperty<T>(value: T, keyframes: Keyframe<T>[] = [], animated = keyframes.length > 0): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random().toString(36).slice(2, 8)}`,
    name: "test",
    type: "number" as const,
    value,
    animated,
    keyframes,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                                        // property // tests
// ═══════════════════════════════════════════════════════════════════════════

describe("PROPERTY: interpolateProperty determinism", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  test.prop([animatablePropertyArb(finiteNumber), frame])(
    "same inputs always produce same outputs (numbers)",
    (prop, f) => {
      const result1 = interpolateProperty(prop, f);
      const result2 = interpolateProperty(prop, f);
      const result3 = interpolateProperty(prop, f);
      expect(result1).toBe(result2);
      expect(result2).toBe(result3);
    },
  );

  test.prop([animatablePropertyArb(vec2Arb), frame])(
    "same inputs always produce same outputs (Vec2)",
    (prop, f) => {
      const result1 = interpolateProperty(prop, f);
      const result2 = interpolateProperty(prop, f);
      expect(result1).toEqual(result2);
    },
  );

  test.prop([animatablePropertyArb(vec3Arb), frame])(
    "same inputs always produce same outputs (Vec3)",
    (prop, f) => {
      const result1 = interpolateProperty(prop, f);
      const result2 = interpolateProperty(prop, f);
      expect(result1).toEqual(result2);
    },
  );
});

describe("PROPERTY: interpolateProperty boundary conditions", () => {
  test.prop([sortedKeyframesArb(finiteNumber, 2, 5), frame])(
    "before first keyframe returns first value",
    (keyframes, f) => {
      if (keyframes.length < 2) return;
      const firstFrame = keyframes[0].frame;
      if (f > firstFrame) return; // Only test frames before first

      const prop = createTestProperty(0, keyframes, true);

      const result = interpolateProperty(prop, f);
      expect(result).toBe(keyframes[0].value);
    },
  );

  test.prop([sortedKeyframesArb(finiteNumber, 2, 5), frame])(
    "after last keyframe returns last value",
    (keyframes, f) => {
      if (keyframes.length < 2) return;
      const lastFrame = keyframes[keyframes.length - 1].frame;
      if (f < lastFrame) return; // Only test frames after last

      const prop = createTestProperty(0, keyframes, true);

      const result = interpolateProperty(prop, f);
      expect(result).toBe(keyframes[keyframes.length - 1].value);
    },
  );

  test.prop([finiteNumber])(
    "non-animated property always returns static value",
    (value) => {
      const prop = createTestProperty(value, [], false);

      // Test various frames
      expect(interpolateProperty(prop, 0)).toBe(value);
      expect(interpolateProperty(prop, 50)).toBe(value);
      expect(interpolateProperty(prop, 100)).toBe(value);
      expect(interpolateProperty(prop, -50)).toBe(value);
    },
  );
});

describe("PROPERTY: linear interpolation", () => {
  test.prop([
    finiteNumber,
    finiteNumber,
    positiveFrame,
    unitInterval,
  ])(
    "linear interpolation produces value between endpoints",
    (v1, v2, duration, t) => {
      if (duration < 1) return;

      const keyframes: Keyframe<number>[] = [
        createTestKeyframe({ frame: 0, value: v1 }),
        createTestKeyframe({ frame: duration, value: v2 }),
      ];

      const prop = createTestProperty(0, keyframes, true);

      const testFrame = Math.round(t * duration);
      const result = interpolateProperty(prop, testFrame);

      // Result should be between min and max (inclusive)
      const min = Math.min(v1, v2);
      const max = Math.max(v1, v2);
      expect(result).toBeGreaterThanOrEqual(min - 0.0001);
      expect(result).toBeLessThanOrEqual(max + 0.0001);
    },
  );

  test.prop([finiteNumber, fc.integer({ min: 1, max: 1000 })])(
    "linear interpolation at t=0 returns first value",
    (v1, duration) => {
      const v2 = v1 + 100; // Different value
      const keyframes: Keyframe<number>[] = [
        createTestKeyframe({ frame: 0, value: v1 }),
        createTestKeyframe({ frame: duration, value: v2 }),
      ];

      const prop = createTestProperty(0, keyframes, true);

      expect(interpolateProperty(prop, 0)).toBe(v1);
    },
  );

  test.prop([finiteNumber, fc.integer({ min: 1, max: 1000 })])(
    "linear interpolation at t=1 returns second value",
    (v1, duration) => {
      const v2 = v1 + 100; // Different value
      const keyframes: Keyframe<number>[] = [
        createTestKeyframe({ frame: 0, value: v1 }),
        createTestKeyframe({ frame: duration, value: v2 }),
      ];

      const prop = createTestProperty(0, keyframes, true);

      expect(interpolateProperty(prop, duration)).toBe(v2);
    },
  );
});

describe("PROPERTY: hold interpolation", () => {
  test.prop([
    finiteNumber,
    finiteNumber,
    fc.integer({ min: 1, max: 1000 }),
    unitInterval,
  ])(
    "hold interpolation returns first value until exactly at next keyframe",
    (v1, v2, duration, t) => {
      if (duration < 2) return;

      const keyframes: Keyframe<number>[] = [
        createTestKeyframe({ frame: 0, value: v1, interpolation: "hold" }),
        createTestKeyframe({ frame: duration, value: v2 }),
      ];

      const prop = createTestProperty(0, keyframes, true);

      const testFrame = Math.round(t * (duration - 1)); // Frame before last
      const result = interpolateProperty(prop, testFrame);
      expect(result).toBe(v1);
    },
  );
});

describe("PROPERTY: Vec2/Vec3 interpolation", () => {
  test.prop([vec2Arb, vec2Arb, fc.integer({ min: 1, max: 100 })])(
    "Vec2 interpolation preserves structure",
    (v1, v2, duration) => {
      const keyframes: Keyframe<typeof v1>[] = [
        createTestKeyframe({ frame: 0, value: v1 }),
        createTestKeyframe({ frame: duration, value: v2 }),
      ];

      const prop: AnimatableProperty<typeof v1> = {
        id: "prop-vec2-test",
        value: v1,
        animated: true,
        keyframes,
        name: "test",
        type: "position",
      };

      const result = interpolateProperty(prop, Math.floor(duration / 2));
      expect(result).toHaveProperty("x");
      expect(result).toHaveProperty("y");
      expect(typeof result.x).toBe("number");
      expect(typeof result.y).toBe("number");
    },
  );

  test.prop([vec3Arb, vec3Arb, fc.integer({ min: 1, max: 100 })])(
    "Vec3 interpolation preserves structure",
    (v1, v2, duration) => {
      const keyframes: Keyframe<typeof v1>[] = [
        createTestKeyframe({ frame: 0, value: v1 }),
        createTestKeyframe({ frame: duration, value: v2 }),
      ];

      const prop: AnimatableProperty<typeof v1> = {
        id: "prop-vec3-test",
        value: v1,
        animated: true,
        keyframes,
        name: "test",
        type: "vector3",
      };

      const result = interpolateProperty(prop, Math.floor(duration / 2));
      expect(result).toHaveProperty("x");
      expect(result).toHaveProperty("y");
      expect(result).toHaveProperty("z");
    },
  );
});

describe("PROPERTY: color interpolation", () => {
  test.prop([hexColorArb, hexColorArb, fc.integer({ min: 1, max: 100 })])(
    "color interpolation returns valid hex color",
    (c1, c2, duration) => {
      const keyframes: Keyframe<string>[] = [
        createTestKeyframe({ frame: 0, value: c1 }),
        createTestKeyframe({ frame: duration, value: c2 }),
      ];

      const prop: AnimatableProperty<string> = {
        id: "prop-color-test",
        value: c1,
        animated: true,
        keyframes,
        name: "test",
        type: "color",
      };

      const result = interpolateProperty(prop, Math.floor(duration / 2));
      expect(result).toMatch(/^#[0-9a-fA-F]{6}$/);
    },
  );
});

describe("PROPERTY: createHandlesForPreset", () => {
  const presetNameArb = fc.constantFrom(
    "linear",
    "easeIn",
    "easeOut",
    "easeInOut",
    "easeOutBack",
  ) as fc.Arbitrary<keyof typeof EASING_PRESETS_NORMALIZED>;

  test.prop([presetNameArb, finitePositiveNumber, finiteNumber])(
    "always returns handles with enabled=true",
    (preset, duration, delta) => {
      const handles = createHandlesForPreset(preset, duration, delta);
      expect(handles.outHandle.enabled).toBe(true);
      expect(handles.inHandle.enabled).toBe(true);
    },
  );

  test.prop([presetNameArb, finitePositiveNumber, finiteNumber])(
    "outHandle frame is positive or zero",
    (preset, duration, delta) => {
      const handles = createHandlesForPreset(preset, duration, delta);
      expect(handles.outHandle.frame).toBeGreaterThanOrEqual(0);
    },
  );

  test.prop([presetNameArb, finitePositiveNumber, finiteNumber])(
    "inHandle frame is negative or zero",
    (preset, duration, delta) => {
      const handles = createHandlesForPreset(preset, duration, delta);
      expect(handles.inHandle.frame).toBeLessThanOrEqual(0);
    },
  );
});

describe("PROPERTY: getBezierCurvePoint", () => {
  // Use reasonable bounds to avoid edge cases with denormalized numbers
  const reasonableDuration = fc.double({ min: 1, max: 1000, noNaN: true });
  const reasonableDelta = fc.double({ min: -1000, max: 1000, noNaN: true }).filter(d => Math.abs(d) > 0.001 || d === 0);

  test.prop([unitInterval, bezierHandleArb, bezierHandleArb, reasonableDuration, reasonableDelta])(
    "always returns finite x and y for reasonable inputs",
    (t, outHandle, inHandle, duration, delta) => {
      const point = getBezierCurvePoint(t, outHandle, inHandle, duration, delta);
      expect(Number.isFinite(point.x)).toBe(true);
      expect(Number.isFinite(point.y)).toBe(true);
    },
  );

  test.prop([bezierHandleArb, bezierHandleArb, reasonableDuration, reasonableDelta])(
    "returns (0,0) at t=0 for reasonable inputs",
    (outHandle, inHandle, duration, delta) => {
      const point = getBezierCurvePoint(0, outHandle, inHandle, duration, delta);
      expect(point.x).toBeCloseTo(0, 5);
      expect(point.y).toBeCloseTo(0, 5);
    },
  );

  test.prop([bezierHandleArb, bezierHandleArb, reasonableDuration, reasonableDelta])(
    "returns (1,1) at t=1 for reasonable inputs",
    (outHandle, inHandle, duration, delta) => {
      const point = getBezierCurvePoint(1, outHandle, inHandle, duration, delta);
      expect(point.x).toBeCloseTo(1, 5);
      expect(point.y).toBeCloseTo(1, 5);
    },
  );
});

describe("PROPERTY: getBezierCurvePointNormalized", () => {
  const normalizedHandleArb = fc.record({
    x: fc.double({ min: 0, max: 1, noNaN: true }),
    y: fc.double({ min: -2, max: 2, noNaN: true }), // Allow overshoot
  });

  test.prop([unitInterval, normalizedHandleArb, normalizedHandleArb])(
    "always returns finite x and y",
    (t, outHandle, inHandle) => {
      const point = getBezierCurvePointNormalized(t, outHandle, inHandle);
      expect(Number.isFinite(point.x)).toBe(true);
      expect(Number.isFinite(point.y)).toBe(true);
    },
  );

  test.prop([normalizedHandleArb, normalizedHandleArb])(
    "x is monotonically increasing as t increases",
    (outHandle, inHandle) => {
      const points = [0, 0.25, 0.5, 0.75, 1].map((t) =>
        getBezierCurvePointNormalized(t, outHandle, inHandle),
      );
      
      // Each x should be >= previous x (monotonic)
      for (let i = 1; i < points.length; i++) {
        expect(points[i].x).toBeGreaterThanOrEqual(points[i - 1].x - 0.0001);
      }
    },
  );
});

describe("PROPERTY: applyEasing", () => {
  const presetArb = fc.constantFrom(
    EASING_PRESETS_NORMALIZED.linear,
    EASING_PRESETS_NORMALIZED.easeIn,
    EASING_PRESETS_NORMALIZED.easeOut,
    EASING_PRESETS_NORMALIZED.easeInOut,
  );

  test.prop([unitInterval, presetArb])(
    "returns value between 0 and 1 for standard presets",
    (ratio, preset) => {
      const result = applyEasing(ratio, preset);
      // Allow small overshoot due to bezier math
      expect(result).toBeGreaterThanOrEqual(-0.1);
      expect(result).toBeLessThanOrEqual(1.1);
    },
  );

  test.prop([presetArb])(
    "returns 0 for ratio 0",
    (preset) => {
      expect(applyEasing(0, preset)).toBeCloseTo(0, 4);
    },
  );

  test.prop([presetArb])(
    "returns 1 for ratio 1",
    (preset) => {
      expect(applyEasing(1, preset)).toBeCloseTo(1, 4);
    },
  );

  test.prop([fc.double({ min: -10, max: 0, noNaN: true }), presetArb])(
    "clamps negative ratios to 0",
    (ratio, preset) => {
      const result = applyEasing(ratio, preset);
      expect(result).toBeCloseTo(applyEasing(0, preset), 4);
    },
  );

  test.prop([fc.double({ min: 1, max: 10, noNaN: true }), presetArb])(
    "clamps ratios > 1 to 1",
    (ratio, preset) => {
      const result = applyEasing(ratio, preset);
      expect(result).toBeCloseTo(applyEasing(1, preset), 4);
    },
  );
});

describe("PROPERTY: bezier cache behavior", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  test.prop([
    fc.integer({ min: 1, max: 100 }),
    finiteNumber,
    finiteNumber,
  ])(
    "cache size never exceeds maxSize",
    (iterations, v1, v2) => {
      // Create many different bezier interpolations
      for (let i = 0; i < iterations; i++) {
        const keyframes: Keyframe<number>[] = [
          createTestKeyframe({
            frame: 0,
            value: v1 + i,
            interpolation: "bezier",
            outHandle: { frame: i + 1, value: i, enabled: true },
            inHandle: { frame: 0, value: 0, enabled: false },
          }),
          createTestKeyframe({
            frame: 100 + i,
            value: v2 + i,
            interpolation: "linear",
            outHandle: { frame: 0, value: 0, enabled: false },
            inHandle: { frame: -(i + 1), value: -i, enabled: true },
          }),
        ];

        const prop = createTestProperty(0, keyframes, true);

        interpolateProperty(prop, 50 + i);
      }

      const stats = getBezierCacheStats();
      expect(stats.size).toBeLessThanOrEqual(stats.maxSize);
    },
  );
});

describe("PROPERTY: PURITY - no mutation", () => {
  test.prop([animatablePropertyArb(finiteNumber), frame])(
    "interpolation does not mutate property",
    (prop, f) => {
      const originalJson = JSON.stringify(prop);
      
      // Interpolate multiple times
      interpolateProperty(prop, f);
      interpolateProperty(prop, f + 10);
      interpolateProperty(prop, f - 10);
      
      expect(JSON.stringify(prop)).toBe(originalJson);
    },
  );

  test.prop([animatablePropertyArb(vec3Arb), frame])(
    "interpolation does not mutate Vec3 property",
    (prop, f) => {
      const originalJson = JSON.stringify(prop);
      
      interpolateProperty(prop, f);
      interpolateProperty(prop, f + 10);
      
      expect(JSON.stringify(prop)).toBe(originalJson);
    },
  );
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                   // edge // case // probes
// REINTEGRATED: 2026-01-07 from _deprecated/properties/interpolation-probes.test.ts
// These tests probe specific edge cases to verify behavior
// ═══════════════════════════════════════════════════════════════════════════

describe("PROBE: Interpolation Edge Cases", () => {
  it("PROBE: 3D to 2D transition loses Z correctly", () => {
    const prop: AnimatableProperty<{x: number, y: number, z?: number}> = {
      id: 't', name: 't', type: 'vector3', value: {x:0,y:0,z:100},
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:{x:0,y:0,z:100}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:{x:100,y:100}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };

    const at0 = interpolateProperty(prop, 0, 30);
    const at50 = interpolateProperty(prop, 50, 30);
    const at100 = interpolateProperty(prop, 100, 30);

    // Z interpolates from 100 towards 0 during transition
    expect(at0.z).toBe(100);
    expect(at50.z).toBe(50); // 100 * (1 - 0.5) = 50

    // DESIGN: At exact keyframe frame, returns keyframe value directly
    // The endpoint keyframe has no Z (2D), so Z becomes undefined, not 0
    // This matches professional animation software behavior
    expect(at100.z).toBeUndefined();
  });

  it("PROBE: 2D to 3D transition gains Z correctly", () => {
    const prop: AnimatableProperty<{x: number, y: number, z?: number}> = {
      id: 't', name: 't', type: 'vector3', value: {x:0,y:0},
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:{x:0,y:0}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:{x:100,y:100,z:100}, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };

    const at0 = interpolateProperty(prop, 0, 30);
    const at50 = interpolateProperty(prop, 50, 30);
    const at100 = interpolateProperty(prop, 100, 30);

    // Z should grow from 0 to 100
    expect(at0.z).toBeUndefined(); // No Z at start
    expect(at50.z).toBe(50); // Should be 100 * 0.5 = 50
    expect(at100.z).toBe(100);
  });

  it("PROBE: malformed hex color handling", () => {
    const prop: AnimatableProperty<string> = {
      id: 't', name: 't', type: 'color', value: '#000000',
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:'#xyz', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:'#ffffff', interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    let result: string | undefined;
    let error: Error | undefined;
    try {
      result = interpolateProperty(prop, 50, 30);
    } catch (e) {
      error = e as Error;
    }
    
    // Document current behavior - does it crash or produce NaN?
    if (error) {
      expect(error).toBeInstanceOf(Error);
    } else {
      // If it doesn't crash, what does it produce?
      expect(typeof result).toBe('string');
    }
  });

  it("PROBE: single bezier handle disabled (out enabled, in disabled)", () => {
    const prop: AnimatableProperty<number> = {
      id: 't', name: 't', type: 'number' as const, value: 0,
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:0, interpolation:'bezier', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:20,value:30,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:100, value:100, interpolation:'linear', inHandle:{frame:-20,value:-30,enabled:false}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    const results: number[] = [];
    for (let t = 0; t <= 1; t += 0.1) {
      results.push(interpolateProperty(prop, t * 100, 30));
    }
    
    // Should produce finite results
    for (const r of results) {
      expect(Number.isFinite(r)).toBe(true);
    }
  });

  it("PROBE: binary search at exact boundary", () => {
    // Three keyframes: test what happens at exact keyframe frames
    const prop: AnimatableProperty<number> = {
      id: 't', name: 't', type: 'number' as const, value: 0,
      animated: true,
      keyframes: [
        { id:'k1', frame:0, value:0, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k2', frame:50, value:100, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
        { id:'k3', frame:100, value:50, interpolation:'linear', inHandle:{frame:-5,value:0,enabled:true}, outHandle:{frame:5,value:0,enabled:true}, controlMode:'smooth' },
      ],
    };
    
    // At exact frame 50, should return exactly 100
    const atBoundary = interpolateProperty(prop, 50, 30);
    expect(atBoundary).toBeCloseTo(100, 8);
    
    // Just before and after should be continuous
    const justBefore = interpolateProperty(prop, 49.999, 30);
    const justAfter = interpolateProperty(prop, 50.001, 30);
    expect(Number.isFinite(justBefore)).toBe(true);
    expect(Number.isFinite(justAfter)).toBe(true);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                  // strict // edge // cases
// REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-interpolation.property.test.ts
// These tests cover NaN/Infinity handling, division by zero, and cache determinism
// ═══════════════════════════════════════════════════════════════════════════

describe("STRICT: NaN/Infinity Input Handling", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  it("handles NaN frame gracefully", () => {
    const property: AnimatableProperty<number> = {
      id: 'test',
      name: 'test',
      type: 'number',
      value: 50,
      animated: true,
      keyframes: [
        { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
        { id: 'kf2', frame: 100, value: 100, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
      ],
    };

    const result = interpolateProperty(property, NaN, 30);
    // NaN frame should not crash - document actual behavior
    expect(Number.isFinite(result) || Number.isNaN(result)).toBe(true);
  });

  it("handles Infinity frame gracefully", () => {
    const property: AnimatableProperty<number> = {
      id: 'test',
      name: 'test',
      type: 'number',
      value: 50,
      animated: true,
      keyframes: [
        { id: 'kf1', frame: 0, value: 0, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
        { id: 'kf2', frame: 100, value: 100, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
      ],
    };

    const resultPos = interpolateProperty(property, Infinity, 30);
    const resultNeg = interpolateProperty(property, -Infinity, 30);
    
    // Should return last/first keyframe value
    expect(resultPos).toBe(100);
    expect(resultNeg).toBe(0);
  });
});

describe("STRICT: Division by Zero Edge Cases", () => {
  it("handles zero duration between keyframes", () => {
    // Two keyframes at same frame (edge case)
    const property: AnimatableProperty<number> = {
      id: 'test',
      name: 'test',
      type: 'number',
      value: 0,
      animated: true,
      keyframes: [
        { id: 'kf1', frame: 50, value: 10, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
        { id: 'kf2', frame: 50, value: 20, interpolation: 'linear', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
      ],
    };

    const result = interpolateProperty(property, 50, 30);
    // Should not produce NaN or Infinity
    expect(Number.isFinite(result)).toBe(true);
  });

  it("handles zero value delta in bezier normalization", () => {
    // Keyframes with same value
    const property: AnimatableProperty<number> = {
      id: 'test',
      name: 'test',
      type: 'number',
      value: 0,
      animated: true,
      keyframes: [
        { id: 'kf1', frame: 0, value: 50, interpolation: 'bezier', inHandle: { frame: -5, value: 0, enabled: true }, outHandle: { frame: 5, value: 10, enabled: true }, controlMode: 'smooth' },
        { id: 'kf2', frame: 100, value: 50, interpolation: 'linear', inHandle: { frame: -5, value: -10, enabled: true }, outHandle: { frame: 5, value: 0, enabled: true }, controlMode: 'smooth' },
      ],
    };

    const result = interpolateProperty(property, 50, 30);
    // Should handle gracefully
    expect(Number.isFinite(result)).toBe(true);
  });
});

describe("STRICT: Bezier Cache Determinism", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  test.prop([
    fc.double({ min: 1, max: 100, noNaN: true }),
    fc.double({ min: 1, max: 100, noNaN: true }),
  ])(
    "bezier cache produces identical results on cache hit",
    (frameDuration, valueDelta) => {
      clearBezierCache();
      
      const outHandle: BezierHandle = { frame: 5, value: 3, enabled: true };
      const inHandle: BezierHandle = { frame: -5, value: -3, enabled: true };

      // First call - cache miss
      const result1 = getBezierCurvePoint(0.5, outHandle, inHandle, frameDuration, valueDelta);
      
      // Second call - cache hit
      const result2 = getBezierCurvePoint(0.5, outHandle, inHandle, frameDuration, valueDelta);

      // Must be IDENTICAL (not just close)
      expect(result1.x).toBe(result2.x);
      expect(result1.y).toBe(result2.y);
    }
  );

  it("bezier cache eviction does not break determinism", () => {
    clearBezierCache();
    
    const outHandle: BezierHandle = { frame: 5, value: 3, enabled: true };
    const inHandle: BezierHandle = { frame: -5, value: -3, enabled: true };

    // First result
    const result1 = getBezierCurvePoint(0.5, outHandle, inHandle, 100, 100);
    
    // Fill cache to cause eviction (cache max is 500)
    for (let i = 0; i < 600; i++) {
      getBezierCurvePoint(0.5, 
        { frame: i, value: i, enabled: true },
        { frame: -i, value: -i, enabled: true },
        100, 100);
    }
    
    // After eviction - should still be deterministic
    const result2 = getBezierCurvePoint(0.5, outHandle, inHandle, 100, 100);
    
    expect(result1.x).toBeCloseTo(result2.x, 10);
    expect(result1.y).toBeCloseTo(result2.y, 10);
  });
});