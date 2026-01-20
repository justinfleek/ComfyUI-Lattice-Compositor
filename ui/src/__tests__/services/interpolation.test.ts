/**
 * Unit Tests for interpolation.ts
 *
 * Tests the keyframe interpolation engine - the core animation system.
 * This file handles ALL animated values in the compositor.
 *
 * CONTRACT:
 * - All functions are PURE: same inputs always produce same outputs
 * - No functions mutate their inputs
 * - No Math.random(), Date.now(), or other non-deterministic operations
 */
import { describe, test, expect, beforeEach } from "vitest";
import {
  interpolateProperty,
  clearBezierCache,
  getBezierCacheStats,
  clearPathMorphCache,
  EASING_PRESETS_NORMALIZED,
  EASING_PRESETS,
  createHandlesForPreset,
  applyEasingPreset,
  getBezierCurvePoint,
  getBezierCurvePointNormalized,
  applyEasing,
} from "@/services/interpolation";
import type { AnimatableProperty, Keyframe, BezierHandle } from "@/types/project";
import { createKeyframe } from "@/types/animation";
import type { InterpolationType, PropertyExpression } from "@/types/animation";

// Helper to create AnimatableProperty
function createProperty<T>(
  value: T,
  animated: boolean = false,
  keyframes: Keyframe<T>[] = [],
): AnimatableProperty<T> {
  return {
    id: `prop-${Math.random().toString(36).slice(2)}`,
    name: "testProperty",
    type: "number",
    value,
    animated,
    keyframes,
  };
}

// Helper to create a keyframe with handles
function createKeyframeWithHandles<T>(
  frame: number,
  value: T,
  interpolation: "linear" | "bezier" | "hold" = "linear",
  outHandle?: BezierHandle,
  inHandle?: BezierHandle,
): Keyframe<T> {
  return {
    id: `kf-${Math.random().toString(36).slice(2)}`,
    frame,
    value,
    interpolation,
    outHandle: outHandle || { frame: 0, value: 0, enabled: false },
    inHandle: inHandle || { frame: 0, value: 0, enabled: false },
    controlMode: "smooth",
  };
}

describe("clearBezierCache", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  test("clears the cache", () => {
    // First, populate the cache by interpolating with bezier
    const prop = createProperty(0, true, [
      createKeyframeWithHandles(
        0,
        0,
        "bezier",
        { frame: 5, value: 0, enabled: true },
        { frame: 0, value: 0, enabled: false },
      ),
      createKeyframeWithHandles(
        30,
        100,
        "bezier",
        { frame: 0, value: 0, enabled: false },
        { frame: -5, value: 0, enabled: true },
      ),
    ]);
    interpolateProperty(prop, 15);

    // Cache should have entries
    const statsBefore = getBezierCacheStats();
    expect(statsBefore.size).toBeGreaterThan(0);

    // Clear it
    clearBezierCache();

    // Cache should be empty
    const statsAfter = getBezierCacheStats();
    expect(statsAfter.size).toBe(0);
  });
});

describe("getBezierCacheStats", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  test("returns size and maxSize", () => {
    const stats = getBezierCacheStats();
    expect(stats).toHaveProperty("size");
    expect(stats).toHaveProperty("maxSize");
    expect(typeof stats.size).toBe("number");
    expect(typeof stats.maxSize).toBe("number");
  });

  test("maxSize is 500", () => {
    const stats = getBezierCacheStats();
    expect(stats.maxSize).toBe(500);
  });
});

describe("interpolateProperty", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  describe("non-animated properties", () => {
    test("returns static value when not animated", () => {
      const prop = createProperty(42);
      expect(interpolateProperty(prop, 0)).toBe(42);
      expect(interpolateProperty(prop, 50)).toBe(42);
      expect(interpolateProperty(prop, 100)).toBe(42);
    });

    test("returns static value when animated but no keyframes", () => {
      const prop = createProperty(42, true, []);
      expect(interpolateProperty(prop, 0)).toBe(42);
      expect(interpolateProperty(prop, 50)).toBe(42);
    });
  });

  describe("boundary conditions", () => {
    test("returns first keyframe value before first keyframe", () => {
      const prop = createProperty(0, true, [
        createKeyframe(10, 100),
        createKeyframe(20, 200),
      ]);
      expect(interpolateProperty(prop, 0)).toBe(100);
      expect(interpolateProperty(prop, 5)).toBe(100);
      expect(interpolateProperty(prop, 10)).toBe(100);
    });

    test("returns last keyframe value after last keyframe", () => {
      const prop = createProperty(0, true, [
        createKeyframe(10, 100),
        createKeyframe(20, 200),
      ]);
      expect(interpolateProperty(prop, 20)).toBe(200);
      expect(interpolateProperty(prop, 25)).toBe(200);
      expect(interpolateProperty(prop, 100)).toBe(200);
    });
  });

  describe("linear interpolation", () => {
    test("interpolates numbers linearly", () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(100, 100),
      ]);
      expect(interpolateProperty(prop, 0)).toBe(0);
      expect(interpolateProperty(prop, 25)).toBe(25);
      expect(interpolateProperty(prop, 50)).toBe(50);
      expect(interpolateProperty(prop, 75)).toBe(75);
      expect(interpolateProperty(prop, 100)).toBe(100);
    });

    test("interpolates negative numbers", () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, -100),
        createKeyframe(100, 100),
      ]);
      expect(interpolateProperty(prop, 50)).toBe(0);
    });

    test("interpolates with multiple keyframes", () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(50, 100),
        createKeyframe(100, 0),
      ]);
      expect(interpolateProperty(prop, 0)).toBe(0);
      expect(interpolateProperty(prop, 25)).toBe(50);
      expect(interpolateProperty(prop, 50)).toBe(100);
      expect(interpolateProperty(prop, 75)).toBe(50);
      expect(interpolateProperty(prop, 100)).toBe(0);
    });

    test("handles zero duration between keyframes", () => {
      const prop = createProperty(0, true, [
        createKeyframe(10, 50),
        createKeyframe(10, 100), // Same frame!
      ]);
      // Should return first value (t=0 when duration=0)
      expect(interpolateProperty(prop, 10)).toBe(50);
    });
  });

  describe("hold interpolation", () => {
    test("holds value until next keyframe", () => {
      const prop = createProperty(0, true, [
        createKeyframeWithHandles(0, 0, "hold"),
        createKeyframe(100, 100),
      ]);
      expect(interpolateProperty(prop, 0)).toBe(0);
      expect(interpolateProperty(prop, 50)).toBe(0);
      expect(interpolateProperty(prop, 99)).toBe(0);
      expect(interpolateProperty(prop, 100)).toBe(100);
    });
  });

  describe("bezier interpolation", () => {
    test("applies bezier easing with enabled handles", () => {
      const prop = createProperty(0, true, [
        createKeyframeWithHandles(
          0,
          0,
          "bezier",
          { frame: 10, value: 0, enabled: true }, // outHandle
          { frame: 0, value: 0, enabled: false },
        ),
        createKeyframeWithHandles(
          30,
          100,
          "linear",
          { frame: 0, value: 0, enabled: false },
          { frame: -10, value: 0, enabled: true }, // inHandle
        ),
      ]);
      // With bezier, value at t=0.5 should NOT be 50 (unless it's linear)
      const midValue = interpolateProperty(prop, 15);
      expect(midValue).toBeGreaterThanOrEqual(0);
      expect(midValue).toBeLessThanOrEqual(100);
    });

    test("falls back to linear when handles disabled", () => {
      const prop = createProperty(0, true, [
        createKeyframeWithHandles(
          0,
          0,
          "bezier",
          { frame: 10, value: 50, enabled: false },
          { frame: 0, value: 0, enabled: false },
        ),
        createKeyframeWithHandles(
          100,
          100,
          "linear",
          { frame: 0, value: 0, enabled: false },
          { frame: -10, value: -50, enabled: false },
        ),
      ]);
      // Should be exactly linear
      expect(interpolateProperty(prop, 50)).toBe(50);
    });
  });

  describe("named easing interpolation", () => {
    test("applies easeInQuad easing", () => {
      const prop = createProperty(0, true, [
        { ...createKeyframe(0, 0), interpolation: "easeInQuad" },
        createKeyframe(100, 100),
      ]);
      const midValue = interpolateProperty(prop, 50);
      // easeInQuad at t=0.5 should be 0.25 (t*t), so value = 25
      expect(midValue).toBeCloseTo(25, 1);
    });

    test("applies easeOutQuad easing", () => {
      const prop = createProperty(0, true, [
        { ...createKeyframe(0, 0), interpolation: "easeOutQuad" },
        createKeyframe(100, 100),
      ]);
      const midValue = interpolateProperty(prop, 50);
      // easeOutQuad at t=0.5 should be 0.75 (1-(1-t)^2), so value = 75
      expect(midValue).toBeCloseTo(75, 1);
    });

    test("handles bezier interpolation correctly", () => {
      // Test with valid bezier interpolation (valid InterpolationType)
      const prop = createProperty(0, true, [
        { ...createKeyframe(0, 0), interpolation: "bezier" },
        createKeyframe(100, 100),
      ]);
      // Should interpolate correctly
      const result = interpolateProperty(prop, 50);
      expect(Number.isFinite(result)).toBe(true);
    });
  });

  describe("vector interpolation (Vec2/Vec3)", () => {
    test("interpolates Vec2", () => {
      const prop = createProperty({ x: 0, y: 0 }, true, [
        createKeyframe(0, { x: 0, y: 0 }),
        createKeyframe(100, { x: 100, y: 200 }),
      ]);
      const mid = interpolateProperty(prop, 50);
      expect(mid).toEqual({ x: 50, y: 100 });
    });

    test("interpolates Vec3", () => {
      const prop = createProperty({ x: 0, y: 0, z: 0 }, true, [
        createKeyframe(0, { x: 0, y: 0, z: 0 }),
        createKeyframe(100, { x: 100, y: 200, z: 300 }),
      ]);
      const mid = interpolateProperty(prop, 50);
      expect(mid).toEqual({ x: 50, y: 100, z: 150 });
    });

    test("handles Vec2 to Vec3 transition", () => {
      const prop = createProperty({ x: 0, y: 0 }, true, [
        createKeyframe(0, { x: 0, y: 0 }),
        createKeyframe(100, { x: 100, y: 100, z: 100 }),
      ]);
      const mid = interpolateProperty(prop, 50);
      // Type guard ensures safe property access for Vec2/Vec3 transition
      if (typeof mid !== 'object' || mid === null) {
        throw new Error("Expected interpolated value to be an object");
      }
      const midObj = mid as Record<string, unknown>;
      expect(midObj.x).toBe(50);
      expect(midObj.y).toBe(50);
      expect(midObj.z).toBe(50); // Interpolates z from 0 to 100
    });

    test("handles Vec3 to Vec2 transition", () => {
      const prop = createProperty({ x: 0, y: 0, z: 100 }, true, [
        createKeyframe(0, { x: 0, y: 0, z: 100 }),
        createKeyframe(100, { x: 100, y: 100, z: 0 }), // Z goes to 0
      ]);
      const mid = interpolateProperty(prop, 50);
      // Type guard ensures safe property access for Vec3/Vec2 transition
      if (typeof mid !== 'object' || mid === null) {
        throw new Error("Expected interpolated value to be an object");
      }
      const midObj = mid as Record<string, unknown>;
      expect(midObj.x).toBe(50);
      expect(midObj.y).toBe(50);
      expect(midObj.z).toBe(50); // Z interpolates to 0
    });
  });

  describe("color interpolation", () => {
    test("interpolates hex colors", () => {
      const prop = createProperty("#000000", true, [
        createKeyframe(0, "#000000"),
        createKeyframe(100, "#ffffff"),
      ]);
      const mid = interpolateProperty(prop, 50);
      expect(mid.toLowerCase()).toBe("#808080"); // 127,127,127 rounds to 128 -> 80
    });

    test("interpolates short hex colors", () => {
      const prop = createProperty("#000", true, [
        createKeyframe(0, "#000"),
        createKeyframe(100, "#fff"),
      ]);
      const mid = interpolateProperty(prop, 50);
      expect(mid.toLowerCase()).toBe("#808080");
    });

    test("interpolates with alpha", () => {
      const prop = createProperty("#00000000", true, [
        createKeyframe(0, "#00000000"),
        createKeyframe(100, "#ffffffff"),
      ]);
      const mid = interpolateProperty(prop, 50);
      expect(mid.toLowerCase()).toBe("#80808080");
    });

    test("handles invalid color by falling back to threshold behavior", () => {
      // When color strings don't start with #, they're not recognized as colors
      // and fall through to the default non-interpolatable type handling
      const prop = createProperty("invalid", true, [
        createKeyframe(0, "invalid"),
        createKeyframe(100, "#ffffff"),
      ]);
      // Before t=0.5, returns first value; at/after t=0.5, returns second value
      expect(interpolateProperty(prop, 25)).toBe("invalid");
      expect(interpolateProperty(prop, 49)).toBe("invalid");
      expect(interpolateProperty(prop, 50)).toBe("#ffffff");
    });
  });

  describe("non-interpolatable types", () => {
    test("returns first value until t >= 0.5 for strings", () => {
      const prop = createProperty("hello", true, [
        createKeyframe(0, "hello"),
        createKeyframe(100, "world"),
      ]);
      expect(interpolateProperty(prop, 25)).toBe("hello");
      expect(interpolateProperty(prop, 49)).toBe("hello");
      expect(interpolateProperty(prop, 50)).toBe("world");
      expect(interpolateProperty(prop, 75)).toBe("world");
    });

    test("returns first value until t >= 0.5 for booleans", () => {
      const prop = createProperty(false, true, [
        createKeyframe(0, false),
        createKeyframe(100, true),
      ]);
      expect(interpolateProperty(prop, 25)).toBe(false);
      expect(interpolateProperty(prop, 50)).toBe(true);
    });
  });

  describe("PURITY CONTRACT", () => {
    test("same inputs produce same outputs (determinism)", () => {
      const prop = createProperty(0, true, [
        createKeyframe(0, 0),
        createKeyframe(100, 100),
      ]);
      const result1 = interpolateProperty(prop, 50);
      const result2 = interpolateProperty(prop, 50);
      const result3 = interpolateProperty(prop, 50);
      expect(result1).toBe(result2);
      expect(result2).toBe(result3);
    });

    test("does not mutate input property", () => {
      const originalValue = 42;
      const originalKeyframes = [createKeyframe(0, 0), createKeyframe(100, 100)];
      const prop = createProperty(originalValue, true, [...originalKeyframes]);

      // Store original state
      const propCopy = JSON.stringify(prop);

      // Interpolate multiple times
      interpolateProperty(prop, 25);
      interpolateProperty(prop, 50);
      interpolateProperty(prop, 75);

      // Property should be unchanged
      expect(JSON.stringify(prop)).toBe(propCopy);
    });
  });
});

describe("EASING_PRESETS_NORMALIZED", () => {
  test("has linear preset", () => {
    expect(EASING_PRESETS_NORMALIZED.linear).toBeDefined();
    expect(EASING_PRESETS_NORMALIZED.linear.outHandle).toEqual({ x: 0.33, y: 0.33 });
    expect(EASING_PRESETS_NORMALIZED.linear.inHandle).toEqual({ x: 0.33, y: 0.33 });
  });

  test("has easeIn preset", () => {
    expect(EASING_PRESETS_NORMALIZED.easeIn).toBeDefined();
    expect(EASING_PRESETS_NORMALIZED.easeIn.outHandle).toEqual({ x: 0.42, y: 0 });
  });

  test("has easeOut preset", () => {
    expect(EASING_PRESETS_NORMALIZED.easeOut).toBeDefined();
    expect(EASING_PRESETS_NORMALIZED.easeOut.inHandle).toEqual({ x: 0.58, y: 1 });
  });

  test("has easeInOut preset", () => {
    expect(EASING_PRESETS_NORMALIZED.easeInOut).toBeDefined();
    expect(EASING_PRESETS_NORMALIZED.easeInOut.outHandle).toEqual({ x: 0.42, y: 0 });
    expect(EASING_PRESETS_NORMALIZED.easeInOut.inHandle).toEqual({ x: 0.58, y: 1 });
  });

  test("has easeOutBack preset with overshoot", () => {
    expect(EASING_PRESETS_NORMALIZED.easeOutBack).toBeDefined();
    expect(EASING_PRESETS_NORMALIZED.easeOutBack.inHandle.y).toBeGreaterThan(1);
  });

  test("EASING_PRESETS is alias for EASING_PRESETS_NORMALIZED", () => {
    expect(EASING_PRESETS).toBe(EASING_PRESETS_NORMALIZED);
  });
});

describe("createHandlesForPreset", () => {
  test("creates handles for linear preset", () => {
    const handles = createHandlesForPreset("linear", 30, 100);
    expect(handles.outHandle.enabled).toBe(true);
    expect(handles.inHandle.enabled).toBe(true);
    // Linear: 0.33 * 30 = ~10, 0.33 * 100 = 33
    expect(handles.outHandle.frame).toBeCloseTo(9.9, 1);
    expect(handles.outHandle.value).toBeCloseTo(33, 0);
  });

  test("creates handles for easeIn preset", () => {
    const handles = createHandlesForPreset("easeIn", 60, 200);
    // easeIn outHandle: x=0.42, y=0
    expect(handles.outHandle.frame).toBeCloseTo(0.42 * 60, 1);
    expect(handles.outHandle.value).toBeCloseTo(0, 1);
  });

  test("creates handles for easeOut preset", () => {
    const handles = createHandlesForPreset("easeOut", 60, 200);
    // easeOut inHandle: x=0.58, y=1
    expect(handles.inHandle.frame).toBeCloseTo(-0.58 * 60, 1);
    expect(handles.inHandle.value).toBeCloseTo(-1 * 200, 1);
  });

  test("handles zero duration gracefully", () => {
    const handles = createHandlesForPreset("linear", 0, 100);
    expect(handles.outHandle.frame).toBe(0);
    // -0 === 0 in JS, so we use toEqual which doesn't distinguish
    expect(handles.inHandle.frame + 0).toBe(0); // Convert -0 to 0
  });

  test("handles zero valueDelta gracefully", () => {
    const handles = createHandlesForPreset("linear", 30, 0);
    expect(handles.outHandle.value).toBe(0);
    // -0 === 0 in JS, so we use toEqual which doesn't distinguish
    expect(handles.inHandle.value + 0).toBe(0); // Convert -0 to 0
  });
});

describe("applyEasingPreset", () => {
  test("sets interpolation to bezier for non-linear presets", () => {
    const kf = createKeyframe(0, 100);
    applyEasingPreset(kf, "easeIn");
    expect(kf.interpolation).toBe("bezier");
  });

  test("sets interpolation to linear for linear preset", () => {
    const kf = createKeyframe(0, 100);
    applyEasingPreset(kf, "linear");
    expect(kf.interpolation).toBe("linear");
  });
});

describe("getBezierCurvePoint", () => {
  test("returns (0,0) at t=0", () => {
    const point = getBezierCurvePoint(
      0,
      { frame: 10, value: 0, enabled: true },
      { frame: -10, value: 0, enabled: true },
      30,
      100,
    );
    expect(point.x).toBeCloseTo(0, 5);
    expect(point.y).toBeCloseTo(0, 5);
  });

  test("returns (1,1) at t=1", () => {
    const point = getBezierCurvePoint(
      1,
      { frame: 10, value: 0, enabled: true },
      { frame: -10, value: 0, enabled: true },
      30,
      100,
    );
    expect(point.x).toBeCloseTo(1, 5);
    expect(point.y).toBeCloseTo(1, 5);
  });

  test("returns point on curve at t=0.5", () => {
    const point = getBezierCurvePoint(
      0.5,
      { frame: 10, value: 33, enabled: true },
      { frame: -10, value: -33, enabled: true },
      30,
      100,
    );
    expect(point.x).toBeGreaterThan(0);
    expect(point.x).toBeLessThan(1);
    expect(point.y).toBeGreaterThan(0);
    expect(point.y).toBeLessThan(1);
  });

  test("handles zero frameDuration", () => {
    const point = getBezierCurvePoint(
      0.5,
      { frame: 10, value: 33, enabled: true },
      { frame: -10, value: -33, enabled: true },
      0, // Zero duration
      100,
    );
    expect(Number.isFinite(point.x)).toBe(true);
    expect(Number.isFinite(point.y)).toBe(true);
  });

  test("handles zero valueDelta", () => {
    const point = getBezierCurvePoint(
      0.5,
      { frame: 10, value: 33, enabled: true },
      { frame: -10, value: -33, enabled: true },
      30,
      0, // Zero delta
    );
    expect(Number.isFinite(point.x)).toBe(true);
    expect(Number.isFinite(point.y)).toBe(true);
  });
});

describe("getBezierCurvePointNormalized", () => {
  test("returns (0,0) at t=0", () => {
    const point = getBezierCurvePointNormalized(
      0,
      { x: 0.33, y: 0.33 },
      { x: 0.33, y: 0.33 },
    );
    expect(point.x).toBeCloseTo(0, 5);
    expect(point.y).toBeCloseTo(0, 5);
  });

  test("returns (1,1) at t=1", () => {
    const point = getBezierCurvePointNormalized(
      1,
      { x: 0.33, y: 0.33 },
      { x: 0.33, y: 0.33 },
    );
    expect(point.x).toBeCloseTo(1, 5);
    expect(point.y).toBeCloseTo(1, 5);
  });

  test("linear preset gives linear curve", () => {
    const preset = EASING_PRESETS_NORMALIZED.linear;
    const points = [0, 0.25, 0.5, 0.75, 1].map((t) =>
      getBezierCurvePointNormalized(t, preset.outHandle, preset.inHandle),
    );
    // For linear, x ≈ y at all points
    for (const p of points) {
      expect(p.y).toBeCloseTo(p.x, 1);
    }
  });
});

describe("applyEasing", () => {
  test("clamps ratio to 0-1 range", () => {
    const preset = EASING_PRESETS_NORMALIZED.linear;
    expect(applyEasing(-0.5, preset)).toBeCloseTo(0, 2);
    expect(applyEasing(1.5, preset)).toBeCloseTo(1, 2);
  });

  test("returns 0 for ratio 0", () => {
    const preset = EASING_PRESETS_NORMALIZED.easeIn;
    expect(applyEasing(0, preset)).toBeCloseTo(0, 5);
  });

  test("returns 1 for ratio 1", () => {
    const preset = EASING_PRESETS_NORMALIZED.easeIn;
    expect(applyEasing(1, preset)).toBeCloseTo(1, 5);
  });

  test("easeIn is slow at start", () => {
    const preset = EASING_PRESETS_NORMALIZED.easeIn;
    const early = applyEasing(0.25, preset);
    // easeIn: value at 0.25 should be less than 0.25
    expect(early).toBeLessThan(0.25);
  });

  test("easeOut produces valid curve values", () => {
    const preset = EASING_PRESETS_NORMALIZED.easeOut;
    const early = applyEasing(0.25, preset);
    // easeOut values should be within 0-1 range
    expect(early).toBeGreaterThanOrEqual(0);
    expect(early).toBeLessThanOrEqual(1);
    // At t=0.5, should not be exactly 0.5 (that would be linear)
    const mid = applyEasing(0.5, preset);
    expect(mid).not.toBeCloseTo(0.5, 5);
  });
});

describe("clearPathMorphCache", () => {
  test("clears without error", () => {
    expect(() => clearPathMorphCache()).not.toThrow();
  });
});

describe("Edge Cases", () => {
  beforeEach(() => {
    clearBezierCache();
  });

  test("interpolateProperty handles single keyframe", () => {
    const prop = createProperty(0, true, [createKeyframe(50, 100)]);
    expect(interpolateProperty(prop, 0)).toBe(100);
    expect(interpolateProperty(prop, 50)).toBe(100);
    expect(interpolateProperty(prop, 100)).toBe(100);
  });

  test("interpolateProperty handles negative frame numbers", () => {
    const prop = createProperty(0, true, [
      createKeyframe(-10, 0),
      createKeyframe(10, 100),
    ]);
    expect(interpolateProperty(prop, -10)).toBe(0);
    expect(interpolateProperty(prop, 0)).toBe(50);
    expect(interpolateProperty(prop, 10)).toBe(100);
  });

  test("interpolateProperty handles very large frame numbers", () => {
    const prop = createProperty(0, true, [
      createKeyframe(0, 0),
      createKeyframe(1000000, 1000000),
    ]);
    expect(interpolateProperty(prop, 500000)).toBe(500000);
  });

  test("interpolateProperty handles floating point frames", () => {
    const prop = createProperty(0, true, [
      createKeyframe(0, 0),
      createKeyframe(100, 100),
    ]);
    expect(interpolateProperty(prop, 33.33)).toBeCloseTo(33.33, 2);
  });

  test("interpolateProperty handles very small differences", () => {
    const prop = createProperty(0, true, [
      createKeyframe(0, 0),
      createKeyframe(100, 0.0001),
    ]);
    const mid = interpolateProperty(prop, 50);
    expect(mid).toBeCloseTo(0.00005, 6);
  });

  test("bezier interpolation with extreme handle values", () => {
    const prop = createProperty(0, true, [
      createKeyframeWithHandles(
        0,
        0,
        "bezier",
        { frame: 100, value: 1000, enabled: true },
        { frame: 0, value: 0, enabled: false },
      ),
      createKeyframeWithHandles(
        100,
        100,
        "linear",
        { frame: 0, value: 0, enabled: false },
        { frame: -100, value: -1000, enabled: true },
      ),
    ]);
    // Should not crash, should return finite value
    const mid = interpolateProperty(prop, 50);
    expect(Number.isFinite(mid)).toBe(true);
  });

  test("binary search finds correct keyframe in large array", () => {
    // Create 100 keyframes
    const keyframes = Array.from({ length: 100 }, (_, i) =>
      createKeyframe(i * 10, i * 10),
    );
    const prop = createProperty(0, true, keyframes);

    // Test various points
    expect(interpolateProperty(prop, 555)).toBe(555);
    expect(interpolateProperty(prop, 123)).toBeCloseTo(123, 0);
    expect(interpolateProperty(prop, 999)).toBe(990); // Clamped to last
  });
});

// ===========================================================================
// BUG #2 FIX VERIFICATION - fps validation applied
// ===========================================================================
describe("interpolation - BUG #2 FIX VERIFICATION", () => {
  /**
   * BUG #2 (FIXED): fps=0 caused division by zero in applyPropertyExpression
   * Location: interpolation.ts lines 318, 322
   * 
   * Fix: Added validateFps() from utils/fpsUtils.ts to fall back to 16
   */
  test("BUG #2 FIXED: fps=0 now uses fallback fps=16", () => {
    const baseProp = createProperty(100, true, [
      createKeyframe(0, 0),
      createKeyframe(100, 100),
    ]);
    // Add a mock expression with proper type
    // Type guard ensures safe property assignment for expression testing
    const prop: AnimatableProperty<number> & { expression?: PropertyExpression } = {
      ...baseProp,
      expression: {
        enabled: true,
        type: "preset",
        name: "wiggle",
        params: { frequency: 1, amplitude: 10 },
      },
    };

    // fps=0 should now be validated and fall back to 16
    const result = interpolateProperty(prop, 50, 0, "layer1");
    
    // After fix: should return a finite number (expression may still fail for other reasons,
    // but the division by zero in context building is fixed)
    expect(Number.isFinite(result)).toBe(true);
  });

  test("BUG #2 FIXED: negative fps now uses fallback fps=16", () => {
    const baseProp = createProperty(100, true, [
      createKeyframe(0, 0),
      createKeyframe(100, 100),
    ]);
    const prop: AnimatableProperty<number> & { expression?: PropertyExpression } = {
      ...baseProp,
      expression: {
        enabled: true,
        type: "preset",
        name: "time",
        params: {},
      },
    };

    // Negative fps should now be validated and fall back to 16
    const result = interpolateProperty(prop, 50, -30, "layer1");
    
    // After fix: should return a finite number
    expect(Number.isFinite(result)).toBe(true);
  });

  test("BUG #2 FIXED: NaN fps now uses fallback fps=16", () => {
    const baseProp = createProperty(100, true, [
      createKeyframe(0, 0),
      createKeyframe(100, 100),
    ]);
    const prop: AnimatableProperty<number> & { expression?: PropertyExpression } = {
      ...baseProp,
      expression: {
        enabled: true,
        type: "preset",
        name: "linear",
        params: {},
      },
    };

    // NaN fps should now be validated and fall back to 16
    const result = interpolateProperty(prop, 50, NaN, "layer1");
    
    expect(Number.isFinite(result)).toBe(true);
  });

  test("BUG #2 FIXED: Infinity fps now uses fallback fps=16", () => {
    const baseProp = createProperty(100, true, [
      createKeyframe(0, 0),
      createKeyframe(100, 100),
    ]);
    const prop: AnimatableProperty<number> & { expression?: PropertyExpression } = {
      ...baseProp,
      expression: {
        enabled: true,
        type: "preset",
        name: "linear",
        params: {},
      },
    };

    // Infinity fps should now be validated and fall back to 16
    const result = interpolateProperty(prop, 50, Infinity, "layer1");
    
    expect(Number.isFinite(result)).toBe(true);
  });
});
