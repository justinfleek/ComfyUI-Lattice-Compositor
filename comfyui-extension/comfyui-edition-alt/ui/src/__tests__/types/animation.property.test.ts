/**
 * Property tests for ui/src/types/animation.ts
 * Tests: createAnimatableProperty, createKeyframe
 *
 * Audit: 2026-01-06
 */

import * as fc from "fast-check";
import { describe, expect, it } from "vitest";
import {
  type AnimatableProperty,
  createAnimatableProperty,
  createKeyframe as createKeyframeProd,
  type InterpolationType,
  type Keyframe,
} from "@/types/animation";

// Test wrapper for createKeyframe with default layerId/propertyPath
const TEST_LAYER_ID = "test-layer";
const TEST_PROPERTY_PATH = "test.property";
function createKeyframe<T>(
  frame: number,
  value: T,
  interpolation: InterpolationType = "linear",
): Keyframe<T> {
  return createKeyframeProd(
    TEST_LAYER_ID,
    TEST_PROPERTY_PATH,
    frame,
    value,
    interpolation,
  );
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                               // arbitraries
// ════════════════════════════════════════════════════════════════════════════

const propertyTypeArb = fc.constantFrom(
  "number" as const,
  "position" as const,
  "color" as const,
  "enum" as const,
  "vector3" as const,
);

const interpolationTypeArb = fc.constantFrom<InterpolationType>(
  "linear",
  "bezier",
  "hold",
  "easeInSine",
  "easeOutSine",
  "easeInOutSine",
  "easeInQuad",
  "easeOutQuad",
  "easeInOutQuad",
  "easeInCubic",
  "easeOutCubic",
  "easeInOutCubic",
  "easeInQuart",
  "easeOutQuart",
  "easeInOutQuart",
  "easeInQuint",
  "easeOutQuint",
  "easeInOutQuint",
  "easeInExpo",
  "easeOutExpo",
  "easeInOutExpo",
  "easeInCirc",
  "easeOutCirc",
  "easeInOutCirc",
  "easeInBack",
  "easeOutBack",
  "easeInOutBack",
  "easeInElastic",
  "easeOutElastic",
  "easeInOutElastic",
  "easeInBounce",
  "easeOutBounce",
  "easeInOutBounce",
);

// Valid frame number (finite, not NaN)
const validFrameArb = fc.integer({ min: -10000, max: 10000 });

// Property name (non-empty string)
const propertyNameArb = fc.string({ minLength: 1, maxLength: 50 });

// Group name (optional)
const groupNameArb = fc.option(fc.string({ minLength: 1, maxLength: 30 }), {
  nil: undefined,
});

// Various value types
const numberValueArb = fc.double({ min: -1e6, max: 1e6, noNaN: true });
const positionValueArb = fc.record({
  x: fc.double({ min: -1e6, max: 1e6, noNaN: true }),
  y: fc.double({ min: -1e6, max: 1e6, noNaN: true }),
});
const position3DValueArb = fc.record({
  x: fc.double({ min: -1e6, max: 1e6, noNaN: true }),
  y: fc.double({ min: -1e6, max: 1e6, noNaN: true }),
  z: fc.double({ min: -1e6, max: 1e6, noNaN: true }),
});
const colorValueArb = fc.record({
  r: fc.integer({ min: 0, max: 255 }),
  g: fc.integer({ min: 0, max: 255 }),
  b: fc.integer({ min: 0, max: 255 }),
  a: fc.double({ min: 0, max: 1, noNaN: true }),
});

// ════════════════════════════════════════════════════════════════════════════
// createAnimatableProperty TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createAnimatableProperty", () => {
  it("returns object with all required fields", () => {
    fc.assert(
      fc.property(
        propertyNameArb,
        numberValueArb,
        propertyTypeArb,
        groupNameArb,
        (name, value, type, group) => {
          const result = createAnimatableProperty(name, value, type, group);

          expect(result).toHaveProperty("id");
          expect(result).toHaveProperty("name");
          expect(result).toHaveProperty("type");
          expect(result).toHaveProperty("value");
          expect(result).toHaveProperty("animated");
          expect(result).toHaveProperty("keyframes");
        },
      ),
    );
  });

  it("id starts with 'prop_'", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value);
        expect(result.id.startsWith("prop_")).toBe(true);
      }),
    );
  });

  it("id contains the property name", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value);
        expect(result.id).toContain(name);
      }),
    );
  });

  it("name matches input", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value);
        expect(result.name).toBe(name);
      }),
    );
  });

  it("value matches input for numbers", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value, "number");
        expect(result.value).toBe(value);
      }),
    );
  });

  it("value matches input for positions", () => {
    fc.assert(
      fc.property(propertyNameArb, positionValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value, "position");
        expect(result.value).toEqual(value);
      }),
    );
  });

  it("value matches input for colors", () => {
    fc.assert(
      fc.property(propertyNameArb, colorValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value, "color");
        expect(result.value).toEqual(value);
      }),
    );
  });

  it("type matches input", () => {
    fc.assert(
      fc.property(
        propertyNameArb,
        numberValueArb,
        propertyTypeArb,
        (name, value, type) => {
          const result = createAnimatableProperty(name, value, type);
          expect(result.type).toBe(type);
        },
      ),
    );
  });

  it("defaults type to 'number'", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value);
        expect(result.type).toBe("number");
      }),
    );
  });

  it("animated defaults to false", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value);
        expect(result.animated).toBe(false);
      }),
    );
  });

  it("keyframes defaults to empty array", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value);
        expect(result.keyframes).toEqual([]);
      }),
    );
  });

  it("group is set when provided", () => {
    fc.assert(
      fc.property(
        propertyNameArb,
        numberValueArb,
        fc.string({ minLength: 1, maxLength: 30 }),
        (name, value, group) => {
          const result = createAnimatableProperty(name, value, "number", group);
          expect(result.group).toBe(group);
        },
      ),
    );
  });

  it("group is undefined when not provided", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result = createAnimatableProperty(name, value);
        expect(result.group).toBeUndefined();
      }),
    );
  });

  it("consecutive calls produce unique IDs", () => {
    fc.assert(
      fc.property(propertyNameArb, numberValueArb, (name, value) => {
        const result1 = createAnimatableProperty(name, value);
        const result2 = createAnimatableProperty(name, value);
        expect(result1.id).not.toBe(result2.id);
      }),
    );
  });
});

// ════════════════════════════════════════════════════════════════════════════
// createKeyframe TESTS
// ════════════════════════════════════════════════════════════════════════════

describe("PROPERTY: createKeyframe", () => {
  it("returns object with all required fields", () => {
    fc.assert(
      fc.property(
        validFrameArb,
        numberValueArb,
        interpolationTypeArb,
        (frame, value, interp) => {
          const result = createKeyframe(frame, value, interp);

          expect(result).toHaveProperty("id");
          expect(result).toHaveProperty("frame");
          expect(result).toHaveProperty("value");
          expect(result).toHaveProperty("interpolation");
          expect(result).toHaveProperty("inHandle");
          expect(result).toHaveProperty("outHandle");
          expect(result).toHaveProperty("controlMode");
        },
      ),
    );
  });

  it("id starts with 'kf_'", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.id.startsWith("kf_")).toBe(true);
      }),
    );
  });

  it("id contains the frame number", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.id).toContain(String(frame));
      }),
    );
  });

  it("frame matches input", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.frame).toBe(frame);
      }),
    );
  });

  it("value matches input for numbers", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.value).toBe(value);
      }),
    );
  });

  it("value matches input for positions", () => {
    fc.assert(
      fc.property(validFrameArb, positionValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.value).toEqual(value);
      }),
    );
  });

  it("value matches input for 3D positions", () => {
    fc.assert(
      fc.property(validFrameArb, position3DValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.value).toEqual(value);
      }),
    );
  });

  it("interpolation matches input", () => {
    fc.assert(
      fc.property(
        validFrameArb,
        numberValueArb,
        interpolationTypeArb,
        (frame, value, interp) => {
          const result = createKeyframe(frame, value, interp);
          expect(result.interpolation).toBe(interp);
        },
      ),
    );
  });

  it("interpolation defaults to 'linear'", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.interpolation).toBe("linear");
      }),
    );
  });

  it("inHandle has correct defaults", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.inHandle).toEqual({ frame: -5, value: 0, enabled: true });
      }),
    );
  });

  it("outHandle has correct defaults", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.outHandle).toEqual({ frame: 5, value: 0, enabled: true });
      }),
    );
  });

  it("controlMode defaults to 'smooth'", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result = createKeyframe(frame, value);
        expect(result.controlMode).toBe("smooth");
      }),
    );
  });

  it("consecutive calls with same inputs produce same ID (deterministic)", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result1 = createKeyframe(frame, value);
        const result2 = createKeyframe(frame, value);
        // Deterministic: same inputs = same ID
        expect(result1.id).toBe(result2.id);
      }),
    );
  });

  it("different inputs produce different IDs", () => {
    fc.assert(
      fc.property(validFrameArb, numberValueArb, (frame, value) => {
        const result1 = createKeyframe(frame, value);
        const result2 = createKeyframe(frame + 1, value);
        expect(result1.id).not.toBe(result2.id);
      }),
    );
  });

  //                                                                       // bug
  it("throws on NaN frame (BUG-002 fix verification)", () => {
    expect(() => createKeyframe(NaN, 100)).toThrow("Invalid keyframe frame");
  });

  it("throws on Infinity frame (BUG-002 fix verification)", () => {
    expect(() => createKeyframe(Infinity, 100)).toThrow(
      "Invalid keyframe frame",
    );
  });

  it("throws on -Infinity frame (BUG-002 fix verification)", () => {
    expect(() => createKeyframe(-Infinity, 100)).toThrow(
      "Invalid keyframe frame",
    );
  });

  it("accepts zero as valid frame", () => {
    const result = createKeyframe(0, 100);
    expect(result.frame).toBe(0);
  });

  it("accepts negative frames", () => {
    fc.assert(
      fc.property(
        fc.integer({ min: -10000, max: -1 }),
        numberValueArb,
        (frame, value) => {
          const result = createKeyframe(frame, value);
          expect(result.frame).toBe(frame);
        },
      ),
    );
  });

  it("handles all 33 interpolation types", () => {
    const allTypes: InterpolationType[] = [
      "linear",
      "bezier",
      "hold",
      "easeInSine",
      "easeOutSine",
      "easeInOutSine",
      "easeInQuad",
      "easeOutQuad",
      "easeInOutQuad",
      "easeInCubic",
      "easeOutCubic",
      "easeInOutCubic",
      "easeInQuart",
      "easeOutQuart",
      "easeInOutQuart",
      "easeInQuint",
      "easeOutQuint",
      "easeInOutQuint",
      "easeInExpo",
      "easeOutExpo",
      "easeInOutExpo",
      "easeInCirc",
      "easeOutCirc",
      "easeInOutCirc",
      "easeInBack",
      "easeOutBack",
      "easeInOutBack",
      "easeInElastic",
      "easeOutElastic",
      "easeInOutElastic",
      "easeInBounce",
      "easeOutBounce",
      "easeInOutBounce",
    ];

    for (const interpType of allTypes) {
      const result = createKeyframe(0, 100, interpType);
      expect(result.interpolation).toBe(interpType);
    }
  });
});
