// ============================================================================
// PROPERTY TESTS: INPUT VALIDATION
// ============================================================================
// Fast-check property tests for input validation edge cases.
// ============================================================================

import { describe, it, expect } from "vitest";
import fc from "fast-check";
import {
  validateString,
  validateFiniteNumber,
  validateInteger,
  validateBoolean,
  validateEnum,
  validateArray,
  validateObject,
  validateVec2,
  validateVec3,
  validateColor,
  optional,
  withDefault,
  ok,
  fail,
} from "@/utils/validation";

describe("Validation Property Tests", () => {
  // ==========================================================================
  // VALIDATE STRING
  // ==========================================================================

  describe("validateString", () => {
    it("accepts any non-empty string", () => {
      fc.assert(
        fc.property(fc.string({ minLength: 1 }), (s) => {
          const result = validateString(s, "test");
          expect(result.ok).toBe(true);
          if (result.ok) expect(result.value).toBe(s);
        })
      );
    });

    it("rejects non-strings", () => {
      fc.assert(
        fc.property(
          fc.anything().filter((x) => typeof x !== "string"),
          (value) => {
            const result = validateString(value, "test");
            expect(result.ok).toBe(false);
          }
        )
      );
    });

    it("rejects empty strings by default", () => {
      const result = validateString("", "test");
      expect(result.ok).toBe(false);
    });

    it("accepts empty strings when allowEmpty is true", () => {
      const result = validateString("", "test", { allowEmpty: true });
      expect(result.ok).toBe(true);
    });

    it("enforces minLength", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: 1, max: 100 }),
          fc.string(),
          (minLength, s) => {
            const result = validateString(s, "test", { minLength, allowEmpty: true });
            if (s.length >= minLength) {
              expect(result.ok).toBe(true);
            } else {
              expect(result.ok).toBe(false);
            }
          }
        )
      );
    });

    it("enforces maxLength", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: 1, max: 100 }),
          fc.string(),
          (maxLength, s) => {
            const result = validateString(s, "test", { maxLength, allowEmpty: true });
            if (s.length <= maxLength) {
              expect(result.ok).toBe(true);
            } else {
              expect(result.ok).toBe(false);
            }
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE FINITE NUMBER
  // ==========================================================================

  describe("validateFiniteNumber", () => {
    it("accepts finite numbers", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (n) => {
            const result = validateFiniteNumber(n, "test");
            expect(result.ok).toBe(true);
            if (result.ok) expect(result.value).toBe(n);
          }
        )
      );
    });

    it("rejects NaN", () => {
      const result = validateFiniteNumber(NaN, "test");
      expect(result.ok).toBe(false);
    });

    it("rejects Infinity", () => {
      expect(validateFiniteNumber(Infinity, "test").ok).toBe(false);
      expect(validateFiniteNumber(-Infinity, "test").ok).toBe(false);
    });

    it("enforces min bound", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (value, min) => {
            const result = validateFiniteNumber(value, "test", { min });
            if (value >= min) {
              expect(result.ok).toBe(true);
            } else {
              expect(result.ok).toBe(false);
            }
          }
        )
      );
    });

    it("enforces max bound", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (value, max) => {
            const result = validateFiniteNumber(value, "test", { max });
            if (value <= max) {
              expect(result.ok).toBe(true);
            } else {
              expect(result.ok).toBe(false);
            }
          }
        )
      );
    });

    it("converts strings to numbers", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (n) => {
            const result = validateFiniteNumber(String(n), "test");
            expect(result.ok).toBe(true);
            if (result.ok) expect(result.value).toBeCloseTo(n, 10);
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE INTEGER
  // ==========================================================================

  describe("validateInteger", () => {
    it("accepts integers", () => {
      fc.assert(
        fc.property(fc.integer(), (n) => {
          const result = validateInteger(n, "test");
          expect(result.ok).toBe(true);
          if (result.ok) expect(result.value).toBe(n);
        })
      );
    });

    it("rejects non-integers", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }).filter(
            (n) => !Number.isInteger(n)
          ),
          (n) => {
            const result = validateInteger(n, "test");
            expect(result.ok).toBe(false);
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE BOOLEAN
  // ==========================================================================

  describe("validateBoolean", () => {
    it("accepts booleans", () => {
      expect(validateBoolean(true, "test").ok).toBe(true);
      expect(validateBoolean(false, "test").ok).toBe(true);
    });

    it("rejects non-booleans", () => {
      fc.assert(
        fc.property(
          fc.anything().filter((x) => typeof x !== "boolean"),
          (value) => {
            const result = validateBoolean(value, "test");
            expect(result.ok).toBe(false);
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE ENUM
  // ==========================================================================

  describe("validateEnum", () => {
    it("accepts values in the enum", () => {
      const allowed = ["a", "b", "c"] as const;
      fc.assert(
        fc.property(fc.constantFrom(...allowed), (value) => {
          const result = validateEnum(value, "test", allowed);
          expect(result.ok).toBe(true);
        })
      );
    });

    it("rejects values not in the enum", () => {
      const allowed = ["a", "b", "c"] as const;
      fc.assert(
        fc.property(
          fc.string().filter((s) => !allowed.includes(s as "a" | "b" | "c")),
          (value) => {
            const result = validateEnum(value, "test", allowed);
            expect(result.ok).toBe(false);
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE ARRAY
  // ==========================================================================

  describe("validateArray", () => {
    it("accepts arrays of valid items", () => {
      fc.assert(
        fc.property(fc.array(fc.integer()), (arr) => {
          const result = validateArray(arr, "test", (item) =>
            validateInteger(item, "item")
          );
          expect(result.ok).toBe(true);
          if (result.ok) {
            expect(result.value).toEqual(arr);
          }
        })
      );
    });

    it("rejects non-arrays", () => {
      fc.assert(
        fc.property(
          fc.anything().filter((x) => !Array.isArray(x)),
          (value) => {
            const result = validateArray(value, "test", () => ok(true));
            expect(result.ok).toBe(false);
          }
        )
      );
    });

    it("enforces minLength", () => {
      fc.assert(
        fc.property(
          fc.array(fc.integer()),
          fc.integer({ min: 0, max: 10 }),
          (arr, minLength) => {
            const result = validateArray(
              arr,
              "test",
              (item) => validateInteger(item, "item"),
              { minLength }
            );
            if (arr.length >= minLength) {
              expect(result.ok).toBe(true);
            } else {
              expect(result.ok).toBe(false);
            }
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE OBJECT
  // ==========================================================================

  describe("validateObject", () => {
    it("accepts objects", () => {
      fc.assert(
        fc.property(fc.object(), (obj) => {
          const result = validateObject(obj, "test");
          expect(result.ok).toBe(true);
        })
      );
    });

    it("rejects null", () => {
      const result = validateObject(null, "test");
      expect(result.ok).toBe(false);
    });

    it("rejects primitives", () => {
      fc.assert(
        fc.property(
          fc.oneof(fc.string(), fc.integer(), fc.boolean()),
          (value) => {
            const result = validateObject(value, "test");
            expect(result.ok).toBe(false);
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE VEC2
  // ==========================================================================

  describe("validateVec2", () => {
    it("accepts valid Vec2 objects", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (x, y) => {
            const result = validateVec2({ x, y }, "test");
            expect(result.ok).toBe(true);
            if (result.ok) {
              expect(result.value.x).toBe(x);
              expect(result.value.y).toBe(y);
            }
          }
        )
      );
    });

    it("rejects objects with non-finite coordinates", () => {
      expect(validateVec2({ x: NaN, y: 0 }, "test").ok).toBe(false);
      expect(validateVec2({ x: 0, y: Infinity }, "test").ok).toBe(false);
    });

    it("rejects objects missing x or y", () => {
      expect(validateVec2({ x: 0 }, "test").ok).toBe(false);
      expect(validateVec2({ y: 0 }, "test").ok).toBe(false);
      expect(validateVec2({}, "test").ok).toBe(false);
    });
  });

  // ==========================================================================
  // VALIDATE VEC3
  // ==========================================================================

  describe("validateVec3", () => {
    it("accepts valid Vec3 objects", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (x, y, z) => {
            const result = validateVec3({ x, y, z }, "test");
            expect(result.ok).toBe(true);
            if (result.ok) {
              expect(result.value.x).toBe(x);
              expect(result.value.y).toBe(y);
              expect(result.value.z).toBe(z);
            }
          }
        )
      );
    });

    it("allows missing z when allowMissingZ is true", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (x, y) => {
            const result = validateVec3({ x, y }, "test", { allowMissingZ: true });
            expect(result.ok).toBe(true);
            if (result.ok) {
              expect(result.value.z).toBe(0);
            }
          }
        )
      );
    });
  });

  // ==========================================================================
  // VALIDATE COLOR
  // ==========================================================================

  describe("validateColor", () => {
    it("accepts valid RGB colors", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: 0, max: 255 }),
          fc.integer({ min: 0, max: 255 }),
          fc.integer({ min: 0, max: 255 }),
          (r, g, b) => {
            const result = validateColor({ r, g, b }, "test");
            expect(result.ok).toBe(true);
          }
        )
      );
    });

    it("accepts valid RGBA colors", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: 0, max: 255 }),
          fc.integer({ min: 0, max: 255 }),
          fc.integer({ min: 0, max: 255 }),
          fc.double({ min: 0, max: 1, noNaN: true }),
          (r, g, b, a) => {
            const result = validateColor({ r, g, b, a }, "test");
            expect(result.ok).toBe(true);
          }
        )
      );
    });

    it("rejects out-of-range color values", () => {
      expect(validateColor({ r: 256, g: 0, b: 0 }, "test").ok).toBe(false);
      expect(validateColor({ r: -1, g: 0, b: 0 }, "test").ok).toBe(false);
      expect(validateColor({ r: 0, g: 0, b: 0, a: 2 }, "test").ok).toBe(false);
    });
  });

  // ==========================================================================
  // OPTIONAL / WITH DEFAULT
  // ==========================================================================

  describe("optional", () => {
    it("returns undefined for undefined/null input", () => {
      const optionalString = optional(validateString);
      expect(optionalString(undefined, "test")).toEqual({ ok: true, value: undefined });
      expect(optionalString(null, "test")).toEqual({ ok: true, value: undefined });
    });

    it("validates non-undefined values", () => {
      const optionalString = optional(validateString);
      fc.assert(
        fc.property(fc.string({ minLength: 1 }), (s) => {
          const result = optionalString(s, "test");
          expect(result.ok).toBe(true);
          if (result.ok) expect(result.value).toBe(s);
        })
      );
    });
  });

  describe("withDefault", () => {
    it("returns default for undefined/null input", () => {
      const stringWithDefault = withDefault(validateString, "default");
      expect(stringWithDefault(undefined, "test")).toEqual({ ok: true, value: "default" });
      expect(stringWithDefault(null, "test")).toEqual({ ok: true, value: "default" });
    });

    it("validates non-undefined values", () => {
      const stringWithDefault = withDefault(validateString, "default");
      fc.assert(
        fc.property(fc.string({ minLength: 1 }), (s) => {
          const result = stringWithDefault(s, "test");
          expect(result.ok).toBe(true);
          if (result.ok) expect(result.value).toBe(s);
        })
      );
    });
  });
});
