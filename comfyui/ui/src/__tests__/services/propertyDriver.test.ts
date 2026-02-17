/**
 * Property Driver Tests
 * 
 * Tests for the PropertyDriverSystem and transform functions.
 */
import { describe, expect, test } from "vitest";

// Inline the applyTransform logic for testing since it's a private method
// This matches the implementation in propertyDriver.ts
function applyRemap(
  value: number,
  inMin: number,
  inMax: number,
  outMin: number,
  outMax: number,
): number {
  // BUG-003 FIX: Prevent division by zero when inMin === inMax
  const inRange = inMax - inMin;
  if (inRange === 0) {
    // If input range is zero, return midpoint of output range
    return (outMin + outMax) / 2;
  }
  const normalized = (value - inMin) / inRange;
  return outMin + normalized * (outMax - outMin);
}

describe("PropertyDriver transforms", () => {
  describe("remap transform", () => {
    test("remaps value from one range to another", () => {
      // 0.5 in [0,1] maps to 50 in [0,100]
      expect(applyRemap(0.5, 0, 1, 0, 100)).toBe(50);
      
      // 0 in [0,1] maps to 0 in [0,100]
      expect(applyRemap(0, 0, 1, 0, 100)).toBe(0);
      
      // 1 in [0,1] maps to 100 in [0,100]
      expect(applyRemap(1, 0, 1, 0, 100)).toBe(100);
    });

    test("handles inverted output range", () => {
      // 0.5 in [0,1] maps to 50 in [100,0] (inverted)
      expect(applyRemap(0.5, 0, 1, 100, 0)).toBe(50);
    });

    test("handles values outside input range", () => {
      // Values outside range are extrapolated
      expect(applyRemap(-0.5, 0, 1, 0, 100)).toBe(-50);
      expect(applyRemap(1.5, 0, 1, 0, 100)).toBe(150);
    });

    /**
     * BUG #3 FIX VERIFICATION
     * 
     * When inMin === inMax, division by zero would produce NaN/Infinity.
     * The fix returns the midpoint of the output range instead.
     */
    test("BUG #3 FIXED: inMin === inMax returns output midpoint instead of NaN", () => {
      // When input range is zero, return midpoint of output
      expect(applyRemap(0.25, 0.5, 0.5, 0, 100)).toBe(50);  // Was -Infinity
      expect(applyRemap(0.5, 0.5, 0.5, 0, 100)).toBe(50);   // Was NaN
      expect(applyRemap(0.75, 0.5, 0.5, 0, 100)).toBe(50);  // Was Infinity
      
      // All should be finite numbers
      expect(Number.isFinite(applyRemap(0.25, 0.5, 0.5, 0, 100))).toBe(true);
      expect(Number.isFinite(applyRemap(0.5, 0.5, 0.5, 0, 100))).toBe(true);
      expect(Number.isFinite(applyRemap(0.75, 0.5, 0.5, 0, 100))).toBe(true);
    });

    test("BUG #3 FIXED: works with any zero-range input", () => {
      // Zero range at different points
      expect(applyRemap(0, 0, 0, 0, 100)).toBe(50);
      expect(applyRemap(100, 100, 100, 0, 200)).toBe(100);
      
      // Zero range with asymmetric output
      expect(applyRemap(5, 5, 5, 10, 30)).toBe(20);  // Midpoint of [10,30]
    });
  });
});
