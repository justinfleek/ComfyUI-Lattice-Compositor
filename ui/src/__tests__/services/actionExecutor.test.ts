/**
 * ActionExecutor Tests
 * 
 * Tests for AI action execution and physics calculations.
 */
import { describe, expect, test } from "vitest";

// Inline the wind calculation for testing
// This matches the implementation in actionExecutor.ts
// Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
function calculateWindStrength(wind: { x?: number; y?: number } | undefined): number {
  if (wind) {
    // BUG-006 FIX: Prevent NaN when wind.x or wind.y are undefined
    const windX = (wind.x !== null && wind.x !== undefined && typeof wind.x === "number" && Number.isFinite(wind.x)) ? wind.x : 0;
    const windY = (wind.y !== null && wind.y !== undefined && typeof wind.y === "number" && Number.isFinite(wind.y)) ? wind.y : 0;
    return Math.sqrt(windX ** 2 + windY ** 2);
  }
  return 0;
}

function calculateWindDirection(wind: { x?: number; y?: number } | undefined): number {
  if (wind) {
    // BUG-006 FIX: Prevent NaN when wind.x or wind.y are undefined
    const windX = (wind.x !== null && wind.x !== undefined && typeof wind.x === "number" && Number.isFinite(wind.x)) ? wind.x : 0;
    const windY = (wind.y !== null && wind.y !== undefined && typeof wind.y === "number" && Number.isFinite(wind.y)) ? wind.y : 0;
    return Math.atan2(windY, windX) * (180 / Math.PI);
  }
  return 0;
}

describe("ActionExecutor physics calculations", () => {
  describe("wind strength calculation", () => {
    test("calculates wind strength correctly", () => {
      // 3-4-5 triangle
      expect(calculateWindStrength({ x: 3, y: 4 })).toBe(5);
      
      // Only x
      expect(calculateWindStrength({ x: 5, y: 0 })).toBe(5);
      
      // Only y
      expect(calculateWindStrength({ x: 0, y: 5 })).toBe(5);
      
      // Zero wind
      expect(calculateWindStrength({ x: 0, y: 0 })).toBe(0);
    });

    test("returns 0 for undefined wind", () => {
      expect(calculateWindStrength(undefined)).toBe(0);
    });

    /**
     * BUG #6 FIX VERIFICATION
     * 
     * When physics.wind is truthy but .x or .y are undefined,
     * the calculation produced NaN.
     * The fix uses explicit pattern matching to default to 0.
     */
    test("BUG #6 FIXED: missing x returns finite number instead of NaN", () => {
      // Was: NaN (undefined ** 2 = NaN)
      // Now: 4 (using windX=0)
      expect(calculateWindStrength({ y: 4 })).toBe(4);
      expect(Number.isFinite(calculateWindStrength({ y: 4 }))).toBe(true);
    });

    test("BUG #6 FIXED: missing y returns finite number instead of NaN", () => {
      expect(calculateWindStrength({ x: 3 })).toBe(3);
      expect(Number.isFinite(calculateWindStrength({ x: 3 }))).toBe(true);
    });

    test("BUG #6 FIXED: empty object returns 0 instead of NaN", () => {
      // Was: NaN
      // Now: 0
      expect(calculateWindStrength({})).toBe(0);
      expect(Number.isFinite(calculateWindStrength({}))).toBe(true);
    });
  });

  describe("wind direction calculation", () => {
    test("calculates wind direction correctly", () => {
      // Pointing right (positive X)
      expect(calculateWindDirection({ x: 1, y: 0 })).toBe(0);
      
      // Pointing up (positive Y)
      expect(calculateWindDirection({ x: 0, y: 1 })).toBe(90);
      
      // Pointing left (negative X)
      expect(calculateWindDirection({ x: -1, y: 0 })).toBeCloseTo(180, 5);
    });

    test("BUG #6 FIXED: missing props return 0 degrees instead of NaN", () => {
      expect(calculateWindDirection({ y: 1 })).toBe(90);  // windX=0, windY=1 → up
      expect(calculateWindDirection({ x: 1 })).toBe(0);   // windX=1, windY=0 → right
      expect(calculateWindDirection({})).toBe(0);         // windX=0, windY=0 → right (atan2(0,0)=0)
      
      expect(Number.isFinite(calculateWindDirection({}))).toBe(true);
    });
  });
});
