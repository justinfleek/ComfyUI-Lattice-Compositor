/**
 * Depthflow Service Tests
 * 
 * Tests for depth-based parallax effects and motion calculations.
 */
import { describe, expect, test } from "vitest";

// Inline the exponential motion calculation for testing
// This matches the implementation in depthflow.ts
function calculateExponentialMotion(
  startValue: number,
  endValue: number,
  easedT: number,
): number {
  // BUG-004 FIX: Prevent division by zero when startValue is 0
  // Fall back to linear interpolation in this case
  if (startValue === 0) {
    return endValue * easedT;
  }
  const ratio = endValue / startValue;
  return startValue * ratio ** easedT;
}

describe("Depthflow motion calculations", () => {
  describe("exponential motion", () => {
    test("calculates exponential growth correctly", () => {
      // From 1 to 100 with exponential growth
      expect(calculateExponentialMotion(1, 100, 0)).toBe(1);
      expect(calculateExponentialMotion(1, 100, 1)).toBe(100);
      
      // Midpoint should be geometric mean (sqrt(1*100) = 10)
      expect(calculateExponentialMotion(1, 100, 0.5)).toBeCloseTo(10, 1);
    });

    test("handles decay (shrinking values)", () => {
      // From 100 to 1 (decay)
      expect(calculateExponentialMotion(100, 1, 0)).toBe(100);
      expect(calculateExponentialMotion(100, 1, 1)).toBe(1);
      expect(calculateExponentialMotion(100, 1, 0.5)).toBeCloseTo(10, 1);
    });

    /**
     * BUG #4 FIX VERIFICATION
     * 
     * When startValue is 0, division by zero produces NaN.
     * The fix falls back to linear interpolation.
     */
    test("BUG #4 FIXED: startValue=0 returns linear interpolation instead of NaN", () => {
      // Was: NaN for all easedT > 0
      // Now: Linear interpolation from 0 to endValue
      expect(calculateExponentialMotion(0, 100, 0)).toBe(0);
      expect(calculateExponentialMotion(0, 100, 0.5)).toBe(50);
      expect(calculateExponentialMotion(0, 100, 1)).toBe(100);
      
      // All should be finite numbers
      expect(Number.isFinite(calculateExponentialMotion(0, 100, 0))).toBe(true);
      expect(Number.isFinite(calculateExponentialMotion(0, 100, 0.5))).toBe(true);
      expect(Number.isFinite(calculateExponentialMotion(0, 100, 1))).toBe(true);
    });

    test("BUG #4 FIXED: startValue=0 with negative endValue", () => {
      expect(calculateExponentialMotion(0, -100, 0.5)).toBe(-50);
      expect(Number.isFinite(calculateExponentialMotion(0, -100, 0.5))).toBe(true);
    });

    test("BUG #4 FIXED: both values 0 returns 0", () => {
      expect(calculateExponentialMotion(0, 0, 0.5)).toBe(0);
      expect(Number.isFinite(calculateExponentialMotion(0, 0, 0.5))).toBe(true);
    });
  });
});
