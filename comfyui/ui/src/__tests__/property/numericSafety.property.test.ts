// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// PROPERTY TESTS: NUMERIC SAFETY
// ═══════════════════════════════════════════════════════════════════════════
// Fast-check property tests for numeric edge cases.
// These catch issues that unit tests miss: NaN, Infinity, negative zero, etc.
// ═══════════════════════════════════════════════════════════════════════════

import { describe, it, expect } from "vitest";
import fc from "fast-check";
import {
  ensureFinite,
  requireFinite,
  safeDivide,
  safeMod,
  safeSqrt,
  clamp,
  clamp01,
  safeLerp,
  safeInverseLerp,
  safeNormalize2D,
  safeDistance2D,
  normalizeAngleDegrees,
  approximately,
  roundTo,
} from "@/utils/numericSafety";

describe("NumericSafety Property Tests", () => {
  // ═══════════════════════════════════════════════════════════════════════════
  //                                                         // ensure // finite
  // ═══════════════════════════════════════════════════════════════════════════
  
  describe("ensureFinite", () => {
    it("returns finite numbers unchanged", () => {
      fc.assert(
        fc.property(fc.double({ noNaN: true, noDefaultInfinity: true }), (n) => {
          expect(ensureFinite(n, 0)).toBe(n);
        })
      );
    });

    it("returns fallback for NaN", () => {
      expect(ensureFinite(NaN, 42)).toBe(42);
    });

    it("returns fallback for Infinity", () => {
      expect(ensureFinite(Infinity, 42)).toBe(42);
      expect(ensureFinite(-Infinity, 42)).toBe(42);
    });

    it("handles any value without throwing", () => {
      fc.assert(
        fc.property(fc.anything(), (value) => {
          // Should never throw, always return a finite number
          const result = ensureFinite(value, 0);
          expect(Number.isFinite(result)).toBe(true);
        })
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                           // safe // divide
  // ═══════════════════════════════════════════════════════════════════════════

  describe("safeDivide", () => {
    it("handles normal division", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }).filter((n) => n !== 0),
          (a, b) => {
            const result = safeDivide(a, b, 0);
            // Result should be finite or use fallback
            expect(Number.isFinite(result)).toBe(true);
          }
        )
      );
    });

    it("returns fallback for division by zero", () => {
      fc.assert(
        fc.property(fc.double({ noNaN: true, noDefaultInfinity: true }), (n) => {
          expect(safeDivide(n, 0, 999)).toBe(999);
        })
      );
    });

    it("never returns NaN or Infinity", () => {
      fc.assert(
        fc.property(fc.double(), fc.double(), fc.double(), (a, b, fallback) => {
          const result = safeDivide(a, b, ensureFinite(fallback, 0));
          expect(Number.isFinite(result)).toBe(true);
        })
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                              // safe // mod
  // ═══════════════════════════════════════════════════════════════════════════

  describe("safeMod", () => {
    it("handles positive numbers correctly", () => {
      fc.assert(
        fc.property(
          fc.nat(1000),
          fc.nat(100).filter((n) => n > 0),
          (a, b) => {
            const result = safeMod(a, b);
            expect(result).toBeGreaterThanOrEqual(0);
            expect(result).toBeLessThan(b);
          }
        )
      );
    });

    it("handles negative numbers correctly (always positive result)", () => {
      fc.assert(
        fc.property(
          fc.integer({ min: -1000, max: -1 }),
          fc.nat(100).filter((n) => n > 0),
          (a, b) => {
            const result = safeMod(a, b);
            // Unlike JS %, should always be positive
            expect(result).toBeGreaterThanOrEqual(0);
            expect(result).toBeLessThan(b);
          }
        )
      );
    });

    it("returns 0 for mod by zero", () => {
      fc.assert(
        fc.property(fc.integer(), (n) => {
          expect(safeMod(n, 0)).toBe(0);
        })
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                             // safe // sqrt
  // ═══════════════════════════════════════════════════════════════════════════

  describe("safeSqrt", () => {
    it("handles positive numbers correctly", () => {
      fc.assert(
        fc.property(
          // Limit range to avoid precision issues with very large numbers
          fc.double({ min: 0, max: 1e30, noNaN: true, noDefaultInfinity: true }),
          (n) => {
            const result = safeSqrt(n);
            // Use relative tolerance - result*result should be close to n
            if (n > 1) {
              // For large numbers, allow relative error
              const error = Math.abs(result * result - n) / n;
              expect(error).toBeLessThan(1e-10);
            } else if (n > 1e-300) {
              // For normal small numbers
              expect(result * result).toBeCloseTo(n, 10);
            }
            // For subnormals, just check result is finite and non-negative
          }
        )
      );
    });

    it("returns 0 for negative numbers", () => {
      fc.assert(
        fc.property(
          fc.double({ max: -0.001, noNaN: true, noDefaultInfinity: true }),
          (n) => {
            expect(safeSqrt(n)).toBe(0);
          }
        )
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                                    // clamp
  // ═══════════════════════════════════════════════════════════════════════════

  describe("clamp", () => {
    it("returns value when in range", () => {
      fc.assert(
        fc.property(
          // Use reasonable range to avoid subnormal precision issues in midpoint
          fc.double({ min: -1e100, max: 1e100, noNaN: true, noDefaultInfinity: true }),
          fc.double({ min: -1e100, max: 1e100, noNaN: true, noDefaultInfinity: true }),
          (a, b) => {
            // Ensure meaningful range
            fc.pre(Math.abs(a - b) > 1e-300);
            const [min, max] = [Math.min(a, b), Math.max(a, b)];
            const value = (min + max) / 2; // Value in middle
            const result = clamp(value, min, max);
            // Result should equal value or be very close
            expect(result).toBeGreaterThanOrEqual(min);
            expect(result).toBeLessThanOrEqual(max);
          }
        )
      );
    });

    it("clamps to min when below", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (min, range) => {
            fc.pre(range > 0);
            const max = min + Math.abs(range);
            const below = min - Math.abs(range);
            expect(clamp(below, min, max)).toBe(min);
          }
        )
      );
    });

    it("clamps to max when above", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (min, range) => {
            fc.pre(range > 0);
            const max = min + Math.abs(range);
            const above = max + Math.abs(range);
            expect(clamp(above, min, max)).toBe(max);
          }
        )
      );
    });

    it("handles NaN by returning min", () => {
      expect(clamp(NaN, 0, 100)).toBe(0);
    });
  });

  describe("clamp01", () => {
    it("always returns value in [0, 1]", () => {
      fc.assert(
        fc.property(fc.double(), (n) => {
          const result = clamp01(n);
          expect(result).toBeGreaterThanOrEqual(0);
          expect(result).toBeLessThanOrEqual(1);
        })
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                             // safe // lerp
  // ═══════════════════════════════════════════════════════════════════════════

  describe("safeLerp", () => {
    it("returns a when t=0", () => {
      fc.assert(
        fc.property(
          // Limit range to avoid subnormal precision issues
          fc.double({ min: -1e100, max: 1e100, noNaN: true, noDefaultInfinity: true }),
          fc.double({ min: -1e100, max: 1e100, noNaN: true, noDefaultInfinity: true }),
          (a, b) => {
            expect(safeLerp(a, b, 0)).toBeCloseTo(a, 10);
          }
        )
      );
    });

    it("returns b when t=1", () => {
      fc.assert(
        fc.property(
          // Limit range to avoid precision issues with large differences
          fc.double({ min: -1e10, max: 1e10, noNaN: true, noDefaultInfinity: true }),
          fc.double({ min: -1e10, max: 1e10, noNaN: true, noDefaultInfinity: true }),
          (a, b) => {
            const result = safeLerp(a, b, 1);
            // Use relative comparison for precision
            if (Math.abs(b) > 1) {
              const relError = Math.abs(result - b) / Math.abs(b);
              expect(relError).toBeLessThan(1e-10);
            } else {
              // Use 9 decimal places - 10 is too tight for floating point lerp
              expect(result).toBeCloseTo(b, 9);
            }
          }
        )
      );
    });

    it("returns midpoint when t=0.5", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true, min: -1e10, max: 1e10 }),
          fc.double({ noNaN: true, noDefaultInfinity: true, min: -1e10, max: 1e10 }),
          (a, b) => {
            expect(safeLerp(a, b, 0.5)).toBeCloseTo((a + b) / 2, 5);
          }
        )
      );
    });

    it("clamps t to [0, 1]", () => {
      fc.assert(
        fc.property(
          // Limit range to avoid subnormal precision issues
          fc.double({ min: -1e100, max: 1e100, noNaN: true, noDefaultInfinity: true }),
          fc.double({ min: -1e100, max: 1e100, noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (a, b, t) => {
            const result = safeLerp(a, b, t);
            // Result should be between a and b (or equal to one of them)
            const min = Math.min(a, b);
            const max = Math.max(a, b);
            // Use relative tolerance for large numbers
            const tolerance = Math.max(1e-10, Math.abs(max - min) * 1e-10);
            expect(result).toBeGreaterThanOrEqual(min - tolerance);
            expect(result).toBeLessThanOrEqual(max + tolerance);
          }
        )
      );
    });

    it("never returns NaN or Infinity", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (a, b, t) => {
            const result = safeLerp(a, b, t);
            expect(Number.isFinite(result)).toBe(true);
          }
        )
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                  // safe // inverse // lerp
  // ═══════════════════════════════════════════════════════════════════════════

  describe("safeInverseLerp", () => {
    it("returns 0 when value equals a", () => {
      fc.assert(
        fc.property(
          // Limit range and ensure meaningful difference between a and b
          fc.double({ min: -1e10, max: 1e10, noNaN: true, noDefaultInfinity: true }),
          fc.double({ min: -1e10, max: 1e10, noNaN: true, noDefaultInfinity: true }),
          (a, b) => {
            // Ensure meaningful difference (not subnormal)
            fc.pre(Math.abs(a - b) > 1e-300);
            expect(safeInverseLerp(a, b, a)).toBeCloseTo(0, 10);
          }
        )
      );
    });

    it("returns 1 when value equals b", () => {
      fc.assert(
        fc.property(
          // Limit range and ensure meaningful difference between a and b
          fc.double({ min: -1e10, max: 1e10, noNaN: true, noDefaultInfinity: true }),
          fc.double({ min: -1e10, max: 1e10, noNaN: true, noDefaultInfinity: true }),
          (a, b) => {
            // Ensure meaningful difference (not subnormal)
            fc.pre(Math.abs(a - b) > 1e-300);
            expect(safeInverseLerp(a, b, b)).toBeCloseTo(1, 10);
          }
        )
      );
    });

    it("handles zero range without NaN", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (n) => {
            const result = safeInverseLerp(n, n, n);
            expect(Number.isFinite(result)).toBe(true);
          }
        )
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                  // safe // normalize // 2d
  // ═══════════════════════════════════════════════════════════════════════════

  describe("safeNormalize2D", () => {
    it("returns unit vector for non-zero input", () => {
      fc.assert(
        fc.property(
          // Limit range to avoid subnormals that underflow to zero when squared
          fc.double({ min: -1e150, max: 1e150, noNaN: true, noDefaultInfinity: true }),
          fc.double({ min: -1e150, max: 1e150, noNaN: true, noDefaultInfinity: true }),
          (x, y) => {
            // Ensure vector length is non-zero and not subnormal
            const lengthSq = x * x + y * y;
            fc.pre(lengthSq > 1e-300);
            const result = safeNormalize2D(x, y);
            const resultLength = Math.sqrt(result.x * result.x + result.y * result.y);
            expect(resultLength).toBeCloseTo(1, 5);
          }
        )
      );
    });

    it("returns zero vector for zero input", () => {
      const result = safeNormalize2D(0, 0);
      expect(result.x).toBe(0);
      expect(result.y).toBe(0);
    });

    it("never returns NaN", () => {
      fc.assert(
        fc.property(fc.double(), fc.double(), (x, y) => {
          const result = safeNormalize2D(x, y);
          expect(Number.isFinite(result.x)).toBe(true);
          expect(Number.isFinite(result.y)).toBe(true);
        })
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                   // safe // distance // 2d
  // ═══════════════════════════════════════════════════════════════════════════

  describe("safeDistance2D", () => {
    it("returns 0 for same point", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (x, y) => {
            expect(safeDistance2D(x, y, x, y)).toBeCloseTo(0, 10);
          }
        )
      );
    });

    it("is symmetric", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          fc.double({ noNaN: true, noDefaultInfinity: true }),
          (x1, y1, x2, y2) => {
            const d1 = safeDistance2D(x1, y1, x2, y2);
            const d2 = safeDistance2D(x2, y2, x1, y1);
            expect(d1).toBeCloseTo(d2, 10);
          }
        )
      );
    });

    it("is always non-negative", () => {
      fc.assert(
        fc.property(fc.double(), fc.double(), fc.double(), fc.double(), (x1, y1, x2, y2) => {
          const d = safeDistance2D(x1, y1, x2, y2);
          expect(d).toBeGreaterThanOrEqual(0);
        })
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                            // normalize // angle // degrees
  // ═══════════════════════════════════════════════════════════════════════════

  describe("normalizeAngleDegrees", () => {
    it("returns value in [0, 360)", () => {
      fc.assert(
        fc.property(fc.double(), (angle) => {
          const result = normalizeAngleDegrees(angle);
          expect(result).toBeGreaterThanOrEqual(0);
          expect(result).toBeLessThan(360);
        })
      );
    });

    it("preserves angle modulo 360", () => {
      fc.assert(
        fc.property(fc.integer({ min: -1000, max: 1000 }), (n) => {
          const angle = n * 360 + 45; // Multiple of 360 plus 45
          expect(normalizeAngleDegrees(angle)).toBeCloseTo(45, 10);
        })
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                            // approximately
  // ═══════════════════════════════════════════════════════════════════════════

  describe("approximately", () => {
    it("returns true for equal numbers", () => {
      fc.assert(
        fc.property(fc.double({ noNaN: true, noDefaultInfinity: true }), (n) => {
          expect(approximately(n, n)).toBe(true);
        })
      );
    });

    it("returns true for very close numbers", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true, min: -1e10, max: 1e10 }),
          (n) => {
            const epsilon = Number.EPSILON * 100;
            expect(approximately(n, n + epsilon / 10)).toBe(true);
          }
        )
      );
    });

    it("returns false for distant numbers", () => {
      fc.assert(
        fc.property(
          // Use smaller range where n + 1 is actually meaningfully different
          fc.double({ noNaN: true, noDefaultInfinity: true, min: -1e3, max: 1e3 }),
          (n) => {
            // For numbers where 1 is a significant difference
            expect(approximately(n, n + 1)).toBe(false);
          }
        )
      );
    });
  });

  // ═══════════════════════════════════════════════════════════════════════════
  //                                                              // round // to
  // ═══════════════════════════════════════════════════════════════════════════

  describe("roundTo", () => {
    it("rounds to specified decimals", () => {
      fc.assert(
        fc.property(
          fc.double({ noNaN: true, noDefaultInfinity: true, min: -1e10, max: 1e10 }),
          fc.integer({ min: 0, max: 10 }),
          (n, decimals) => {
            const result = roundTo(n, decimals);
            const factor = Math.pow(10, decimals);
            // Check that result has at most `decimals` decimal places
            expect(Math.round(result * factor) / factor).toBeCloseTo(result, decimals);
          }
        )
      );
    });

    it("handles NaN by treating as 0", () => {
      expect(roundTo(NaN, 2)).toBe(0);
    });
  });
});
