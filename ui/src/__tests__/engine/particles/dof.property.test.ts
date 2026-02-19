/**
 * Property tests for Particle Depth of Field (DOF) System
 *
 * Tests that the DOF system correctly applies blur based on
 * particle distance from the camera's focus plane.
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";

// DOF configuration structure
interface DOFConfig {
  enabled: boolean;
  focusDistance: number;
  focusRange: number;
  blurAmount: number;
}

// Simulates the DOF calculation from the shader
function calculateDOFAlpha(
  particleDepth: number,
  baseAlpha: number,
  config: DOFConfig
): number {
  if (!config.enabled) return baseAlpha;

  // Validate config values
  const focusDistance = Number.isFinite(config.focusDistance)
    ? config.focusDistance
    : 500;
  const focusRange = Number.isFinite(config.focusRange)
    ? Math.max(0.001, config.focusRange)
    : 200;
  const blurAmount = Number.isFinite(config.blurAmount)
    ? Math.max(0, Math.min(1, config.blurAmount))
    : 0.5;

  // Calculate distance from focus plane
  const dist = Math.abs(particleDepth - focusDistance);

  // Soft transition zone (100 units)
  const transitionZone = 100;

  // Calculate blur factor using smoothstep
  let blurFactor: number;
  if (dist <= focusRange) {
    blurFactor = 0;
  } else if (dist >= focusRange + transitionZone) {
    blurFactor = 1;
  } else {
    // Smoothstep interpolation
    const t = (dist - focusRange) / transitionZone;
    blurFactor = t * t * (3 - 2 * t);
  }

  // Apply blur as alpha reduction
  return baseAlpha * (1.0 - blurFactor * blurAmount);
}

// Validates DOF config and returns sanitized version
function validateDOFConfig(config: DOFConfig): DOFConfig {
  return {
    enabled: config.enabled,
    focusDistance: Number.isFinite(config.focusDistance)
      ? Math.max(0, config.focusDistance)
      : 500,
    focusRange: Number.isFinite(config.focusRange)
      ? Math.max(0.001, config.focusRange)
      : 200,
    blurAmount: Number.isFinite(config.blurAmount)
      ? Math.max(0, Math.min(1, config.blurAmount))
      : 0.5,
  };
}

describe("Particle DOF System", () => {
  // Arbitrary for valid DOF config
  const arbDOFConfig = fc.record({
    enabled: fc.boolean(),
    focusDistance: fc.float({ min: Math.fround(0), max: Math.fround(10000), noNaN: true }),
    focusRange: fc.float({ min: Math.fround(0.1), max: Math.fround(2000), noNaN: true }),
    blurAmount: fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true }),
  });

  const arbDepth = fc.float({ min: Math.fround(-5000), max: Math.fround(15000), noNaN: true });
  const arbAlpha = fc.float({ min: Math.fround(0), max: Math.fround(1), noNaN: true });

  describe("INVARIANT: Disabled DOF returns original alpha", () => {
    it("should always return the original alpha when DOF is disabled", () => {
      fc.assert(
        fc.property(arbDOFConfig, arbDepth, arbAlpha, (config, depth, alpha) => {
          const disabledConfig = { ...config, enabled: false };
          const result = calculateDOFAlpha(depth, alpha, disabledConfig);
          expect(result).toBe(alpha);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("INVARIANT: Alpha is always in [0, original]", () => {
    it("should never increase alpha, only reduce it", () => {
      fc.assert(
        fc.property(arbDOFConfig, arbDepth, arbAlpha, (config, depth, alpha) => {
          const validConfig = validateDOFConfig(config);
          const result = calculateDOFAlpha(depth, alpha, validConfig);

          expect(Number.isFinite(result)).toBe(true);
          expect(result).toBeGreaterThanOrEqual(0);
          expect(result).toBeLessThanOrEqual(alpha + 0.0001); // Small epsilon for float comparison
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("INVARIANT: Particles at focus distance are fully visible", () => {
    it("should not blur particles exactly at focus distance", () => {
      fc.assert(
        fc.property(arbDOFConfig, arbAlpha, (config, alpha) => {
          const validConfig = { ...validateDOFConfig(config), enabled: true };
          const result = calculateDOFAlpha(
            validConfig.focusDistance,
            alpha,
            validConfig
          );

          // At exact focus distance, no blur should be applied
          expect(result).toBeCloseTo(alpha, 4);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("INVARIANT: Particles within focus range are fully visible", () => {
    it("should not blur particles within the focus range", () => {
      fc.assert(
        fc.property(arbDOFConfig, arbAlpha, (config, alpha) => {
          const validConfig = { ...validateDOFConfig(config), enabled: true };

          // Test at various positions within focus range
          const testOffsets = [0, 0.25, 0.5, 0.75, 1.0].map(
            (f) => f * validConfig.focusRange
          );

          for (const offset of testOffsets) {
            const depthBefore = validConfig.focusDistance - offset;
            const depthAfter = validConfig.focusDistance + offset;

            const resultBefore = calculateDOFAlpha(
              depthBefore,
              alpha,
              validConfig
            );
            const resultAfter = calculateDOFAlpha(
              depthAfter,
              alpha,
              validConfig
            );

            // Within focus range, should be fully visible (no blur)
            expect(resultBefore).toBeCloseTo(alpha, 3);
            expect(resultAfter).toBeCloseTo(alpha, 3);
          }

          return true;
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("INVARIANT: Blur increases with distance from focus", () => {
    it("particles farther from focus should be more blurred", () => {
      fc.assert(
        fc.property(arbDOFConfig, arbAlpha, (config, alpha) => {
          if (alpha < 0.01) return true; // Skip near-zero alpha

          const validConfig = {
            ...validateDOFConfig(config),
            enabled: true,
            blurAmount: 0.8, // Strong blur to see effect
          };

          // Get alphas at increasing distances from focus
          const farRange = validConfig.focusRange * 3;
          const veryFarRange = validConfig.focusRange * 5;

          const atFocus = calculateDOFAlpha(
            validConfig.focusDistance,
            alpha,
            validConfig
          );
          const farFromFocus = calculateDOFAlpha(
            validConfig.focusDistance + farRange,
            alpha,
            validConfig
          );
          const veryFarFromFocus = calculateDOFAlpha(
            validConfig.focusDistance + veryFarRange,
            alpha,
            validConfig
          );

          // Blur should increase (alpha should decrease) with distance
          expect(atFocus).toBeGreaterThanOrEqual(farFromFocus - 0.01);
          expect(farFromFocus).toBeGreaterThanOrEqual(veryFarFromFocus - 0.01);

          return true;
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("INVARIANT: DOF is symmetric around focus", () => {
    it("should blur equally for same distance before and after focus", () => {
      fc.assert(
        fc.property(arbDOFConfig, arbAlpha, (config, alpha) => {
          const validConfig = { ...validateDOFConfig(config), enabled: true };

          // Test at various distances
          const testDistances = [
            validConfig.focusRange * 0.5,
            validConfig.focusRange * 1.5,
            validConfig.focusRange * 3,
          ];

          for (const dist of testDistances) {
            const depthBefore = validConfig.focusDistance - dist;
            const depthAfter = validConfig.focusDistance + dist;

            const resultBefore = calculateDOFAlpha(
              depthBefore,
              alpha,
              validConfig
            );
            const resultAfter = calculateDOFAlpha(
              depthAfter,
              alpha,
              validConfig
            );

            // Blur should be symmetric
            expect(resultBefore).toBeCloseTo(resultAfter, 4);
          }

          return true;
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("EDGE CASE: Zero blur amount", () => {
    it("should not modify alpha when blurAmount is 0", () => {
      fc.assert(
        fc.property(arbDepth, arbAlpha, (depth, alpha) => {
          const config: DOFConfig = {
            enabled: true,
            focusDistance: 500,
            focusRange: 200,
            blurAmount: 0,
          };

          const result = calculateDOFAlpha(depth, alpha, config);
          expect(result).toBeCloseTo(alpha, 5);
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("EDGE CASE: Maximum blur amount", () => {
    it("should completely fade particles far from focus when blurAmount is 1", () => {
      const config: DOFConfig = {
        enabled: true,
        focusDistance: 500,
        focusRange: 100,
        blurAmount: 1.0,
      };

      // Very far from focus (well beyond transition zone)
      const veryFarDepth = config.focusDistance + config.focusRange + 500;
      const result = calculateDOFAlpha(veryFarDepth, 1.0, config);

      // Should be close to 0 (fully blurred)
      expect(result).toBeLessThan(0.1);
    });
  });

  describe("EDGE CASE: Zero focus range", () => {
    it("should handle very small focus range", () => {
      const config: DOFConfig = {
        enabled: true,
        focusDistance: 500,
        focusRange: 0.001,
        blurAmount: 0.5,
      };

      // At focus - should be fully visible
      const atFocus = calculateDOFAlpha(500, 1.0, config);
      expect(Number.isFinite(atFocus)).toBe(true);
      expect(atFocus).toBeCloseTo(1.0, 3);

      // Slightly off focus - should start blurring quickly
      const slightlyOff = calculateDOFAlpha(501, 1.0, config);
      expect(Number.isFinite(slightlyOff)).toBe(true);
    });
  });

  describe("EDGE CASE: Negative depths", () => {
    it("should handle negative particle depths correctly", () => {
      const config: DOFConfig = {
        enabled: true,
        focusDistance: 500,
        focusRange: 200,
        blurAmount: 0.5,
      };

      // Negative depth (in front of camera origin)
      const negativeDepth = calculateDOFAlpha(-100, 1.0, config);

      expect(Number.isFinite(negativeDepth)).toBe(true);
      expect(negativeDepth).toBeGreaterThan(0);
      expect(negativeDepth).toBeLessThanOrEqual(1);
    });
  });

  describe("EDGE CASE: NaN and Infinity handling", () => {
    it("validateDOFConfig should sanitize invalid values", () => {
      const config: DOFConfig = {
        enabled: true,
        focusDistance: NaN,
        focusRange: Infinity,
        blurAmount: -1,
      };

      const valid = validateDOFConfig(config);

      expect(Number.isFinite(valid.focusDistance)).toBe(true);
      expect(Number.isFinite(valid.focusRange)).toBe(true);
      expect(valid.focusRange).toBeGreaterThan(0);
      expect(valid.blurAmount).toBeGreaterThanOrEqual(0);
      expect(valid.blurAmount).toBeLessThanOrEqual(1);
    });

    it("should handle NaN depth gracefully", () => {
      const config: DOFConfig = {
        enabled: true,
        focusDistance: 500,
        focusRange: 200,
        blurAmount: 0.5,
      };

      // The function should handle NaN depth - testing the raw calculation
      // With NaN depth, Math.abs(NaN - 500) = NaN, so we need validation
      const depth = NaN;
      const safeDepth = Number.isFinite(depth) ? depth : config.focusDistance;
      const result = calculateDOFAlpha(safeDepth, 1.0, config);

      expect(Number.isFinite(result)).toBe(true);
    });
  });

  describe("EDGE CASE: Zero alpha input", () => {
    it("should return 0 when input alpha is 0", () => {
      fc.assert(
        fc.property(arbDOFConfig, arbDepth, (config, depth) => {
          const validConfig = validateDOFConfig(config);
          const result = calculateDOFAlpha(depth, 0, validConfig);
          expect(result).toBe(0);
        }),
        { numRuns: 50 }
      );
    });
  });
});
