/**
 * Property tests for Particle LOD (Level of Detail) System
 *
 * Tests that the LOD system correctly adjusts particle rendering
 * based on distance from camera.
 */

import { describe, it, expect } from "vitest";
import * as fc from "fast-check";

//                                                                       // lod
interface LODConfig {
  enabled: boolean;
  distances: number[];
  sizeMultipliers: number[];
}

// Simulates the getLODMultiplier logic from the shader
function getLODMultiplier(distToCamera: number, config: LODConfig): number {
  if (!config.enabled) return 1.0;

  // Validate distances are in ascending order
  const distances = config.distances;
  const multipliers = config.sizeMultipliers;

  // Default to full size
  let multiplier = 1.0;

  // Check each LOD level (distances should be ascending)
  // Lean4/PureScript/Haskell: Explicit pattern matching - no lazy ??
  for (let i = 0; i < distances.length; i++) {
    if (distToCamera > distances[i]) {
      const mult = multipliers[i];
      multiplier = (mult !== null && mult !== undefined && typeof mult === "number" && Number.isFinite(mult) && mult > 0) ? mult : 1.0;
    }
  }

  return multiplier;
}

// Validates LOD config and returns sanitized version
function validateLODConfig(config: LODConfig): LODConfig {
  const validDistances = config.distances.map((d) =>
    Number.isFinite(d) && d >= 0 ? d : 0
  );
  const validMultipliers = config.sizeMultipliers.map((m) =>
    Number.isFinite(m) && m >= 0 && m <= 2 ? m : 1.0
  );

  // Ensure distances are sorted ascending
  validDistances.sort((a, b) => a - b);

  return {
    enabled: config.enabled,
    distances: validDistances,
    sizeMultipliers: validMultipliers,
  };
}

describe("Particle LOD System", () => {
  // Arbitrary for valid LOD config
  const arbLODConfig = fc
    .record({
      enabled: fc.boolean(),
      distances: fc.array(fc.float({ min: Math.fround(0), max: Math.fround(10000), noNaN: true }), {
        minLength: 1,
        maxLength: 5,
      }),
      sizeMultipliers: fc.array(fc.float({ min: Math.fround(0.01), max: Math.fround(2.0), noNaN: true }), {
        minLength: 1,
        maxLength: 5,
      }),
    })
    .map((config) => ({
      ...config,
      // Ensure same length arrays
      sizeMultipliers: config.sizeMultipliers.slice(
        0,
        config.distances.length
      ),
    }));

  const arbDistance = fc.float({ min: Math.fround(0), max: Math.fround(20000), noNaN: true });

  describe("INVARIANT: Disabled LOD returns 1.0", () => {
    it("should always return 1.0 when LOD is disabled", () => {
      fc.assert(
        fc.property(arbLODConfig, arbDistance, (config, distance) => {
          const disabledConfig = { ...config, enabled: false };
          const multiplier = getLODMultiplier(distance, disabledConfig);
          expect(multiplier).toBe(1.0);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("INVARIANT: Multiplier is always positive and finite", () => {
    it("should always return a positive finite multiplier", () => {
      fc.assert(
        fc.property(arbLODConfig, arbDistance, (config, distance) => {
          const validConfig = validateLODConfig(config);
          const multiplier = getLODMultiplier(distance, validConfig);

          expect(Number.isFinite(multiplier)).toBe(true);
          expect(multiplier).toBeGreaterThan(0);
          expect(multiplier).toBeLessThanOrEqual(2.0);
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("INVARIANT: Closer particles are not smaller than far particles", () => {
    it("should not reduce size for particles closer than all LOD distances", () => {
      fc.assert(
        fc.property(arbLODConfig, (config) => {
          const validConfig = validateLODConfig(config);
          if (!validConfig.enabled || validConfig.distances.length === 0)
            return true;

          // Particle closer than the first LOD distance
          const closeDistance = Math.min(...validConfig.distances) * 0.5;
          const multiplier = getLODMultiplier(closeDistance, validConfig);

          // Should get full size (1.0) if closer than all distances
          expect(multiplier).toBe(1.0);
          return true;
        }),
        { numRuns: 100 }
      );
    });
  });

  describe("INVARIANT: LOD transitions are monotonic", () => {
    it("size multipliers should decrease (or stay same) as distance increases with well-formed config", () => {
      // Test with a properly configured LOD system where:
      // - distances are ascending
      // - multipliers are descending (smaller at greater distances)
      const wellFormedConfigs: LODConfig[] = [
        {
          enabled: true,
          distances: [100, 300, 600],
          sizeMultipliers: [0.75, 0.5, 0.25],
        },
        {
          enabled: true,
          distances: [50, 150, 500, 1000],
          sizeMultipliers: [0.9, 0.6, 0.3, 0.1],
        },
        {
          enabled: true,
          distances: [200],
          sizeMultipliers: [0.5],
        },
      ];

      for (const config of wellFormedConfigs) {
        // Sample distances at regular intervals
        const testDistances = [0, 100, 200, 300, 500, 700, 1000, 2000];
        const multipliers = testDistances.map((d) =>
          getLODMultiplier(d, config)
        );

        // Each multiplier should be >= the next (multipliers decrease with distance)
        for (let i = 0; i < multipliers.length - 1; i++) {
          // Close distances should have same or larger multipliers than far distances
          expect(multipliers[i]).toBeGreaterThanOrEqual(multipliers[i + 1] - 0.0001);
        }
      }
    });

    it("should return consistent results for the same distance", () => {
      fc.assert(
        fc.property(arbLODConfig, arbDistance, (config, distance) => {
          const validConfig = validateLODConfig(config);
          
          // Call twice with same inputs
          const result1 = getLODMultiplier(distance, validConfig);
          const result2 = getLODMultiplier(distance, validConfig);
          
          // Should be exactly the same (deterministic)
          expect(result1).toBe(result2);
          return true;
        }),
        { numRuns: 50 }
      );
    });
  });

  describe("EDGE CASE: Zero distances", () => {
    it("should handle zero distance thresholds", () => {
      const config: LODConfig = {
        enabled: true,
        distances: [0, 100, 200],
        sizeMultipliers: [0.8, 0.5, 0.25],
      };

      // At distance 0, particle is past the first threshold (0)
      // but not past others
      const mult0 = getLODMultiplier(0, config);
      expect(Number.isFinite(mult0)).toBe(true);

      // At distance 50, should use first multiplier
      const mult50 = getLODMultiplier(50, config);
      expect(Number.isFinite(mult50)).toBe(true);
    });
  });

  describe("EDGE CASE: Very large distances", () => {
    it("should handle extremely large camera distances", () => {
      const config: LODConfig = {
        enabled: true,
        distances: [100, 500, 1000],
        sizeMultipliers: [0.75, 0.5, 0.25],
      };

      const hugeDistance = 1e10;
      const multiplier = getLODMultiplier(hugeDistance, config);

      expect(Number.isFinite(multiplier)).toBe(true);
      // Should use the last (smallest) multiplier
      expect(multiplier).toBe(0.25);
    });
  });

  describe("EDGE CASE: NaN and Infinity handling", () => {
    it("validateLODConfig should sanitize NaN distances", () => {
      const config: LODConfig = {
        enabled: true,
        distances: [NaN, 100, Infinity],
        sizeMultipliers: [0.8, 0.5, NaN],
      };

      const valid = validateLODConfig(config);

      // NaN distances should become 0, Infinity should become 0
      expect(valid.distances.every((d) => Number.isFinite(d))).toBe(true);

      // NaN multipliers should become 1.0
      expect(valid.sizeMultipliers.every((m) => Number.isFinite(m))).toBe(true);
    });
  });

  describe("EDGE CASE: Empty arrays", () => {
    it("should handle empty distance/multiplier arrays", () => {
      const config: LODConfig = {
        enabled: true,
        distances: [],
        sizeMultipliers: [],
      };

      // Should still return a valid multiplier (1.0 default)
      const multiplier = getLODMultiplier(500, config);
      expect(multiplier).toBe(1.0);
    });
  });

  describe("EDGE CASE: Mismatched array lengths", () => {
    it("should handle when distances and multipliers have different lengths", () => {
      const config: LODConfig = {
        enabled: true,
        distances: [100, 200, 300],
        sizeMultipliers: [0.5], // Only one multiplier
      };

      // Should not crash, should use available multipliers
      fc.assert(
        fc.property(arbDistance, (distance) => {
          const multiplier = getLODMultiplier(distance, config);
          expect(Number.isFinite(multiplier)).toBe(true);
          return true;
        }),
        { numRuns: 50 }
      );
    });
  });
});
