/**
 * Unit Tests for SeededRandom.ts
 *
 * Tests the seeded random number generator - CRITICAL for particle determinism.
 * Same seed MUST produce same sequence, every time.
 */
import { describe, test, expect, beforeEach } from "vitest";
import { SeededRandom } from "@/services/particles/SeededRandom";

describe("SeededRandom", () => {
  describe("constructor", () => {
    test("creates with default seed 12345", () => {
      const rng = new SeededRandom();
      expect(rng.getSeed()).toBe(12345);
    });

    test("creates with custom seed", () => {
      const rng = new SeededRandom(42);
      expect(rng.getSeed()).toBe(42);
    });

    test("creates with seed 0", () => {
      const rng = new SeededRandom(0);
      expect(rng.getSeed()).toBe(0);
    });

    test("creates with negative seed", () => {
      const rng = new SeededRandom(-12345);
      expect(rng.getSeed()).toBe(-12345);
    });

    test("creates with very large seed", () => {
      const rng = new SeededRandom(Number.MAX_SAFE_INTEGER);
      expect(rng.getSeed()).toBe(Number.MAX_SAFE_INTEGER);
    });
  });

  describe("reset", () => {
    test("reset returns to initial sequence", () => {
      const rng = new SeededRandom(42);
      const firstSequence = [rng.next(), rng.next(), rng.next()];
      
      rng.reset();
      const secondSequence = [rng.next(), rng.next(), rng.next()];
      
      expect(secondSequence).toEqual(firstSequence);
    });

    test("reset works after many calls", () => {
      const rng = new SeededRandom(42);
      const firstValue = rng.next();
      
      // Generate many random numbers
      for (let i = 0; i < 10000; i++) {
        rng.next();
      }
      
      rng.reset();
      expect(rng.next()).toBe(firstValue);
    });
  });

  describe("setSeed", () => {
    test("setSeed changes the sequence", () => {
      const rng = new SeededRandom(42);
      const firstValue = rng.next();
      
      rng.setSeed(999);
      const newValue = rng.next();
      
      expect(newValue).not.toBe(firstValue);
      expect(rng.getSeed()).toBe(999);
    });

    test("setSeed makes subsequent reset use new seed", () => {
      const rng = new SeededRandom(42);
      rng.setSeed(999);
      const expected = rng.next();
      
      rng.next();
      rng.next();
      rng.reset();
      
      expect(rng.next()).toBe(expected);
      expect(rng.getSeed()).toBe(999);
    });
  });

  describe("getState / setState", () => {
    test("getState returns current internal state", () => {
      const rng = new SeededRandom(42);
      rng.next();
      const state = rng.getState();
      expect(typeof state).toBe("number");
    });

    test("setState restores exact position in sequence", () => {
      const rng = new SeededRandom(42);
      rng.next();
      rng.next();
      const checkpoint = rng.getState();
      const expectedSequence = [rng.next(), rng.next(), rng.next()];
      
      // Continue generating
      for (let i = 0; i < 100; i++) {
        rng.next();
      }
      
      // Restore checkpoint
      rng.setState(checkpoint);
      const restoredSequence = [rng.next(), rng.next(), rng.next()];
      
      expect(restoredSequence).toEqual(expectedSequence);
    });
  });

  describe("next", () => {
    test("returns values in [0, 1)", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 10000; i++) {
        const v = rng.next();
        expect(v).toBeGreaterThanOrEqual(0);
        expect(v).toBeLessThan(1);
      }
    });

    test("produces deterministic sequence for same seed", () => {
      const rng1 = new SeededRandom(12345);
      const rng2 = new SeededRandom(12345);
      
      for (let i = 0; i < 100; i++) {
        expect(rng1.next()).toBe(rng2.next());
      }
    });

    test("different seeds produce different sequences", () => {
      const rng1 = new SeededRandom(1);
      const rng2 = new SeededRandom(2);
      
      // Very unlikely to match by chance
      let matches = 0;
      for (let i = 0; i < 100; i++) {
        if (rng1.next() === rng2.next()) matches++;
      }
      expect(matches).toBeLessThan(5);
    });

    test("sequence is statistically uniform", () => {
      const rng = new SeededRandom(42);
      const buckets = new Array(10).fill(0);
      const samples = 100000;
      
      for (let i = 0; i < samples; i++) {
        const bucket = Math.floor(rng.next() * 10);
        buckets[bucket]++;
      }
      
      // Each bucket should have ~10% (10000 samples)
      // Allow 5% deviation
      const expected = samples / 10;
      for (const count of buckets) {
        expect(count).toBeGreaterThan(expected * 0.95);
        expect(count).toBeLessThan(expected * 1.05);
      }
    });
  });

  describe("range", () => {
    test("returns values in [min, max]", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 1000; i++) {
        const v = rng.range(10, 20);
        expect(v).toBeGreaterThanOrEqual(10);
        expect(v).toBeLessThanOrEqual(20);
      }
    });

    test("handles negative range", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 100; i++) {
        const v = rng.range(-100, -50);
        expect(v).toBeGreaterThanOrEqual(-100);
        expect(v).toBeLessThanOrEqual(-50);
      }
    });

    test("handles min > max (inverted range)", () => {
      const rng = new SeededRandom(42);
      // When min > max, the math still works but range is inverted
      const v = rng.range(100, 0);
      // Result will be 100 + next() * (0 - 100) = 100 - next()*100
      // So result is in [0, 100]
      expect(v).toBeGreaterThanOrEqual(0);
      expect(v).toBeLessThanOrEqual(100);
    });

    test("returns exactly min when min === max", () => {
      const rng = new SeededRandom(42);
      expect(rng.range(5, 5)).toBe(5);
    });
  });

  describe("int", () => {
    test("returns integers in [min, max] inclusive", () => {
      const rng = new SeededRandom(42);
      const seen = new Set<number>();
      
      for (let i = 0; i < 10000; i++) {
        const v = rng.int(1, 6);
        expect(Number.isInteger(v)).toBe(true);
        expect(v).toBeGreaterThanOrEqual(1);
        expect(v).toBeLessThanOrEqual(6);
        seen.add(v);
      }
      
      // Should see all values 1-6
      expect(seen.size).toBe(6);
    });

    test("handles single value range", () => {
      const rng = new SeededRandom(42);
      expect(rng.int(5, 5)).toBe(5);
    });

    test("handles negative integers", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 100; i++) {
        const v = rng.int(-10, -5);
        expect(Number.isInteger(v)).toBe(true);
        expect(v).toBeGreaterThanOrEqual(-10);
        expect(v).toBeLessThanOrEqual(-5);
      }
    });
  });

  describe("variance", () => {
    test("returns values centered around base", () => {
      const rng = new SeededRandom(42);
      const base = 100;
      const variance = 10;
      let sum = 0;
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        sum += rng.variance(base, variance);
      }
      
      const avg = sum / samples;
      // Average should be close to base
      expect(avg).toBeCloseTo(base, 0);
    });

    test("stays within base ± variance", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 1000; i++) {
        const v = rng.variance(50, 10);
        expect(v).toBeGreaterThanOrEqual(40);
        expect(v).toBeLessThanOrEqual(60);
      }
    });

    test("handles zero variance", () => {
      const rng = new SeededRandom(42);
      // With variance=0, result is base + (next()-0.5)*2*0 = base
      // But next() is consumed, so it's not exactly base
      const v = rng.variance(100, 0);
      expect(v).toBe(100);
    });
  });

  describe("bool", () => {
    test("returns boolean", () => {
      const rng = new SeededRandom(42);
      const v = rng.bool();
      expect(typeof v).toBe("boolean");
    });

    test("default probability is 50%", () => {
      const rng = new SeededRandom(42);
      let trueCount = 0;
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        if (rng.bool()) trueCount++;
      }
      
      const ratio = trueCount / samples;
      expect(ratio).toBeGreaterThan(0.45);
      expect(ratio).toBeLessThan(0.55);
    });

    test("probability 0 always returns false", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 100; i++) {
        expect(rng.bool(0)).toBe(false);
      }
    });

    test("probability 1 always returns true", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 100; i++) {
        expect(rng.bool(1)).toBe(true);
      }
    });

    test("custom probability works", () => {
      const rng = new SeededRandom(42);
      let trueCount = 0;
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        if (rng.bool(0.8)) trueCount++;
      }
      
      const ratio = trueCount / samples;
      expect(ratio).toBeGreaterThan(0.75);
      expect(ratio).toBeLessThan(0.85);
    });
  });

  describe("angle", () => {
    test("returns values in [0, 2π)", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 1000; i++) {
        const v = rng.angle();
        expect(v).toBeGreaterThanOrEqual(0);
        expect(v).toBeLessThan(Math.PI * 2);
      }
    });
  });

  describe("inCircle", () => {
    test("returns point with x and y properties", () => {
      const rng = new SeededRandom(42);
      const p = rng.inCircle();
      expect(p).toHaveProperty("x");
      expect(p).toHaveProperty("y");
    });

    test("all points are within unit circle", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 1000; i++) {
        const p = rng.inCircle();
        const distSq = p.x * p.x + p.y * p.y;
        expect(distSq).toBeLessThanOrEqual(1);
      }
    });

    test("distribution is uniform (not clustered at center)", () => {
      const rng = new SeededRandom(42);
      let innerCount = 0;
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        const p = rng.inCircle();
        const dist = Math.sqrt(p.x * p.x + p.y * p.y);
        if (dist < 0.5) innerCount++;
      }
      
      // Inner circle (r=0.5) has area π*0.25, full circle has area π
      // So ~25% should be in inner circle
      const ratio = innerCount / samples;
      expect(ratio).toBeGreaterThan(0.20);
      expect(ratio).toBeLessThan(0.30);
    });
  });

  describe("onSphere", () => {
    test("returns point with x, y, z properties", () => {
      const rng = new SeededRandom(42);
      const p = rng.onSphere();
      expect(p).toHaveProperty("x");
      expect(p).toHaveProperty("y");
      expect(p).toHaveProperty("z");
    });

    test("all points are on unit sphere surface", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 1000; i++) {
        const p = rng.onSphere();
        const dist = Math.sqrt(p.x * p.x + p.y * p.y + p.z * p.z);
        expect(dist).toBeCloseTo(1, 10);
      }
    });
  });

  describe("gaussian", () => {
    test("returns finite numbers", () => {
      const rng = new SeededRandom(42);
      for (let i = 0; i < 1000; i++) {
        const v = rng.gaussian();
        expect(Number.isFinite(v)).toBe(true);
      }
    });

    test("default mean is 0", () => {
      const rng = new SeededRandom(42);
      let sum = 0;
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        sum += rng.gaussian();
      }
      
      const avg = sum / samples;
      expect(avg).toBeCloseTo(0, 1);
    });

    test("default stdDev is 1", () => {
      const rng = new SeededRandom(42);
      const values: number[] = [];
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        values.push(rng.gaussian());
      }
      
      // Calculate standard deviation
      const mean = values.reduce((a, b) => a + b, 0) / samples;
      const variance = values.reduce((sum, v) => sum + (v - mean) ** 2, 0) / samples;
      const stdDev = Math.sqrt(variance);
      
      expect(stdDev).toBeCloseTo(1, 1);
    });

    test("custom mean shifts distribution", () => {
      const rng = new SeededRandom(42);
      let sum = 0;
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        sum += rng.gaussian(100, 1);
      }
      
      const avg = sum / samples;
      expect(avg).toBeCloseTo(100, 0);
    });

    test("custom stdDev changes spread", () => {
      const rng = new SeededRandom(42);
      const values: number[] = [];
      const samples = 10000;
      
      for (let i = 0; i < samples; i++) {
        values.push(rng.gaussian(0, 5));
      }
      
      const mean = values.reduce((a, b) => a + b, 0) / samples;
      const variance = values.reduce((sum, v) => sum + (v - mean) ** 2, 0) / samples;
      const stdDev = Math.sqrt(variance);
      
      expect(stdDev).toBeCloseTo(5, 0);
    });
  });

  describe("DETERMINISM CONTRACT", () => {
    test("same seed produces identical sequence across instances", () => {
      const seed = 987654321;
      const rng1 = new SeededRandom(seed);
      const rng2 = new SeededRandom(seed);
      
      // Test all methods produce same results
      for (let i = 0; i < 10; i++) {
        expect(rng1.next()).toBe(rng2.next());
        expect(rng1.range(0, 100)).toBe(rng2.range(0, 100));
        expect(rng1.int(1, 10)).toBe(rng2.int(1, 10));
        expect(rng1.variance(50, 10)).toBe(rng2.variance(50, 10));
        expect(rng1.bool(0.5)).toBe(rng2.bool(0.5));
        expect(rng1.angle()).toBe(rng2.angle());
        
        const c1 = rng1.inCircle();
        const c2 = rng2.inCircle();
        expect(c1.x).toBe(c2.x);
        expect(c1.y).toBe(c2.y);
        
        const s1 = rng1.onSphere();
        const s2 = rng2.onSphere();
        expect(s1.x).toBe(s2.x);
        expect(s1.y).toBe(s2.y);
        expect(s1.z).toBe(s2.z);
        
        expect(rng1.gaussian(0, 1)).toBe(rng2.gaussian(0, 1));
      }
    });

    test("checkpoint restore produces identical continuation", () => {
      const rng = new SeededRandom(42);
      
      // Advance to some point
      for (let i = 0; i < 50; i++) {
        rng.next();
      }
      
      // Save checkpoint
      const checkpoint = rng.getState();
      const expectedSequence: number[] = [];
      for (let i = 0; i < 100; i++) {
        expectedSequence.push(rng.next());
      }
      
      // Advance further
      for (let i = 0; i < 1000; i++) {
        rng.next();
      }
      
      // Restore and verify
      rng.setState(checkpoint);
      for (let i = 0; i < 100; i++) {
        expect(rng.next()).toBe(expectedSequence[i]);
      }
    });

    test("reset produces identical sequence from start", () => {
      const rng = new SeededRandom(42);
      const originalSequence: number[] = [];
      for (let i = 0; i < 100; i++) {
        originalSequence.push(rng.next());
      }
      
      // Do random operations
      rng.range(0, 100);
      rng.int(1, 10);
      rng.gaussian();
      
      // Reset and verify
      rng.reset();
      for (let i = 0; i < 100; i++) {
        expect(rng.next()).toBe(originalSequence[i]);
      }
    });
  });

  describe("Edge Cases", () => {
    test("handles seed = 0", () => {
      const rng = new SeededRandom(0);
      const v = rng.next();
      expect(Number.isFinite(v)).toBe(true);
      expect(v).toBeGreaterThanOrEqual(0);
      expect(v).toBeLessThan(1);
    });

    test("handles very large iterations without degradation", () => {
      const rng = new SeededRandom(42);
      
      // Generate a million numbers
      for (let i = 0; i < 1000000; i++) {
        rng.next();
      }
      
      // Should still produce valid output
      const v = rng.next();
      expect(v).toBeGreaterThanOrEqual(0);
      expect(v).toBeLessThan(1);
    });

    test("gaussian handles edge case when u1 is very close to 0", () => {
      // The code has: Math.log(u1 || 1e-10)
      // This prevents log(0) = -Infinity
      const rng = new SeededRandom(42);
      // Can't force u1=0 but verify no crashes in many samples
      for (let i = 0; i < 10000; i++) {
        const v = rng.gaussian();
        expect(Number.isFinite(v)).toBe(true);
      }
    });
  });

  describe("Invalid Input Handling", () => {
    test("NaN seed produces consistent (though potentially problematic) output", () => {
      // Document behavior: NaN seed will work but produce same sequence as NaN coerces to 0-ish
      const rng = new SeededRandom(NaN);
      const v = rng.next();
      // Should still produce a number (even if not ideal behavior)
      expect(typeof v).toBe("number");
    });

    test("Infinity seed produces valid output", () => {
      const rng = new SeededRandom(Infinity);
      const v = rng.next();
      expect(typeof v).toBe("number");
      // Value may not be in [0,1) due to overflow, but shouldn't crash
    });

    test("-Infinity seed produces valid output", () => {
      const rng = new SeededRandom(-Infinity);
      const v = rng.next();
      expect(typeof v).toBe("number");
    });

    test("range with NaN min/max", () => {
      const rng = new SeededRandom(42);
      const v = rng.range(NaN, 10);
      expect(Number.isNaN(v)).toBe(true);
    });

    test("range with Infinity", () => {
      const rng = new SeededRandom(42);
      const v = rng.range(0, Infinity);
      // Result will be some value from 0 to Infinity * next()
      expect(typeof v).toBe("number");
    });

    test("int with NaN produces NaN", () => {
      const rng = new SeededRandom(42);
      const v = rng.int(NaN, 10);
      expect(Number.isNaN(v)).toBe(true);
    });

    test("variance with NaN base", () => {
      const rng = new SeededRandom(42);
      const v = rng.variance(NaN, 5);
      expect(Number.isNaN(v)).toBe(true);
    });

    test("bool with NaN probability", () => {
      const rng = new SeededRandom(42);
      // next() < NaN is always false
      expect(rng.bool(NaN)).toBe(false);
    });

    test("gaussian with NaN mean produces NaN", () => {
      const rng = new SeededRandom(42);
      const v = rng.gaussian(NaN, 1);
      expect(Number.isNaN(v)).toBe(true);
    });

    test("gaussian with NaN stdDev produces NaN", () => {
      const rng = new SeededRandom(42);
      const v = rng.gaussian(0, NaN);
      expect(Number.isNaN(v)).toBe(true);
    });

    test("gaussian with negative stdDev flips distribution", () => {
      const rng1 = new SeededRandom(42);
      const rng2 = new SeededRandom(42);
      // With negative stdDev, result is mean - |z * stdDev| instead of mean + z * stdDev
      // The values will be mirrored around mean
      const v1 = rng1.gaussian(100, 5);
      const v2 = rng2.gaussian(100, -5);
      // v1 = 100 + z*5, v2 = 100 + z*(-5) = 100 - z*5
      // So v1 + v2 = 200 (they mirror around 100)
      expect(v1 + v2).toBeCloseTo(200, 10);
    });

    test("int with very large max near MAX_SAFE_INTEGER", () => {
      const rng = new SeededRandom(42);
      // When max is MAX_SAFE_INTEGER, max + 1 loses precision
      // This documents the limitation
      const v = rng.int(0, Number.MAX_SAFE_INTEGER);
      expect(typeof v).toBe("number");
      // Note: result may not include MAX_SAFE_INTEGER due to precision loss
    });

    test("range with very large span", () => {
      const rng = new SeededRandom(42);
      const v = rng.range(-1e15, 1e15);
      expect(v).toBeGreaterThanOrEqual(-1e15);
      expect(v).toBeLessThanOrEqual(1e15);
    });
  });
});
