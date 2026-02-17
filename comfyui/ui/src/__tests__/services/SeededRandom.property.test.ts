/**
 * Property Tests for SeededRandom.ts
 *
 * Tests mathematical invariants and determinism guarantees.
 */
import { describe, expect } from "vitest";
import { test } from "@fast-check/vitest";
import * as fc from "fast-check";
import { SeededRandom } from "@/services/particles/SeededRandom";

// Arbitraries
const seed = fc.integer({ min: -2147483648, max: 2147483647 });
const positiveSeed = fc.integer({ min: 1, max: 2147483647 });
const iterCount = fc.integer({ min: 1, max: 100 });
const rangeMin = fc.double({ min: -1e6, max: 1e6, noNaN: true, noDefaultInfinity: true });
const rangeSpan = fc.double({ min: 0, max: 1e6, noNaN: true, noDefaultInfinity: true });
const probability = fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true });
const variance = fc.double({ min: 0, max: 1e3, noNaN: true, noDefaultInfinity: true });
const intMin = fc.integer({ min: -1000, max: 1000 });
const intRange = fc.integer({ min: 0, max: 100 });

describe("SeededRandom Property Tests", () => {
  describe("DETERMINISM INVARIANTS", () => {
    test.prop([seed])(
      "same seed always produces identical first value",
      (s) => {
        const rng1 = new SeededRandom(s);
        const rng2 = new SeededRandom(s);
        expect(rng1.next()).toBe(rng2.next());
      },
    );

    test.prop([seed, iterCount])(
      "same seed produces identical sequence for any length",
      (s, n) => {
        const rng1 = new SeededRandom(s);
        const rng2 = new SeededRandom(s);
        for (let i = 0; i < n; i++) {
          expect(rng1.next()).toBe(rng2.next());
        }
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    // More comprehensive determinism test (1000 numbers)
    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      "STRICT: same seed produces identical sequence (1000 numbers)",
      (s) => {
        const rng1 = new SeededRandom(s);
        const rng2 = new SeededRandom(s);
        for (let i = 0; i < 1000; i++) {
          expect(rng1.next()).toBe(rng2.next());
        }
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.integer({ min: 0, max: 2147483647 }),
    ])(
      "STRICT: different seeds produce different sequences",
      (seed1, seed2) => {
        fc.pre(seed1 !== seed2);
        
        const rng1 = new SeededRandom(seed1);
        const rng2 = new SeededRandom(seed2);

        // Generate sequences
        const seq1: number[] = [];
        const seq2: number[] = [];
        for (let i = 0; i < 100; i++) {
          seq1.push(rng1.next());
          seq2.push(rng2.next());
        }

        // At least 90% should be different
        let differences = 0;
        for (let i = 0; i < 100; i++) {
          if (seq1[i] !== seq2[i]) differences++;
        }
        expect(differences).toBeGreaterThan(90);
      },
    );

    test.prop([seed, iterCount])(
      "reset always returns to start of sequence",
      (s, n) => {
        const rng = new SeededRandom(s);
        const first = rng.next();
        
        for (let i = 0; i < n; i++) {
          rng.next();
        }
        
        rng.reset();
        expect(rng.next()).toBe(first);
      },
    );

    test.prop([seed, iterCount, iterCount])(
      "checkpoint/restore produces identical continuation",
      (s, skipCount, checkCount) => {
        const rng = new SeededRandom(s);
        
        // Skip some values
        for (let i = 0; i < skipCount; i++) {
          rng.next();
        }
        
        // Checkpoint
        const checkpoint = rng.getState();
        const expected: number[] = [];
        for (let i = 0; i < checkCount; i++) {
          expected.push(rng.next());
        }
        
        // More random calls
        for (let i = 0; i < 50; i++) {
          rng.next();
        }
        
        // Restore
        rng.setState(checkpoint);
        for (let i = 0; i < checkCount; i++) {
          expect(rng.next()).toBe(expected[i]);
        }
      },
    );
  });

  describe("OUTPUT BOUNDS", () => {
    test.prop([seed, iterCount])(
      "next() always returns value in [0, 1)",
      (s, n) => {
        const rng = new SeededRandom(s);
        for (let i = 0; i < n; i++) {
          const v = rng.next();
          expect(v).toBeGreaterThanOrEqual(0);
          expect(v).toBeLessThan(1);
        }
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    // More comprehensive bounds test (1000 iterations)
    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      "STRICT: next() always returns [0, 1) (1000 iterations)",
      (s) => {
        const rng = new SeededRandom(s);
        for (let i = 0; i < 1000; i++) {
          const value = rng.next();
          expect(value).toBeGreaterThanOrEqual(0);
          expect(value).toBeLessThan(1);
        }
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      "next() is never NaN or Infinity",
      (s) => {
        const rng = new SeededRandom(s);
        for (let i = 0; i < 1000; i++) {
          const value = rng.next();
          expect(Number.isFinite(value)).toBe(true);
          expect(Number.isNaN(value)).toBe(false);
        }
      },
    );

    test.prop([seed, rangeMin, rangeSpan])(
      "range(min, max) returns value in [min, max]",
      (s, min, span) => {
        const max = min + span;
        const rng = new SeededRandom(s);
        const v = rng.range(min, max);
        expect(v).toBeGreaterThanOrEqual(min);
        expect(v).toBeLessThanOrEqual(max);
      },
    );

    test.prop([seed, intMin, intRange])(
      "int(min, max) returns integer in [min, max]",
      (s, min, range) => {
        const max = min + range;
        const rng = new SeededRandom(s);
        const v = rng.int(min, max);
        expect(Number.isInteger(v)).toBe(true);
        expect(v).toBeGreaterThanOrEqual(min);
        expect(v).toBeLessThanOrEqual(max);
      },
    );

    test.prop([seed])(
      "angle() returns value in [0, 2π)",
      (s) => {
        const rng = new SeededRandom(s);
        const v = rng.angle();
        expect(v).toBeGreaterThanOrEqual(0);
        expect(v).toBeLessThan(Math.PI * 2);
      },
    );

    test.prop([seed])(
      "bool() returns boolean",
      (s) => {
        const rng = new SeededRandom(s);
        expect(typeof rng.bool()).toBe("boolean");
      },
    );
  });

  describe("MATHEMATICAL INVARIANTS", () => {
    test.prop([seed])(
      "inCircle() point is within unit circle (distance <= 1)",
      (s) => {
        const rng = new SeededRandom(s);
        const p = rng.inCircle();
        const distSq = p.x * p.x + p.y * p.y;
        expect(distSq).toBeLessThanOrEqual(1);
      },
    );

    test.prop([seed])(
      "onSphere() point is on unit sphere surface (distance ≈ 1)",
      (s) => {
        const rng = new SeededRandom(s);
        const p = rng.onSphere();
        const dist = Math.sqrt(p.x * p.x + p.y * p.y + p.z * p.z);
        expect(dist).toBeCloseTo(1, 10);
      },
    );

    test.prop([seed, fc.double({ min: -1e6, max: 1e6, noNaN: true, noDefaultInfinity: true }), variance])(
      "variance(base, v) returns value within base ± v",
      (s, base, v) => {
        const rng = new SeededRandom(s);
        const result = rng.variance(base, v);
        expect(result).toBeGreaterThanOrEqual(base - v);
        expect(result).toBeLessThanOrEqual(base + v);
      },
    );

    test.prop([seed])(
      "gaussian() always returns finite number",
      (s) => {
        const rng = new SeededRandom(s);
        const v = rng.gaussian();
        expect(Number.isFinite(v)).toBe(true);
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      "gaussian(0, 1) produces values centered around 0",
      (s) => {
        const rng = new SeededRandom(s);
        let sum = 0;
        const count = 1000;
        
        for (let i = 0; i < count; i++) {
          sum += rng.gaussian();
        }
        
        const mean = sum / count;
        // Mean should be close to 0 (within 0.2 for 1000 samples)
        expect(Math.abs(mean)).toBeLessThan(0.2);
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.double({ min: -100, max: 100, noNaN: true }),
    ])(
      "gaussian(mean, 1) produces values centered around mean",
      (s, mean) => {
        const rng = new SeededRandom(s);
        let sum = 0;
        const count = 1000;
        
        for (let i = 0; i < count; i++) {
          sum += rng.gaussian(mean, 1);
        }
        
        const observedMean = sum / count;
        expect(Math.abs(observedMean - mean)).toBeLessThan(0.2);
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      "gaussian() never returns NaN or Infinity (1000 iterations)",
      (s) => {
        const rng = new SeededRandom(s);
        for (let i = 0; i < 1000; i++) {
          const value = rng.gaussian();
          expect(Number.isFinite(value)).toBe(true);
          expect(Number.isNaN(value)).toBe(false);
        }
      },
    );
  });

  describe("PROBABILITY CORRECTNESS", () => {
    test.prop([seed])(
      "bool(0) always returns false",
      (s) => {
        const rng = new SeededRandom(s);
        expect(rng.bool(0)).toBe(false);
      },
    );

    test.prop([seed])(
      "bool(1) always returns true",
      (s) => {
        const rng = new SeededRandom(s);
        expect(rng.bool(1)).toBe(true);
      },
    );

    // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.double({ min: 0.3, max: 0.7, noNaN: true }),
    ])(
      "bool(p) produces roughly p probability",
      (s, probability) => {
        const rng = new SeededRandom(s);
        let trueCount = 0;
        const trials = 10000;
        
        for (let i = 0; i < trials; i++) {
          if (rng.bool(probability)) trueCount++;
        }
        
        const observedProbability = trueCount / trials;
        // Allow 5% deviation from expected probability
        expect(Math.abs(observedProbability - probability)).toBeLessThan(0.05);
      },
    );
  });

  // REINTEGRATED: 2026-01-07 from _deprecated/properties/strict-seededrandom.property.test.ts
  describe("DISTRIBUTION QUALITY", () => {
    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      "next() has reasonable mean (~0.5)",
      (s) => {
        const rng = new SeededRandom(s);
        let sum = 0;
        const count = 10000;
        
        for (let i = 0; i < count; i++) {
          sum += rng.next();
        }
        
        const mean = sum / count;
        // Mean should be close to 0.5 (within 2%)
        expect(Math.abs(mean - 0.5)).toBeLessThan(0.02);
      },
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      "int() covers full range evenly",
      (s) => {
        const rng = new SeededRandom(s);
        const buckets = new Array(10).fill(0);
        const trialsPerBucket = 1000;
        
        for (let i = 0; i < trialsPerBucket * 10; i++) {
          const value = rng.int(0, 9);
          buckets[value]++;
        }
        
        // Each bucket should have ~1000 hits (allow 20% deviation)
        for (const count of buckets) {
          expect(count).toBeGreaterThan(trialsPerBucket * 0.8);
          expect(count).toBeLessThan(trialsPerBucket * 1.2);
        }
      },
    );
  });

  describe("SEED OPERATIONS", () => {
    test.prop([seed])(
      "getSeed() returns constructor seed",
      (s) => {
        const rng = new SeededRandom(s);
        expect(rng.getSeed()).toBe(s);
      },
    );

    test.prop([seed, seed])(
      "setSeed() updates both seed and state",
      (s1, s2) => {
        const rng = new SeededRandom(s1);
        rng.setSeed(s2);
        expect(rng.getSeed()).toBe(s2);
        
        // Verify sequence matches fresh instance
        const fresh = new SeededRandom(s2);
        expect(rng.next()).toBe(fresh.next());
      },
    );
  });

  describe("MULBERRY32 SPECIFIC", () => {
    test.prop([positiveSeed])(
      "mulberry32 produces non-zero after reasonable iterations",
      (s) => {
        const rng = new SeededRandom(s);
        let hasNonZero = false;
        
        for (let i = 0; i < 100; i++) {
          if (rng.next() > 0.001) {
            hasNonZero = true;
            break;
          }
        }
        
        expect(hasNonZero).toBe(true);
      },
    );

    test.prop([seed])(
      "state advances on each call",
      (s) => {
        const rng = new SeededRandom(s);
        const states: number[] = [];
        
        for (let i = 0; i < 10; i++) {
          states.push(rng.getState());
          rng.next();
        }
        
        // All states should be unique
        const unique = new Set(states);
        expect(unique.size).toBe(10);
      },
    );
  });

  describe("PURITY AND ISOLATION", () => {
    test.prop([seed, seed])(
      "instances do not affect each other",
      (s1, s2) => {
        const rng1 = new SeededRandom(s1);
        const rng2 = new SeededRandom(s2);
        
        const first1 = rng1.next();
        const first2 = rng2.next();
        
        // Advance rng1 many times
        for (let i = 0; i < 1000; i++) {
          rng1.next();
        }
        
        // rng2's next value should be independent
        const rng2Fresh = new SeededRandom(s2);
        rng2Fresh.next(); // consume first
        expect(rng2.next()).toBe(rng2Fresh.next());
      },
    );
  });
});
