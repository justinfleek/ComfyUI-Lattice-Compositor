/**
 * STRICT SeededRandom Property Tests
 * 
 * Created: Fresh audit - do NOT trust old tests
 * 
 * Tests EVERY edge case in SeededRandom.ts:
 * - Determinism (same seed = same sequence)
 * - State checkpointing
 * - Reset behavior
 * - Range methods
 * - Distribution quality
 */

import { describe, expect, beforeEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import { SeededRandom } from '@/services/particles/SeededRandom';

describe('STRICT: SeededRandom', () => {

  // =========================================================================
  // DETERMINISM - MOST CRITICAL
  // =========================================================================

  describe('determinism', () => {

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'STRICT: same seed produces identical sequence (1000 numbers)',
      (seed) => {
        const rng1 = new SeededRandom(seed);
        const rng2 = new SeededRandom(seed);

        for (let i = 0; i < 1000; i++) {
          const v1 = rng1.next();
          const v2 = rng2.next();
          expect(v1).toBe(v2);
        }
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'STRICT: reset returns to initial sequence',
      (seed) => {
        const rng = new SeededRandom(seed);
        
        // Generate some numbers
        const firstSequence: number[] = [];
        for (let i = 0; i < 100; i++) {
          firstSequence.push(rng.next());
        }

        // Reset
        rng.reset();

        // Should produce identical sequence
        for (let i = 0; i < 100; i++) {
          expect(rng.next()).toBe(firstSequence[i]);
        }
      }
    );

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.integer({ min: 0, max: 2147483647 }),
    ])(
      'STRICT: different seeds produce different sequences',
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
      }
    );
  });

  // =========================================================================
  // STATE CHECKPOINTING
  // =========================================================================

  describe('state checkpointing', () => {

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.integer({ min: 1, max: 500 }),
    ])(
      'STRICT: getState/setState allows resuming sequence',
      (seed, stepsBeforeCheckpoint) => {
        const rng = new SeededRandom(seed);

        // Advance some steps
        for (let i = 0; i < stepsBeforeCheckpoint; i++) {
          rng.next();
        }

        // Checkpoint
        const state = rng.getState();

        // Generate more numbers
        const nextSequence: number[] = [];
        for (let i = 0; i < 100; i++) {
          nextSequence.push(rng.next());
        }

        // Restore checkpoint
        rng.setState(state);

        // Should produce identical sequence from checkpoint
        for (let i = 0; i < 100; i++) {
          expect(rng.next()).toBe(nextSequence[i]);
        }
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'getSeed returns initial seed',
      (seed) => {
        const rng = new SeededRandom(seed);
        expect(rng.getSeed()).toBe(seed);
        
        // Even after generating numbers
        for (let i = 0; i < 100; i++) rng.next();
        expect(rng.getSeed()).toBe(seed);
      }
    );

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.integer({ min: 0, max: 2147483647 }),
    ])(
      'setSeed changes both seed and resets state',
      (seed1, seed2) => {
        const rng = new SeededRandom(seed1);
        
        // Generate some numbers
        for (let i = 0; i < 50; i++) rng.next();
        
        // Set new seed
        rng.setSeed(seed2);
        
        // Should have new seed
        expect(rng.getSeed()).toBe(seed2);
        
        // Should produce same sequence as fresh instance with seed2
        const fresh = new SeededRandom(seed2);
        for (let i = 0; i < 100; i++) {
          expect(rng.next()).toBe(fresh.next());
        }
      }
    );
  });

  // =========================================================================
  // NEXT() OUTPUT RANGE
  // =========================================================================

  describe('next() output', () => {

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'STRICT: next() always returns [0, 1)',
      (seed) => {
        const rng = new SeededRandom(seed);
        
        // Reduced from 10000 to 1000 to avoid timeout
        for (let i = 0; i < 1000; i++) {
          const value = rng.next();
          expect(value).toBeGreaterThanOrEqual(0);
          expect(value).toBeLessThan(1);
        }
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'next() is never NaN or Infinity',
      (seed) => {
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const value = rng.next();
          expect(Number.isFinite(value)).toBe(true);
          expect(Number.isNaN(value)).toBe(false);
        }
      }
    );
  });

  // =========================================================================
  // RANGE METHODS
  // =========================================================================

  describe('range methods', () => {

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.double({ min: -1e6, max: 1e6, noNaN: true }),
      fc.double({ min: 1, max: 1e6, noNaN: true }),
    ])(
      'STRICT: range(min, max) returns values in [min, max]',
      (seed, min, delta) => {
        const max = min + delta;
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const value = rng.range(min, max);
          expect(value).toBeGreaterThanOrEqual(min);
          expect(value).toBeLessThanOrEqual(max);
        }
      }
    );

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.integer({ min: -1000, max: 1000 }),
      fc.integer({ min: 1, max: 100 }),
    ])(
      'STRICT: int(min, max) returns integers in [min, max]',
      (seed, min, delta) => {
        const max = min + delta;
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const value = rng.int(min, max);
          expect(Number.isInteger(value)).toBe(true);
          expect(value).toBeGreaterThanOrEqual(min);
          expect(value).toBeLessThanOrEqual(max);
        }
      }
    );

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.double({ min: -1000, max: 1000, noNaN: true }),
      fc.double({ min: 0, max: 100, noNaN: true }),
    ])(
      'STRICT: variance(base, v) returns values in [base-v, base+v]',
      (seed, base, variance) => {
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const value = rng.variance(base, variance);
          expect(value).toBeGreaterThanOrEqual(base - variance);
          expect(value).toBeLessThanOrEqual(base + variance);
        }
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'STRICT: angle() returns values in [0, 2*PI)',
      (seed) => {
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const value = rng.angle();
          expect(value).toBeGreaterThanOrEqual(0);
          expect(value).toBeLessThan(Math.PI * 2);
        }
      }
    );
  });

  // =========================================================================
  // BOOLEAN METHOD
  // =========================================================================

  describe('bool method', () => {

    test('bool(0) always returns false', () => {
      const rng = new SeededRandom(12345);
      for (let i = 0; i < 100; i++) {
        expect(rng.bool(0)).toBe(false);
      }
    });

    test('bool(1) always returns true', () => {
      const rng = new SeededRandom(12345);
      for (let i = 0; i < 100; i++) {
        expect(rng.bool(1)).toBe(true);
      }
    });

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.double({ min: 0.3, max: 0.7, noNaN: true }),
    ])(
      'bool(p) produces roughly p probability',
      (seed, probability) => {
        const rng = new SeededRandom(seed);
        let trueCount = 0;
        const trials = 10000;
        
        for (let i = 0; i < trials; i++) {
          if (rng.bool(probability)) trueCount++;
        }
        
        const observedProbability = trueCount / trials;
        // Allow 5% deviation from expected probability
        expect(Math.abs(observedProbability - probability)).toBeLessThan(0.05);
      }
    );
  });

  // =========================================================================
  // GEOMETRIC METHODS
  // =========================================================================

  describe('geometric methods', () => {

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'STRICT: inCircle() returns points within unit circle',
      (seed) => {
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const { x, y } = rng.inCircle();
          const distSq = x * x + y * y;
          expect(distSq).toBeLessThanOrEqual(1 + 1e-10); // Unit circle
        }
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'STRICT: onSphere() returns points on unit sphere',
      (seed) => {
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const { x, y, z } = rng.onSphere();
          const dist = Math.sqrt(x * x + y * y + z * z);
          expect(dist).toBeCloseTo(1, 10); // Should be exactly on unit sphere
        }
      }
    );
  });

  // =========================================================================
  // DISTRIBUTION QUALITY
  // =========================================================================

  describe('distribution quality', () => {

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'next() has reasonable mean (~0.5)',
      (seed) => {
        const rng = new SeededRandom(seed);
        let sum = 0;
        const count = 10000;
        
        for (let i = 0; i < count; i++) {
          sum += rng.next();
        }
        
        const mean = sum / count;
        // Mean should be close to 0.5 (within 2%)
        expect(Math.abs(mean - 0.5)).toBeLessThan(0.02);
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'int() covers full range evenly',
      (seed) => {
        const rng = new SeededRandom(seed);
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
      }
    );
  });

  // =========================================================================
  // GAUSSIAN METHOD
  // =========================================================================

  describe('gaussian method', () => {

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'gaussian(0, 1) produces values centered around 0',
      (seed) => {
        const rng = new SeededRandom(seed);
        let sum = 0;
        const count = 1000;
        
        for (let i = 0; i < count; i++) {
          sum += rng.gaussian();
        }
        
        const mean = sum / count;
        // Mean should be close to 0 (within 0.2 for 1000 samples)
        expect(Math.abs(mean)).toBeLessThan(0.2);
      }
    );

    test.prop([
      fc.integer({ min: 0, max: 2147483647 }),
      fc.double({ min: -100, max: 100, noNaN: true }),
    ])(
      'gaussian(mean, 1) produces values centered around mean',
      (seed, mean) => {
        const rng = new SeededRandom(seed);
        let sum = 0;
        const count = 1000;
        
        for (let i = 0; i < count; i++) {
          sum += rng.gaussian(mean, 1);
        }
        
        const observedMean = sum / count;
        expect(Math.abs(observedMean - mean)).toBeLessThan(0.2);
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'gaussian() never returns NaN or Infinity',
      (seed) => {
        const rng = new SeededRandom(seed);
        
        for (let i = 0; i < 1000; i++) {
          const value = rng.gaussian();
          expect(Number.isFinite(value)).toBe(true);
          expect(Number.isNaN(value)).toBe(false);
        }
      }
    );

    test.prop([fc.integer({ min: 0, max: 2147483647 })])(
      'gaussian() is deterministic (same seed = same sequence)',
      (seed) => {
        const rng1 = new SeededRandom(seed);
        const rng2 = new SeededRandom(seed);
        
        for (let i = 0; i < 100; i++) {
          expect(rng1.gaussian()).toBe(rng2.gaussian());
        }
      }
    );
  });

  // =========================================================================
  // EDGE CASES
  // =========================================================================

  describe('edge cases', () => {

    test('handles seed = 0', () => {
      const rng = new SeededRandom(0);
      const values: number[] = [];
      for (let i = 0; i < 100; i++) {
        const v = rng.next();
        expect(Number.isFinite(v)).toBe(true);
        values.push(v);
      }
      // Should not be all zeros
      expect(values.some(v => v !== 0)).toBe(true);
    });

    test('handles negative seed', () => {
      const rng = new SeededRandom(-12345);
      for (let i = 0; i < 100; i++) {
        const v = rng.next();
        expect(v).toBeGreaterThanOrEqual(0);
        expect(v).toBeLessThan(1);
      }
    });

    test('handles very large seed', () => {
      const rng = new SeededRandom(2147483647);
      for (let i = 0; i < 100; i++) {
        const v = rng.next();
        expect(v).toBeGreaterThanOrEqual(0);
        expect(v).toBeLessThan(1);
      }
    });

    test('range with min = max returns that value', () => {
      const rng = new SeededRandom(12345);
      for (let i = 0; i < 100; i++) {
        expect(rng.range(42, 42)).toBe(42);
      }
    });

    test('int with min = max returns that value', () => {
      const rng = new SeededRandom(12345);
      for (let i = 0; i < 100; i++) {
        expect(rng.int(7, 7)).toBe(7);
      }
    });

    test('variance with 0 variance returns base', () => {
      const rng = new SeededRandom(12345);
      for (let i = 0; i < 100; i++) {
        expect(rng.variance(100, 0)).toBe(100);
      }
    });
  });
});
