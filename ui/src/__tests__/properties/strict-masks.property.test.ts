/**
 * STRICT Property Tests for Mask Generator
 * 
 * Tests the invariants that must hold for mask generation:
 * 1. Determinism: same seed = same mask
 * 2. Bounds: mask values are 0 or 255 (binary)
 * 3. Area: mask area is within specified range
 * 4. Dimensions: output matches input dimensions
 * 
 * TOLERANCE: STRICT - Mask bugs cause visible compositing errors
 */

import { describe, it, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  generateMask,
  type MaskGeneratorOptions,
  type MaskShapeType,
} from '@/services/maskGenerator';

// ============================================================================
// TEST DATA GENERATORS
// ============================================================================

const arbitraryShapeType = (): fc.Arbitrary<MaskShapeType> =>
  fc.constantFrom('ellipse', 'superellipse', 'fourier', 'concavePolygon', 'centeredRectangle');

const arbitraryMaskOptions = (): fc.Arbitrary<MaskGeneratorOptions> =>
  fc.record({
    width: fc.integer({ min: 16, max: 256 }),
    height: fc.integer({ min: 16, max: 256 }),
    areaRatioRange: fc.tuple(
      fc.double({ min: 0.05, max: 0.4, noNaN: true, noDefaultInfinity: true }),
      fc.double({ min: 0.4, max: 0.8, noNaN: true, noDefaultInfinity: true })
    ),
    shapeTypes: fc.array(arbitraryShapeType(), { minLength: 1, maxLength: 5 }),
    seed: fc.integer({ min: 0, max: 1000000 }),
  });

// ============================================================================
// STRICT DETERMINISM TESTS
// ============================================================================

describe('STRICT: Mask Determinism', () => {
  test.prop([
    fc.integer({ min: 32, max: 128 }),
    fc.integer({ min: 32, max: 128 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('same seed produces identical masks', (width, height, seed) => {
    const options: MaskGeneratorOptions = {
      width,
      height,
      seed,
      areaRatioRange: [0.1, 0.5],
    };
    
    const mask1 = generateMask(options);
    const mask2 = generateMask(options);
    
    // Masks should be identical
    expect(mask1.length).toBe(mask2.length);
    
    for (let i = 0; i < mask1.length; i++) {
      expect(mask1[i]).toBe(mask2[i]);
    }
  });

  test.prop([
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 0, max: 1000000 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('different seeds produce different masks', (width, height, seed1, seed2) => {
    fc.pre(seed1 !== seed2);
    
    const mask1 = generateMask({ width, height, seed: seed1, areaRatioRange: [0.1, 0.5] });
    const mask2 = generateMask({ width, height, seed: seed2, areaRatioRange: [0.1, 0.5] });
    
    // At least one pixel should differ
    let allSame = true;
    for (let i = 0; i < mask1.length; i++) {
      if (mask1[i] !== mask2[i]) {
        allSame = false;
        break;
      }
    }
    
    expect(allSame).toBe(false);
  });

  test.prop([
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('mask generation is pure (no side effects)', (width, height, seed) => {
    const options: MaskGeneratorOptions = { width, height, seed, areaRatioRange: [0.2, 0.6] };
    
    // Generate multiple times
    const results: Uint8Array[] = [];
    for (let i = 0; i < 3; i++) {
      results.push(generateMask(options));
    }
    
    // All should be identical
    for (let i = 1; i < results.length; i++) {
      for (let j = 0; j < results[0].length; j++) {
        expect(results[i][j]).toBe(results[0][j]);
      }
    }
  });
});

// ============================================================================
// STRICT BOUNDS TESTS
// ============================================================================

describe('STRICT: Mask Bounds', () => {
  test.prop([
    fc.integer({ min: 16, max: 128 }),
    fc.integer({ min: 16, max: 128 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('mask values are binary (0 or 255)', (width, height, seed) => {
    const mask = generateMask({ width, height, seed, areaRatioRange: [0.1, 0.5] });
    
    for (let i = 0; i < mask.length; i++) {
      expect(mask[i] === 0 || mask[i] === 255).toBe(true);
    }
  });

  test.prop([
    fc.integer({ min: 16, max: 128 }),
    fc.integer({ min: 16, max: 128 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('mask dimensions match input', (width, height, seed) => {
    const mask = generateMask({ width, height, seed, areaRatioRange: [0.1, 0.5] });
    
    expect(mask.length).toBe(width * height);
  });

  test.prop([
    fc.integer({ min: 32, max: 128 }),
    fc.integer({ min: 32, max: 128 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('mask is not all zeros', (width, height, seed) => {
    const mask = generateMask({ width, height, seed, areaRatioRange: [0.1, 0.5] });
    
    // At least some pixels should be 255
    let hasWhite = false;
    for (let i = 0; i < mask.length; i++) {
      if (mask[i] === 255) {
        hasWhite = true;
        break;
      }
    }
    
    expect(hasWhite).toBe(true);
  });

  test.prop([
    fc.integer({ min: 32, max: 128 }),
    fc.integer({ min: 32, max: 128 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('mask is not all ones', (width, height, seed) => {
    const mask = generateMask({ width, height, seed, areaRatioRange: [0.1, 0.5] });
    
    // At least some pixels should be 0
    let hasBlack = false;
    for (let i = 0; i < mask.length; i++) {
      if (mask[i] === 0) {
        hasBlack = true;
        break;
      }
    }
    
    expect(hasBlack).toBe(true);
  });
});

// ============================================================================
// STRICT AREA TESTS
// ============================================================================

describe('STRICT: Mask Area', () => {
  test.prop([
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 32, max: 64 }),
    fc.integer({ min: 0, max: 1000000 }),
    fc.double({ min: 0.05, max: 0.3, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 0.5, max: 0.8, noNaN: true, noDefaultInfinity: true })
  ])('mask area is within specified range', (width, height, seed, areaLo, areaHi) => {
    const mask = generateMask({
      width,
      height,
      seed,
      areaRatioRange: [areaLo, areaHi],
    });
    
    // Count white pixels
    let whiteCount = 0;
    for (let i = 0; i < mask.length; i++) {
      if (mask[i] === 255) whiteCount++;
    }
    
    const totalPixels = width * height;
    const areaRatio = whiteCount / totalPixels;
    
    // Allow some tolerance due to shape constraints
    const tolerance = 0.1;
    expect(areaRatio).toBeGreaterThanOrEqual(areaLo - tolerance);
    expect(areaRatio).toBeLessThanOrEqual(areaHi + tolerance);
  });
});

// ============================================================================
// STRICT SHAPE TYPE TESTS
// ============================================================================

describe('STRICT: Shape Types', () => {
  const shapeTypes: MaskShapeType[] = [
    'ellipse',
    'superellipse',
    'fourier',
    'concavePolygon',
    'centeredRectangle',
  ];

  for (const shapeType of shapeTypes) {
    test.prop([
      fc.integer({ min: 32, max: 64 }),
      fc.integer({ min: 32, max: 64 }),
      fc.integer({ min: 0, max: 1000000 })
    ])(`${shapeType} produces valid mask`, (width, height, seed) => {
      const mask = generateMask({
        width,
        height,
        seed,
        shapeTypes: [shapeType],
        areaRatioRange: [0.1, 0.5],
      });
      
      // Should produce valid output
      expect(mask.length).toBe(width * height);
      
      // Should have some content
      let whiteCount = 0;
      for (let i = 0; i < mask.length; i++) {
        if (mask[i] === 255) whiteCount++;
      }
      
      expect(whiteCount).toBeGreaterThan(0);
    });
  }
});

// ============================================================================
// STRICT RNG TESTS
// ============================================================================

describe('STRICT: Mask RNG', () => {
  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('seed 0 produces valid mask', (unusedSeed) => {
    // Test specifically with seed 0
    const mask = generateMask({
      width: 64,
      height: 64,
      seed: 0,
      areaRatioRange: [0.1, 0.5],
    });
    
    // Should still produce valid output
    expect(mask.length).toBe(64 * 64);
    
    let whiteCount = 0;
    for (let i = 0; i < mask.length; i++) {
      if (mask[i] === 255) whiteCount++;
    }
    
    expect(whiteCount).toBeGreaterThan(0);
  });

  test.prop([
    fc.integer({ min: 0, max: 1000000 })
  ])('large seed values work correctly', (seed) => {
    const largeSeed = seed + 2147483647; // Near max int32
    
    const mask = generateMask({
      width: 32,
      height: 32,
      seed: largeSeed,
      areaRatioRange: [0.1, 0.5],
    });
    
    expect(mask.length).toBe(32 * 32);
    
    // Check it's not all zeros
    let hasWhite = false;
    for (let i = 0; i < mask.length; i++) {
      if (mask[i] === 255) {
        hasWhite = true;
        break;
      }
    }
    
    expect(hasWhite).toBe(true);
  });
});

// ============================================================================
// STRESS TESTS
// ============================================================================

describe('STRESS: Mask Generator Under Load', () => {
  test.prop([
    fc.array(fc.integer({ min: 0, max: 1000000 }), { minLength: 20, maxLength: 50 })
  ])('multiple masks with different seeds', (seeds) => {
    const uniqueMasks = new Set<string>();
    
    for (const seed of seeds) {
      const mask = generateMask({
        width: 32,
        height: 32,
        seed,
        areaRatioRange: [0.1, 0.5],
      });
      
      // Create a hash of the mask
      let hash = 0;
      for (let i = 0; i < mask.length; i++) {
        hash = ((hash << 5) - hash + mask[i]) | 0;
      }
      
      uniqueMasks.add(hash.toString());
    }
    
    // Most masks should be unique (allowing for some collisions)
    expect(uniqueMasks.size).toBeGreaterThan(seeds.length * 0.8);
  });

  test.prop([
    fc.integer({ min: 128, max: 512 }),
    fc.integer({ min: 128, max: 512 }),
    fc.integer({ min: 0, max: 1000000 })
  ])('large masks are handled correctly', (width, height, seed) => {
    const mask = generateMask({
      width,
      height,
      seed,
      areaRatioRange: [0.1, 0.5],
    });
    
    expect(mask.length).toBe(width * height);
    
    // All values should be valid
    for (let i = 0; i < mask.length; i++) {
      expect(mask[i] === 0 || mask[i] === 255).toBe(true);
    }
  });
});
