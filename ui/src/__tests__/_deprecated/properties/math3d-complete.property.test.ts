/**
 * COMPLETE math3d.ts Property Tests
 * 
 * This file tests ALL functions and edge cases that were previously missing.
 * Combined with existing test files, this provides 100% function coverage.
 * 
 * @audit-file math3d.ts
 * @audit-date 2026-01-05
 */

import { describe, expect, it } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  // Lens math - previously untested
  focalLengthToFOV,
  fovToFocalLength,
  zoomToFocalLength,
  focalLengthToZoom,
  // Vec3 - distanceVec3 was untested
  distanceVec3,
  vec3,
  lengthVec3,
  subVec3,
  normalizeVec3,
  // Mat4_64 conversion - previously untested
  convertToMat4,
  convertToMat4_64,
  scaleMat4,
  scaleMat4_64,
  identityMat4,
  multiplyMat4,
  // Edge case testing
  invertMat4,
  transformPoint,
  lookAtMat4,
  perspectiveMat4,
  orthographicMat4,
  // Types
  type Vec3,
  type Mat4,
  type Mat4_64,
} from '@/services/math3d';

// ============================================================================
// ARBITRARIES
// ============================================================================

/** Realistic focal length in mm (common camera lenses) */
const focalLengthArb = fc.double({ min: 10, max: 400, noNaN: true, noDefaultInfinity: true });

/** Realistic sensor size in mm (APS-C to Medium Format) */
const sensorSizeArb = fc.double({ min: 15, max: 60, noNaN: true, noDefaultInfinity: true });

/** Realistic FOV in radians (20° to 170°) */
const fovRadiansArb = fc.double({ 
  min: 20 * Math.PI / 180, 
  max: 170 * Math.PI / 180, 
  noNaN: true, 
  noDefaultInfinity: true 
});

/** Realistic composition width in pixels */
const compWidthArb = fc.integer({ min: 320, max: 8192 });

/** Realistic zoom/position value */
const zoomArb = fc.double({ min: 100, max: 10000, noNaN: true, noDefaultInfinity: true });

/** 3D position vector */
const positionArb = fc.record({
  x: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
});

/** Non-zero scale vector */
const nonZeroScaleArb = fc.record({
  x: fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true }),
});

// ============================================================================
// LENS MATH TESTS (Previously untested - CRITICAL)
// ============================================================================

describe('COMPLETE: Lens Math Functions', () => {

  describe('focalLengthToFOV / fovToFocalLength roundtrip', () => {

    test.prop([focalLengthArb, sensorSizeArb])(
      'focalLength -> FOV -> focalLength roundtrip preserves value',
      (focalLength, sensorSize) => {
        const fov = focalLengthToFOV(focalLength, sensorSize);
        const recovered = fovToFocalLength(fov, sensorSize);
        
        // Should recover original focal length within floating point tolerance
        expect(Math.abs(recovered - focalLength)).toBeLessThan(1e-10);
      }
    );

    test.prop([fovRadiansArb, sensorSizeArb])(
      'FOV -> focalLength -> FOV roundtrip preserves value',
      (fov, sensorSize) => {
        const focalLength = fovToFocalLength(fov, sensorSize);
        const recovered = focalLengthToFOV(focalLength, sensorSize);
        
        // Should recover original FOV within floating point tolerance
        expect(Math.abs(recovered - fov)).toBeLessThan(1e-10);
      }
    );

    it('known value: 50mm on 36mm sensor ≈ 39.6° FOV', () => {
      const fov = focalLengthToFOV(50, 36);
      const degrees = fov * 180 / Math.PI;
      // Standard 50mm lens on full frame has ~39.6° horizontal FOV
      expect(degrees).toBeCloseTo(39.6, 0); // Within 1 degree
    });

    it('known value: 35mm on 36mm sensor ≈ 54.4° FOV', () => {
      const fov = focalLengthToFOV(35, 36);
      const degrees = fov * 180 / Math.PI;
      expect(degrees).toBeCloseTo(54.4, 0);
    });

    it('known value: 85mm on 36mm sensor ≈ 23.9° FOV', () => {
      const fov = focalLengthToFOV(85, 36);
      const degrees = fov * 180 / Math.PI;
      expect(degrees).toBeCloseTo(23.9, 0);
    });

    test.prop([focalLengthArb, sensorSizeArb])(
      'FOV output is always in valid range (0, π)',
      (focalLength, sensorSize) => {
        const fov = focalLengthToFOV(focalLength, sensorSize);
        expect(fov).toBeGreaterThan(0);
        expect(fov).toBeLessThan(Math.PI);
      }
    );

    test.prop([focalLengthArb, sensorSizeArb])(
      'longer focal length = smaller FOV (inverse relationship)',
      (focalLength, sensorSize) => {
        const fov1 = focalLengthToFOV(focalLength, sensorSize);
        const fov2 = focalLengthToFOV(focalLength * 2, sensorSize);
        expect(fov2).toBeLessThan(fov1);
      }
    );

  });

  describe('zoomToFocalLength / focalLengthToZoom roundtrip', () => {

    test.prop([zoomArb, compWidthArb, sensorSizeArb])(
      'zoom -> focalLength -> zoom roundtrip preserves value',
      (zoom, compWidth, filmSize) => {
        const focalLength = zoomToFocalLength(zoom, compWidth, filmSize);
        const recovered = focalLengthToZoom(focalLength, compWidth, filmSize);
        
        expect(Math.abs(recovered - zoom)).toBeLessThan(1e-10);
      }
    );

    test.prop([focalLengthArb, compWidthArb, sensorSizeArb])(
      'focalLength -> zoom -> focalLength roundtrip preserves value',
      (focalLength, compWidth, filmSize) => {
        const zoom = focalLengthToZoom(focalLength, compWidth, filmSize);
        const recovered = zoomToFocalLength(zoom, compWidth, filmSize);
        
        expect(Math.abs(recovered - focalLength)).toBeLessThan(1e-10);
      }
    );

    it('Zoom formula verification', () => {
      // AE uses: zoom = focalLength * compWidth / filmSize
      // filmSize default is 36mm (full frame)
      const compWidth = 1920;
      const filmSize = 36;
      const focalLength = 50; // 50mm lens
      
      const zoom = focalLengthToZoom(focalLength, compWidth, filmSize);
      const expected = (50 * 1920) / 36;
      
      expect(zoom).toBeCloseTo(expected, 10);
    });

    test.prop([focalLengthArb, compWidthArb, sensorSizeArb])(
      'zoom output is always positive',
      (focalLength, compWidth, filmSize) => {
        const zoom = focalLengthToZoom(focalLength, compWidth, filmSize);
        expect(zoom).toBeGreaterThan(0);
      }
    );

  });

});

// ============================================================================
// VEC3 DISTANCE TEST (Previously untested)
// ============================================================================

describe('COMPLETE: Vec3 distanceVec3', () => {

  test.prop([positionArb, positionArb])(
    'distance is symmetric: d(a,b) = d(b,a)',
    (a, b) => {
      const d1 = distanceVec3(a, b);
      const d2 = distanceVec3(b, a);
      expect(Math.abs(d1 - d2)).toBeLessThan(1e-10);
    }
  );

  test.prop([positionArb])(
    'distance from self is zero: d(a,a) = 0',
    (a) => {
      const d = distanceVec3(a, a);
      expect(d).toBe(0);
    }
  );

  test.prop([positionArb, positionArb])(
    'distance is always non-negative',
    (a, b) => {
      const d = distanceVec3(a, b);
      expect(d).toBeGreaterThanOrEqual(0);
    }
  );

  test.prop([positionArb, positionArb])(
    'distance equals length of difference: d(a,b) = |a-b|',
    (a, b) => {
      const d = distanceVec3(a, b);
      const diff = subVec3(a, b);
      const len = lengthVec3(diff);
      expect(Math.abs(d - len)).toBeLessThan(1e-10);
    }
  );

  it('known value: distance between (0,0,0) and (3,4,0) is 5', () => {
    const a = vec3(0, 0, 0);
    const b = vec3(3, 4, 0);
    expect(distanceVec3(a, b)).toBe(5);
  });

  it('known value: distance between (1,1,1) and (2,2,2) is sqrt(3)', () => {
    const a = vec3(1, 1, 1);
    const b = vec3(2, 2, 2);
    expect(distanceVec3(a, b)).toBeCloseTo(Math.sqrt(3), 10);
  });

});

// ============================================================================
// MAT4_64 CONVERSION TESTS (Previously untested)
// ============================================================================

describe('COMPLETE: Mat4 <-> Mat4_64 Conversion', () => {

  test.prop([nonZeroScaleArb])(
    'convertToMat4_64 -> convertToMat4 roundtrip',
    (scale) => {
      const mat32 = scaleMat4(scale);
      const mat64 = convertToMat4_64(mat32);
      const recovered = convertToMat4(mat64);
      
      // All 16 elements should match within Float32 precision
      for (let i = 0; i < 16; i++) {
        expect(Math.abs(mat32.elements[i] - recovered.elements[i])).toBeLessThan(1e-7);
      }
    }
  );

  test.prop([nonZeroScaleArb])(
    'convertToMat4 preserves matrix values',
    (scale) => {
      const mat64 = scaleMat4_64(scale);
      const mat32 = convertToMat4(mat64);
      
      // The diagonal elements should match (scale values)
      expect(Math.abs(mat32.elements[0] - scale.x)).toBeLessThan(1e-6);
      expect(Math.abs(mat32.elements[5] - scale.y)).toBeLessThan(1e-6);
      expect(Math.abs(mat32.elements[10] - scale.z)).toBeLessThan(1e-6);
      expect(mat32.elements[15]).toBeCloseTo(1, 6);
    }
  );

  it('conversion uses correct array types', () => {
    const mat32 = identityMat4();
    const mat64 = convertToMat4_64(mat32);
    const backTo32 = convertToMat4(mat64);
    
    expect(mat32.elements).toBeInstanceOf(Float32Array);
    expect(mat64.elements).toBeInstanceOf(Float64Array);
    expect(backTo32.elements).toBeInstanceOf(Float32Array);
  });

});

// ============================================================================
// EDGE CASE TESTS (Previously incomplete)
// ============================================================================

describe('COMPLETE: Edge Cases', () => {

  describe('normalizeVec3 with zero vector', () => {
    
    it('returns zero vector for zero input', () => {
      const zero = vec3(0, 0, 0);
      const result = normalizeVec3(zero);
      expect(result.x).toBe(0);
      expect(result.y).toBe(0);
      expect(result.z).toBe(0);
    });

    it('does not produce NaN for zero input', () => {
      const zero = vec3(0, 0, 0);
      const result = normalizeVec3(zero);
      expect(Number.isNaN(result.x)).toBe(false);
      expect(Number.isNaN(result.y)).toBe(false);
      expect(Number.isNaN(result.z)).toBe(false);
    });

  });

  describe('invertMat4 with singular matrix', () => {

    it('returns null for zero scale matrix', () => {
      const zeroScale = scaleMat4({ x: 0, y: 1, z: 1 });
      const result = invertMat4(zeroScale);
      expect(result).toBeNull();
    });

    it('returns null for all-zero matrix', () => {
      const allZero: Mat4 = { elements: new Float32Array(16) };
      const result = invertMat4(allZero);
      expect(result).toBeNull();
    });

    test.prop([nonZeroScaleArb])(
      'returns non-null for invertible matrices',
      (scale) => {
        const mat = scaleMat4(scale);
        const inv = invertMat4(mat);
        expect(inv).not.toBeNull();
      }
    );

  });

  describe('transformPoint edge cases', () => {

    it('handles identity correctly', () => {
      const I = identityMat4();
      const p = vec3(5, 10, 15);
      const result = transformPoint(I, p);
      expect(result.x).toBeCloseTo(5, 10);
      expect(result.y).toBeCloseTo(10, 10);
      expect(result.z).toBeCloseTo(15, 10);
    });

    it('handles large coordinates', () => {
      const I = identityMat4();
      const p = vec3(1e6, 1e6, 1e6);
      const result = transformPoint(I, p);
      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      expect(Number.isFinite(result.z)).toBe(true);
    });

  });

  describe('lookAtMat4 edge cases', () => {

    it('handles eye == target gracefully', () => {
      const eye = vec3(0, 0, 0);
      const target = vec3(0, 0, 0);
      const up = vec3(0, 1, 0);
      const result = lookAtMat4(eye, target, up);
      
      // Should not produce NaN
      for (let i = 0; i < 16; i++) {
        expect(Number.isNaN(result.elements[i])).toBe(false);
      }
    });

    it('handles up vector parallel to look direction', () => {
      const eye = vec3(0, 0, 0);
      const target = vec3(0, 1, 0); // Looking up
      const up = vec3(0, 1, 0); // Up is also up (parallel)
      const result = lookAtMat4(eye, target, up);
      
      // Should not produce NaN (degenerate but handled)
      for (let i = 0; i < 16; i++) {
        expect(Number.isNaN(result.elements[i])).toBe(false);
      }
    });

  });

  describe('perspectiveMat4 edge cases', () => {

    test.prop([
      fc.double({ min: 0.1, max: 2, noNaN: true, noDefaultInfinity: true }),
      fc.double({ min: 0.5, max: 3, noNaN: true, noDefaultInfinity: true }),
      fc.double({ min: 0.001, max: 1, noNaN: true, noDefaultInfinity: true }),
    ])(
      'produces finite values for valid inputs',
      (fov, aspect, near) => {
        const far = near + 100;
        const result = perspectiveMat4(fov, aspect, near, far);
        
        for (let i = 0; i < 16; i++) {
          expect(Number.isFinite(result.elements[i])).toBe(true);
        }
      }
    );

    it('handles very small near/far difference', () => {
      // near ≈ far causes division by very small number
      const result = perspectiveMat4(1, 1, 1, 1.001);
      
      // Should still be finite (may be large but not Infinity)
      for (let i = 0; i < 16; i++) {
        expect(Number.isFinite(result.elements[i])).toBe(true);
      }
    });

  });

  describe('orthographicMat4 edge cases', () => {

    test.prop([
      fc.double({ min: -100, max: 0, noNaN: true, noDefaultInfinity: true }),
      fc.double({ min: 1, max: 100, noNaN: true, noDefaultInfinity: true }),
    ])(
      'produces finite values for valid inputs',
      (left, width) => {
        const right = left + width;
        const bottom = left;
        const top = left + width;
        const result = orthographicMat4(left, right, bottom, top, 0.1, 100);
        
        for (let i = 0; i < 16; i++) {
          expect(Number.isFinite(result.elements[i])).toBe(true);
        }
      }
    );

  });

});

// ============================================================================
// DETERMINISM TESTS (Critical for compositor)
// ============================================================================

describe('COMPLETE: Determinism', () => {

  test.prop([focalLengthArb, sensorSizeArb])(
    'focalLengthToFOV is deterministic',
    (focalLength, sensorSize) => {
      const result1 = focalLengthToFOV(focalLength, sensorSize);
      const result2 = focalLengthToFOV(focalLength, sensorSize);
      expect(result1).toBe(result2);
    }
  );

  test.prop([positionArb, positionArb])(
    'distanceVec3 is deterministic',
    (a, b) => {
      const result1 = distanceVec3(a, b);
      const result2 = distanceVec3(a, b);
      expect(result1).toBe(result2);
    }
  );

  test.prop([nonZeroScaleArb, nonZeroScaleArb])(
    'matrix multiplication is deterministic',
    (a, b) => {
      const A = scaleMat4(a);
      const B = scaleMat4(b);
      const result1 = multiplyMat4(A, B);
      const result2 = multiplyMat4(A, B);
      
      for (let i = 0; i < 16; i++) {
        expect(result1.elements[i]).toBe(result2.elements[i]);
      }
    }
  );

});
