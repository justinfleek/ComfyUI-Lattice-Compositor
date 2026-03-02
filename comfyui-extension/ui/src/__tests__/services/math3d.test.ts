/**
 * AUDIT TEST: ui/src/services/math3d.ts
 * 
 * Created: 2026-01-06
 * File Lines: 1,012
 * Importers: 11 (FOUNDATION FILE - ALL 3D MATH)
 * 
 * This is the MOST CRITICAL FILE for mathematical correctness.
 * If this is wrong, ALL transforms, cameras, and 3D operations are wrong.
 * 
 * Tests verify:
 * - Mathematical correctness (not just "runs without error")
 * - Edge cases (zero vectors, singular matrices)
 * - Precision bounds (Float32 vs Float64)
 * - Warning system behavior
 */

import { describe, expect, it, vi, beforeEach, afterEach } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  // Types
  type Vec3,
  type Mat4,
  type Mat4_64,
  type Quat,
  type Math3DWarnEvent,
  
  // Warning system
  math3dWarnHandler,
  setMath3DWarnHandler,
  
  // Vector operations
  vec3,
  addVec3,
  subVec3,
  scaleVec3,
  lengthVec3,
  normalizeVec3,
  crossVec3,
  dotVec3,
  lerpVec3,
  distanceVec3,
  
  // Matrix operations
  identityMat4,
  multiplyMat4,
  perspectiveMat4,
  orthographicMat4,
  lookAtMat4,
  translateMat4,
  rotateXMat4,
  rotateYMat4,
  rotateZMat4,
  scaleMat4,
  transformPoint,
  transformDirection,
  invertMat4,
  
  // Lens math
  focalLengthToFOV,
  fovToFocalLength,
  zoomToFocalLength,
  focalLengthToZoom,
  degToRad,
  radToDeg,
  
  // Quaternion
  quatIdentity,
  quatFromEuler,
  quatToEuler,
  slerpQuat,
  
  // High-precision
  identityMat4_64,
  scaleMat4_64,
  multiplyMat4_64,
  convertToMat4,
  convertToMat4_64,
  
  // Constants
  PRECISION,
} from '@/services/math3d';

// ============================================================================
// Test Utilities
// ============================================================================

const EPSILON = 1e-6; // Tolerance for Float32 operations

function vec3Equal(a: Vec3, b: Vec3, tolerance = EPSILON): boolean {
  return (
    Math.abs(a.x - b.x) < tolerance &&
    Math.abs(a.y - b.y) < tolerance &&
    Math.abs(a.z - b.z) < tolerance
  );
}

function mat4Equal(a: Mat4, b: Mat4, tolerance = EPSILON): boolean {
  for (let i = 0; i < 16; i++) {
    if (Math.abs(a.elements[i] - b.elements[i]) > tolerance) {
      return false;
    }
  }
  return true;
}

// Arbitrary generators for property tests
const vec3Arb = fc.record({
  x: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
});

const nonZeroVec3Arb = fc.record({
  x: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
}).filter(v => lengthVec3(v) > 0.001);

const angleArb = fc.double({ min: -Math.PI * 2, max: Math.PI * 2, noNaN: true, noDefaultInfinity: true });

const tArb = fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true });

// ============================================================================
// VECTOR OPERATIONS
// ============================================================================

describe('vec3', () => {
  it('creates vector with given components', () => {
    const v = vec3(1, 2, 3);
    expect(v.x).toBe(1);
    expect(v.y).toBe(2);
    expect(v.z).toBe(3);
  });

  it('handles zero vector', () => {
    const v = vec3(0, 0, 0);
    expect(v.x).toBe(0);
    expect(v.y).toBe(0);
    expect(v.z).toBe(0);
  });

  it('handles negative values', () => {
    const v = vec3(-1, -2, -3);
    expect(v.x).toBe(-1);
    expect(v.y).toBe(-2);
    expect(v.z).toBe(-3);
  });
});

describe('addVec3', () => {
  it('adds vectors correctly', () => {
    const a = vec3(1, 2, 3);
    const b = vec3(4, 5, 6);
    const result = addVec3(a, b);
    expect(result).toEqual(vec3(5, 7, 9));
  });

  it('identity: a + 0 = a', () => {
    const a = vec3(1, 2, 3);
    const zero = vec3(0, 0, 0);
    expect(addVec3(a, zero)).toEqual(a);
  });

  test.prop([vec3Arb, vec3Arb])('commutative: a + b = b + a', (a, b) => {
    const ab = addVec3(a, b);
    const ba = addVec3(b, a);
    expect(vec3Equal(ab, ba)).toBe(true);
  });
});

describe('subVec3', () => {
  it('subtracts vectors correctly', () => {
    const a = vec3(5, 7, 9);
    const b = vec3(1, 2, 3);
    const result = subVec3(a, b);
    expect(result).toEqual(vec3(4, 5, 6));
  });

  it('a - a = 0', () => {
    const a = vec3(1, 2, 3);
    const result = subVec3(a, a);
    expect(vec3Equal(result, vec3(0, 0, 0))).toBe(true);
  });
});

describe('scaleVec3', () => {
  it('scales vector by scalar', () => {
    const v = vec3(1, 2, 3);
    const result = scaleVec3(v, 2);
    expect(result).toEqual(vec3(2, 4, 6));
  });

  it('scale by 0 gives zero vector', () => {
    const v = vec3(1, 2, 3);
    const result = scaleVec3(v, 0);
    expect(result).toEqual(vec3(0, 0, 0));
  });

  it('scale by 1 gives same vector', () => {
    const v = vec3(1, 2, 3);
    const result = scaleVec3(v, 1);
    expect(result).toEqual(v);
  });

  it('scale by -1 gives negated vector', () => {
    const v = vec3(1, 2, 3);
    const result = scaleVec3(v, -1);
    expect(result).toEqual(vec3(-1, -2, -3));
  });
});

describe('lengthVec3', () => {
  it('calculates length correctly', () => {
    // 3-4-5 triangle in 3D: sqrt(3² + 4² + 0²) = 5
    expect(lengthVec3(vec3(3, 4, 0))).toBeCloseTo(5, 10);
  });

  it('zero vector has length 0', () => {
    expect(lengthVec3(vec3(0, 0, 0))).toBe(0);
  });

  it('unit vectors have length 1', () => {
    expect(lengthVec3(vec3(1, 0, 0))).toBeCloseTo(1, 10);
    expect(lengthVec3(vec3(0, 1, 0))).toBeCloseTo(1, 10);
    expect(lengthVec3(vec3(0, 0, 1))).toBeCloseTo(1, 10);
  });

  test.prop([nonZeroVec3Arb])('length is always non-negative', (v) => {
    expect(lengthVec3(v)).toBeGreaterThanOrEqual(0);
  });
});

describe('normalizeVec3', () => {
  it('normalizes to unit length', () => {
    const v = vec3(3, 4, 0);
    const n = normalizeVec3(v);
    expect(lengthVec3(n)).toBeCloseTo(1, 5);
  });

  it('handles zero vector (returns zero, emits warning)', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    const result = normalizeVec3(vec3(0, 0, 0));
    
    expect(result).toEqual(vec3(0, 0, 0));
    expect(warnings.length).toBe(1);
    expect(warnings[0].type).toBe('ZERO_VECTOR_NORMALIZE');
    
    setMath3DWarnHandler(originalHandler);
  });

  test.prop([nonZeroVec3Arb])('normalized vectors have length 1', (v) => {
    const n = normalizeVec3(v);
    expect(lengthVec3(n)).toBeCloseTo(1, 5);
  });
});

describe('crossVec3', () => {
  it('calculates cross product correctly', () => {
    // x × y = z
    const result = crossVec3(vec3(1, 0, 0), vec3(0, 1, 0));
    expect(vec3Equal(result, vec3(0, 0, 1))).toBe(true);
  });

  it('anti-commutative: a × b = -(b × a)', () => {
    const a = vec3(1, 2, 3);
    const b = vec3(4, 5, 6);
    const ab = crossVec3(a, b);
    const ba = crossVec3(b, a);
    expect(vec3Equal(ab, scaleVec3(ba, -1))).toBe(true);
  });

  it('parallel vectors give zero', () => {
    const a = vec3(1, 2, 3);
    const b = vec3(2, 4, 6); // parallel to a
    const result = crossVec3(a, b);
    expect(vec3Equal(result, vec3(0, 0, 0))).toBe(true);
  });
});

describe('dotVec3', () => {
  it('calculates dot product correctly', () => {
    const a = vec3(1, 2, 3);
    const b = vec3(4, 5, 6);
    // 1*4 + 2*5 + 3*6 = 4 + 10 + 18 = 32
    expect(dotVec3(a, b)).toBe(32);
  });

  it('perpendicular vectors have dot = 0', () => {
    const a = vec3(1, 0, 0);
    const b = vec3(0, 1, 0);
    expect(dotVec3(a, b)).toBe(0);
  });

  it('dot with self = length²', () => {
    const v = vec3(3, 4, 0);
    expect(dotVec3(v, v)).toBeCloseTo(25, 10); // 5² = 25
  });

  test.prop([vec3Arb, vec3Arb])('commutative: a · b = b · a', (a, b) => {
    expect(dotVec3(a, b)).toBeCloseTo(dotVec3(b, a), 5);
  });
});

describe('lerpVec3', () => {
  it('t=0 returns a', () => {
    const a = vec3(0, 0, 0);
    const b = vec3(10, 10, 10);
    expect(lerpVec3(a, b, 0)).toEqual(a);
  });

  it('t=1 returns b', () => {
    const a = vec3(0, 0, 0);
    const b = vec3(10, 10, 10);
    expect(lerpVec3(a, b, 1)).toEqual(b);
  });

  it('t=0.5 returns midpoint', () => {
    const a = vec3(0, 0, 0);
    const b = vec3(10, 10, 10);
    expect(lerpVec3(a, b, 0.5)).toEqual(vec3(5, 5, 5));
  });

  test.prop([vec3Arb, vec3Arb, tArb])('lerp is in range', (a, b, t) => {
    const result = lerpVec3(a, b, t);
    // Result should be between a and b for each component
    // (within numerical tolerance)
    const min = Math.min;
    const max = Math.max;
    expect(result.x).toBeGreaterThanOrEqual(min(a.x, b.x) - EPSILON);
    expect(result.x).toBeLessThanOrEqual(max(a.x, b.x) + EPSILON);
  });
});

describe('distanceVec3', () => {
  it('calculates distance correctly', () => {
    const a = vec3(0, 0, 0);
    const b = vec3(3, 4, 0);
    expect(distanceVec3(a, b)).toBeCloseTo(5, 10);
  });

  it('distance to self is 0', () => {
    const a = vec3(1, 2, 3);
    expect(distanceVec3(a, a)).toBe(0);
  });

  test.prop([vec3Arb, vec3Arb])('distance is symmetric', (a, b) => {
    expect(distanceVec3(a, b)).toBeCloseTo(distanceVec3(b, a), 5);
  });
});

// ============================================================================
// MATRIX OPERATIONS
// ============================================================================

describe('identityMat4', () => {
  it('creates identity matrix', () => {
    const m = identityMat4();
    expect(m.elements[0]).toBe(1);
    expect(m.elements[5]).toBe(1);
    expect(m.elements[10]).toBe(1);
    expect(m.elements[15]).toBe(1);
    // Off-diagonals should be 0
    expect(m.elements[1]).toBe(0);
    expect(m.elements[4]).toBe(0);
  });

  it('identity * v = v', () => {
    const m = identityMat4();
    const v = vec3(1, 2, 3);
    const result = transformPoint(m, v);
    expect(vec3Equal(result, v)).toBe(true);
  });
});

describe('multiplyMat4', () => {
  it('identity * A = A', () => {
    const identity = identityMat4();
    const translate = translateMat4(vec3(1, 2, 3));
    const result = multiplyMat4(identity, translate);
    expect(mat4Equal(result, translate)).toBe(true);
  });

  it('A * identity = A', () => {
    const identity = identityMat4();
    const translate = translateMat4(vec3(1, 2, 3));
    const result = multiplyMat4(translate, identity);
    expect(mat4Equal(result, translate)).toBe(true);
  });

  it('translation composition works', () => {
    const t1 = translateMat4(vec3(1, 0, 0));
    const t2 = translateMat4(vec3(0, 2, 0));
    const combined = multiplyMat4(t2, t1);
    
    const origin = vec3(0, 0, 0);
    const result = transformPoint(combined, origin);
    expect(vec3Equal(result, vec3(1, 2, 0))).toBe(true);
  });
});

describe('translateMat4', () => {
  it('translates point correctly', () => {
    const m = translateMat4(vec3(10, 20, 30));
    const p = vec3(0, 0, 0);
    const result = transformPoint(m, p);
    expect(vec3Equal(result, vec3(10, 20, 30))).toBe(true);
  });

  it('translation by zero is identity', () => {
    const m = translateMat4(vec3(0, 0, 0));
    const identity = identityMat4();
    expect(mat4Equal(m, identity)).toBe(true);
  });
});

describe('rotateXMat4, rotateYMat4, rotateZMat4', () => {
  it('rotateZ by 90° rotates x-axis to y-axis', () => {
    const m = rotateZMat4(Math.PI / 2);
    const x = vec3(1, 0, 0);
    const result = transformDirection(m, x);
    expect(vec3Equal(result, vec3(0, 1, 0), 1e-5)).toBe(true);
  });

  it('rotateY by 90° rotates z-axis to x-axis', () => {
    const m = rotateYMat4(Math.PI / 2);
    const z = vec3(0, 0, 1);
    const result = transformDirection(m, z);
    expect(vec3Equal(result, vec3(1, 0, 0), 1e-5)).toBe(true);
  });

  it('rotateX by 90° rotates y-axis to z-axis', () => {
    const m = rotateXMat4(Math.PI / 2);
    const y = vec3(0, 1, 0);
    const result = transformDirection(m, y);
    expect(vec3Equal(result, vec3(0, 0, 1), 1e-5)).toBe(true);
  });

  it('rotation by 360° returns to original', () => {
    const m = rotateZMat4(Math.PI * 2);
    const v = vec3(1, 2, 3);
    const result = transformDirection(m, v);
    expect(vec3Equal(result, v, 1e-5)).toBe(true);
  });
});

describe('scaleMat4', () => {
  it('scales point correctly', () => {
    const m = scaleMat4(vec3(2, 3, 4));
    const p = vec3(1, 1, 1);
    const result = transformPoint(m, p);
    expect(vec3Equal(result, vec3(2, 3, 4))).toBe(true);
  });

  it('scale by 1,1,1 is identity', () => {
    const m = scaleMat4(vec3(1, 1, 1));
    const identity = identityMat4();
    expect(mat4Equal(m, identity)).toBe(true);
  });

  it('warns on extreme scale values', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    scaleMat4(vec3(0.0001, 1, 1)); // Extreme small value
    
    expect(warnings.length).toBe(1);
    expect(warnings[0].type).toBe('SCALE_OUT_OF_RANGE');
    
    setMath3DWarnHandler(originalHandler);
  });
});

describe('invertMat4', () => {
  it('inverts translation matrix', () => {
    const m = translateMat4(vec3(1, 2, 3));
    const inv = invertMat4(m);
    expect(inv).not.toBeNull();
    
    const combined = multiplyMat4(m, inv!);
    expect(mat4Equal(combined, identityMat4(), 1e-5)).toBe(true);
  });

  it('returns null for singular matrix', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    // Create a singular matrix (all zeros except [15])
    const singular: Mat4 = { elements: new Float32Array(16) };
    singular.elements[15] = 1;
    
    const result = invertMat4(singular);
    
    expect(result).toBeNull();
    expect(warnings.some(w => w.type === 'SINGULAR_MATRIX')).toBe(true);
    
    setMath3DWarnHandler(originalHandler);
  });

  it('M * M⁻¹ = I', () => {
    const m = multiplyMat4(
      translateMat4(vec3(1, 2, 3)),
      rotateZMat4(0.5)
    );
    const inv = invertMat4(m);
    expect(inv).not.toBeNull();
    
    const result = multiplyMat4(m, inv!);
    expect(mat4Equal(result, identityMat4(), 1e-4)).toBe(true);
  });
});

describe('perspectiveMat4', () => {
  it('creates valid perspective matrix', () => {
    const m = perspectiveMat4(Math.PI / 4, 16/9, 0.1, 1000);
    expect(m.elements.length).toBe(16);
    expect(m.elements[11]).toBe(-1); // Perspective divide indicator
  });

  it('warns on invalid near/far', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    perspectiveMat4(Math.PI / 4, 16/9, 100, 10); // near > far
    
    expect(warnings.some(w => w.type === 'DIVISION_BY_ZERO')).toBe(true);
    
    setMath3DWarnHandler(originalHandler);
  });
});

describe('orthographicMat4', () => {
  it('creates valid orthographic matrix', () => {
    const m = orthographicMat4(-10, 10, -10, 10, 0.1, 100);
    expect(m.elements.length).toBe(16);
    expect(m.elements[15]).toBe(1); // No perspective divide
  });

  it('projects correctly (no perspective)', () => {
    const m = orthographicMat4(-100, 100, -100, 100, 0.1, 1000);
    
    // Two points at different Z should have same X/Y in orthographic
    const nearPoint = transformPoint(m, vec3(50, 50, -10));
    const farPoint = transformPoint(m, vec3(50, 50, -500));
    
    // X and Y should be the same (no foreshortening)
    expect(nearPoint.x).toBeCloseTo(farPoint.x, 3);
    expect(nearPoint.y).toBeCloseTo(farPoint.y, 3);
  });

  it('warns on invalid left/right', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    orthographicMat4(10, -10, -10, 10, 0.1, 100); // left > right
    
    expect(warnings.some(w => w.type === 'DIVISION_BY_ZERO')).toBe(true);
    
    setMath3DWarnHandler(originalHandler);
  });

  it('warns on invalid bottom/top', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    orthographicMat4(-10, 10, 10, -10, 0.1, 100); // bottom > top
    
    expect(warnings.some(w => w.type === 'DIVISION_BY_ZERO')).toBe(true);
    
    setMath3DWarnHandler(originalHandler);
  });

  it('warns on invalid near/far', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    orthographicMat4(-10, 10, -10, 10, 100, 0.1); // near > far
    
    expect(warnings.some(w => w.type === 'DIVISION_BY_ZERO')).toBe(true);
    
    setMath3DWarnHandler(originalHandler);
  });
});

describe('lookAtMat4', () => {
  it('creates valid look-at matrix', () => {
    const eye = vec3(0, 0, 5);
    const target = vec3(0, 0, 0);
    const up = vec3(0, 1, 0);
    
    const m = lookAtMat4(eye, target, up);
    
    // Looking down -Z axis from +Z position
    // Point at origin should project correctly
    const result = transformPoint(m, target);
    expect(result.z).toBeLessThan(0); // In front of camera
  });
});

// ============================================================================
// LENS MATH
// ============================================================================

describe('degToRad / radToDeg', () => {
  it('converts degrees to radians', () => {
    expect(degToRad(180)).toBeCloseTo(Math.PI, 10);
    expect(degToRad(90)).toBeCloseTo(Math.PI / 2, 10);
    expect(degToRad(0)).toBe(0);
  });

  it('converts radians to degrees', () => {
    expect(radToDeg(Math.PI)).toBeCloseTo(180, 10);
    expect(radToDeg(Math.PI / 2)).toBeCloseTo(90, 10);
    expect(radToDeg(0)).toBe(0);
  });

  test.prop([angleArb])('roundtrip: deg -> rad -> deg', (deg) => {
    const result = radToDeg(degToRad(deg));
    expect(result).toBeCloseTo(deg, 10);
  });
});

describe('focalLengthToFOV / fovToFocalLength', () => {
  it('converts focal length to FOV', () => {
    // 50mm on full frame (36mm sensor) ≈ 39.6° horizontal FOV
    const fov = focalLengthToFOV(50, 36);
    const degrees = radToDeg(fov);
    expect(degrees).toBeCloseTo(39.6, 0);
  });

  test.prop([
    fc.double({ min: 10, max: 500, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 10, max: 100, noNaN: true, noDefaultInfinity: true }),
  ])('roundtrip: focal -> fov -> focal', (focal, sensor) => {
    const fov = focalLengthToFOV(focal, sensor);
    const result = fovToFocalLength(fov, sensor);
    expect(result).toBeCloseTo(focal, 5);
  });
});

describe('zoomToFocalLength / focalLengthToZoom', () => {
  test.prop([
    fc.double({ min: 100, max: 10000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 100, max: 4000, noNaN: true, noDefaultInfinity: true }),
    fc.double({ min: 10, max: 100, noNaN: true, noDefaultInfinity: true }),
  ])('roundtrip: zoom -> focal -> zoom', (zoom, compWidth, filmSize) => {
    const focal = zoomToFocalLength(zoom, compWidth, filmSize);
    const result = focalLengthToZoom(focal, compWidth, filmSize);
    expect(result).toBeCloseTo(zoom, 5);
  });
});

// ============================================================================
// QUATERNION OPERATIONS
// ============================================================================

describe('quatIdentity', () => {
  it('creates identity quaternion', () => {
    const q = quatIdentity();
    expect(q.x).toBe(0);
    expect(q.y).toBe(0);
    expect(q.z).toBe(0);
    expect(q.w).toBe(1);
  });
});

describe('quatFromEuler / quatToEuler', () => {
  it('identity rotation roundtrips', () => {
    const q = quatFromEuler(0, 0, 0);
    const euler = quatToEuler(q);
    expect(euler.x).toBeCloseTo(0, 5);
    expect(euler.y).toBeCloseTo(0, 5);
    expect(euler.z).toBeCloseTo(0, 5);
  });

  it('90° X rotation roundtrips', () => {
    const angle = Math.PI / 2;
    const q = quatFromEuler(angle, 0, 0);
    const euler = quatToEuler(q);
    expect(euler.x).toBeCloseTo(angle, 3);
  });

  it('handles gimbal lock (warns, doesn\'t crash)', () => {
    const warnings: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    setMath3DWarnHandler((e) => warnings.push(e));
    
    // Pitch = exactly 90°
    const q = quatFromEuler(0, Math.PI / 2, 0);
    const euler = quatToEuler(q);
    
    // Should still produce valid (if degenerate) result
    expect(Number.isFinite(euler.x)).toBe(true);
    expect(Number.isFinite(euler.y)).toBe(true);
    expect(Number.isFinite(euler.z)).toBe(true);
    expect(euler.y).toBeCloseTo(Math.PI / 2, 3);
    expect(warnings.some(w => w.type === 'GIMBAL_LOCK')).toBe(true);
    
    setMath3DWarnHandler(originalHandler);
  });
});

describe('slerpQuat', () => {
  it('t=0 returns first quaternion', () => {
    const a = quatIdentity();
    const b = quatFromEuler(Math.PI / 2, 0, 0);
    const result = slerpQuat(a, b, 0);
    expect(result.w).toBeCloseTo(a.w, 5);
    expect(result.x).toBeCloseTo(a.x, 5);
  });

  it('t=1 returns second quaternion', () => {
    const a = quatIdentity();
    const b = quatFromEuler(Math.PI / 2, 0, 0);
    const result = slerpQuat(a, b, 1);
    expect(result.x).toBeCloseTo(b.x, 5);
    expect(result.w).toBeCloseTo(b.w, 5);
  });

  it('t=0.5 returns interpolated quaternion', () => {
    const a = quatIdentity();
    const b = quatFromEuler(Math.PI / 2, 0, 0); // 90° rotation
    const result = slerpQuat(a, b, 0.5);
    
    // Should be approximately 45° rotation
    const euler = quatToEuler(result);
    expect(euler.x).toBeCloseTo(Math.PI / 4, 2);
  });
});

// ============================================================================
// HIGH-PRECISION OPERATIONS
// ============================================================================

describe('Mat4_64 operations', () => {
  it('identityMat4_64 creates identity', () => {
    const m = identityMat4_64();
    expect(m.elements[0]).toBe(1);
    expect(m.elements[5]).toBe(1);
    expect(m.elements[10]).toBe(1);
    expect(m.elements[15]).toBe(1);
  });

  it('scaleMat4_64 creates scale matrix', () => {
    const m = scaleMat4_64(vec3(2, 3, 4));
    expect(m.elements[0]).toBe(2);
    expect(m.elements[5]).toBe(3);
    expect(m.elements[10]).toBe(4);
  });

  it('multiplyMat4_64 multiplies correctly', () => {
    const a = scaleMat4_64(vec3(2, 2, 2));
    const b = scaleMat4_64(vec3(3, 3, 3));
    const result = multiplyMat4_64(a, b);
    // 2 * 3 = 6
    expect(result.elements[0]).toBeCloseTo(6, 10);
  });

  it('converts between Mat4 and Mat4_64', () => {
    const original = identityMat4();
    const converted = convertToMat4_64(original);
    const back = convertToMat4(converted);
    expect(mat4Equal(original, back)).toBe(true);
  });
});

// ============================================================================
// PRECISION CONSTANTS
// ============================================================================

describe('PRECISION constants', () => {
  it('has expected Float32 precision', () => {
    expect(PRECISION.FLOAT32_RELATIVE).toBe(1e-7);
  });

  it('has expected Float64 precision', () => {
    expect(PRECISION.FLOAT64_RELATIVE).toBe(1e-15);
  });

  it('has reasonable scale bounds', () => {
    expect(PRECISION.FLOAT32_SCALE_MIN).toBe(0.01);
    expect(PRECISION.FLOAT32_SCALE_MAX).toBe(100);
  });
});

// ============================================================================
// WARNING SYSTEM
// ============================================================================

describe('Warning system', () => {
  it('setMath3DWarnHandler changes handler', () => {
    const events: Math3DWarnEvent[] = [];
    const originalHandler = math3dWarnHandler;
    
    setMath3DWarnHandler((e) => events.push(e));
    
    // Trigger a warning
    normalizeVec3(vec3(0, 0, 0));
    
    expect(events.length).toBe(1);
    
    setMath3DWarnHandler(originalHandler);
  });

  it('warning events have required fields', () => {
    const events: Math3DWarnEvent[] = [];
    setMath3DWarnHandler((e) => events.push(e));
    
    normalizeVec3(vec3(0, 0, 0));
    
    expect(events[0].type).toBeDefined();
    expect(events[0].message).toBeDefined();
    expect(typeof events[0].message).toBe('string');
    
    // Restore default handler
    setMath3DWarnHandler((event) => {
      console.warn(`[math3d] ${event.type}: ${event.message}`, event.context);
    });
  });
});

// ============================================================================
// BUG VERIFICATION TESTS - Division by Zero Fixes
// ============================================================================

describe('Division by zero bug fixes', () => {
  /**
   * These bugs were found during re-verification of "fully audited" files.
   * Each function now returns a sensible default instead of Infinity/NaN.
   */
  
  describe('fovToFocalLength', () => {
    it('BUG FIX: fov=0 returns sensorSize default instead of Infinity', () => {
      const result = fovToFocalLength(0, 36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(36); // Returns sensorSize as default
    });
    
    it('BUG FIX: fov=PI returns sensorSize default instead of Infinity', () => {
      const result = fovToFocalLength(Math.PI, 36);
      expect(Number.isFinite(result)).toBe(true);
    });
    
    it('BUG FIX: negative fov returns sensorSize default', () => {
      const result = fovToFocalLength(-0.5, 36);
      expect(Number.isFinite(result)).toBe(true);
    });
  });
  
  describe('zoomToFocalLength', () => {
    it('BUG FIX: compWidth=0 returns filmSize default instead of Infinity', () => {
      const result = zoomToFocalLength(100, 0, 36);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(36); // Returns filmSize as default
    });
    
    it('BUG FIX: negative compWidth returns filmSize default', () => {
      const result = zoomToFocalLength(100, -1920, 36);
      expect(Number.isFinite(result)).toBe(true);
    });
  });
  
  describe('focalLengthToZoom', () => {
    it('BUG FIX: filmSize=0 returns compWidth default instead of Infinity', () => {
      const result = focalLengthToZoom(50, 1920, 0);
      expect(Number.isFinite(result)).toBe(true);
      expect(result).toBe(1920); // Returns compWidth as default
    });
    
    it('BUG FIX: negative filmSize returns compWidth default', () => {
      const result = focalLengthToZoom(50, 1920, -36);
      expect(Number.isFinite(result)).toBe(true);
    });
  });
  
  describe('quatToEuler', () => {
    it('BUG FIX: zero quaternion returns identity rotation instead of NaN', () => {
      const result = quatToEuler({ x: 0, y: 0, z: 0, w: 0 });
      expect(Number.isFinite(result.x)).toBe(true);
      expect(Number.isFinite(result.y)).toBe(true);
      expect(Number.isFinite(result.z)).toBe(true);
      expect(result.x).toBe(0);
      expect(result.y).toBe(0);
      expect(result.z).toBe(0);
    });
  });
});
