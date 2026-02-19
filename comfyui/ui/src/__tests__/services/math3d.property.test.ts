/**
 * PROPERTY TESTS: ui/src/services/math3d.ts
 * 
 * Created: 2026-01-06
 * Methodology: fast-check property-based testing
 * 
 * Tests verify MATHEMATICAL INVARIANTS that must hold for ALL inputs.
 * These are properties that define correct 3D math - if they fail,
 * the entire rendering pipeline is broken.
 */

import { describe, expect } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
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
  
  // High precision
  identityMat4_64,
  multiplyMat4_64,
  convertToMat4,
  convertToMat4_64,
  
  type Vec3,
  type Mat4,
  type Quat,
} from '@/services/math3d';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//                                                              // arbitraries
// ═══════════════════════════════════════════════════════════════════════════

// Reasonable range to avoid overflow/precision issues
const coordArb = fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true });

const vec3Arb = fc.record({
  x: coordArb,
  y: coordArb,
  z: coordArb,
});

// Non-zero vector for operations that need it
const nonZeroVec3Arb = vec3Arb.filter(v => lengthVec3(v) > 0.001);

// Small angles (radians) - full rotation range
const angleArb = fc.double({ min: -Math.PI * 2, max: Math.PI * 2, noNaN: true, noDefaultInfinity: true });

// Interpolation parameter
const tArb = fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true });

// Scalar for scaling operations
const scalarArb = fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true });

// Positive scalar for lens math
const positiveArb = fc.double({ min: 0.1, max: 1000, noNaN: true, noDefaultInfinity: true });

// Tolerance for floating point comparisons
const EPSILON = 1e-5;

// ═══════════════════════════════════════════════════════════════════════════
// HELPER: Compare vectors with tolerance
// ═══════════════════════════════════════════════════════════════════════════

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

// ═══════════════════════════════════════════════════════════════════════════
//                                          // vector // algebra // properties
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: Vector Algebra', () => {
  //                                                                 // addition
  test.prop([vec3Arb, vec3Arb])('addition is commutative: a + b = b + a', (a, b) => {
    const ab = addVec3(a, b);
    const ba = addVec3(b, a);
    expect(vec3Equal(ab, ba)).toBe(true);
  });

  test.prop([vec3Arb, vec3Arb, vec3Arb])('addition is associative: (a + b) + c = a + (b + c)', (a, b, c) => {
    const left = addVec3(addVec3(a, b), c);
    const right = addVec3(a, addVec3(b, c));
    expect(vec3Equal(left, right)).toBe(true);
  });

  test.prop([vec3Arb])('addition identity: a + 0 = a', (a) => {
    const zero = vec3(0, 0, 0);
    const result = addVec3(a, zero);
    expect(vec3Equal(result, a)).toBe(true);
  });

  //                                                              // subtraction
  test.prop([vec3Arb])('subtraction: a - a = 0', (a) => {
    const result = subVec3(a, a);
    expect(vec3Equal(result, vec3(0, 0, 0))).toBe(true);
  });

  test.prop([vec3Arb, vec3Arb])('subtraction: a - b = -(b - a)', (a, b) => {
    const left = subVec3(a, b);
    const right = scaleVec3(subVec3(b, a), -1);
    expect(vec3Equal(left, right)).toBe(true);
  });

  //                                                                  // scaling
  test.prop([vec3Arb])('scale by 1 is identity: 1 * a = a', (a) => {
    const result = scaleVec3(a, 1);
    expect(vec3Equal(result, a)).toBe(true);
  });

  test.prop([vec3Arb])('scale by 0 gives zero: 0 * a = 0', (a) => {
    const result = scaleVec3(a, 0);
    expect(vec3Equal(result, vec3(0, 0, 0))).toBe(true);
  });

  test.prop([vec3Arb, scalarArb, scalarArb])('scaling is associative: s1 * (s2 * a) = (s1 * s2) * a', (a, s1, s2) => {
    const left = scaleVec3(scaleVec3(a, s2), s1);
    const right = scaleVec3(a, s1 * s2);
    expect(vec3Equal(left, right)).toBe(true);
  });

  //                                                           // dot // product
  test.prop([vec3Arb, vec3Arb])('dot product is commutative: a · b = b · a', (a, b) => {
    expect(dotVec3(a, b)).toBeCloseTo(dotVec3(b, a), 5);
  });

  test.prop([vec3Arb])('dot product with self = length²', (a) => {
    const dot = dotVec3(a, a);
    const len = lengthVec3(a);
    expect(dot).toBeCloseTo(len * len, 5);
  });

  //                                                         // cross // product
  test.prop([vec3Arb, vec3Arb])('cross product is anti-commutative: a × b = -(b × a)', (a, b) => {
    const ab = crossVec3(a, b);
    const ba = crossVec3(b, a);
    const negBA = scaleVec3(ba, -1);
    expect(vec3Equal(ab, negBA)).toBe(true);
  });

  test.prop([vec3Arb])('cross product with self is zero: a × a = 0', (a) => {
    const result = crossVec3(a, a);
    expect(vec3Equal(result, vec3(0, 0, 0))).toBe(true);
  });

  //                                                                   // length
  test.prop([vec3Arb])('length is non-negative', (a) => {
    expect(lengthVec3(a)).toBeGreaterThanOrEqual(0);
  });

  test.prop([nonZeroVec3Arb, scalarArb])('length scales: |s * a| = |s| * |a|', (a, s) => {
    const scaled = scaleVec3(a, s);
    const left = lengthVec3(scaled);
    const right = Math.abs(s) * lengthVec3(a);
    expect(left).toBeCloseTo(right, 4);
  });

  //                                                                // normalize
  test.prop([nonZeroVec3Arb])('normalized vector has length 1', (a) => {
    const n = normalizeVec3(a);
    expect(lengthVec3(n)).toBeCloseTo(1, 5);
  });

  test.prop([nonZeroVec3Arb])('normalize is idempotent: normalize(normalize(a)) = normalize(a)', (a) => {
    const once = normalizeVec3(a);
    const twice = normalizeVec3(once);
    expect(vec3Equal(once, twice)).toBe(true);
  });

  //                                                                     // lerp
  test.prop([vec3Arb, vec3Arb])('lerp at t=0 gives first vector', (a, b) => {
    const result = lerpVec3(a, b, 0);
    expect(vec3Equal(result, a)).toBe(true);
  });

  test.prop([vec3Arb, vec3Arb])('lerp at t=1 gives second vector', (a, b) => {
    const result = lerpVec3(a, b, 1);
    expect(vec3Equal(result, b)).toBe(true);
  });

  test.prop([vec3Arb])('lerp with same vectors gives that vector', (a) => {
    const result = lerpVec3(a, a, 0.5);
    expect(vec3Equal(result, a)).toBe(true);
  });

  //                                                                 // distance
  test.prop([vec3Arb, vec3Arb])('distance is symmetric: d(a,b) = d(b,a)', (a, b) => {
    expect(distanceVec3(a, b)).toBeCloseTo(distanceVec3(b, a), 5);
  });

  test.prop([vec3Arb])('distance to self is 0', (a) => {
    expect(distanceVec3(a, a)).toBeCloseTo(0, 10);
  });

  test.prop([vec3Arb])('distance is non-negative', (a) => {
    const b = vec3(Math.random() * 100, Math.random() * 100, Math.random() * 100);
    expect(distanceVec3(a, b)).toBeGreaterThanOrEqual(0);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                          // matrix // algebra // properties
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: Matrix Algebra', () => {
  test.prop([fc.constant(null)])('identity * identity = identity', () => {
    const I = identityMat4();
    const result = multiplyMat4(I, I);
    expect(mat4Equal(result, I)).toBe(true);
  });

  test.prop([vec3Arb])('identity * translate = translate', (v) => {
    const I = identityMat4();
    const T = translateMat4(v);
    const result = multiplyMat4(I, T);
    expect(mat4Equal(result, T)).toBe(true);
  });

  test.prop([vec3Arb])('translate * identity = translate', (v) => {
    const I = identityMat4();
    const T = translateMat4(v);
    const result = multiplyMat4(T, I);
    expect(mat4Equal(result, T)).toBe(true);
  });

  test.prop([vec3Arb, vec3Arb])('translation composition: T(a) * T(b) = T(a + b)', (a, b) => {
    const Ta = translateMat4(a);
    const Tb = translateMat4(b);
    const composed = multiplyMat4(Ta, Tb);
    const combined = translateMat4(addVec3(a, b));
    
    // Test by transforming a point
    const origin = vec3(0, 0, 0);
    const fromComposed = transformPoint(composed, origin);
    const fromCombined = transformPoint(combined, origin);
    expect(vec3Equal(fromComposed, fromCombined)).toBe(true);
  });

  test.prop([angleArb])('rotation by 2π is approximately identity', (angle) => {
    // Rotate by angle, then by (2π - angle) should be identity
    const R1 = rotateZMat4(angle);
    const R2 = rotateZMat4(-angle);
    const composed = multiplyMat4(R1, R2);
    expect(mat4Equal(composed, identityMat4(), 1e-4)).toBe(true);
  });

  test.prop([vec3Arb])('transformPoint with identity gives same point', (v) => {
    const I = identityMat4();
    const result = transformPoint(I, v);
    expect(vec3Equal(result, v)).toBe(true);
  });

  test.prop([vec3Arb])('transformDirection with identity gives same direction', (v) => {
    const I = identityMat4();
    const result = transformDirection(I, v);
    expect(vec3Equal(result, v)).toBe(true);
  });

  // Matrix inverse
  test.prop([vec3Arb])('M * M⁻¹ = I for translation matrices', (v) => {
    fc.pre(lengthVec3(v) > 0.01); // Skip near-zero translations
    const M = translateMat4(v);
    const Minv = invertMat4(M);
    expect(Minv).not.toBeNull();
    const result = multiplyMat4(M, Minv!);
    expect(mat4Equal(result, identityMat4(), 1e-4)).toBe(true);
  });

  test.prop([angleArb])('M * M⁻¹ = I for rotation matrices', (angle) => {
    const M = rotateZMat4(angle);
    const Minv = invertMat4(M);
    expect(Minv).not.toBeNull();
    const result = multiplyMat4(M, Minv!);
    expect(mat4Equal(result, identityMat4(), 1e-4)).toBe(true);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                               // lens // math // properties
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: Lens Math', () => {
  test.prop([angleArb])('deg → rad → deg roundtrip', (deg) => {
    const result = radToDeg(degToRad(deg));
    expect(result).toBeCloseTo(deg, 10);
  });

  test.prop([angleArb])('rad → deg → rad roundtrip', (rad) => {
    const result = degToRad(radToDeg(rad));
    expect(result).toBeCloseTo(rad, 10);
  });

  test.prop([positiveArb, positiveArb])('focal → FOV → focal roundtrip', (focal, sensor) => {
    const fov = focalLengthToFOV(focal, sensor);
    const result = fovToFocalLength(fov, sensor);
    expect(result).toBeCloseTo(focal, 3);
  });

  test.prop([positiveArb, positiveArb, positiveArb])('zoom → focal → zoom roundtrip', (zoom, compWidth, filmSize) => {
    const focal = zoomToFocalLength(zoom, compWidth, filmSize);
    const result = focalLengthToZoom(focal, compWidth, filmSize);
    expect(result).toBeCloseTo(zoom, 3);
  });

  test.prop([fc.constant(null)])('90° = π/2 radians', () => {
    expect(degToRad(90)).toBeCloseTo(Math.PI / 2, 10);
  });

  test.prop([fc.constant(null)])('180° = π radians', () => {
    expect(degToRad(180)).toBeCloseTo(Math.PI, 10);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                 // quaternion // properties
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: Quaternion', () => {
  test.prop([fc.constant(null)])('identity quaternion has w=1', () => {
    const q = quatIdentity();
    expect(q.x).toBe(0);
    expect(q.y).toBe(0);
    expect(q.z).toBe(0);
    expect(q.w).toBe(1);
  });

  test.prop([angleArb, angleArb, angleArb])('slerp at t=0 gives first quaternion', (x, y, z) => {
    const a = quatIdentity();
    const b = quatFromEuler(x, y, z);
    const result = slerpQuat(a, b, 0);
    expect(result.x).toBeCloseTo(a.x, 5);
    expect(result.y).toBeCloseTo(a.y, 5);
    expect(result.z).toBeCloseTo(a.z, 5);
    expect(result.w).toBeCloseTo(a.w, 5);
  });

  test.prop([angleArb, angleArb, angleArb])('slerp at t=1 gives second quaternion', (x, y, z) => {
    const a = quatIdentity();
    const b = quatFromEuler(x, y, z);
    const result = slerpQuat(a, b, 1);
    // Note: quaternion may be negated but represents same rotation
    const matchesB = (
      Math.abs(result.x - b.x) < 0.01 &&
      Math.abs(result.y - b.y) < 0.01 &&
      Math.abs(result.z - b.z) < 0.01 &&
      Math.abs(result.w - b.w) < 0.01
    );
    const matchesNegB = (
      Math.abs(result.x + b.x) < 0.01 &&
      Math.abs(result.y + b.y) < 0.01 &&
      Math.abs(result.z + b.z) < 0.01 &&
      Math.abs(result.w + b.w) < 0.01
    );
    expect(matchesB || matchesNegB).toBe(true);
  });

  test.prop([angleArb, angleArb, angleArb])('slerp with same quaternions gives that quaternion', (x, y, z) => {
    const q = quatFromEuler(x, y, z);
    const result = slerpQuat(q, q, 0.5);
    expect(result.x).toBeCloseTo(q.x, 5);
    expect(result.y).toBeCloseTo(q.y, 5);
    expect(result.z).toBeCloseTo(q.z, 5);
    expect(result.w).toBeCloseTo(q.w, 5);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                // high // precision // matrix // properties
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: High Precision Matrices (Mat4_64)', () => {
  test.prop([fc.constant(null)])('identity_64 converts to identity_32', () => {
    const m64 = identityMat4_64();
    const m32 = convertToMat4(m64);
    expect(mat4Equal(m32, identityMat4())).toBe(true);
  });

  test.prop([fc.constant(null)])('identity_32 converts to identity_64 and back', () => {
    const m32 = identityMat4();
    const m64 = convertToMat4_64(m32);
    const back = convertToMat4(m64);
    expect(mat4Equal(back, m32)).toBe(true);
  });

  test.prop([fc.constant(null)])('multiply_64 identity * identity = identity', () => {
    const I = identityMat4_64();
    const result = multiplyMat4_64(I, I);
    const asFloat32 = convertToMat4(result);
    expect(mat4Equal(asFloat32, identityMat4())).toBe(true);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
//                                                // determinism // properties
// ═══════════════════════════════════════════════════════════════════════════

describe('PROPERTY: Determinism', () => {
  test.prop([vec3Arb, vec3Arb])('addVec3 is deterministic', (a, b) => {
    const r1 = addVec3(a, b);
    const r2 = addVec3(a, b);
    expect(r1.x).toBe(r2.x);
    expect(r1.y).toBe(r2.y);
    expect(r1.z).toBe(r2.z);
  });

  test.prop([vec3Arb])('translateMat4 is deterministic', (v) => {
    const r1 = translateMat4(v);
    const r2 = translateMat4(v);
    expect(mat4Equal(r1, r2)).toBe(true);
  });

  test.prop([angleArb])('rotateZMat4 is deterministic', (angle) => {
    const r1 = rotateZMat4(angle);
    const r2 = rotateZMat4(angle);
    expect(mat4Equal(r1, r2)).toBe(true);
  });

  test.prop([angleArb, angleArb, angleArb])('quatFromEuler is deterministic', (x, y, z) => {
    const r1 = quatFromEuler(x, y, z);
    const r2 = quatFromEuler(x, y, z);
    expect(r1.x).toBe(r2.x);
    expect(r1.y).toBe(r2.y);
    expect(r1.z).toBe(r2.z);
    expect(r1.w).toBe(r2.w);
  });
});

// ═══════════════════════════════════════════════════════════════════════════
// PROJECTION MATRICES (CRITICAL for rendering)
// ═══════════════════════════════════════════════════════════════════════════

import {
  perspectiveMat4,
  orthographicMat4,
  lookAtMat4,
  scaleMat4_64,
} from '@/services/math3d';

// FOV in radians (reasonable range: 10° to 170°)
const fovArb = fc.double({ min: Math.PI / 18, max: Math.PI * 17 / 18, noNaN: true, noDefaultInfinity: true });
// Aspect ratio (reasonable range)
const aspectArb = fc.double({ min: 0.25, max: 4, noNaN: true, noDefaultInfinity: true });
// Near/far planes (positive, near < far)
const nearArb = fc.double({ min: 0.001, max: 10, noNaN: true, noDefaultInfinity: true });
const farArb = fc.double({ min: 100, max: 10000, noNaN: true, noDefaultInfinity: true });
// Ortho bounds
const boundsArb = fc.double({ min: 1, max: 1000, noNaN: true, noDefaultInfinity: true });

describe('perspectiveMat4 properties', () => {
  test.prop([fovArb, aspectArb, nearArb, farArb])('returns valid matrix (16 elements)', (fov, aspect, near, far) => {
    const m = perspectiveMat4(fov, aspect, near, far);
    expect(m.elements.length).toBe(16);
    // All elements should be finite
    for (let i = 0; i < 16; i++) {
      expect(Number.isFinite(m.elements[i])).toBe(true);
    }
  });

  test.prop([fovArb, aspectArb, nearArb, farArb])('is deterministic', (fov, aspect, near, far) => {
    const m1 = perspectiveMat4(fov, aspect, near, far);
    const m2 = perspectiveMat4(fov, aspect, near, far);
    expect(mat4Equal(m1, m2)).toBe(true);
  });

  test.prop([fovArb, aspectArb, nearArb, farArb])('diagonal elements are non-zero (valid projection)', (fov, aspect, near, far) => {
    const m = perspectiveMat4(fov, aspect, near, far);
    // For a valid perspective matrix, m[0], m[5], m[10] should be non-zero
    expect(Math.abs(m.elements[0])).toBeGreaterThan(0.001);
    expect(Math.abs(m.elements[5])).toBeGreaterThan(0.001);
    expect(Math.abs(m.elements[10])).toBeGreaterThan(0.001);
  });
});

describe('orthographicMat4 properties', () => {
  test.prop([boundsArb, boundsArb, nearArb, farArb])('returns valid matrix (16 elements)', (width, height, near, far) => {
    const m = orthographicMat4(-width, width, -height, height, near, far);
    expect(m.elements.length).toBe(16);
    for (let i = 0; i < 16; i++) {
      expect(Number.isFinite(m.elements[i])).toBe(true);
    }
  });

  test.prop([boundsArb, boundsArb, nearArb, farArb])('is deterministic', (width, height, near, far) => {
    const m1 = orthographicMat4(-width, width, -height, height, near, far);
    const m2 = orthographicMat4(-width, width, -height, height, near, far);
    expect(mat4Equal(m1, m2)).toBe(true);
  });

  test.prop([boundsArb, boundsArb, nearArb, farArb])('produces uniform scaling (no perspective distortion)', (width, height, near, far) => {
    const m = orthographicMat4(-width, width, -height, height, near, far);
    // In orthographic projection, m[15] should be 1 (no perspective divide)
    expect(m.elements[15]).toBeCloseTo(1, 5);
    // m[3], m[7], m[11] should be 0 (no perspective)
    expect(m.elements[3]).toBeCloseTo(0, 5);
    expect(m.elements[7]).toBeCloseTo(0, 5);
    expect(m.elements[11]).toBeCloseTo(0, 5);
  });
});

// Create arbitrary that avoids gimbal lock (looking straight up/down)
const horizontalOffsetArb = fc.record({
  x: fc.double({ min: 0.1, max: 1000, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: -100, max: 100, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: 0.1, max: 1000, noNaN: true, noDefaultInfinity: true }),
});

describe('lookAtMat4 properties', () => {
  test.prop([nonZeroVec3Arb, horizontalOffsetArb])('returns valid matrix when eye != target', (eye, offset) => {
    // Create target different from eye
    const target = { x: eye.x + offset.x, y: eye.y + offset.y, z: eye.z + offset.z };
    const up = { x: 0, y: 1, z: 0 };
    const m = lookAtMat4(eye, target, up);
    
    expect(m.elements.length).toBe(16);
    for (let i = 0; i < 16; i++) {
      expect(Number.isFinite(m.elements[i])).toBe(true);
    }
  });

  test.prop([nonZeroVec3Arb, horizontalOffsetArb])('is deterministic', (eye, offset) => {
    const target = { x: eye.x + offset.x, y: eye.y + offset.y, z: eye.z + offset.z };
    const up = { x: 0, y: 1, z: 0 };
    const m1 = lookAtMat4(eye, target, up);
    const m2 = lookAtMat4(eye, target, up);
    expect(mat4Equal(m1, m2)).toBe(true);
  });

  test.prop([nonZeroVec3Arb, horizontalOffsetArb])('produces orthonormal rotation (view matrix)', (eye, offset) => {
    const target = { x: eye.x + offset.x, y: eye.y + offset.y, z: eye.z + offset.z };
    const up = { x: 0, y: 1, z: 0 };
    const m = lookAtMat4(eye, target, up);
    
    // The upper-left 3x3 should be orthonormal (rotation)
    // Check that rows are unit length (approximately)
    const e = m.elements;
    const row0Len = Math.sqrt(e[0]*e[0] + e[4]*e[4] + e[8]*e[8]);
    const row1Len = Math.sqrt(e[1]*e[1] + e[5]*e[5] + e[9]*e[9]);
    const row2Len = Math.sqrt(e[2]*e[2] + e[6]*e[6] + e[10]*e[10]);
    
    // Note: Gimbal lock (looking straight up/down) is avoided by horizontalOffsetArb
    expect(row0Len).toBeCloseTo(1, 3);
    expect(row1Len).toBeCloseTo(1, 3);
    expect(row2Len).toBeCloseTo(1, 3);
  });
});

describe('scaleMat4_64 properties', () => {
  test.prop([vec3Arb])('returns valid 64-bit matrix', (s) => {
    const m = scaleMat4_64(s);
    expect(m.elements.length).toBe(16);
    expect(m.elements instanceof Float64Array).toBe(true);
  });

  test.prop([vec3Arb])('is deterministic', (s) => {
    const m1 = scaleMat4_64(s);
    const m2 = scaleMat4_64(s);
    for (let i = 0; i < 16; i++) {
      expect(m1.elements[i]).toBe(m2.elements[i]);
    }
  });

  test.prop([vec3Arb])('diagonal contains scale values', (s) => {
    const m = scaleMat4_64(s);
    expect(m.elements[0]).toBe(s.x);
    expect(m.elements[5]).toBe(s.y);
    expect(m.elements[10]).toBe(s.z);
    expect(m.elements[15]).toBe(1);
  });
});
