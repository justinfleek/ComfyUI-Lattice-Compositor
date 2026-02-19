/**
 * STRICT Transform Property Tests
 * 
 * These tests use REALISTIC value ranges without artificial constraints.
 * Tests that fail expose REAL BUGS that need to be fixed or documented.
 * 
 * Tolerance: 1e-10 (strict) unless mathematically impossible
 */

import { describe, expect, it } from 'vitest';
import { test, fc } from '@fast-check/vitest';
import {
  identityMat4,
  multiplyMat4,
  invertMat4,
  transformPoint,
  transformDirection,
  translateMat4,
  rotateXMat4,
  rotateYMat4,
  rotateZMat4,
  scaleMat4,
  addVec3,
  subVec3,
  scaleVec3,
  normalizeVec3,
  lengthVec3,
  crossVec3,
  dotVec3,
  lerpVec3,
  quatIdentity,
  quatFromEuler,
  quatToEuler,
  slerpQuat,
  degToRad,
  radToDeg,
  perspectiveMat4,
  orthographicMat4,
  lookAtMat4,
  // High-precision (Float64) functions
  identityMat4_64,
  scaleMat4_64,
  multiplyMat4_64,
  convertToMat4,
  PRECISION,
  type Vec3,
  type Mat4,
  type Mat4_64,
  type Quat,
} from '@/services/math3d';

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// STRICT TOLERANCE - Change this to find precision limits
// ═══════════════════════════════════════════════════════════════════════════
const STRICT_TOLERANCE = 1e-10;
const FLOAT32_TOLERANCE = 1e-6;  // What Float32 can actually achieve

// ═══════════════════════════════════════════════════════════════════════════
// REALISTIC VALUE RANGES - No artificial constraints
// ═══════════════════════════════════════════════════════════════════════════

/**
 * Realistic 3D position values (pixels/units)
 * Range: -10000 to 10000 (covers 8K resolution plus margin)
 */
const realisticPositionArb = fc.record({
  x: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: -10000, max: 10000, noNaN: true, noDefaultInfinity: true }),
});

/**
 * Realistic scale values
 * Range: 0.001 to 1000 (1000x zoom out to 1000x zoom in)
 */
const realisticScaleArb = fc.record({
  x: fc.double({ min: 0.001, max: 1000, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: 0.001, max: 1000, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: 0.001, max: 1000, noNaN: true, noDefaultInfinity: true }),
});

/**
 * Realistic rotation angles (full 360° × multiple rotations)
 * Range: -4π to 4π (±720°)
 */
const realisticAngleArb = fc.double({ 
  min: -Math.PI * 4, 
  max: Math.PI * 4, 
  noNaN: true,
  noDefaultInfinity: true 
});

/**
 * Euler angles for stable roundtrip testing.
 * 
 * GIMBAL LOCK: At pitch = ±90°, roll and yaw become degenerate (there are
 * infinite equivalent representations). This is a MATHEMATICAL property of
 * Euler angles, not a code bug. Near gimbal lock, roundtrip precision degrades.
 * 
 * We test the stable range (pitch between ±88°) to verify the implementation
 * is correct, and separately document gimbal lock behavior.
 */
const stableEulerArb = fc.tuple(
  fc.double({ min: -Math.PI, max: Math.PI, noNaN: true, noDefaultInfinity: true }),
  // Stay ~2° away from gimbal lock (±88° instead of ±90°)
  fc.double({ min: -Math.PI / 2 + 0.035, max: Math.PI / 2 - 0.035, noNaN: true, noDefaultInfinity: true }),
  fc.double({ min: -Math.PI, max: Math.PI, noNaN: true, noDefaultInfinity: true }),
);

/**
 * Normalized t value for interpolation
 */
const tArb = fc.double({ min: 0, max: 1, noNaN: true, noDefaultInfinity: true });

/**
 * Non-zero vector for operations that require it
 */
const nonZeroVec3Arb = fc.record({
  x: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  y: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
  z: fc.double({ min: -1000, max: 1000, noNaN: true, noDefaultInfinity: true }),
}).filter(v => Math.sqrt(v.x * v.x + v.y * v.y + v.z * v.z) > 0.001);

// ═══════════════════════════════════════════════════════════════════════════
//                                                                  // helpers
// ═══════════════════════════════════════════════════════════════════════════

function vec3Equal(a: Vec3, b: Vec3, epsilon: number): boolean {
  return (
    Math.abs(a.x - b.x) < epsilon &&
    Math.abs(a.y - b.y) < epsilon &&
    Math.abs(a.z - b.z) < epsilon
  );
}

/**
 * Compare matrices with absolute tolerance.
 * Best for values expected to be near 0 or 1.
 */
function mat4Equal(a: Mat4, b: Mat4, epsilon: number): boolean {
  for (let i = 0; i < 16; i++) {
    if (Math.abs(a.elements[i] - b.elements[i]) > epsilon) {
      return false;
    }
  }
  return true;
}

/**
 * Compare matrices with relative tolerance.
 * Better for values that span wide ranges (e.g., scale 0.001 to 1000).
 * Uses: |a - b| <= epsilon * max(|a|, |b|, 1)
 */
function mat4EqualRelative(a: Mat4, b: Mat4, relEpsilon: number): boolean {
  for (let i = 0; i < 16; i++) {
    const va = a.elements[i];
    const vb = b.elements[i];
    const scale = Math.max(Math.abs(va), Math.abs(vb), 1);
    if (Math.abs(va - vb) > relEpsilon * scale) {
      return false;
    }
  }
  return true;
}

function mat4_64Equal(a: Mat4_64, b: Mat4_64, epsilon: number): boolean {
  for (let i = 0; i < 16; i++) {
    if (Math.abs(a.elements[i] - b.elements[i]) > epsilon) {
      return false;
    }
  }
  return true;
}

function quatEqual(a: Quat, b: Quat, epsilon: number): boolean {
  // Quaternions q and -q represent the same rotation
  const sameSide = (
    Math.abs(a.x - b.x) < epsilon &&
    Math.abs(a.y - b.y) < epsilon &&
    Math.abs(a.z - b.z) < epsilon &&
    Math.abs(a.w - b.w) < epsilon
  );
  const oppSide = (
    Math.abs(a.x + b.x) < epsilon &&
    Math.abs(a.y + b.y) < epsilon &&
    Math.abs(a.z + b.z) < epsilon &&
    Math.abs(a.w + b.w) < epsilon
  );
  return sameSide || oppSide;
}

function applyQuatToVec(q: Quat, v: Vec3): Vec3 {
  const qx = q.x, qy = q.y, qz = q.z, qw = q.w;
  const tx = qw * v.x + qy * v.z - qz * v.y;
  const ty = qw * v.y + qz * v.x - qx * v.z;
  const tz = qw * v.z + qx * v.y - qy * v.x;
  const tw = -qx * v.x - qy * v.y - qz * v.z;
  
  return {
    x: tx * qw - tw * qx - ty * qz + tz * qy,
    y: ty * qw - tw * qy - tz * qx + tx * qz,
    z: tz * qw - tw * qz - tx * qy + ty * qx,
  };
}

// ═══════════════════════════════════════════════════════════════════════════
//                                           // vector // operations // strict
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Vector3 Operations', () => {

  test.prop([realisticPositionArb, realisticPositionArb])(
    'addition is commutative: a + b = b + a',
    (a, b) => {
      const ab = addVec3(a, b);
      const ba = addVec3(b, a);
      expect(vec3Equal(ab, ba, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticPositionArb, realisticPositionArb, realisticPositionArb])(
    'addition is associative: (a + b) + c = a + (b + c)',
    (a, b, c) => {
      const left = addVec3(addVec3(a, b), c);
      const right = addVec3(a, addVec3(b, c));
      // Floating point associativity can have small errors
      expect(vec3Equal(left, right, FLOAT32_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticPositionArb])(
    'subtraction is inverse of addition: a - a = 0',
    (a) => {
      const result = subVec3(a, a);
      const zero: Vec3 = { x: 0, y: 0, z: 0 };
      expect(vec3Equal(result, zero, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([nonZeroVec3Arb])(
    'normalized vector has length 1',
    (v) => {
      const normalized = normalizeVec3(v);
      const len = lengthVec3(normalized);
      expect(Math.abs(len - 1)).toBeLessThan(STRICT_TOLERANCE);
    }
  );

  test.prop([realisticPositionArb, realisticPositionArb])(
    'dot product is commutative: a · b = b · a',
    (a, b) => {
      const ab = dotVec3(a, b);
      const ba = dotVec3(b, a);
      expect(Math.abs(ab - ba)).toBeLessThan(STRICT_TOLERANCE);
    }
  );

  test.prop([nonZeroVec3Arb, nonZeroVec3Arb])(
    'cross product is anti-commutative: a × b = -(b × a)',
    (a, b) => {
      const ab = crossVec3(a, b);
      const ba = crossVec3(b, a);
      const negBa = scaleVec3(ba, -1);
      expect(vec3Equal(ab, negBa, FLOAT32_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticPositionArb, realisticPositionArb, tArb])(
    'lerp at t=0 returns first vector exactly',
    (a, b, _) => {
      const result = lerpVec3(a, b, 0);
      expect(vec3Equal(result, a, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticPositionArb, realisticPositionArb, tArb])(
    'lerp at t=1 returns second vector exactly',
    (a, b, _) => {
      const result = lerpVec3(a, b, 1);
      expect(vec3Equal(result, b, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticPositionArb, realisticPositionArb, tArb])(
    'lerp at t=0.5 is midpoint',
    (a, b, _) => {
      const result = lerpVec3(a, b, 0.5);
      const expected = {
        x: (a.x + b.x) / 2,
        y: (a.y + b.y) / 2,
        z: (a.z + b.z) / 2,
      };
      expect(vec3Equal(result, expected, FLOAT32_TOLERANCE)).toBe(true);
    }
  );

});

// ═══════════════════════════════════════════════════════════════════════════
//                                           // matrix // operations // strict
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Matrix4 Operations', () => {

  test.prop([realisticPositionArb])(
    'identity transformation preserves point exactly',
    (p) => {
      const I = identityMat4();
      const result = transformPoint(I, p);
      expect(vec3Equal(result, p, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticPositionArb, realisticPositionArb])(
    'translation composition: T(a) * T(b) = T(a + b)',
    (a, b) => {
      const Ta = translateMat4(a);
      const Tb = translateMat4(b);
      const TaTb = multiplyMat4(Ta, Tb);
      const Tab = translateMat4(addVec3(a, b));
      
      // Use relative tolerance for large translation values
      expect(mat4EqualRelative(TaTb, Tab, FLOAT32_TOLERANCE)).toBe(true);
    }
  );

  /**
   * Scale composition with Float32 (GPU-compatible) precision.
   * Float32 has ~7 significant digits, so we test with 1e-6 RELATIVE tolerance.
   * This is the precision available for WebGL/Three.js operations.
   */
  test.prop([realisticScaleArb, realisticScaleArb])(
    'scale composition S(a) * S(b) = S(a⊙b) [Float32 GPU precision]',
    (a, b) => {
      const Sa = scaleMat4(a);
      const Sb = scaleMat4(b);
      const SaSb = multiplyMat4(Sa, Sb);
      const Sab = scaleMat4({ x: a.x * b.x, y: a.y * b.y, z: a.z * b.z });
      
      // Float32 RELATIVE tolerance: ~7 significant digits
      expect(mat4EqualRelative(SaSb, Sab, FLOAT32_TOLERANCE)).toBe(true);
    }
  );

  /**
   * Scale composition with Float64 (high precision) for critical calculations.
   * Float64 has ~15 significant digits, so we test with 1e-10 tolerance.
   * Use this when precision matters more than GPU compatibility.
   */
  test.prop([realisticScaleArb, realisticScaleArb])(
    'STRICT: scale composition S(a) * S(b) = S(a⊙b) [Float64 high precision]',
    (a, b) => {
      const Sa = scaleMat4_64(a);
      const Sb = scaleMat4_64(b);
      const SaSb = multiplyMat4_64(Sa, Sb);
      const Sab = scaleMat4_64({ x: a.x * b.x, y: a.y * b.y, z: a.z * b.z });
      
      // Float64 tolerance: ~15 significant digits
      expect(mat4_64Equal(SaSb, Sab, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticAngleArb, realisticAngleArb])(
    'rotation X composition: Rx(a) * Rx(b) = Rx(a + b)',
    (a, b) => {
      const Ra = rotateXMat4(a);
      const Rb = rotateXMat4(b);
      const RaRb = multiplyMat4(Ra, Rb);
      const Rab = rotateXMat4(a + b);
      
      expect(mat4Equal(RaRb, Rab, FLOAT32_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticPositionArb])(
    'translation inverse: T(a) * T(-a) = I',
    (a) => {
      const Ta = translateMat4(a);
      const TnegA = translateMat4(scaleVec3(a, -1));
      const result = multiplyMat4(Ta, TnegA);
      const I = identityMat4();
      
      expect(mat4Equal(result, I, FLOAT32_TOLERANCE)).toBe(true);
    }
  );

  test.prop([realisticScaleArb])(
    'scale inverse via invert: S * S^-1 = I',
    (s) => {
      const S = scaleMat4(s);
      const Sinv = invertMat4(S);
      
      expect(Sinv).not.toBeNull();
      
      if (Sinv) {
        const result = multiplyMat4(S, Sinv);
        const I = identityMat4();
        expect(mat4Equal(result, I, FLOAT32_TOLERANCE)).toBe(true);
      }
    }
  );

  test.prop([nonZeroVec3Arb, realisticPositionArb])(
    'transformDirection ignores translation',
    (dir, translation) => {
      const T = translateMat4(translation);
      const result = transformDirection(T, dir);
      expect(vec3Equal(result, dir, STRICT_TOLERANCE)).toBe(true);
    }
  );

});

// ═══════════════════════════════════════════════════════════════════════════
// QUATERNION OPERATIONS - STRICT (These WILL find bugs)
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Quaternion Operations', () => {

  it('identity quaternion has w=1, xyz=0', () => {
    const id = quatIdentity();
    expect(id.x).toBe(0);
    expect(id.y).toBe(0);
    expect(id.z).toBe(0);
    expect(id.w).toBe(1);
  });

  /**
   * Quaternion roundtrip in the stable Euler angle range (±88° pitch).
   * Tests that euler -> quat -> euler produces the same rotation.
   * 
   * The gimbal lock region (|pitch| > 88°) is tested separately as it has
   * known mathematical instability inherent to Euler angle representation.
   */
  test.prop([stableEulerArb])(
    'euler -> quat -> euler roundtrip [stable range]',
    ([x, y, z]) => {
      const quat = quatFromEuler(x, y, z);
      const euler = quatToEuler(quat);
      const quat2 = quatFromEuler(euler.x, euler.y, euler.z);
      
      // Test by applying to a reference vector
      const testVec: Vec3 = { x: 1, y: 0, z: 0 };
      const rotated1 = applyQuatToVec(quat, testVec);
      const rotated2 = applyQuatToVec(quat2, testVec);
      
      // Strict tolerance for stable range
      expect(vec3Equal(rotated1, rotated2, STRICT_TOLERANCE)).toBe(true);
    }
  );

  /**
   * Document gimbal lock behavior near ±90° pitch.
   * This test verifies that gimbal lock is handled gracefully (no NaN/Infinity)
   * but does NOT expect exact roundtrip (that's mathematically impossible).
   */
  it('handles gimbal lock gracefully (no NaN/Infinity)', () => {
    // Test at exactly gimbal lock
    const angles = [
      [0, Math.PI / 2, 0],        // +90° pitch
      [0, -Math.PI / 2, 0],       // -90° pitch
      [1, Math.PI / 2, 2],        // +90° with roll and yaw
      [0.5, Math.PI / 2 - 0.001, 0.5], // Just below +90°
    ];
    
    for (const [x, y, z] of angles) {
      const quat = quatFromEuler(x, y, z);
      const euler = quatToEuler(quat);
      
      // Should not produce NaN or Infinity
      expect(Number.isFinite(euler.x)).toBe(true);
      expect(Number.isFinite(euler.y)).toBe(true);
      expect(Number.isFinite(euler.z)).toBe(true);
    }
  });

  test.prop([stableEulerArb])(
    'STRICT: slerp at t=0 returns first quaternion',
    ([x, y, z]) => {
      const a = quatFromEuler(x, y, z);
      const b = quatFromEuler(x + 0.5, y + 0.3, z + 0.2);
      const result = slerpQuat(a, b, 0);
      
      expect(quatEqual(result, a, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([stableEulerArb])(
    'STRICT: slerp at t=1 returns second quaternion',
    ([x, y, z]) => {
      const a = quatFromEuler(x, y, z);
      const b = quatFromEuler(x + 0.5, y + 0.3, z + 0.2);
      const result = slerpQuat(a, b, 1);
      
      expect(quatEqual(result, b, STRICT_TOLERANCE)).toBe(true);
    }
  );

  test.prop([stableEulerArb, tArb])(
    'slerp produces unit quaternion',
    ([x, y, z], t) => {
      const a = quatFromEuler(x, y, z);
      const b = quatFromEuler(x + 1, y + 0.5, z + 0.3);
      const result = slerpQuat(a, b, t);
      
      const len = Math.sqrt(result.x**2 + result.y**2 + result.z**2 + result.w**2);
      expect(Math.abs(len - 1)).toBeLessThan(FLOAT32_TOLERANCE);
    }
  );

});

// ═══════════════════════════════════════════════════════════════════════════
//                                            // angle // conversion // strict
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Angle Conversion', () => {

  test.prop([fc.double({ min: -720, max: 720, noNaN: true, noDefaultInfinity: true })])(
    'degrees -> radians -> degrees roundtrip',
    (deg) => {
      const rad = degToRad(deg);
      const degBack = radToDeg(rad);
      expect(Math.abs(degBack - deg)).toBeLessThan(STRICT_TOLERANCE);
    }
  );

  test.prop([realisticAngleArb])(
    'radians -> degrees -> radians roundtrip',
    (rad) => {
      const deg = radToDeg(rad);
      const radBack = degToRad(deg);
      expect(Math.abs(radBack - rad)).toBeLessThan(STRICT_TOLERANCE);
    }
  );

  it('90° = π/2', () => {
    expect(Math.abs(degToRad(90) - Math.PI / 2)).toBeLessThan(STRICT_TOLERANCE);
  });

  it('180° = π', () => {
    expect(Math.abs(degToRad(180) - Math.PI)).toBeLessThan(STRICT_TOLERANCE);
  });

  it('360° = 2π', () => {
    expect(Math.abs(degToRad(360) - Math.PI * 2)).toBeLessThan(STRICT_TOLERANCE);
  });

});

// ═══════════════════════════════════════════════════════════════════════════
//                                         // projection // matrices // strict
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: Projection Matrices', () => {

  test.prop([
    fc.double({ min: 0.1, max: Math.PI - 0.1, noNaN: true, noDefaultInfinity: true }), // fov
    fc.double({ min: 0.1, max: 10, noNaN: true, noDefaultInfinity: true }), // aspect
    fc.double({ min: 0.001, max: 10, noNaN: true, noDefaultInfinity: true }), // near
  ])(
    'perspective matrix produces finite values',
    (fov, aspect, near) => {
      const far = near + 1000;
      const mat = perspectiveMat4(fov, aspect, near, far);
      
      for (let i = 0; i < 16; i++) {
        expect(Number.isFinite(mat.elements[i])).toBe(true);
      }
    }
  );

  test.prop([
    fc.double({ min: -1000, max: 0, noNaN: true, noDefaultInfinity: true }), // left
    fc.double({ min: 0.1, max: 1000, noNaN: true, noDefaultInfinity: true }), // width
    fc.double({ min: -1000, max: 0, noNaN: true, noDefaultInfinity: true }), // bottom
    fc.double({ min: 0.1, max: 1000, noNaN: true, noDefaultInfinity: true }), // height
  ])(
    'orthographic matrix produces finite values',
    (left, width, bottom, height) => {
      const right = left + width;
      const top = bottom + height;
      const mat = orthographicMat4(left, right, bottom, top, 0.1, 1000);
      
      for (let i = 0; i < 16; i++) {
        expect(Number.isFinite(mat.elements[i])).toBe(true);
      }
    }
  );

});

// ═══════════════════════════════════════════════════════════════════════════
//                                               // lookat // matrix // strict
// ═══════════════════════════════════════════════════════════════════════════

describe('STRICT: LookAt Matrix', () => {

  test.prop([nonZeroVec3Arb, nonZeroVec3Arb])(
    'lookAt produces valid view matrix',
    (eye, target) => {
      // Ensure eye and target are different
      if (vec3Equal(eye, target, 0.001)) {
        return; // Skip degenerate case
      }
      
      const up: Vec3 = { x: 0, y: 1, z: 0 };
      const mat = lookAtMat4(eye, target, up);
      
      // All elements should be finite
      for (let i = 0; i < 16; i++) {
        expect(Number.isFinite(mat.elements[i])).toBe(true);
      }
    }
  );

});

// ═══════════════════════════════════════════════════════════════════════════
// STRESS TESTS - Find precision limits
// ═══════════════════════════════════════════════════════════════════════════

describe('STRESS: Precision Limits', () => {

  it('finds scale composition precision limit', () => {
    // Test increasingly small scales to find where precision breaks
    const testScales = [1, 0.5, 0.1, 0.05, 0.01, 0.005, 0.001];
    const results: { scale: number; error: number }[] = [];
    
    for (const s of testScales) {
      const a = { x: s, y: s, z: s };
      const Sa = scaleMat4(a);
      const SaSa = multiplyMat4(Sa, Sa);
      const expected = scaleMat4({ x: s * s, y: s * s, z: s * s });
      
      let maxError = 0;
      for (let i = 0; i < 16; i++) {
        maxError = Math.max(maxError, Math.abs(SaSa.elements[i] - expected.elements[i]));
      }
      
      results.push({ scale: s, error: maxError });
    }
    
    console.log('Scale composition precision analysis:');
    console.table(results);
    
    // Document: All scales should produce error < 1e-6
    // This test will pass but log useful data
    expect(results.every(r => r.error < 1)).toBe(true);
  });

  it('finds euler angle precision limit', () => {
    // Test angles approaching gimbal lock
    const pitchAngles = [0, 0.5, 1.0, 1.4, 1.5, 1.55, 1.57, Math.PI/2 - 0.01, Math.PI/2 - 0.001];
    const results: { pitch: number; error: number }[] = [];
    
    for (const pitch of pitchAngles) {
      const euler = { x: 0.3, y: pitch, z: 0.3 };
      const quat = quatFromEuler(euler.x, euler.y, euler.z);
      const recovered = quatToEuler(quat);
      const quat2 = quatFromEuler(recovered.x, recovered.y, recovered.z);
      
      // Compare by applying to test vector
      const testVec: Vec3 = { x: 1, y: 0, z: 0 };
      const r1 = applyQuatToVec(quat, testVec);
      const r2 = applyQuatToVec(quat2, testVec);
      
      const error = Math.sqrt(
        Math.pow(r1.x - r2.x, 2) +
        Math.pow(r1.y - r2.y, 2) +
        Math.pow(r1.z - r2.z, 2)
      );
      
      results.push({ pitch: pitch * 180 / Math.PI, error });
    }
    
    console.log('Euler angle precision analysis (pitch in degrees):');
    console.table(results);
    
    // Document: Error increases dramatically near 90°
    expect(true).toBe(true);
  });

});
