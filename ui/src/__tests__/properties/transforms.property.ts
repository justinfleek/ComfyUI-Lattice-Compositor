/**
 * TRANSFORM Property Tests
 * 
 * Mathematical properties that MUST hold for transform operations.
 * These are invariants from linear algebra that ensure correctness.
 */

import { describe, expect } from 'vitest';
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
  type Vec3,
  type Mat4,
  type Quat,
} from '@/services/math3d';

// ============================================================================
// ARBITRARIES
// ============================================================================

/**
 * 3D Vector with reasonable values
 */
const vec3Arb = fc.record({
  x: fc.double({ min: -1000, max: 1000, noNaN: true }),
  y: fc.double({ min: -1000, max: 1000, noNaN: true }),
  z: fc.double({ min: -1000, max: 1000, noNaN: true }),
});

/**
 * Small vector for numerical stability in tests
 */
const smallVec3Arb = fc.record({
  x: fc.double({ min: -10, max: 10, noNaN: true }),
  y: fc.double({ min: -10, max: 10, noNaN: true }),
  z: fc.double({ min: -10, max: 10, noNaN: true }),
});

/**
 * Non-zero vector (for normalization tests)
 */
const nonZeroVec3Arb = fc.record({
  x: fc.double({ min: -1000, max: 1000, noNaN: true }),
  y: fc.double({ min: -1000, max: 1000, noNaN: true }),
  z: fc.double({ min: -1000, max: 1000, noNaN: true }),
}).filter(v => Math.abs(v.x) + Math.abs(v.y) + Math.abs(v.z) > 0.001);

/**
 * Scale vector (positive non-zero)
 */
const scaleVecArb = fc.record({
  x: fc.double({ min: 0.01, max: 10, noNaN: true }),
  y: fc.double({ min: 0.01, max: 10, noNaN: true }),
  z: fc.double({ min: 0.01, max: 10, noNaN: true }),
});

/**
 * Angle in radians (reasonable range)
 */
const angleArb = fc.double({ min: -Math.PI * 4, max: Math.PI * 4, noNaN: true });

/**
 * Angle in degrees
 */
const degreesArb = fc.double({ min: -720, max: 720, noNaN: true });

/**
 * Normalized t value (0-1)
 */
const normalizedArb = fc.double({ min: 0, max: 1, noNaN: true });

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/**
 * Compare two vectors with tolerance
 */
function vec3Equal(a: Vec3, b: Vec3, epsilon = 1e-6): boolean {
  return (
    Math.abs(a.x - b.x) < epsilon &&
    Math.abs(a.y - b.y) < epsilon &&
    Math.abs(a.z - b.z) < epsilon
  );
}

/**
 * Compare two matrices with tolerance
 */
function mat4Equal(a: Mat4, b: Mat4, epsilon = 1e-6): boolean {
  for (let i = 0; i < 16; i++) {
    if (Math.abs(a.elements[i] - b.elements[i]) > epsilon) {
      return false;
    }
  }
  return true;
}

/**
 * Compare two quaternions with tolerance (handles sign ambiguity)
 */
function quatEqual(a: Quat, b: Quat, epsilon = 1e-6): boolean {
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

describe('TRANSFORM Properties', () => {

  // =========================================================================
  // VECTOR OPERATIONS
  // =========================================================================

  describe('Vector3 operations', () => {

    test.prop([vec3Arb, vec3Arb])(
      'addition is commutative: a + b = b + a',
      (a, b) => {
        const ab = addVec3(a, b);
        const ba = addVec3(b, a);
        expect(vec3Equal(ab, ba)).toBe(true);
      }
    );

    test.prop([vec3Arb, vec3Arb, vec3Arb])(
      'addition is associative: (a + b) + c = a + (b + c)',
      (a, b, c) => {
        const left = addVec3(addVec3(a, b), c);
        const right = addVec3(a, addVec3(b, c));
        expect(vec3Equal(left, right)).toBe(true);
      }
    );

    test.prop([vec3Arb])(
      'addition identity: a + 0 = a',
      (a) => {
        const zero: Vec3 = { x: 0, y: 0, z: 0 };
        const result = addVec3(a, zero);
        expect(vec3Equal(result, a)).toBe(true);
      }
    );

    test.prop([vec3Arb])(
      'subtraction is inverse of addition: a - a = 0',
      (a) => {
        const result = subVec3(a, a);
        const zero: Vec3 = { x: 0, y: 0, z: 0 };
        expect(vec3Equal(result, zero)).toBe(true);
      }
    );

    test.prop([vec3Arb, fc.double({ min: -100, max: 100, noNaN: true })])(
      'scalar multiplication distributes: s * a',
      (a, s) => {
        const result = scaleVec3(a, s);
        expect(result.x).toBeCloseTo(a.x * s, 10);
        expect(result.y).toBeCloseTo(a.y * s, 10);
        expect(result.z).toBeCloseTo(a.z * s, 10);
      }
    );

    test.prop([nonZeroVec3Arb])(
      'normalized vector has length 1',
      (v) => {
        const normalized = normalizeVec3(v);
        const len = lengthVec3(normalized);
        expect(len).toBeCloseTo(1, 6);
      }
    );

    test.prop([vec3Arb, vec3Arb])(
      'dot product is commutative: a · b = b · a',
      (a, b) => {
        const ab = dotVec3(a, b);
        const ba = dotVec3(b, a);
        expect(ab).toBeCloseTo(ba, 10);
      }
    );

    test.prop([nonZeroVec3Arb, nonZeroVec3Arb])(
      'cross product is anti-commutative: a × b = -(b × a)',
      (a, b) => {
        const ab = crossVec3(a, b);
        const ba = crossVec3(b, a);
        expect(vec3Equal(ab, scaleVec3(ba, -1))).toBe(true);
      }
    );

    test.prop([nonZeroVec3Arb])(
      'cross product with self is zero: a × a = 0',
      (a) => {
        const result = crossVec3(a, a);
        const zero: Vec3 = { x: 0, y: 0, z: 0 };
        expect(vec3Equal(result, zero)).toBe(true);
      }
    );

    test.prop([vec3Arb, vec3Arb, normalizedArb])(
      'lerp at t=0 returns first vector',
      (a, b, _t) => {
        const result = lerpVec3(a, b, 0);
        expect(vec3Equal(result, a)).toBe(true);
      }
    );

    test.prop([vec3Arb, vec3Arb, normalizedArb])(
      'lerp at t=1 returns second vector',
      (a, b, _t) => {
        const result = lerpVec3(a, b, 1);
        expect(vec3Equal(result, b)).toBe(true);
      }
    );

    test.prop([vec3Arb, vec3Arb, normalizedArb])(
      'lerp result is between endpoints',
      (a, b, t) => {
        const result = lerpVec3(a, b, t);
        
        // For each component, result should be between a and b
        const checkBetween = (r: number, va: number, vb: number) => {
          const min = Math.min(va, vb);
          const max = Math.max(va, vb);
          return r >= min - 1e-10 && r <= max + 1e-10;
        };

        expect(checkBetween(result.x, a.x, b.x)).toBe(true);
        expect(checkBetween(result.y, a.y, b.y)).toBe(true);
        expect(checkBetween(result.z, a.z, b.z)).toBe(true);
      }
    );

  });

  // =========================================================================
  // MATRIX OPERATIONS
  // =========================================================================

  describe('Matrix4 operations', () => {

    test.prop([vec3Arb])(
      'identity transformation: I * p = p',
      (p) => {
        const I = identityMat4();
        const result = transformPoint(I, p);
        expect(vec3Equal(result, p)).toBe(true);
      }
    );

    test.prop([smallVec3Arb, smallVec3Arb])(
      'translation composition: T(a) * T(b) = T(a + b)',
      (a, b) => {
        const Ta = translateMat4(a);
        const Tb = translateMat4(b);
        const TaTb = multiplyMat4(Ta, Tb);
        const Tab = translateMat4(addVec3(a, b));
        
        expect(mat4Equal(TaTb, Tab)).toBe(true);
      }
    );

    test.prop([scaleVecArb, scaleVecArb])(
      'scale composition: S(a) * S(b) = S(a ⊙ b) (component-wise)',
      (a, b) => {
        const Sa = scaleMat4(a);
        const Sb = scaleMat4(b);
        const SaSb = multiplyMat4(Sa, Sb);
        const Sab = scaleMat4({ x: a.x * b.x, y: a.y * b.y, z: a.z * b.z });
        
        expect(mat4Equal(SaSb, Sab)).toBe(true);
      }
    );

    test.prop([angleArb, angleArb])(
      'rotation X composition: Rx(a) * Rx(b) = Rx(a + b)',
      (a, b) => {
        const Ra = rotateXMat4(a);
        const Rb = rotateXMat4(b);
        const RaRb = multiplyMat4(Ra, Rb);
        const Rab = rotateXMat4(a + b);
        
        expect(mat4Equal(RaRb, Rab, 1e-5)).toBe(true);
      }
    );

    test.prop([angleArb, angleArb])(
      'rotation Y composition: Ry(a) * Ry(b) = Ry(a + b)',
      (a, b) => {
        const Ra = rotateYMat4(a);
        const Rb = rotateYMat4(b);
        const RaRb = multiplyMat4(Ra, Rb);
        const Rab = rotateYMat4(a + b);
        
        expect(mat4Equal(RaRb, Rab, 1e-5)).toBe(true);
      }
    );

    test.prop([angleArb, angleArb])(
      'rotation Z composition: Rz(a) * Rz(b) = Rz(a + b)',
      (a, b) => {
        const Ra = rotateZMat4(a);
        const Rb = rotateZMat4(b);
        const RaRb = multiplyMat4(Ra, Rb);
        const Rab = rotateZMat4(a + b);
        
        expect(mat4Equal(RaRb, Rab, 1e-5)).toBe(true);
      }
    );

    test.prop([smallVec3Arb])(
      'translation inverse: T(a) * T(-a) = I',
      (a) => {
        const Ta = translateMat4(a);
        const TnegA = translateMat4(scaleVec3(a, -1));
        const result = multiplyMat4(Ta, TnegA);
        const I = identityMat4();
        
        expect(mat4Equal(result, I)).toBe(true);
      }
    );

    test.prop([angleArb])(
      'rotation Z inverse: Rz(a) * Rz(-a) = I',
      (a) => {
        const Ra = rotateZMat4(a);
        const RnegA = rotateZMat4(-a);
        const result = multiplyMat4(Ra, RnegA);
        const I = identityMat4();
        
        expect(mat4Equal(result, I, 1e-5)).toBe(true);
      }
    );

    test.prop([scaleVecArb])(
      'scale inverse property via invert',
      (s) => {
        const S = scaleMat4(s);
        const Sinv = invertMat4(S);
        
        expect(Sinv).not.toBeNull();
        
        if (Sinv) {
          const result = multiplyMat4(S, Sinv);
          const I = identityMat4();
          expect(mat4Equal(result, I, 1e-5)).toBe(true);
        }
      }
    );

    test.prop([smallVec3Arb, smallVec3Arb])(
      'transform point with translation: T(v) * p = p + v',
      (v, p) => {
        const T = translateMat4(v);
        const result = transformPoint(T, p);
        const expected = addVec3(p, v);
        
        expect(vec3Equal(result, expected)).toBe(true);
      }
    );

    test.prop([nonZeroVec3Arb, smallVec3Arb])(
      'transformDirection ignores translation',
      (dir, translation) => {
        const T = translateMat4(translation);
        const result = transformDirection(T, dir);
        
        // Direction should be unchanged by pure translation
        expect(vec3Equal(result, dir)).toBe(true);
      }
    );

  });

  // =========================================================================
  // MATRIX ASSOCIATIVITY
  // =========================================================================

  describe('Matrix associativity', () => {

    test.prop([smallVec3Arb, smallVec3Arb, smallVec3Arb])(
      'matrix multiplication is associative: (A * B) * C = A * (B * C)',
      (a, b, c) => {
        const A = translateMat4(a);
        const B = translateMat4(b);
        const C = translateMat4(c);
        
        const left = multiplyMat4(multiplyMat4(A, B), C);
        const right = multiplyMat4(A, multiplyMat4(B, C));
        
        expect(mat4Equal(left, right)).toBe(true);
      }
    );

    test.prop([angleArb, scaleVecArb, smallVec3Arb])(
      'mixed transform composition is associative',
      (angle, scale, translation) => {
        const R = rotateZMat4(angle);
        const S = scaleMat4(scale);
        const T = translateMat4(translation);
        
        const left = multiplyMat4(multiplyMat4(R, S), T);
        const right = multiplyMat4(R, multiplyMat4(S, T));
        
        expect(mat4Equal(left, right, 1e-5)).toBe(true);
      }
    );

  });

  // =========================================================================
  // QUATERNION OPERATIONS
  // =========================================================================

  describe('Quaternion operations', () => {

    test.prop([])(
      'identity quaternion has w=1, xyz=0',
      () => {
        const id = quatIdentity();
        expect(id.x).toBe(0);
        expect(id.y).toBe(0);
        expect(id.z).toBe(0);
        expect(id.w).toBe(1);
      }
    );

    test.prop([
      fc.double({ min: -Math.PI, max: Math.PI, noNaN: true }),
      fc.double({ min: -Math.PI / 2 + 0.1, max: Math.PI / 2 - 0.1, noNaN: true }), // Avoid gimbal lock
      fc.double({ min: -Math.PI, max: Math.PI, noNaN: true }),
    ])(
      'quaternion roundtrip: euler -> quat -> euler (avoiding gimbal lock)',
      (x, y, z) => {
        const quat = quatFromEuler(x, y, z);
        const euler = quatToEuler(quat);
        
        // Reconstruct quaternion from recovered euler
        const quat2 = quatFromEuler(euler.x, euler.y, euler.z);
        
        // The quaternions should be equivalent (same rotation)
        expect(quatEqual(quat, quat2, 1e-5)).toBe(true);
      }
    );

    test.prop([
      fc.double({ min: -Math.PI, max: Math.PI, noNaN: true }),
      fc.double({ min: -Math.PI / 2, max: Math.PI / 2, noNaN: true }),
      fc.double({ min: -Math.PI, max: Math.PI, noNaN: true }),
    ])(
      'slerp at t=0 returns first quaternion',
      (x, y, z) => {
        const a = quatFromEuler(x, y, z);
        const b = quatFromEuler(x + 0.5, y + 0.3, z + 0.2);
        const result = slerpQuat(a, b, 0);
        
        expect(quatEqual(result, a, 1e-5)).toBe(true);
      }
    );

    test.prop([
      fc.double({ min: -Math.PI, max: Math.PI, noNaN: true }),
      fc.double({ min: -Math.PI / 2, max: Math.PI / 2, noNaN: true }),
      fc.double({ min: -Math.PI, max: Math.PI, noNaN: true }),
    ])(
      'slerp at t=1 returns second quaternion',
      (x, y, z) => {
        const a = quatFromEuler(x, y, z);
        const b = quatFromEuler(x + 0.5, y + 0.3, z + 0.2);
        const result = slerpQuat(a, b, 1);
        
        expect(quatEqual(result, b, 1e-5)).toBe(true);
      }
    );

  });

  // =========================================================================
  // ANGLE CONVERSION
  // =========================================================================

  describe('Angle conversion', () => {

    test.prop([degreesArb])(
      'degrees -> radians -> degrees roundtrip',
      (deg) => {
        const rad = degToRad(deg);
        const degBack = radToDeg(rad);
        expect(degBack).toBeCloseTo(deg, 10);
      }
    );

    test.prop([angleArb])(
      'radians -> degrees -> radians roundtrip',
      (rad) => {
        const deg = radToDeg(rad);
        const radBack = degToRad(deg);
        expect(radBack).toBeCloseTo(rad, 10);
      }
    );

    test.prop([])(
      '90 degrees = PI/2 radians',
      () => {
        expect(degToRad(90)).toBeCloseTo(Math.PI / 2, 10);
        expect(radToDeg(Math.PI / 2)).toBeCloseTo(90, 10);
      }
    );

    test.prop([])(
      '180 degrees = PI radians',
      () => {
        expect(degToRad(180)).toBeCloseTo(Math.PI, 10);
        expect(radToDeg(Math.PI)).toBeCloseTo(180, 10);
      }
    );

  });

});
