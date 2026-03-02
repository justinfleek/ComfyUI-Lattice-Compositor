-- | Property-based tests for 3D math: Vec3, Mat4, Quat
-- | Ported from ui/src/__tests__/services/transforms.property.test.ts

module Test.Lattice.Services.TransformProps where

import Prelude
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.QuickCheck (quickCheck, Result, (===))
import Test.Lattice.TestHelpers (assertCloseTo)
import Math (abs, pi, sqrt, cos, sin) as Math
import Lattice.Services.Math3D.Vec3 as V
import Lattice.Services.Math3D.Vec3 (Vec3(..))
import Lattice.Services.Math3D.Mat4 as M4
import Lattice.Services.Math3D.Mat4 (Mat4(..), InvertResult(..))
import Lattice.Services.Math3D.Quat as Q
import Lattice.Services.Math3D.Quat (Quat(..))

-- | Tolerance constants
strictTol :: Number
strictTol = 1e-10

float32Tol :: Number
float32Tol = 1e-5

-- | Check if two Vec3 are close
vec3Close :: Vec3 -> Vec3 -> Number -> Boolean
vec3Close (Vec3 a) (Vec3 b) eps =
  Math.abs (a.x - b.x) < eps &&
  Math.abs (a.y - b.y) < eps &&
  Math.abs (a.z - b.z) < eps

-- | Check if two Mat4 are close (check all 16 elements)
mat4Close :: Mat4 -> Mat4 -> Number -> Boolean
mat4Close (Mat4 a) (Mat4 b) eps =
  Math.abs (a.m00 - b.m00) < eps &&
  Math.abs (a.m10 - b.m10) < eps &&
  Math.abs (a.m20 - b.m20) < eps &&
  Math.abs (a.m30 - b.m30) < eps &&
  Math.abs (a.m01 - b.m01) < eps &&
  Math.abs (a.m11 - b.m11) < eps &&
  Math.abs (a.m21 - b.m21) < eps &&
  Math.abs (a.m31 - b.m31) < eps &&
  Math.abs (a.m02 - b.m02) < eps &&
  Math.abs (a.m12 - b.m12) < eps &&
  Math.abs (a.m22 - b.m22) < eps &&
  Math.abs (a.m32 - b.m32) < eps &&
  Math.abs (a.m03 - b.m03) < eps &&
  Math.abs (a.m13 - b.m13) < eps &&
  Math.abs (a.m23 - b.m23) < eps &&
  Math.abs (a.m33 - b.m33) < eps

-- | Check if two Quats are close (handles q ≈ -q equivalence)
quatClose :: Quat -> Quat -> Number -> Boolean
quatClose (Quat a) (Quat b) eps =
  let direct =
        Math.abs (a.x - b.x) < eps &&
        Math.abs (a.y - b.y) < eps &&
        Math.abs (a.z - b.z) < eps &&
        Math.abs (a.w - b.w) < eps
      negated =
        Math.abs (a.x + b.x) < eps &&
        Math.abs (a.y + b.y) < eps &&
        Math.abs (a.z + b.z) < eps &&
        Math.abs (a.w + b.w) < eps
  in direct || negated

spec :: Spec Unit
spec = describe "STRICT: Transform Properties" do

  describe "Vector3 Operations" do
    it "addition is commutative: a + b = b + a" do
      let pairs =
            [ { a: V.vec3 1.0 2.0 3.0, b: V.vec3 4.0 5.0 6.0 }
            , { a: V.vec3 (-1.0) 0.0 1.0, b: V.vec3 100.0 (-50.0) 0.0 }
            , { a: V.vec3 0.001 0.002 0.003, b: V.vec3 1000.0 2000.0 3000.0 }
            ]
      map (\p -> V.add p.a p.b == V.add p.b p.a) pairs
        `shouldEqual` [true, true, true]

    it "subtraction inverse: a - a = zero" do
      let vecs =
            [ V.vec3 1.0 2.0 3.0
            , V.vec3 (-100.0) 50.0 0.0
            , V.vec3 0.001 0.002 0.003
            ]
      map (\v -> vec3Close (V.sub v v) V.zero strictTol) vecs
        `shouldEqual` [true, true, true]

    it "normalization produces unit length" do
      let vecs =
            [ V.vec3 3.0 4.0 0.0
            , V.vec3 1.0 1.0 1.0
            , V.vec3 0.0 0.0 5.0
            , V.vec3 100.0 200.0 300.0
            ]
          results = map (\v ->
            let n = V.normalize v
                len = V.lengthVec3 n
            in Math.abs (len - 1.0) < 1e-10
          ) vecs
      results `shouldEqual` [true, true, true, true]

    it "zero vector normalizes to zero" do
      V.normalize V.zero `shouldEqual` V.zero

    it "dot product is commutative" do
      let a = V.vec3 1.0 2.0 3.0
          b = V.vec3 4.0 5.0 6.0
      assertCloseTo (V.dot a b) (V.dot b a) strictTol

    it "cross product is anti-commutative: a×b = -(b×a)" do
      let a = V.vec3 1.0 0.0 0.0
          b = V.vec3 0.0 1.0 0.0
          axb = V.cross a b
          bxa = V.cross b a
      vec3Close axb (V.neg bxa) strictTol `shouldEqual` true

    it "lerp at t=0 returns first vector" do
      let a = V.vec3 1.0 2.0 3.0
          b = V.vec3 10.0 20.0 30.0
      V.lerp a b 0.0 `shouldEqual` a

    it "lerp at t=1 returns second vector" do
      let a = V.vec3 1.0 2.0 3.0
          b = V.vec3 10.0 20.0 30.0
      V.lerp a b 1.0 `shouldEqual` b

    it "lerp at t=0.5 returns midpoint" do
      let a = V.vec3 0.0 0.0 0.0
          b = V.vec3 10.0 20.0 30.0
          mid = V.lerp a b 0.5
      vec3Close mid (V.vec3 5.0 10.0 15.0) strictTol `shouldEqual` true

  describe "Matrix4 Operations" do
    it "identity preserves points" do
      let points =
            [ V.vec3 1.0 2.0 3.0
            , V.vec3 (-100.0) 50.0 0.0
            , V.vec3 0.0 0.0 0.0
            ]
      map (\p -> M4.transformPoint M4.identity p == p) points
        `shouldEqual` [true, true, true]

    it "translation composition: T(a) * T(b) = T(a+b)" do
      let a = V.vec3 10.0 20.0 30.0
          b = V.vec3 5.0 10.0 15.0
          composed = M4.multiply (M4.translate a) (M4.translate b)
          direct = M4.translate (V.add a b)
      mat4Close composed direct strictTol `shouldEqual` true

    it "translation inverse: T(a) * T(-a) = I" do
      let v = V.vec3 10.0 20.0 30.0
          composed = M4.multiply (M4.translate v) (M4.translate (V.neg v))
      mat4Close composed M4.identity strictTol `shouldEqual` true

    it "scale composition: S(a) * S(b) = S(a*b)" do
      let a = V.vec3 2.0 3.0 4.0
          b = V.vec3 5.0 6.0 7.0
          composed = M4.multiply (M4.scaleMat a) (M4.scaleMat b)
          direct = M4.scaleMat (V.mul a b)
      mat4Close composed direct float32Tol `shouldEqual` true

    it "rotation X composition: Rx(a) * Rx(b) = Rx(a+b)" do
      let a = 0.3
          b = 0.7
          composed = M4.multiply (M4.rotateX a) (M4.rotateX b)
          direct = M4.rotateX (a + b)
      mat4Close composed direct float32Tol `shouldEqual` true

    it "transformDirection ignores translation" do
      let t = M4.translate (V.vec3 100.0 200.0 300.0)
          dir = V.vec3 1.0 0.0 0.0
      M4.transformDirection t dir `shouldEqual` dir

    it "determinant of identity is 1" do
      assertCloseTo (M4.determinant M4.identity) 1.0 strictTol

    it "determinant of scale matrix is product of scales" do
      let s = M4.scaleMat (V.vec3 2.0 3.0 4.0)
      assertCloseTo (M4.determinant s) 24.0 strictTol

    it "invert identity yields identity" do
      case M4.invert M4.identity of
        InvertSuccess inv -> mat4Close inv M4.identity strictTol `shouldEqual` true
        SingularMatrix -> false `shouldEqual` true  -- should not happen

    it "invert of scale: S * S^-1 = I" do
      let s = M4.scaleMat (V.vec3 2.0 3.0 4.0)
      case M4.invert s of
        InvertSuccess inv ->
          mat4Close (M4.multiply s inv) M4.identity float32Tol `shouldEqual` true
        SingularMatrix -> false `shouldEqual` true

    it "zero matrix is singular" do
      case M4.invert M4.zeroMat of
        SingularMatrix -> true `shouldEqual` true
        InvertSuccess _ -> false `shouldEqual` true

    it "transpose is self-inverse" do
      let m = M4.multiply (M4.rotateX 0.5) (M4.translate (V.vec3 1.0 2.0 3.0))
          mt = M4.transposeMat m
          mtt = M4.transposeMat mt
      mat4Close mtt m strictTol `shouldEqual` true

    it "lookAt produces finite matrix" do
      let eye = V.vec3 0.0 0.0 5.0
          target = V.vec3 0.0 0.0 0.0
          up = V.vec3 0.0 1.0 0.0
          Mat4 m = M4.lookAt eye target up
          allFinite =
            isFiniteNum m.m00 && isFiniteNum m.m10 && isFiniteNum m.m20 && isFiniteNum m.m30 &&
            isFiniteNum m.m01 && isFiniteNum m.m11 && isFiniteNum m.m21 && isFiniteNum m.m31 &&
            isFiniteNum m.m02 && isFiniteNum m.m12 && isFiniteNum m.m22 && isFiniteNum m.m32 &&
            isFiniteNum m.m03 && isFiniteNum m.m13 && isFiniteNum m.m23 && isFiniteNum m.m33
      allFinite `shouldEqual` true

    it "perspective produces finite matrix" do
      let Mat4 m = M4.perspective (Math.pi / 4.0) (16.0 / 9.0) 0.1 1000.0
          allFinite =
            isFiniteNum m.m00 && isFiniteNum m.m10 && isFiniteNum m.m20 && isFiniteNum m.m30 &&
            isFiniteNum m.m01 && isFiniteNum m.m11 && isFiniteNum m.m21 && isFiniteNum m.m31 &&
            isFiniteNum m.m02 && isFiniteNum m.m12 && isFiniteNum m.m22 && isFiniteNum m.m32 &&
            isFiniteNum m.m03 && isFiniteNum m.m13 && isFiniteNum m.m23 && isFiniteNum m.m33
      allFinite `shouldEqual` true

    it "orthographic produces finite matrix" do
      let Mat4 m = M4.orthographic (-10.0) 10.0 (-10.0) 10.0 0.1 100.0
          allFinite =
            isFiniteNum m.m00 && isFiniteNum m.m10 && isFiniteNum m.m20 && isFiniteNum m.m30 &&
            isFiniteNum m.m01 && isFiniteNum m.m11 && isFiniteNum m.m21 && isFiniteNum m.m31 &&
            isFiniteNum m.m02 && isFiniteNum m.m12 && isFiniteNum m.m22 && isFiniteNum m.m32 &&
            isFiniteNum m.m03 && isFiniteNum m.m13 && isFiniteNum m.m23 && isFiniteNum m.m33
      allFinite `shouldEqual` true

  describe "Quaternion Operations" do
    it "identity quaternion is (0,0,0,1)" do
      Q.identity `shouldEqual` Quat { x: 0.0, y: 0.0, z: 0.0, w: 1.0 }

    it "normalize preserves unit quaternion" do
      Q.normalize Q.identity `shouldEqual` Q.identity

    it "normalize rescales non-unit quaternion" do
      let q = Quat { x: 0.0, y: 0.0, z: 0.0, w: 2.0 }
          n = Q.normalize q
      quatClose n Q.identity strictTol `shouldEqual` true

    it "conjugate flips xyz, keeps w" do
      let q = Quat { x: 1.0, y: 2.0, z: 3.0, w: 4.0 }
          Quat c = Q.conjugate q
      c.x `shouldEqual` (-1.0)
      c.y `shouldEqual` (-2.0)
      c.z `shouldEqual` (-3.0)
      c.w `shouldEqual` 4.0

    it "multiply identity is identity: q * I = q" do
      let q = Q.fromEuler 0.5 0.3 0.1
      quatClose (Q.multiply q Q.identity) q strictTol `shouldEqual` true

    it "multiply by inverse gives identity: q * q^-1 = I" do
      let q = Q.fromEuler 0.5 0.3 0.1
          inv = Q.invert q
          result = Q.multiply q inv
      quatClose result Q.identity float32Tol `shouldEqual` true

    it "fromEuler -> toEuler roundtrip in stable range" do
      -- Avoid gimbal lock (pitch near ±90°)
      let cases =
            [ { x: 0.0, y: 0.0, z: 0.0 }
            , { x: 0.5, y: 0.3, z: 0.1 }
            , { x: (-0.5), y: 0.3, z: (-0.1) }
            , { x: 1.0, y: 0.5, z: 0.2 }
            ]
      map (\c ->
        let q = Q.fromEuler c.x c.y c.z
            Vec3 e = Q.toEuler q
        in Math.abs (e.x - c.x) < 0.01 &&
           Math.abs (e.y - c.y) < 0.01 &&
           Math.abs (e.z - c.z) < 0.01
      ) cases `shouldEqual` [true, true, true, true]

    it "gimbal lock does not produce NaN" do
      -- pitch at exactly ±90° (pi/2)
      let q = Q.fromEuler 0.0 (Math.pi / 2.0) 0.0
          Vec3 e = Q.toEuler q
      isFiniteNum e.x `shouldEqual` true
      isFiniteNum e.y `shouldEqual` true
      isFiniteNum e.z `shouldEqual` true

    it "fromAxisAngle -> toAxisAngle roundtrip" do
      let axis = V.normalize (V.vec3 1.0 1.0 0.0)
          angle = 1.0
          q = Q.fromAxisAngle axis angle
          Tuple axisOut angleOut = Q.toAxisAngle q
      assertCloseTo angleOut angle 0.01
      vec3Close (V.normalize axisOut) axis 0.01 `shouldEqual` true

    it "slerp at t=0 returns first quaternion" do
      let a = Q.fromEuler 0.0 0.0 0.0
          b = Q.fromEuler 1.0 0.0 0.0
      quatClose (Q.slerp a b 0.0) a float32Tol `shouldEqual` true

    it "slerp at t=1 returns second quaternion" do
      let a = Q.fromEuler 0.0 0.0 0.0
          b = Q.fromEuler 1.0 0.0 0.0
      quatClose (Q.slerp a b 1.0) b float32Tol `shouldEqual` true

    it "slerp preserves unit quaternion" do
      let a = Q.fromEuler 0.0 0.0 0.0
          b = Q.fromEuler 1.0 0.5 0.3
          mid = Q.slerp a b 0.5
          len = Q.lengthQuat mid
      assertCloseTo len 1.0 float32Tol

    it "rotateVec3 by identity returns original vector" do
      let v = V.vec3 1.0 2.0 3.0
      vec3Close (Q.rotateVec3 Q.identity v) v strictTol `shouldEqual` true

    it "90° rotation around Z maps X to Y" do
      let q = Q.fromAxisAngle V.unitZ (Math.pi / 2.0)
          rotated = Q.rotateVec3 q V.unitX
      -- X axis rotated 90° around Z should give Y axis
      vec3Close rotated V.unitY float32Tol `shouldEqual` true

    it "dotQuat is commutative" do
      let a = Q.fromEuler 0.5 0.3 0.1
          b = Q.fromEuler 0.1 0.2 0.3
      assertCloseTo (Q.dotQuat a b) (Q.dotQuat b a) strictTol

  describe "Vec3 conversion" do
    it "toArray -> fromArray roundtrip" do
      let v = V.vec3 1.0 2.0 3.0
      V.fromArray (V.toArray v) `shouldEqual` v

    it "fromArray with short array returns zero" do
      V.fromArray [1.0, 2.0] `shouldEqual` V.zero

  describe "Quat conversion" do
    it "toArray -> fromArray roundtrip" do
      let q = Q.quatFromComponents 0.1 0.2 0.3 0.9
      Q.fromArray (Q.toArray q) `shouldEqual` q

    it "fromArray with short array returns identity" do
      Q.fromArray [1.0, 2.0] `shouldEqual` Q.identity

-- | Helper: check if a number is finite (not NaN and not Infinity)
isFiniteNum :: Number -> Boolean
isFiniteNum n = n == n && n /= (1.0 / 0.0) && n /= (-(1.0 / 0.0))
