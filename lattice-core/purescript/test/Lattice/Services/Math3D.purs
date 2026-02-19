-- | Port of ui/src/__tests__/services/math3d.test.ts
-- |
-- | Tests 3D vector and matrix operations.
-- | Placeholder — full port in Wave 1.

module Test.Lattice.Services.Math3D (spec) where

import Prelude

import Data.Int (toNumber) as Int
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite, epsilon)

import Lattice.Services.Math3D.Vec3
  ( Vec3(..), vec3, zero, unitX, unitY, unitZ
  , add, sub, scale, neg, dot, cross
  , lengthSq, lengthVec3, distance, normalize
  , lerp
  )

spec :: Spec Unit
spec = do
  describe "Vec3 Operations" do
    describe "constructors" do
      it "vec3 creates vector with correct components" do
        let (Vec3 v) = vec3 1.0 2.0 3.0
        v.x `shouldEqual` 1.0
        v.y `shouldEqual` 2.0
        v.z `shouldEqual` 3.0

      it "zero is (0,0,0)" do
        let (Vec3 v) = zero
        v.x `shouldEqual` 0.0
        v.y `shouldEqual` 0.0
        v.z `shouldEqual` 0.0

    describe "basic operations" do
      it "add is component-wise" do
        let result = add (vec3 1.0 2.0 3.0) (vec3 4.0 5.0 6.0)
        let (Vec3 v) = result
        v.x `shouldEqual` 5.0
        v.y `shouldEqual` 7.0
        v.z `shouldEqual` 9.0

      it "sub is component-wise" do
        let result = sub (vec3 4.0 5.0 6.0) (vec3 1.0 2.0 3.0)
        let (Vec3 v) = result
        v.x `shouldEqual` 3.0
        v.y `shouldEqual` 3.0
        v.z `shouldEqual` 3.0

      it "scale multiplies all components" do
        let result = scale (vec3 1.0 2.0 3.0) 2.0
        let (Vec3 v) = result
        v.x `shouldEqual` 2.0
        v.y `shouldEqual` 4.0
        v.z `shouldEqual` 6.0

      it "neg negates all components" do
        let result = neg (vec3 1.0 (-2.0) 3.0)
        let (Vec3 v) = result
        v.x `shouldEqual` (-1.0)
        v.y `shouldEqual` 2.0
        v.z `shouldEqual` (-3.0)

    describe "dot product" do
      it "dot of orthogonal vectors is 0" do
        assertCloseTo epsilon 0.0 (dot unitX unitY)
        assertCloseTo epsilon 0.0 (dot unitY unitZ)
        assertCloseTo epsilon 0.0 (dot unitX unitZ)

      it "dot of parallel vectors is product of lengths" do
        assertCloseTo epsilon 1.0 (dot unitX unitX)
        assertCloseTo epsilon 14.0 (dot (vec3 1.0 2.0 3.0) (vec3 1.0 2.0 3.0))

    describe "cross product" do
      it "x cross y = z" do
        cross unitX unitY `shouldEqual` unitZ

      it "y cross x = -z" do
        cross unitY unitX `shouldEqual` neg unitZ

      it "cross product of parallel vectors is zero" do
        cross unitX unitX `shouldEqual` zero

    describe "length" do
      it "length of unit vectors is 1" do
        assertCloseTo epsilon 1.0 (lengthVec3 unitX)
        assertCloseTo epsilon 1.0 (lengthVec3 unitY)
        assertCloseTo epsilon 1.0 (lengthVec3 unitZ)

      it "length of zero is 0" do
        assertCloseTo epsilon 0.0 (lengthVec3 zero)

      it "length of (3,4,0) is 5" do
        assertCloseTo epsilon 5.0 (lengthVec3 (vec3 3.0 4.0 0.0))

    describe "normalize" do
      it "normalized vector has length 1" do
        let n = normalize (vec3 3.0 4.0 0.0)
        assertCloseTo epsilon 1.0 (lengthVec3 n)

      it "normalized unit vector is itself" do
        normalize unitX `shouldEqual` unitX

    describe "lerp" do
      it "lerp at 0 returns first vector" do
        lerp (vec3 0.0 0.0 0.0) (vec3 10.0 10.0 10.0) 0.0 `shouldEqual` vec3 0.0 0.0 0.0

      it "lerp at 1 returns second vector" do
        lerp (vec3 0.0 0.0 0.0) (vec3 10.0 10.0 10.0) 1.0 `shouldEqual` vec3 10.0 10.0 10.0

      it "lerp at 0.5 returns midpoint" do
        let result = lerp (vec3 0.0 0.0 0.0) (vec3 10.0 10.0 10.0) 0.5
        let (Vec3 v) = result
        assertCloseTo epsilon 5.0 v.x
        assertCloseTo epsilon 5.0 v.y
        assertCloseTo epsilon 5.0 v.z

    describe "distance" do
      it "distance between same points is 0" do
        assertCloseTo epsilon 0.0 (distance (vec3 1.0 2.0 3.0) (vec3 1.0 2.0 3.0))

      it "distance between origin and (3,4,0) is 5" do
        assertCloseTo epsilon 5.0 (distance zero (vec3 3.0 4.0 0.0))

    describe "identity properties" do
      it "a + zero = a" do
        let a = vec3 1.0 2.0 3.0
        add a zero `shouldEqual` a

      it "a - a = zero" do
        let a = vec3 1.0 2.0 3.0
        sub a a `shouldEqual` zero

      it "scale 1 a = a" do
        let a = vec3 1.0 2.0 3.0
        scale a 1.0 `shouldEqual` a

      it "scale 0 a = zero" do
        let a = vec3 1.0 2.0 3.0
        scale a 0.0 `shouldEqual` zero
