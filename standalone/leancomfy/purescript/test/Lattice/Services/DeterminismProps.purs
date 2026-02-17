-- | Determinism property tests
-- | Ported from ui/src/__tests__/services/determinism.property.test.ts
-- |
-- | Verifies that all interpolation and math functions are pure:
-- | same input always produces same output.

module Test.Lattice.Services.DeterminismProps where

import Prelude
import Data.Array (reverse) as Array
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.QuickCheck (quickCheck, (===))
import Lattice.Services.Interpolation as I
import Lattice.Services.Particles.SeededRandom as R
import Lattice.Services.Math3D.Vec3 as V
import Lattice.Services.Math3D.Vec3 (Vec3(..))
import Lattice.Services.Math3D.Mat4 as M4
import Lattice.Services.Math3D.Quat as Q

spec :: Spec Unit
spec = describe "DETERMINISM: Pure function contracts" do

  describe "interpolation determinism" do
    it "lerp is deterministic for all inputs" do
      liftEffect $ quickCheck \(a :: Number) (b :: Number) (t :: Number) ->
        I.lerp a b t === I.lerp a b t

    it "safeLerp is deterministic for all inputs" do
      liftEffect $ quickCheck \(a :: Number) (b :: Number) (t :: Number) ->
        I.safeLerp a b t === I.safeLerp a b t

    it "bezierPoint is deterministic" do
      liftEffect $ quickCheck \(t :: Number) (p0 :: Number) (p1 :: Number) ->
        I.bezierPoint t p0 p1 p1 p0 === I.bezierPoint t p0 p1 p1 p0

    it "cubicBezierEasing produces consistent results" do
      let ts = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
          run1 = map (\t -> I.cubicBezierEasing t 0.42 0.0 0.58 1.0) ts
          run2 = map (\t -> I.cubicBezierEasing t 0.42 0.0 0.58 1.0) ts
          run3 = map (\t -> I.cubicBezierEasing t 0.42 0.0 0.58 1.0) ts
      run1 `shouldEqual` run2
      run2 `shouldEqual` run3

    it "applyEasingPreset is deterministic across all presets" do
      let presets = [I.easeLinear, I.easeIn, I.easeOut, I.easeInOut, I.easeOutBack]
          ts = [0.0, 0.25, 0.5, 0.75, 1.0]
          run1 = map (\p -> map (\t -> I.applyEasingPreset t p) ts) presets
          run2 = map (\p -> map (\t -> I.applyEasingPreset t p) ts) presets
      run1 `shouldEqual` run2

  describe "evaluation order independence" do
    it "evaluating lerp in different order produces same results" do
      let pairs = [ {a: 0.0, b: 100.0, t: 0.25}
                  , {a: 0.0, b: 100.0, t: 0.75}
                  , {a: 0.0, b: 100.0, t: 0.5}
                  ]
          -- Forward order
          forward = map (\p -> I.lerp p.a p.b p.t) pairs
          -- Reverse order
          reversed = map (\p -> I.lerp p.a p.b p.t) (Array.reverse pairs)
      -- Same results regardless of evaluation order (just reversed)
      forward `shouldEqual` Array.reverse reversed

    it "evaluating same inputs 10 times produces identical results" do
      let v = I.cubicBezierEasing 0.5 0.42 0.0 0.58 1.0
          results = [v, v, v, v, v, v, v, v, v, v]
          expected = map (\_ -> I.cubicBezierEasing 0.5 0.42 0.0 0.58 1.0)
                         [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
      results `shouldEqual` expected

  describe "no state crosstalk" do
    it "SeededRandom instances do not affect each other" do
      let rng1 = R.create 42.0
          rng2 = R.create 123.0
          -- Advance rng1
          Tuple v1 rng1' = R.next rng1
          -- rng2 should be unaffected
          Tuple v2 rng2' = R.next rng2
          -- Create fresh instances and compare
          rngFresh2 = R.create 123.0
          Tuple v2Fresh _ = R.next rngFresh2
      v2 `shouldEqual` v2Fresh

    it "interpolation functions do not share state" do
      -- Two different bezier evaluations don't affect each other
      let v1 = I.cubicBezierEasing 0.5 0.42 0.0 0.58 1.0
          v2 = I.cubicBezierEasing 0.5 0.33 0.33 0.67 0.67
          -- Redo first evaluation
          v1Again = I.cubicBezierEasing 0.5 0.42 0.0 0.58 1.0
      v1 `shouldEqual` v1Again

  describe "Vec3/Mat4/Quat determinism" do
    it "Vec3 operations are deterministic" do
      liftEffect $ quickCheck \(x :: Number) (y :: Number) (z :: Number) ->
        let v = V.vec3 x y z
        in V.lengthSq v === V.lengthSq v

    it "Mat4 multiply is deterministic" do
      let a = M4.rotateX 0.5
          b = M4.translate (V.vec3 1.0 2.0 3.0)
          r1 = M4.multiply a b
          r2 = M4.multiply a b
      r1 `shouldEqual` r2

    it "Quat fromEuler is deterministic" do
      liftEffect $ quickCheck \(x :: Number) (y :: Number) (z :: Number) ->
        Q.fromEuler x y z === Q.fromEuler x y z

  describe "findKeyframeIndex determinism" do
    it "binary search returns same result for same input" do
      let frames = [0.0, 10.0, 20.0, 30.0, 40.0, 50.0]
          testFrames = [(-5.0), 0.0, 5.0, 15.0, 25.0, 35.0, 45.0, 55.0]
          run1 = map (\f -> I.findKeyframeIndex frames f) testFrames
          run2 = map (\f -> I.findKeyframeIndex frames f) testFrames
      run1 `shouldEqual` run2

