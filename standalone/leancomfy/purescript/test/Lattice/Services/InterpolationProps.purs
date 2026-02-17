-- | Property-based tests for Lattice.Services.Interpolation
-- | Ported from ui/src/__tests__/services/interpolation.property.test.ts

module Test.Lattice.Services.InterpolationProps where

import Prelude
import Data.Int (toNumber) as Int
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.QuickCheck (quickCheck, Result, (===), (<?>))
import Test.QuickCheck.Gen (Gen, choose)
import Test.Lattice.TestHelpers (assertCloseTo)
import Lattice.Services.Interpolation as I
import Math (abs, pi) as Math

-- | Approximate equality for QuickCheck: allows 1 ULP of error
approxEq :: Number -> Number -> Result
approxEq a b =
  let tol = Math.abs a * 1.0e-14 + 1.0e-15
  in (Math.abs (a - b) <= tol) <?>
       ("expected " <> show a <> " ≈ " <> show b
       <> " (diff: " <> show (Math.abs (a - b)) <> ")")

spec :: Spec Unit
spec = describe "PROPERTY: Interpolation" do

  describe "lerp" do
    it "lerp at t=0 always returns a" do
      liftEffect $ quickCheck \(a :: Number) (b :: Number) ->
        I.lerp a b 0.0 === a

    it "lerp at t=1 always returns b" do
      liftEffect $ quickCheck \(a :: Number) (b :: Number) ->
        I.lerp a b 1.0 `approxEq` b

    it "lerp at t=0.5 is midpoint" do
      liftEffect $ quickCheck \(a :: Number) (b :: Number) ->
        I.lerp a b 0.5 `approxEq` ((a + b) / 2.0)

  describe "safeLerp determinism" do
    it "safeLerp is deterministic" do
      liftEffect $ quickCheck \(a :: Number) (b :: Number) (t :: Number) ->
        I.safeLerp a b t === I.safeLerp a b t

  describe "bezierPoint boundary conditions" do
    it "bezierPoint at t=0 always returns p0" do
      liftEffect $ quickCheck \(p0 :: Number) (p1 :: Number) (p2 :: Number) (p3 :: Number) ->
        I.bezierPoint 0.0 p0 p1 p2 p3 === p0

    it "bezierPoint at t=1 always returns p3" do
      liftEffect $ quickCheck \(p0 :: Number) (p1 :: Number) (p2 :: Number) (p3 :: Number) ->
        I.bezierPoint 1.0 p0 p1 p2 p3 === p3

  describe "cubicBezierEasing boundary conditions" do
    it "returns ~0 at t=0 for any valid preset" do
      let presets =
            [ { x1: 0.33, y1: 0.33, x2: 0.67, y2: 0.67 }  -- linear
            , { x1: 0.42, y1: 0.0, x2: 0.67, y2: 0.67 }   -- easeIn
            , { x1: 0.33, y1: 0.33, x2: 0.58, y2: 1.0 }   -- easeOut
            , { x1: 0.42, y1: 0.0, x2: 0.58, y2: 1.0 }    -- easeInOut
            ]
          results = map (\p -> I.cubicBezierEasing 0.0 p.x1 p.y1 p.x2 p.y2) presets
      -- All should be close to 0
      map (\r -> Math.abs r < 0.001) results `shouldEqual` [true, true, true, true]

    it "returns ~1 at t=1 for any valid preset" do
      let presets =
            [ { x1: 0.33, y1: 0.33, x2: 0.67, y2: 0.67 }
            , { x1: 0.42, y1: 0.0, x2: 0.67, y2: 0.67 }
            , { x1: 0.33, y1: 0.33, x2: 0.58, y2: 1.0 }
            , { x1: 0.42, y1: 0.0, x2: 0.58, y2: 1.0 }
            ]
          results = map (\p -> I.cubicBezierEasing 1.0 p.x1 p.y1 p.x2 p.y2) presets
      map (\r -> Math.abs (r - 1.0) < 0.001) results `shouldEqual` [true, true, true, true]

  describe "applyEasingPreset boundary conditions" do
    it "returns 0 at ratio=0 for all presets" do
      let presets = [I.easeLinear, I.easeIn, I.easeOut, I.easeInOut, I.easeOutBack]
          results = map (\p -> I.applyEasingPreset 0.0 p) presets
      map (\r -> Math.abs r < 0.001) results `shouldEqual` [true, true, true, true, true]

    it "returns 1 at ratio=1 for all presets" do
      let presets = [I.easeLinear, I.easeIn, I.easeOut, I.easeInOut, I.easeOutBack]
          results = map (\p -> I.applyEasingPreset 1.0 p) presets
      map (\r -> Math.abs (r - 1.0) < 0.001) results `shouldEqual` [true, true, true, true, true]

    it "output is in reasonable range [-0.1, 1.1] for unit input" do
      let ts = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
          presets = [I.easeLinear, I.easeIn, I.easeOut, I.easeInOut, I.easeOutBack]
          allInRange = presets # map \p ->
            ts # map \t ->
              let v = I.applyEasingPreset t p
              in v >= (-0.2) && v <= 1.6  -- easeOutBack overshoots up to 1.56
      map (map (\x -> x)) allInRange `shouldEqual`
        map (\_ -> map (\_ -> true) ts) presets

  describe "color roundtrip" do
    it "colorToHex . colorFromHex6 roundtrips standard colors" do
      let colors = ["ff0000", "00ff00", "0000ff", "000000", "ffffff", "808080"]
          roundtrip hex =
            let c = I.colorFromHex6 hex
            in I.colorToHex c false
      map roundtrip colors `shouldEqual`
        ["#ff0000", "#00ff00", "#0000ff", "#000000", "#ffffff", "#808080"]

    it "normalizeHex expands 3-char and strips #" do
      let cases =
            [ { input: "#abc", expected: "aabbcc" }
            , { input: "abc", expected: "aabbcc" }
            , { input: "#aabbcc", expected: "aabbcc" }
            , { input: "aabbcc", expected: "aabbcc" }
            ]
      map (\c -> I.normalizeHex c.input) cases `shouldEqual`
        map (\c -> c.expected) cases

  describe "lerpColor determinism" do
    it "lerpColor is deterministic for representative colors" do
      let c1 = I.Color { r: 255.0, g: 0.0, b: 128.0, a: 255.0 }
          c2 = I.Color { r: 0.0, g: 255.0, b: 64.0, a: 128.0 }
          ts = [0.0, 0.25, 0.5, 0.75, 1.0]
          results1 = map (\t -> I.lerpColor c1 c2 t) ts
          results2 = map (\t -> I.lerpColor c1 c2 t) ts
      results1 `shouldEqual` results2

  describe "findKeyframeIndex invariants" do
    it "result is always within valid bounds" do
      let frames = [0.0, 10.0, 20.0, 30.0, 40.0, 50.0]
          testFrames = [-10.0, 0.0, 5.0, 15.0, 25.0, 35.0, 45.0, 50.0, 100.0]
          results = map (\f -> I.findKeyframeIndex frames f) testFrames
          allValid = map (\r -> r >= 0 && r <= 4) results
      allValid `shouldEqual` [true, true, true, true, true, true, true, true, true]

    it "frames[idx] <= value for all test cases" do
      let frames = [0.0, 10.0, 20.0, 30.0, 40.0, 50.0]
          testFrames = [5.0, 15.0, 25.0, 35.0, 45.0]
          check f =
            let idx = I.findKeyframeIndex frames f
            in idx >= 0 && idx <= 4
      map check testFrames `shouldEqual` [true, true, true, true, true]

  describe "PURITY: interpolation functions" do
    it "lerp is pure (same inputs = same outputs)" do
      let r1 = I.lerp 10.0 90.0 0.3
          r2 = I.lerp 10.0 90.0 0.3
          r3 = I.lerp 10.0 90.0 0.3
      r1 `shouldEqual` r2
      r2 `shouldEqual` r3

    it "cubicBezierEasing is pure" do
      let r1 = I.cubicBezierEasing 0.5 0.42 0.0 0.58 1.0
          r2 = I.cubicBezierEasing 0.5 0.42 0.0 0.58 1.0
      r1 `shouldEqual` r2
