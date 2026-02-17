-- | Tests for Lattice.Services.Interpolation
-- | Ported from ui/src/__tests__/services/interpolation.test.ts

module Test.Lattice.Services.Interpolation where

import Prelude
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo)
import Lattice.Services.Interpolation as I

spec :: Spec Unit
spec = describe "Lattice.Services.Interpolation" do

  describe "lerp" do
    it "interpolates at t=0 returning first value" do
      I.lerp 0.0 100.0 0.0 `shouldEqual` 0.0

    it "interpolates at t=1 returning second value" do
      I.lerp 0.0 100.0 1.0 `shouldEqual` 100.0

    it "interpolates at t=0.5 returning midpoint" do
      I.lerp 0.0 100.0 0.5 `shouldEqual` 50.0

    it "handles negative numbers" do
      I.lerp (-100.0) 100.0 0.5 `shouldEqual` 0.0

    it "handles reversed range" do
      I.lerp 100.0 0.0 0.5 `shouldEqual` 50.0

    it "handles t < 0 (extrapolation)" do
      I.lerp 0.0 100.0 (-0.5) `shouldEqual` (-50.0)

    it "handles t > 1 (extrapolation)" do
      I.lerp 0.0 100.0 1.5 `shouldEqual` 150.0

  describe "safeLerp" do
    it "matches lerp for normal values" do
      I.safeLerp 0.0 100.0 0.5 `shouldEqual` 50.0

    it "returns a for NaN result when t < 0.5" do
      -- Infinity * 0 = NaN, so safeLerp catches it
      let result = I.safeLerp (1.0 / 0.0) (-(1.0 / 0.0)) 0.25
      -- t < 0.5 so returns a
      result `shouldEqual` (1.0 / 0.0)

    it "returns b for NaN result when t >= 0.5" do
      let result = I.safeLerp (1.0 / 0.0) (-(1.0 / 0.0)) 0.75
      result `shouldEqual` (-(1.0 / 0.0))

  describe "lerpVec2" do
    it "interpolates x and y independently" do
      let a = I.Vec2 { x: 0.0, y: 0.0 }
          b = I.Vec2 { x: 100.0, y: 200.0 }
          result = I.lerpVec2 a b 0.5
      result `shouldEqual` I.Vec2 { x: 50.0, y: 100.0 }

    it "returns first vec at t=0" do
      let a = I.Vec2 { x: 10.0, y: 20.0 }
          b = I.Vec2 { x: 30.0, y: 40.0 }
      I.lerpVec2 a b 0.0 `shouldEqual` a

    it "returns second vec at t=1" do
      let a = I.Vec2 { x: 10.0, y: 20.0 }
          b = I.Vec2 { x: 30.0, y: 40.0 }
      I.lerpVec2 a b 1.0 `shouldEqual` b

  describe "lerpVec3" do
    it "interpolates all three components" do
      let a = I.Vec3 { x: 0.0, y: 0.0, z: 0.0 }
          b = I.Vec3 { x: 10.0, y: 20.0, z: 30.0 }
          result = I.lerpVec3 a b 0.5
      result `shouldEqual` I.Vec3 { x: 5.0, y: 10.0, z: 15.0 }

  describe "lerpColor" do
    it "interpolates RGB channels with rounding" do
      let c1 = I.Color { r: 0.0, g: 0.0, b: 0.0, a: 255.0 }
          c2 = I.Color { r: 255.0, g: 255.0, b: 255.0, a: 255.0 }
          result = I.lerpColor c1 c2 0.5
      result `shouldEqual` I.Color { r: 128.0, g: 128.0, b: 128.0, a: 255.0 }

    it "interpolates alpha channel" do
      let c1 = I.Color { r: 0.0, g: 0.0, b: 0.0, a: 0.0 }
          c2 = I.Color { r: 0.0, g: 0.0, b: 0.0, a: 255.0 }
          I.Color result = I.lerpColor c1 c2 0.5
      assertCloseTo 1.0 128.0 result.a

  describe "bezierPoint" do
    it "returns p0 at t=0" do
      assertCloseTo 1e-10 0.0 (I.bezierPoint 0.0 0.0 0.33 0.67 1.0)

    it "returns p3 at t=1" do
      assertCloseTo 1e-10 1.0 (I.bezierPoint 1.0 0.0 0.33 0.67 1.0)

    it "returns midpoint-ish at t=0.5 for symmetric curve" do
      let v = I.bezierPoint 0.5 0.0 0.0 1.0 1.0
      -- For p0=0, p1=0, p2=1, p3=1, at t=0.5: 0.5
      assertCloseTo 1e-10 0.5 v

    it "evaluates linear control points as linear" do
      -- p0=0, p1=0.33, p2=0.67, p3=1 is approximately linear
      let v = I.bezierPoint 0.5 0.0 0.333333 0.666667 1.0
      assertCloseTo 0.01 0.5 v

  describe "bezierDerivative" do
    it "returns positive derivative for ascending curve" do
      let d = I.bezierDerivative 0.5 0.0 0.33 0.67 1.0
      -- derivative should be positive for ascending curve
      d `shouldEqual` d -- just check it's finite
      -- Verify it's > 0
      (d > 0.0) `shouldEqual` true

  describe "solveBezierX" do
    it "returns ~0.5 for x=0.5 on linear-ish curve" do
      let t = I.solveBezierX 0.5 0.33 0.67 8
      assertCloseTo 0.01 0.5 t

    it "returns ~0 for x near 0" do
      let t = I.solveBezierX 0.01 0.33 0.67 8
      assertCloseTo 0.02 0.01 t

    it "returns ~1 for x near 1" do
      let t = I.solveBezierX 0.99 0.33 0.67 8
      assertCloseTo 0.02 0.99 t

  describe "cubicBezierEasing" do
    it "returns 0 at t=0" do
      assertCloseTo 1e-6 0.0 (I.cubicBezierEasing 0.0 0.33 0.33 0.67 0.67)

    it "returns 1 at t=1" do
      assertCloseTo 1e-6 1.0 (I.cubicBezierEasing 1.0 0.33 0.33 0.67 0.67)

    it "returns ~0.5 at t=0.5 for linear preset" do
      assertCloseTo 0.02 0.5 (I.cubicBezierEasing 0.5 0.33 0.33 0.67 0.67)

    it "easeIn is slower at start" do
      let easeInVal = I.cubicBezierEasing 0.25 0.42 0.0 0.67 0.67
      -- easeIn: value at 0.25 should be less than 0.25 (slower start)
      (easeInVal < 0.25) `shouldEqual` true

    it "easeOut is faster at start" do
      let easeOutVal = I.cubicBezierEasing 0.25 0.33 0.33 0.58 1.0
      -- easeOut: value at 0.25 should be more than 0.25 (faster start)
      (easeOutVal > 0.25) `shouldEqual` true

  describe "colorFromHex6" do
    it "parses 6-digit hex correctly" do
      let I.Color c = I.colorFromHex6 "ff8040"
      assertCloseTo 0.5 255.0 c.r
      assertCloseTo 0.5 128.0 c.g
      assertCloseTo 0.5 64.0 c.b
      assertCloseTo 0.5 255.0 c.a

    it "parses black" do
      let I.Color c = I.colorFromHex6 "000000"
      assertCloseTo 0.5 0.0 c.r
      assertCloseTo 0.5 0.0 c.g
      assertCloseTo 0.5 0.0 c.b

    it "parses white" do
      let I.Color c = I.colorFromHex6 "ffffff"
      assertCloseTo 0.5 255.0 c.r
      assertCloseTo 0.5 255.0 c.g
      assertCloseTo 0.5 255.0 c.b

    it "parses 8-digit hex with alpha" do
      let I.Color c = I.colorFromHex6 "ff804080"
      assertCloseTo 0.5 255.0 c.r
      assertCloseTo 0.5 128.0 c.g
      assertCloseTo 0.5 64.0 c.b
      assertCloseTo 0.5 128.0 c.a

    it "returns black for short strings" do
      I.colorFromHex6 "ff" `shouldEqual` I.Color { r: 0.0, g: 0.0, b: 0.0, a: 255.0 }

  describe "normalizeHex" do
    it "strips leading #" do
      I.normalizeHex "#ff8040" `shouldEqual` "ff8040"

    it "passes through 6-digit hex without #" do
      I.normalizeHex "ff8040" `shouldEqual` "ff8040"

    it "expands 3-digit shorthand" do
      I.normalizeHex "f80" `shouldEqual` "ff8800"

    it "expands 3-digit shorthand with #" do
      I.normalizeHex "#f80" `shouldEqual` "ff8800"

    it "expands 4-digit shorthand with alpha" do
      I.normalizeHex "#f80a" `shouldEqual` "ff8800aa"

  describe "colorToHex" do
    it "converts color to hex without alpha" do
      let c = I.Color { r: 255.0, g: 128.0, b: 64.0, a: 255.0 }
      I.colorToHex c false `shouldEqual` "#ff8040"

    it "converts color to hex with alpha" do
      let c = I.Color { r: 255.0, g: 128.0, b: 64.0, a: 128.0 }
      I.colorToHex c true `shouldEqual` "#ff804080"

    it "converts black" do
      let c = I.Color { r: 0.0, g: 0.0, b: 0.0, a: 255.0 }
      I.colorToHex c false `shouldEqual` "#000000"

    it "converts white" do
      let c = I.Color { r: 255.0, g: 255.0, b: 255.0, a: 255.0 }
      I.colorToHex c false `shouldEqual` "#ffffff"

  describe "easing presets" do
    it "linear preset values" do
      let I.EasingPreset p = I.easeLinear
      assertCloseTo 1e-10 0.33 p.outX
      assertCloseTo 1e-10 0.33 p.outY
      assertCloseTo 1e-10 0.33 p.inX
      assertCloseTo 1e-10 0.33 p.inY

    it "easeIn preset values" do
      let I.EasingPreset p = I.easeIn
      assertCloseTo 1e-10 0.42 p.outX
      assertCloseTo 1e-10 0.0 p.outY

    it "easeOut preset values" do
      let I.EasingPreset p = I.easeOut
      assertCloseTo 1e-10 0.58 p.inX
      assertCloseTo 1e-10 1.0 p.inY

    it "easeInOut combines easeIn and easeOut" do
      let I.EasingPreset p = I.easeInOut
      assertCloseTo 1e-10 0.42 p.outX
      assertCloseTo 1e-10 0.0 p.outY
      assertCloseTo 1e-10 0.58 p.inX
      assertCloseTo 1e-10 1.0 p.inY

    it "easeOutBack has overshoot" do
      let I.EasingPreset p = I.easeOutBack
      -- inY > 1.0 indicates overshoot
      (p.inY > 1.0) `shouldEqual` true

  describe "applyEasingPreset" do
    it "returns 0 at ratio 0" do
      assertCloseTo 1e-6 0.0 (I.applyEasingPreset 0.0 I.easeLinear)

    it "returns 1 at ratio 1" do
      assertCloseTo 1e-6 1.0 (I.applyEasingPreset 1.0 I.easeLinear)

    it "returns ~0.5 at ratio 0.5 for linear" do
      assertCloseTo 0.02 0.5 (I.applyEasingPreset 0.5 I.easeLinear)

    it "easeIn is slower at start" do
      let v = I.applyEasingPreset 0.25 I.easeIn
      (v < 0.25) `shouldEqual` true

    it "easeOut is faster at start" do
      let v = I.applyEasingPreset 0.25 I.easeOut
      (v > 0.25) `shouldEqual` true

    it "clamps negative ratio to 0" do
      assertCloseTo 1e-6 0.0 (I.applyEasingPreset (-0.5) I.easeLinear)

    it "clamps ratio > 1 to 1" do
      assertCloseTo 1e-6 1.0 (I.applyEasingPreset 1.5 I.easeLinear)

  describe "findKeyframeIndex" do
    it "returns 0 for frame before first keyframe" do
      I.findKeyframeIndex [0.0, 30.0, 60.0, 90.0] (-10.0) `shouldEqual` 0

    it "returns last valid index for frame after last keyframe" do
      I.findKeyframeIndex [0.0, 30.0, 60.0, 90.0] 100.0 `shouldEqual` 2

    it "returns correct index for frame at first keyframe" do
      I.findKeyframeIndex [0.0, 30.0, 60.0, 90.0] 0.0 `shouldEqual` 0

    it "returns correct index for frame between keyframes" do
      I.findKeyframeIndex [0.0, 30.0, 60.0, 90.0] 45.0 `shouldEqual` 1

    it "returns correct index for frame at exact keyframe" do
      I.findKeyframeIndex [0.0, 30.0, 60.0, 90.0] 30.0 `shouldEqual` 1

    it "returns 0 for array with less than 2 elements" do
      I.findKeyframeIndex [42.0] 10.0 `shouldEqual` 0

    it "returns 0 for empty array" do
      I.findKeyframeIndex [] 10.0 `shouldEqual` 0

    it "works with 100-element array" do
      let frames = range100
          idx = I.findKeyframeIndex frames 555.0
      -- 555.0 is between frame 550 (index 55) and 560 (index 56)
      idx `shouldEqual` 55

    it "handles floating point frames" do
      I.findKeyframeIndex [0.0, 100.0] 33.33 `shouldEqual` 0

-- Helper: array of 100 numbers [0, 10, 20, ..., 990]
range100 :: Array Number
range100 = map (\i -> i * 10.0) vals
  where
    vals = [ 0.0, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 9.0
           , 10.0, 11.0, 12.0, 13.0, 14.0, 15.0, 16.0, 17.0, 18.0, 19.0
           , 20.0, 21.0, 22.0, 23.0, 24.0, 25.0, 26.0, 27.0, 28.0, 29.0
           , 30.0, 31.0, 32.0, 33.0, 34.0, 35.0, 36.0, 37.0, 38.0, 39.0
           , 40.0, 41.0, 42.0, 43.0, 44.0, 45.0, 46.0, 47.0, 48.0, 49.0
           , 50.0, 51.0, 52.0, 53.0, 54.0, 55.0, 56.0, 57.0, 58.0, 59.0
           , 60.0, 61.0, 62.0, 63.0, 64.0, 65.0, 66.0, 67.0, 68.0, 69.0
           , 70.0, 71.0, 72.0, 73.0, 74.0, 75.0, 76.0, 77.0, 78.0, 79.0
           , 80.0, 81.0, 82.0, 83.0, 84.0, 85.0, 86.0, 87.0, 88.0, 89.0
           , 90.0, 91.0, 92.0, 93.0, 94.0, 95.0, 96.0, 97.0, 98.0, 99.0
           ]
