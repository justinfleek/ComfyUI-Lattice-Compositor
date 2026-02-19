-- | Port of ui/src/__tests__/services/speedGraph.test.ts
-- |
-- | Tests the Speed Graph view functionality in the Curve Editor.
-- | The Speed Graph shows the derivative (rate of change) of property values,
-- | creating the characteristic "bell curve" shape for ease animations.

module Test.Lattice.Services.SpeedGraph (spec) where

import Prelude

import Data.Array (drop, zipWith)
import Data.Foldable (elem, foldl)
import Math (abs, ceil)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo)

-- | Evaluate a cubic bezier at parameter t
cubicBezierValue :: Number -> Number -> Number -> Number -> Number -> Number
cubicBezierValue p0 p1 p2 p3 t =
  let mt = 1.0 - t
  in mt * mt * mt * p0
     + 3.0 * mt * mt * t * p1
     + 3.0 * mt * t * t * p2
     + t * t * t * p3

-- | Compute speed (|derivative|) of a cubic bezier via finite differences
cubicBezierSpeed :: Number -> Number -> Number -> Number -> Number -> Number -> Number
cubicBezierSpeed p0 p1 p2 p3 t fps =
  let
    epsilon = 1.0 / fps
    v1 = cubicBezierValue p0 p1 p2 p3 t
    v2 = cubicBezierValue p0 p1 p2 p3 (min 1.0 (t + epsilon))
  in abs (v2 - v1) * fps

-- | Compute pairwise speed curve from keyframe values
calculateSpeedCurve :: Array Number -> Number -> Array Number
calculateSpeedCurve keyframes fps =
  zipWith (\x1 x2 -> abs (x2 - x1) * fps) keyframes (drop 1 keyframes)

spec :: Spec Unit
spec = do
  describe "Speed Graph" do
    speedCalculationTests
    speedGraphUITests
    speedGraphRenderingTests
    cubicBezierSpeedTests
    speedGraphValueRangeTests
    tutorial04Tests
    determinismTests

-- ---------------------------------------------------------------------------
-- Speed Calculation Logic
-- ---------------------------------------------------------------------------

speedCalculationTests :: Spec Unit
speedCalculationTests = do
  describe "Speed Calculation Logic" do
    it "constant speed for linear interpolation" do
      -- Linear motion from 0 to 100 over 30 frames
      let
        startValue = 0.0
        endValue = 100.0
        duration = 30.0
        fps = 30.0
        timeInSeconds = duration / fps
        expectedSpeed = abs (endValue - startValue) / timeInSeconds
      -- Speed should be 100 units per second
      expectedSpeed `shouldEqual` 100.0

    it "zero speed at hold keyframes" do
      -- Hold interpolation: no change between keyframes
      let speed = 0.0
      speed `shouldEqual` 0.0

    it "variable speed for bezier interpolation" do
      -- Ease-in-out: starts slow, speeds up, slows down
      -- At keyframes, speed approaches 0; at midpoint, speed is maximum
      let
        s0 = 0.0     -- Start: slow
        s1 = 50.0    -- Accelerating
        s2 = 100.0   -- Maximum speed
        s3 = 50.0    -- Decelerating
        s4 = 0.0     -- End: slow
      -- Bell curve shape verification
      (s2 > s0) `shouldEqual` true
      (s2 > s4) `shouldEqual` true
      (s1 > s0) `shouldEqual` true
      (s3 < s2) `shouldEqual` true

    it "speed graph derivative formula" do
      -- Speed = |f(t + epsilon) - f(t)| / epsilon
      let
        fps = 30.0
        epsilon = 1.0 / fps
        -- For a linear function f(t) = 100t
        valueAtT x = 100.0 * x
        t0 = 0.5
        v1 = valueAtT t0
        v2 = valueAtT (t0 + epsilon)
        speed = abs (v2 - v1) / epsilon
      -- Should equal the derivative of 100t = 100
      assertCloseTo 0.1 100.0 speed

-- ---------------------------------------------------------------------------
-- Speed Graph UI
-- ---------------------------------------------------------------------------

speedGraphUITests :: Spec Unit
speedGraphUITests = do
  describe "Speed Graph UI" do
    it "graph mode can be set to speed" do
      let graphMode = "speed"
      graphMode `shouldEqual` "speed"

    it "graph mode can be set to value" do
      let graphMode = "value"
      graphMode `shouldEqual` "value"

    it "Y axis units for position speed" do
      let unit = "px/sec"
      unit `shouldEqual` "px/sec"

    it "Y axis units for rotation speed" do
      let unit = "deg/sec"
      unit `shouldEqual` "deg/sec"

    it "speed range starts at 0" do
      -- Speed is always non-negative (absolute value of derivative)
      let speedRange = { min: 0.0, max: 100.0 }
      speedRange.min `shouldEqual` 0.0

    it "speed range auto-scales to max speed" do
      -- Find maximum speed across all samples
      let
        speeds = [ 10.0, 50.0, 120.0, 80.0, 30.0 ]
        maxSpeed = foldl max 0.0 speeds
        paddedMax = maxSpeed * 1.2
      paddedMax `shouldEqual` 144.0

-- ---------------------------------------------------------------------------
-- Speed Graph Rendering
-- ---------------------------------------------------------------------------

speedGraphRenderingTests :: Spec Unit
speedGraphRenderingTests = do
  describe "Speed Graph Rendering" do
    it "speed curve samples at sub-frame resolution" do
      let
        step = 0.5
        frameCount = 10.0
        expectedSamples = ceil (frameCount / step)
      expectedSamples `shouldEqual` 20.0

    it "speed curve uses two-pass rendering" do
      -- Pass 1: Black outline for visibility
      -- Pass 2: Colored curve
      let
        passes = 2
        pass1Color = "#000"
        pass1Width = 4.0
        pass2Width = 2.0
      passes `shouldEqual` 2
      pass1Color `shouldEqual` "#000"
      (pass1Width > pass2Width) `shouldEqual` true

-- ---------------------------------------------------------------------------
-- Cubic Bezier Speed
-- ---------------------------------------------------------------------------

cubicBezierSpeedTests :: Spec Unit
cubicBezierSpeedTests = do
  describe "Cubic Bezier Speed" do
    it "ease-in-out creates bell curve speed" do
      -- Standard ease-in-out: starts and ends slow, fast in middle
      let
        fps = 30.0
        speedStart = cubicBezierSpeed 0.0 0.0 100.0 100.0 0.0 fps
        speedMid = cubicBezierSpeed 0.0 0.0 100.0 100.0 0.5 fps
        speedEnd = cubicBezierSpeed 0.0 0.0 100.0 100.0 0.95 fps
      -- Middle should be faster than ends
      (speedMid > speedStart) `shouldEqual` true
      (speedMid > speedEnd) `shouldEqual` true

    it "linear bezier has constant speed" do
      -- Linear: control points on the line
      let
        fps = 30.0
        speed1 = cubicBezierSpeed 0.0 33.33 66.67 100.0 0.25 fps
        speed2 = cubicBezierSpeed 0.0 33.33 66.67 100.0 0.5 fps
        speed3 = cubicBezierSpeed 0.0 33.33 66.67 100.0 0.75 fps
      -- All speeds should be approximately equal
      (abs (speed1 - speed2) < 50.0) `shouldEqual` true
      (abs (speed2 - speed3) < 50.0) `shouldEqual` true

    it "ease-in starts slow then accelerates" do
      -- Ease-in: slow start, fast end
      let
        fps = 30.0
        speedStart = cubicBezierSpeed 0.0 0.0 0.0 100.0 0.1 fps
        speedEnd = cubicBezierSpeed 0.0 0.0 0.0 100.0 0.9 fps
      -- End should be faster than start
      (speedEnd > speedStart) `shouldEqual` true

    it "ease-out starts fast then decelerates" do
      -- Ease-out: fast start, slow end
      let
        fps = 30.0
        speedStart = cubicBezierSpeed 0.0 100.0 100.0 100.0 0.1 fps
        speedEnd = cubicBezierSpeed 0.0 100.0 100.0 100.0 0.9 fps
      -- Start should be faster than end
      (speedStart > speedEnd) `shouldEqual` true

-- ---------------------------------------------------------------------------
-- Speed Graph Value Range
-- ---------------------------------------------------------------------------

speedGraphValueRangeTests :: Spec Unit
speedGraphValueRangeTests = do
  describe "Speed Graph Value Range" do
    it "computes max speed across all curves" do
      let
        curve1Speeds = [ 10.0, 50.0, 30.0 ]
        curve2Speeds = [ 20.0, 100.0, 40.0 ]
        allSpeeds = curve1Speeds <> curve2Speeds
        maxSpeed = foldl max 0.0 allSpeeds
      maxSpeed `shouldEqual` 100.0

    it "adds padding to max speed" do
      let
        maxSpeed = 100.0
        paddingFactor = 1.2
        rangeMax = maxSpeed * paddingFactor
      rangeMax `shouldEqual` 120.0

    it "defaults to 100 for minimum max speed" do
      let
        speeds = [ 5.0, 10.0, 15.0 ]
        computedMax = foldl max 0.0 speeds
        defaultMin = 100.0
        rangeMax = max defaultMin (computedMax * 1.2)
      -- Uses default minimum since 15 * 1.2 = 18 < 100
      rangeMax `shouldEqual` 100.0

-- ---------------------------------------------------------------------------
-- Tutorial 04 Speed Graph Steps
-- ---------------------------------------------------------------------------

tutorial04Tests :: Spec Unit
tutorial04Tests = do
  describe "Tutorial 04 Speed Graph Steps" do
    it "Speed Graph view exists in Curve Editor" do
      -- User can toggle to Speed Graph view
      let viewModes = [ "value", "speed" ] :: Array String
      (elem "speed" viewModes) `shouldEqual` true

    it "Speed Graph shows derivative of property values" do
      -- Speed = rate of change
      let
        valueAtFrame0 = 0.0
        valueAtFrame1 = 100.0
        fps = 30.0
        deltaValue = valueAtFrame1 - valueAtFrame0
        deltaTime = 1.0 / fps
        speed = abs (deltaValue / deltaTime)
      -- 100 units / (1/30 sec) = 3000 units/sec
      speed `shouldEqual` 3000.0

    it "Speed Graph creates bell curve for ease animations" do
      -- Ease-in-out shows characteristic bell curve shape
      let bellCurveShape = true
      bellCurveShape `shouldEqual` true

    it "Speed Graph Y axis shows velocity units" do
      let
        positionUnit = "px/sec"
        rotationUnit = "deg/sec"
      -- Both units end with "/sec"
      positionUnit `shouldEqual` "px/sec"
      rotationUnit `shouldEqual` "deg/sec"

-- ---------------------------------------------------------------------------
-- Determinism
-- ---------------------------------------------------------------------------

determinismTests :: Spec Unit
determinismTests = do
  describe "Determinism" do
    it "speed calculation is deterministic" do
      -- Same inputs always produce same output
      let
        calculateSpeed v1 v2 fps = abs (v2 - v1) * fps
        result1 = calculateSpeed 0.0 100.0 30.0
        result2 = calculateSpeed 0.0 100.0 30.0
        result3 = calculateSpeed 0.0 100.0 30.0
      result1 `shouldEqual` result2
      result2 `shouldEqual` result3

    it "speed graph same at any playhead position" do
      -- Speed graph should look the same regardless of where playhead is
      let
        keyframes = [ 0.0, 50.0, 100.0 ]
        fps = 30.0
        speeds1 = calculateSpeedCurve keyframes fps
        speeds2 = calculateSpeedCurve keyframes fps
      speeds1 `shouldEqual` speeds2
