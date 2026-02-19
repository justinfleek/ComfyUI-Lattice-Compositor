-- | Port of ui/src/__tests__/services/expressions.property.test.ts
-- |
-- | Property-based tests for expression math functions.
-- | Tests: lerp, clamp, map, smoothstep, seedRandom, sine,
-- | sawtooth, square, timeRamp, ease, degreesToRadians/radiansToDegrees,
-- | distance.

module Test.Lattice.Services.ExpressionProps (spec) where

import Prelude

import Data.Foldable (for_)
import Data.Int (toNumber)
import Math (abs, pi, sin, sqrt, floor)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite, assertInRange)

-- ────────────────────────────────────────────────────────────────────────────
-- Pure math functions (port of expressionEvaluator)
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation: lerp(a, b, t) = a + (b - a) * t
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Clamp a value to [lo, hi]
clamp :: Number -> Number -> Number -> Number
clamp value lo hi
  | value < lo = lo
  | value > hi = hi
  | otherwise = value

-- | Map (remap) a value from input range to output range.
-- | When inMin == inMax, returns outMin to avoid division by zero.
mapRange :: Number -> Number -> Number -> Number -> Number -> Number
mapRange value inMin inMax outMin outMax =
  let inRange = inMax - inMin
  in if inRange == 0.0
       then outMin
       else
         let normalized = (value - inMin) / inRange
         in outMin + normalized * (outMax - outMin)

-- | Smoothstep Hermite interpolation
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x =
  let range = edge1 - edge0
  in if range == 0.0
       then 0.0
       else
         let t = clamp ((x - edge0) / range) 0.0 1.0
         in t * t * (3.0 - 2.0 * t)

-- | Seeded random using a simple hash function.
-- | Deterministic: same seed always produces same result.
seedRandom :: Int -> Number
seedRandom seed =
  let
    -- Simple hash-based PRNG (matches JS implementation concept)
    s1 = (seed * 16807 + 1) `mod` 2147483647
    normalized = toNumber (if s1 < 0 then -s1 else s1) / 2147483647.0
  in normalized

-- | Seeded random with min/max bounds
seedRandomBounded :: Int -> Number -> Number -> Number
seedRandomBounded seed lo hi =
  let base = seedRandom seed
  in lo + base * (hi - lo)

-- | Sine wave: amplitude * sin(2*pi*frequency*time + phase)
sineWave :: Number -> Number -> Number -> Number -> Number
sineWave time frequency amplitude phase =
  amplitude * sin (2.0 * pi * frequency * time + phase)

-- | Sawtooth wave: maps time to [-amplitude, amplitude] periodically
sawtoothWave :: Number -> Number -> Number -> Number
sawtoothWave time frequency amplitude =
  let period = 1.0 / frequency
      phase = time / period - floor (time / period)
  in amplitude * (2.0 * phase - 1.0)

-- | Square wave: returns +amplitude or -amplitude
squareWave :: Number -> Number -> Number -> Number
squareWave time frequency amplitude =
  let period = 1.0 / frequency
      phase = time / period - floor (time / period)
  in if phase < 0.5
       then amplitude
       else negate amplitude

-- | Time ramp: linear interpolation from startValue to endValue
-- | between startTime and endTime, clamped at boundaries.
timeRamp :: Number -> Number -> Number -> Number -> Number -> Number
timeRamp startTime endTime startValue endValue time
  | time <= startTime = startValue
  | time >= endTime = endValue
  | otherwise =
      let t = (time - startTime) / (endTime - startTime)
      in startValue + (endValue - startValue) * t

-- | Expression ease (smoothstep-based)
expressionEase :: Number -> Number -> Number -> Number -> Number -> Number
expressionEase time tMin tMax vMin vMax =
  let t = clamp ((time - tMin) / (tMax - tMin)) 0.0 1.0
      eased = t * t * (3.0 - 2.0 * t)
  in vMin + (vMax - vMin) * eased

-- | Expression ease-in (quadratic)
expressionEaseIn :: Number -> Number -> Number -> Number -> Number -> Number
expressionEaseIn time tMin tMax vMin vMax =
  let t = clamp ((time - tMin) / (tMax - tMin)) 0.0 1.0
      eased = t * t
  in vMin + (vMax - vMin) * eased

-- | Expression ease-out (quadratic)
expressionEaseOut :: Number -> Number -> Number -> Number -> Number -> Number
expressionEaseOut time tMin tMax vMin vMax =
  let t = clamp ((time - tMin) / (tMax - tMin)) 0.0 1.0
      eased = t * (2.0 - t)
  in vMin + (vMax - vMin) * eased

-- | Degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Radians to degrees
radiansToDegrees :: Number -> Number
radiansToDegrees rad = rad * 180.0 / pi

-- | Euclidean distance between two 2D points
distance :: Number -> Number -> Number -> Number -> Number
distance x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in sqrt (dx * dx + dy * dy)

-- ────────────────────────────────────────────────────────────────────────────
-- Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "EXPRESSION Properties" do
    lerpProperties
    clampProperties
    mapProperties
    smoothstepProperties
    seedRandomProperties
    sineProperties
    sawtoothProperties
    squareProperties
    timeRampProperties
    easeProperties
    degreeRadianProperties
    distanceProperties

-- ────────────────────────────────────────────────────────────────────────────
-- Lerp Properties
-- ────────────────────────────────────────────────────────────────────────────

lerpProperties :: Spec Unit
lerpProperties = do
  describe "mathExpressions.lerp" do
    it "lerp(a, b, 0) = a" do
      for_ sampleValues \a ->
        for_ sampleValues \b ->
          assertCloseTo 1.0e-10 a (lerp a b 0.0)

    it "lerp(a, b, 1) = b" do
      for_ sampleValues \a ->
        for_ sampleValues \b -> do
          let result = lerp a b 1.0
          let tolerance = max (abs b * 1.0e-9) 1.0e-10
          assertCloseTo tolerance b result

    it "lerp(a, b, 0.5) = midpoint" do
      for_ sampleValues \a ->
        for_ sampleValues \b -> do
          let result = lerp a b 0.5
          let expected = (a + b) / 2.0
          let tolerance = max (abs expected * 1.0e-9) 1.0e-9
          assertCloseTo tolerance expected result

    it "lerp(a, a, t) = a (same endpoints)" do
      for_ sampleValues \a ->
        for_ [0.0, 0.25, 0.5, 0.75, 1.0] \t ->
          assertCloseTo 1.0e-10 a (lerp a a t)

    it "lerp result is bounded between a and b" do
      for_ [0.0, 10.0, 50.0, 100.0] \a ->
        for_ [101.0, 150.0, 200.0] \b ->
          for_ [0.0, 0.25, 0.5, 0.75, 1.0] \t -> do
            let result = lerp a b t
            assertInRange (min a b - 1.0e-10) (max a b + 1.0e-10) result

-- ────────────────────────────────────────────────────────────────────────────
-- Clamp Properties
-- ────────────────────────────────────────────────────────────────────────────

clampProperties :: Spec Unit
clampProperties = do
  describe "mathExpressions.clamp" do
    it "clamp result is always within [min, max]" do
      for_ sampleValues \value ->
        for_ sampleValues \a ->
          for_ sampleValues \b -> do
            let lo = min a b
            let hi = max a b
            let result = clamp value lo hi
            assertInRange lo hi result

    it "clamp(value, min, max) = value when min <= value <= max" do
      for_ [50.0, 75.0, 100.0] \value -> do
        let result = clamp value 0.0 150.0
        result `shouldEqual` value

    it "clamp(value, min, min) = min" do
      for_ sampleValues \lo -> do
        let result = clamp (lo + 100.0) lo lo
        result `shouldEqual` lo

-- ────────────────────────────────────────────────────────────────────────────
-- Map Properties
-- ────────────────────────────────────────────────────────────────────────────

mapProperties :: Spec Unit
mapProperties = do
  describe "mathExpressions.map" do
    it "map(inMin, inMin, inMax, outMin, outMax) = outMin" do
      for_ [0.0, -10.0, 50.0] \inMin ->
        for_ [100.0, 200.0] \inMax ->
          for_ [0.0, -50.0] \outMin ->
            for_ [100.0, 300.0] \outMax ->
              assertCloseTo 1.0e-6 outMin (mapRange inMin inMin inMax outMin outMax)

    it "map(inMax, inMin, inMax, outMin, outMax) = outMax" do
      for_ [0.0, -10.0] \inMin ->
        for_ [100.0, 200.0] \inMax ->
          for_ [0.0, -50.0] \outMin ->
            for_ [100.0, 300.0] \outMax ->
              assertCloseTo 1.0e-6 outMax (mapRange inMax inMin inMax outMin outMax)

    it "map preserves midpoint" do
      for_ [0.0, -100.0, 50.0] \inMin ->
        for_ [0.0, -200.0, 100.0] \outMin -> do
          let inMax = inMin + 100.0
          let outMax = outMin + 200.0
          let midIn = (inMin + inMax) / 2.0
          let expectedMidOut = (outMin + outMax) / 2.0
          assertCloseTo 1.0e-6 expectedMidOut (mapRange midIn inMin inMax outMin outMax)

-- ────────────────────────────────────────────────────────────────────────────
-- Smoothstep Properties
-- ────────────────────────────────────────────────────────────────────────────

smoothstepProperties :: Spec Unit
smoothstepProperties = do
  describe "mathExpressions.smoothstep" do
    it "smoothstep(edge0, edge1, edge0) = 0" do
      for_ [0.0, -10.0, 50.0] \edge0 ->
        for_ [100.0, 200.0, 500.0] \edge1 ->
          assertCloseTo 1.0e-6 0.0 (smoothstep edge0 edge1 edge0)

    it "smoothstep(edge0, edge1, edge1) = 1" do
      for_ [0.0, -10.0, 50.0] \edge0 ->
        for_ [100.0, 200.0, 500.0] \edge1 ->
          assertCloseTo 1.0e-6 1.0 (smoothstep edge0 edge1 edge1)

    it "smoothstep is bounded in [0, 1]" do
      for_ sampleValues \x -> do
        let result = smoothstep 0.0 100.0 x
        assertInRange (-1.0e-10) (1.0 + 1.0e-10) result

    it "smoothstep(0, 1, 0.5) = 0.5" do
      assertCloseTo 1.0e-6 0.5 (smoothstep 0.0 1.0 0.5)

-- ────────────────────────────────────────────────────────────────────────────
-- SeedRandom Properties
-- ────────────────────────────────────────────────────────────────────────────

seedRandomProperties :: Spec Unit
seedRandomProperties = do
  describe "mathExpressions.seedRandom" do
    it "seedRandom is deterministic (same seed = same result)" do
      for_ [0, 1, 42, 12345, 999999] \seed -> do
        let result1 = seedRandom seed
        let result2 = seedRandom seed
        result1 `shouldEqual` result2

    it "seedRandom respects min/max bounds" do
      for_ [0, 1, 42, 999] \seed ->
        for_ [{ lo: 0.0, hi: 100.0 }, { lo: -50.0, hi: 50.0 }, { lo: 10.0, hi: 20.0 }] \{ lo, hi } -> do
          let result = seedRandomBounded seed lo hi
          assertInRange (lo - 1.0e-10) (hi + 1.0e-10) result

    it "seedRandom always returns finite" do
      for_ [0, 1, 42, 12345, 999999] \seed ->
        assertFinite (seedRandom seed)

-- ────────────────────────────────────────────────────────────────────────────
-- Sine Properties
-- ────────────────────────────────────────────────────────────────────────────

sineProperties :: Spec Unit
sineProperties = do
  describe "timeExpressions.sine" do
    it "sine is bounded by amplitude" do
      for_ [1.0, 5.0, 100.0] \amplitude ->
        for_ [0.0, 0.25, 0.5, 0.75, 1.0, 2.0] \time -> do
          let result = sineWave time 1.0 amplitude 0.0
          assertInRange (negate amplitude - 1.0e-10) (amplitude + 1.0e-10) result

    it "sine(0, f, a, 0) = 0" do
      for_ [1.0, 10.0, 50.0] \amplitude ->
        assertCloseTo 1.0e-6 0.0 (sineWave 0.0 1.0 amplitude 0.0)

    it "sine is periodic: sine(t) = sine(t + period)" do
      for_ [0.1, 0.25, 0.5, 0.7] \time ->
        for_ [1.0, 10.0, 50.0] \amplitude -> do
          let frequency = 1.0
          let period = 1.0 / frequency
          let result1 = sineWave time frequency amplitude 0.0
          let result2 = sineWave (time + period) frequency amplitude 0.0
          assertCloseTo 1.0e-6 result1 result2

-- ────────────────────────────────────────────────────────────────────────────
-- Sawtooth Properties
-- ────────────────────────────────────────────────────────────────────────────

sawtoothProperties :: Spec Unit
sawtoothProperties = do
  describe "timeExpressions.sawtooth" do
    it "sawtooth is bounded by amplitude" do
      for_ [1.0, 5.0, 100.0] \amplitude ->
        for_ [0.01, 0.25, 0.5, 0.75, 0.99, 1.5, 2.3] \time -> do
          let result = sawtoothWave time 1.0 amplitude
          assertInRange (negate amplitude - 1.0e-6) (amplitude + 1.0e-6) result

    it "sawtooth is periodic" do
      for_ [0.1, 0.3, 0.7] \time ->
        for_ [1.0, 10.0] \amplitude -> do
          let frequency = 1.0
          let period = 1.0 / frequency
          let t1 = time
          let t2 = time + period * 3.0
          let result1 = sawtoothWave t1 frequency amplitude
          let result2 = sawtoothWave t2 frequency amplitude
          assertCloseTo 1.0e-4 result1 result2

-- ────────────────────────────────────────────────────────────────────────────
-- Square Properties
-- ────────────────────────────────────────────────────────────────────────────

squareProperties :: Spec Unit
squareProperties = do
  describe "timeExpressions.square" do
    it "square only produces +amplitude or -amplitude" do
      for_ [1.0, 5.0, 100.0] \amplitude ->
        for_ [0.1, 0.25, 0.3, 0.6, 0.75, 0.9] \time -> do
          let result = squareWave time 1.0 amplitude
          let isPositive = abs (result - amplitude) < 1.0e-6
          let isNegative = abs (result + amplitude) < 1.0e-6
          if isPositive || isNegative
            then pure unit
            else fail ("square(" <> show time <> ") = " <> show result <> ", expected ±" <> show amplitude)

    it "square is periodic" do
      for_ [0.1, 0.3] \time ->
        for_ [1.0, 10.0] \amplitude -> do
          let frequency = 1.0
          let period = 1.0 / frequency
          let t1 = time + 0.01
          let t2 = t1 + period * 2.0
          let result1 = squareWave t1 frequency amplitude
          let result2 = squareWave t2 frequency amplitude
          assertCloseTo 1.0e-4 result1 result2

-- ────────────────────────────────────────────────────────────────────────────
-- TimeRamp Properties
-- ────────────────────────────────────────────────────────────────────────────

timeRampProperties :: Spec Unit
timeRampProperties = do
  describe "timeExpressions.timeRamp" do
    it "timeRamp at startTime returns startValue" do
      for_ sampleValues \startValue ->
        for_ sampleValues \endValue -> do
          let startTime = 0.0
          let endTime = 10.0
          assertCloseTo 1.0e-6 startValue
            (timeRamp startTime endTime startValue endValue startTime)

    it "timeRamp at endTime returns endValue" do
      for_ sampleValues \startValue ->
        for_ sampleValues \endValue -> do
          let startTime = 0.0
          let endTime = 10.0
          assertCloseTo 1.0e-6 endValue
            (timeRamp startTime endTime startValue endValue endTime)

    it "timeRamp before startTime returns startValue" do
      for_ sampleValues \startValue ->
        for_ sampleValues \endValue -> do
          let startTime = 10.0
          let endTime = 20.0
          timeRamp startTime endTime startValue endValue 5.0
            `shouldEqual` startValue

    it "timeRamp after endTime returns endValue" do
      for_ sampleValues \startValue ->
        for_ sampleValues \endValue -> do
          let startTime = 10.0
          let endTime = 20.0
          timeRamp startTime endTime startValue endValue 25.0
            `shouldEqual` endValue

-- ────────────────────────────────────────────────────────────────────────────
-- Ease Properties
-- ────────────────────────────────────────────────────────────────────────────

easeProperties :: Spec Unit
easeProperties = do
  describe "expressionEase" do
    it "ease at tMin returns vMin" do
      for_ sampleValues \vMin ->
        for_ sampleValues \vMax -> do
          let tMin = 0.0
          let tMax = 10.0
          assertCloseTo 1.0e-6 vMin
            (expressionEase tMin tMin tMax vMin vMax)

    it "ease at tMax returns vMax" do
      for_ sampleValues \vMin ->
        for_ sampleValues \vMax -> do
          let tMin = 0.0
          let tMax = 10.0
          assertCloseTo 1.0e-6 vMax
            (expressionEase tMax tMin tMax vMin vMax)

    it "easeIn at tMin returns vMin" do
      for_ sampleValues \vMin ->
        for_ sampleValues \vMax -> do
          let tMin = 0.0
          let tMax = 10.0
          assertCloseTo 1.0e-6 vMin
            (expressionEaseIn tMin tMin tMax vMin vMax)

    it "easeOut at tMax returns vMax" do
      for_ sampleValues \vMin ->
        for_ sampleValues \vMax -> do
          let tMin = 0.0
          let tMax = 10.0
          assertCloseTo 1.0e-6 vMax
            (expressionEaseOut tMax tMin tMax vMin vMax)

-- ────────────────────────────────────────────────────────────────────────────
-- Degree/Radian Properties
-- ────────────────────────────────────────────────────────────────────────────

degreeRadianProperties :: Spec Unit
degreeRadianProperties = do
  describe "degreesToRadians / radiansToDegrees" do
    it "degreesToRadians -> radiansToDegrees roundtrip" do
      for_ sampleValues \deg -> do
        let rad = degreesToRadians deg
        let back = radiansToDegrees rad
        assertCloseTo 1.0e-6 deg back

    it "90 degrees = PI/2 radians" do
      assertCloseTo 1.0e-10 (pi / 2.0) (degreesToRadians 90.0)

    it "180 degrees = PI radians" do
      assertCloseTo 1.0e-10 pi (degreesToRadians 180.0)

    it "360 degrees = 2*PI radians" do
      assertCloseTo 1.0e-10 (2.0 * pi) (degreesToRadians 360.0)

-- ────────────────────────────────────────────────────────────────────────────
-- Distance Properties
-- ────────────────────────────────────────────────────────────────────────────

distanceProperties :: Spec Unit
distanceProperties = do
  describe "mathExpressions.distance" do
    it "distance from point to itself is 0" do
      for_ sampleValues \x ->
        for_ sampleValues \y ->
          distance x y x y `shouldEqual` 0.0

    it "distance is symmetric: d(A,B) = d(B,A)" do
      for_ samplePairs \{ x1, y1, x2, y2 } -> do
        let d1 = distance x1 y1 x2 y2
        let d2 = distance x2 y2 x1 y1
        assertCloseTo 1.0e-10 d1 d2

    it "distance is always non-negative" do
      for_ samplePairs \{ x1, y1, x2, y2 } -> do
        let d = distance x1 y1 x2 y2
        if d >= 0.0
          then pure unit
          else fail ("distance was negative: " <> show d)

    it "distance matches known values" do
      -- 3-4-5 triangle
      assertCloseTo 1.0e-10 5.0 (distance 0.0 0.0 3.0 4.0)
      -- Horizontal distance
      assertCloseTo 1.0e-10 10.0 (distance 0.0 0.0 10.0 0.0)
      -- Vertical distance
      assertCloseTo 1.0e-10 7.0 (distance 0.0 0.0 0.0 7.0)

-- ────────────────────────────────────────────────────────────────────────────
-- Sample data
-- ────────────────────────────────────────────────────────────────────────────

sampleValues :: Array Number
sampleValues = [ -100.0, -10.0, -1.0, 0.0, 1.0, 10.0, 100.0 ]

samplePairs :: Array { x1 :: Number, y1 :: Number, x2 :: Number, y2 :: Number }
samplePairs =
  [ { x1: 0.0, y1: 0.0, x2: 3.0, y2: 4.0 }
  , { x1: -5.0, y1: 10.0, x2: 5.0, y2: -10.0 }
  , { x1: 100.0, y1: 100.0, x2: -100.0, y2: -100.0 }
  , { x1: 0.0, y1: 0.0, x2: 0.0, y2: 0.0 }
  , { x1: 1.0, y1: 0.0, x2: 0.0, y2: 1.0 }
  ]
