-- | Port of ui/src/__tests__/services/depthflow.test.ts
-- |
-- | Tests depth-based parallax exponential motion calculations.
-- | BUG-004 FIX: Falls back to linear interpolation when startValue is 0.

module Test.Lattice.Services.Depthflow (spec) where

import Prelude

import Math (pow)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite)

-- | Calculate exponential motion between two values.
-- | BUG-004 FIX: When startValue is 0, division by zero is prevented
-- | by falling back to linear interpolation.
calculateExponentialMotion :: Number -> Number -> Number -> Number
calculateExponentialMotion startValue endValue easedT
  | startValue == 0.0 = endValue * easedT
  | otherwise =
      let ratio = endValue / startValue
      in startValue * pow ratio easedT

spec :: Spec Unit
spec = do
  describe "Depthflow motion calculations" do
    describe "exponential motion" do
      it "calculates exponential growth correctly" do
        -- From 1 to 100 with exponential growth
        calculateExponentialMotion 1.0 100.0 0.0 `shouldEqual` 1.0
        calculateExponentialMotion 1.0 100.0 1.0 `shouldEqual` 100.0
        -- Midpoint should be geometric mean (sqrt(1*100) = 10)
        assertCloseTo 0.1 10.0 (calculateExponentialMotion 1.0 100.0 0.5)

      it "handles decay (shrinking values)" do
        -- From 100 to 1 (decay)
        calculateExponentialMotion 100.0 1.0 0.0 `shouldEqual` 100.0
        calculateExponentialMotion 100.0 1.0 1.0 `shouldEqual` 1.0
        assertCloseTo 0.1 10.0 (calculateExponentialMotion 100.0 1.0 0.5)

      it "BUG #4 FIXED: startValue=0 returns linear interpolation instead of NaN" do
        -- Was: NaN for all easedT > 0
        -- Now: Linear interpolation from 0 to endValue
        calculateExponentialMotion 0.0 100.0 0.0 `shouldEqual` 0.0
        calculateExponentialMotion 0.0 100.0 0.5 `shouldEqual` 50.0
        calculateExponentialMotion 0.0 100.0 1.0 `shouldEqual` 100.0
        -- All should be finite numbers
        assertFinite (calculateExponentialMotion 0.0 100.0 0.0)
        assertFinite (calculateExponentialMotion 0.0 100.0 0.5)
        assertFinite (calculateExponentialMotion 0.0 100.0 1.0)

      it "BUG #4 FIXED: startValue=0 with negative endValue" do
        calculateExponentialMotion 0.0 (-100.0) 0.5 `shouldEqual` (-50.0)
        assertFinite (calculateExponentialMotion 0.0 (-100.0) 0.5)

      it "BUG #4 FIXED: both values 0 returns 0" do
        calculateExponentialMotion 0.0 0.0 0.5 `shouldEqual` 0.0
        assertFinite (calculateExponentialMotion 0.0 0.0 0.5)
