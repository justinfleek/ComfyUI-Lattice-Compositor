-- | Port of ui/src/__tests__/services/propertyDriver.test.ts
-- |
-- | Tests property driver remap transform function.
-- | BUG-003 FIX: Prevents division by zero when inMin === inMax.

module Test.Lattice.Services.PropertyDriver (spec) where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertFinite)

-- | Remap a value from one range to another.
-- | BUG-003 FIX: When input range is zero (inMin == inMax),
-- | returns midpoint of output range instead of NaN/Infinity.
applyRemap :: Number -> Number -> Number -> Number -> Number -> Number
applyRemap value inMin inMax outMin outMax =
  let inRange = inMax - inMin
  in
    if inRange == 0.0
      then (outMin + outMax) / 2.0
      else
        let normalized = (value - inMin) / inRange
        in outMin + normalized * (outMax - outMin)

spec :: Spec Unit
spec = do
  describe "PropertyDriver transforms" do
    describe "remap transform" do
      it "remaps value from one range to another" do
        -- 0.5 in [0,1] maps to 50 in [0,100]
        applyRemap 0.5 0.0 1.0 0.0 100.0 `shouldEqual` 50.0
        -- 0 in [0,1] maps to 0 in [0,100]
        applyRemap 0.0 0.0 1.0 0.0 100.0 `shouldEqual` 0.0
        -- 1 in [0,1] maps to 100 in [0,100]
        applyRemap 1.0 0.0 1.0 0.0 100.0 `shouldEqual` 100.0

      it "handles inverted output range" do
        -- 0.5 in [0,1] maps to 50 in [100,0] (inverted)
        applyRemap 0.5 0.0 1.0 100.0 0.0 `shouldEqual` 50.0

      it "handles values outside input range" do
        -- Values outside range are extrapolated
        applyRemap (-0.5) 0.0 1.0 0.0 100.0 `shouldEqual` (-50.0)
        applyRemap 1.5 0.0 1.0 0.0 100.0 `shouldEqual` 150.0

      it "BUG #3 FIXED: inMin === inMax returns output midpoint instead of NaN" do
        -- When input range is zero, return midpoint of output
        applyRemap 0.25 0.5 0.5 0.0 100.0 `shouldEqual` 50.0
        applyRemap 0.5 0.5 0.5 0.0 100.0 `shouldEqual` 50.0
        applyRemap 0.75 0.5 0.5 0.0 100.0 `shouldEqual` 50.0
        -- All should be finite numbers
        assertFinite (applyRemap 0.25 0.5 0.5 0.0 100.0)
        assertFinite (applyRemap 0.5 0.5 0.5 0.0 100.0)
        assertFinite (applyRemap 0.75 0.5 0.5 0.0 100.0)

      it "BUG #3 FIXED: works with any zero-range input" do
        -- Zero range at different points
        applyRemap 0.0 0.0 0.0 0.0 100.0 `shouldEqual` 50.0
        applyRemap 100.0 100.0 100.0 0.0 200.0 `shouldEqual` 100.0
        -- Zero range with asymmetric output
        applyRemap 5.0 5.0 5.0 10.0 30.0 `shouldEqual` 20.0
