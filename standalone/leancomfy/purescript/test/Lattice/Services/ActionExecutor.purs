-- | Port of ui/src/__tests__/services/actionExecutor.test.ts
-- |
-- | Tests wind vector magnitude and direction calculations.
-- | BUG-006 FIX: Handles missing wind components via Maybe pattern.

module Test.Lattice.Services.ActionExecutor (spec) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Number as Number
import Math (sqrt, atan2, pi)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite)

-- | Wind vector with optional components
type Wind = { x :: Maybe Number, y :: Maybe Number }

-- | Safely extract a wind component, defaulting to 0.0 for Nothing or non-finite
safeComponent :: Maybe Number -> Number
safeComponent (Just n)
  | Number.isFinite n = n
safeComponent _ = 0.0

-- | Calculate wind strength (magnitude) from wind vector.
-- | BUG-006 FIX: Missing x/y handled by Maybe — no NaN possible.
calculateWindStrength :: Maybe Wind -> Number
calculateWindStrength Nothing = 0.0
calculateWindStrength (Just wind) =
  let
    windX = safeComponent wind.x
    windY = safeComponent wind.y
  in
    sqrt (windX * windX + windY * windY)

-- | Calculate wind direction in degrees from wind vector.
-- | BUG-006 FIX: Missing x/y handled by Maybe — no NaN possible.
calculateWindDirection :: Maybe Wind -> Number
calculateWindDirection Nothing = 0.0
calculateWindDirection (Just wind) =
  let
    windX = safeComponent wind.x
    windY = safeComponent wind.y
  in
    atan2 windY windX * (180.0 / pi)

spec :: Spec Unit
spec = do
  describe "ActionExecutor physics calculations" do
    windStrengthTests
    windDirectionTests

windStrengthTests :: Spec Unit
windStrengthTests = do
  describe "wind strength calculation" do
    it "calculates wind strength correctly" do
      -- 3-4-5 triangle
      calculateWindStrength (Just { x: Just 3.0, y: Just 4.0 }) `shouldEqual` 5.0
      -- Only x
      calculateWindStrength (Just { x: Just 5.0, y: Just 0.0 }) `shouldEqual` 5.0
      -- Only y
      calculateWindStrength (Just { x: Just 0.0, y: Just 5.0 }) `shouldEqual` 5.0
      -- Zero wind
      calculateWindStrength (Just { x: Just 0.0, y: Just 0.0 }) `shouldEqual` 0.0

    it "returns 0 for missing wind" do
      calculateWindStrength Nothing `shouldEqual` 0.0

    it "BUG #6 FIXED: missing x returns finite number instead of NaN" do
      -- Was: NaN (absent value ** 2 = NaN)
      -- Now: 4 (using windX=0)
      calculateWindStrength (Just { x: Nothing, y: Just 4.0 }) `shouldEqual` 4.0
      assertFinite (calculateWindStrength (Just { x: Nothing, y: Just 4.0 }))

    it "BUG #6 FIXED: missing y returns finite number instead of NaN" do
      calculateWindStrength (Just { x: Just 3.0, y: Nothing }) `shouldEqual` 3.0
      assertFinite (calculateWindStrength (Just { x: Just 3.0, y: Nothing }))

    it "BUG #6 FIXED: empty object returns 0 instead of NaN" do
      -- Was: NaN
      -- Now: 0
      calculateWindStrength (Just { x: Nothing, y: Nothing }) `shouldEqual` 0.0
      assertFinite (calculateWindStrength (Just { x: Nothing, y: Nothing }))

windDirectionTests :: Spec Unit
windDirectionTests = do
  describe "wind direction calculation" do
    it "calculates wind direction correctly" do
      -- Pointing right (positive X)
      calculateWindDirection (Just { x: Just 1.0, y: Just 0.0 }) `shouldEqual` 0.0
      -- Pointing up (positive Y)
      assertCloseTo 1.0e-10 90.0
        (calculateWindDirection (Just { x: Just 0.0, y: Just 1.0 }))
      -- Pointing left (negative X)
      assertCloseTo 1.0e-5 180.0
        (calculateWindDirection (Just { x: Just (-1.0), y: Just 0.0 }))

    it "BUG #6 FIXED: missing props return correct degrees instead of NaN" do
      -- windX=0, windY=1 -> up (90 degrees)
      assertCloseTo 1.0e-10 90.0
        (calculateWindDirection (Just { x: Nothing, y: Just 1.0 }))
      -- windX=1, windY=0 -> right (0 degrees)
      calculateWindDirection (Just { x: Just 1.0, y: Nothing }) `shouldEqual` 0.0
      -- windX=0, windY=0 -> atan2(0,0)=0
      calculateWindDirection (Just { x: Nothing, y: Nothing }) `shouldEqual` 0.0
      assertFinite (calculateWindDirection (Just { x: Nothing, y: Nothing }))
