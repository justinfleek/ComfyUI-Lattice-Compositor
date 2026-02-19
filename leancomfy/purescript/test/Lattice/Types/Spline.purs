-- | Port of ui/src/__tests__/types/spline.property.test.ts (partial)
-- |
-- | Tests createDefaultSplineData and createDefaultPathLayerData:
-- |   - All required properties present
-- |   - Default values correct
-- |   - Determinism
-- |
-- | 14 tests across 2 describe blocks

module Test.Lattice.Types.Spline (spec) where

import Prelude

import Data.Array (length)
import Data.Maybe (isNothing)
import Effect.Aff (Aff)
import Lattice.Primitives (unNonEmptyString, unPositiveFloat, unFiniteFloat, unPercentage)
import Lattice.Spline
  ( StrokeType(..)
  , createDefaultSplineData
  , createDefaultPathLayerData
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

shouldBeCloseTo :: Number -> Number -> Number -> Aff Unit
shouldBeCloseTo actual expected tolerance =
  let diff = if actual > expected then actual - expected else expected - actual
  in if diff <= tolerance
    then pure unit
    else fail ("Expected " <> show actual <> " to be close to " <> show expected
               <> " (tolerance " <> show tolerance <> ", diff " <> show diff <> ")")

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Spline - Type Tests" do
    splineDataTests
    pathLayerDataTests

--------------------------------------------------------------------------------
-- 1. createDefaultSplineData
--------------------------------------------------------------------------------

splineDataTests :: Spec Unit
splineDataTests = do
  describe "createDefaultSplineData" do

    it "should have empty pathData" do
      createDefaultSplineData.pathData `shouldEqual` ""

    it "should have empty controlPoints" do
      length createDefaultSplineData.controlPoints `shouldEqual` 0

    it "should not be closed" do
      createDefaultSplineData.closed `shouldEqual` false

    it "should have white stroke (#ffffff)" do
      unNonEmptyString createDefaultSplineData.stroke `shouldEqual` "#ffffff"

    it "should have strokeWidth 2" do
      shouldBeCloseTo (unPositiveFloat createDefaultSplineData.strokeWidth) 2.0 0.01

    it "should have no fill" do
      isNothing createDefaultSplineData.fill `shouldEqual` true

    it "should be deterministic" do
      let s1 = createDefaultSplineData
      let s2 = createDefaultSplineData
      s1.pathData `shouldEqual` s2.pathData
      s1.closed `shouldEqual` s2.closed

    it "should have solid stroke type" do
      createDefaultSplineData.strokeType `shouldEqual` STSolid

    it "should not be animated" do
      createDefaultSplineData.animated `shouldEqual` false

    it "should have no audio reactive" do
      createDefaultSplineData.audioReactiveEnabled `shouldEqual` false

--------------------------------------------------------------------------------
-- 2. createDefaultPathLayerData
--------------------------------------------------------------------------------

pathLayerDataTests :: Spec Unit
pathLayerDataTests = do
  describe "createDefaultPathLayerData" do

    it "should have empty pathData" do
      createDefaultPathLayerData.pathData `shouldEqual` ""

    it "should show guide by default" do
      createDefaultPathLayerData.showGuide `shouldEqual` true

    it "should have cyan guide color (#00FFFF)" do
      unNonEmptyString createDefaultPathLayerData.guideColor `shouldEqual` "#00FFFF"

    it "should have guide dash pattern 5,5" do
      shouldBeCloseTo (unFiniteFloat createDefaultPathLayerData.guideDashPattern.dash) 5.0 0.01
      shouldBeCloseTo (unFiniteFloat createDefaultPathLayerData.guideDashPattern.gap) 5.0 0.01
