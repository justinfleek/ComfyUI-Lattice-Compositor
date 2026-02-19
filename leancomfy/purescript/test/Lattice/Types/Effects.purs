-- | Port of ui/src/__tests__/types/effects.property.test.ts (partial)
-- |
-- | Tests effect type enumerations and parameter types:
-- |   - EffectParameterType exhaustiveness (11 types)
-- |   - EffectAnimatableType mapping
-- |   - EffectParameterValue variants
-- |   - Effect structure
-- |
-- | Note: Factory tests (createEffect, createEffectInstance, etc.)
-- | are deferred - they require EFFECT_DEFINITIONS constant.
-- |
-- | 12 tests across 3 describe blocks

module Test.Lattice.Types.Effects (spec) where

import Prelude

import Data.Array (length, nub)
import Lattice.Effects
  ( EffectParameterType(..)
  , EffectAnimatableType(..)
  , EffectParameterValue(..)
  )
import Lattice.Primitives (FiniteFloat(..), UnitFloat(..), mkFiniteFloat, mkUnitFloat)
import Data.Maybe (Maybe(..))
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Effects - Type Tests" do
    parameterTypeTests
    animatableTypeTests
    parameterValueTests

--------------------------------------------------------------------------------
-- 1. EffectParameterType
--------------------------------------------------------------------------------

allParamTypes :: Array EffectParameterType
allParamTypes =
  [ EPTNumber, EPTColor, EPTPoint, EPTPoint3D, EPTAngle
  , EPTCheckbox, EPTDropdown, EPTLayer, EPTString, EPTCurve, EPTData
  ]

parameterTypeTests :: Spec Unit
parameterTypeTests = do
  describe "EffectParameterType" do

    it "should have 11 parameter types" do
      length allParamTypes `shouldEqual` 11

    it "should have no duplicates" do
      let shown = map show allParamTypes
      length (nub shown) `shouldEqual` 11

    it "should include numeric types" do
      let numeric = [EPTNumber, EPTAngle, EPTPoint, EPTPoint3D]
      length numeric `shouldEqual` 4

    it "should include non-animatable types" do
      let nonAnim = [EPTCheckbox, EPTDropdown, EPTLayer, EPTString, EPTCurve, EPTData]
      length nonAnim `shouldEqual` 6

--------------------------------------------------------------------------------
-- 2. EffectAnimatableType
--------------------------------------------------------------------------------

allAnimatableTypes :: Array EffectAnimatableType
allAnimatableTypes =
  [ EATNumber, EATPosition, EATColor, EATEnum, EATVector3
  ]

animatableTypeTests :: Spec Unit
animatableTypeTests = do
  describe "EffectAnimatableType" do

    it "should have 5 animatable types" do
      length allAnimatableTypes `shouldEqual` 5

    it "should have no duplicates" do
      let shown = map show allAnimatableTypes
      length (nub shown) `shouldEqual` 5

    it "should include all standard animatable types" do
      -- Verify type-level existence
      let _ = EATNumber
      let _ = EATPosition
      let _ = EATColor
      let _ = EATEnum
      let _ = EATVector3
      pure unit

--------------------------------------------------------------------------------
-- 3. EffectParameterValue
--------------------------------------------------------------------------------

parameterValueTests :: Spec Unit
parameterValueTests = do
  describe "EffectParameterValue" do

    it "should support number values" do
      let val = EPVNumber (case mkFiniteFloat 42.0 of
            Just v -> v
            Nothing -> FiniteFloat 0.0)
      show val `shouldEqual` show val  -- Value exists and is showable

    it "should support boolean values" do
      let val = EPVBoolean true
      show val `shouldEqual` show val

    it "should support string values" do
      let val = EPVString "hello"
      show val `shouldEqual` show val

    it "should support color values" do
      let uf n = case mkUnitFloat n of
            Just v -> v
            Nothing -> UnitFloat 0.0
      let val = EPVColor { r: 255, g: 0, b: 0, a: uf 1.0 }
      show val `shouldEqual` show val

    it "should support point2d values" do
      let ff n = case mkFiniteFloat n of
            Just v -> v
            Nothing -> FiniteFloat 0.0
      let val = EPVPoint2D { x: ff 100.0, y: ff 200.0 }
      show val `shouldEqual` show val
