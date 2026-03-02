-- | Port of ui/src/__tests__/types/animation.test.ts and animation.property.test.ts
-- |
-- | Tests mkAnimatableProperty and mkKeyframe factories:
-- |   - All required fields present and correct
-- |   - Default values (animated=false, keyframes=[], etc.)
-- |   - Keyframe handle defaults (-5/+5 frame offset)
-- |   - Interpolation and control mode defaults
-- |   - FullInterpolationType classification
-- |   - defaultInHandle and defaultOutHandle
-- |
-- | 25 tests across 5 describe blocks

module Test.Lattice.Types.Animation (spec) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(..), isNothing)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( NonEmptyString(..), mkNonEmptyString
  , FrameNumber(..)
  , unFiniteFloat
  , unNonEmptyString
  )
import Lattice.Entities (PropertyValueType(..), ControlMode(..))
import Lattice.Enums (InterpolationType(..))
import Lattice.Animation
  ( FullInterpolationType(..)
  , isBaseInterpolation
  , isEasingInterpolation
  , defaultInHandle
  , defaultOutHandle
  , mkAnimatableProperty
  , mkKeyframe
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

nes :: String -> NonEmptyString
nes s = case mkNonEmptyString s of
  Just v -> v
  Nothing -> NonEmptyString "error"

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Animation - Type Tests" do
    mkAnimatablePropertyTests
    mkKeyframeTests
    defaultHandleTests
    interpolationTypeTests
    fullInterpolationTypeTests

--------------------------------------------------------------------------------
-- 1. mkAnimatableProperty
--------------------------------------------------------------------------------

mkAnimatablePropertyTests :: Spec Unit
mkAnimatablePropertyTests = do
  describe "mkAnimatableProperty" do

    it "should set id correctly" do
      let prop = mkAnimatableProperty (nes "prop_opacity_1") (nes "opacity") PVTNumber "0" Nothing
      unNonEmptyString prop.id `shouldEqual` "prop_opacity_1"

    it "should set name correctly" do
      let prop = mkAnimatableProperty (nes "id1") (nes "opacity") PVTNumber "0" Nothing
      unNonEmptyString prop.name `shouldEqual` "opacity"

    it "should set value correctly" do
      let prop = mkAnimatableProperty (nes "id1") (nes "opacity") PVTNumber "100" Nothing
      prop.value `shouldEqual` "100"

    it "should set propertyType correctly" do
      let prop = mkAnimatableProperty (nes "id1") (nes "pos") PVTPosition "{}" Nothing
      prop.propertyType `shouldEqual` PVTPosition

    it "should default animated to false" do
      let prop = mkAnimatableProperty (nes "id1") (nes "opacity") PVTNumber "0" Nothing
      prop.animated `shouldEqual` false

    it "should default keyframes to empty array" do
      let prop = mkAnimatableProperty (nes "id1") (nes "opacity") PVTNumber "0" Nothing
      length prop.keyframes `shouldEqual` 0

    it "should set group when provided" do
      let prop = mkAnimatableProperty (nes "id1") (nes "opacity") PVTNumber "0" (Just (nes "Transform"))
      case prop.group of
        Just g -> unNonEmptyString g `shouldEqual` "Transform"
        Nothing -> fail "Expected group to be Just"

    it "should set group to Nothing when not provided" do
      let prop = mkAnimatableProperty (nes "id1") (nes "opacity") PVTNumber "0" Nothing
      isNothing prop.group `shouldEqual` true

    it "should set expression to Nothing" do
      let prop = mkAnimatableProperty (nes "id1") (nes "opacity") PVTNumber "0" Nothing
      isNothing prop.expression `shouldEqual` true

    it "should handle all property types" do
      let n = mkAnimatableProperty (nes "id1") (nes "n") PVTNumber "0" Nothing
      let p = mkAnimatableProperty (nes "id2") (nes "p") PVTPosition "{}" Nothing
      let c = mkAnimatableProperty (nes "id3") (nes "c") PVTColor "#fff" Nothing
      let e = mkAnimatableProperty (nes "id4") (nes "e") PVTEnum "a" Nothing
      let v = mkAnimatableProperty (nes "id5") (nes "v") PVTVector3 "{}" Nothing
      n.propertyType `shouldEqual` PVTNumber
      p.propertyType `shouldEqual` PVTPosition
      c.propertyType `shouldEqual` PVTColor
      e.propertyType `shouldEqual` PVTEnum
      v.propertyType `shouldEqual` PVTVector3

--------------------------------------------------------------------------------
-- 2. mkKeyframe
--------------------------------------------------------------------------------

mkKeyframeTests :: Spec Unit
mkKeyframeTests = do
  describe "mkKeyframe" do

    it "should set id correctly" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 10) "100"
      unNonEmptyString kf.id `shouldEqual` "kf_1"

    it "should set frame correctly" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 30) "100"
      kf.frame `shouldEqual` FrameNumber 30

    it "should set value correctly" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 10) "42.5"
      kf.value `shouldEqual` "42.5"

    it "should default interpolation to ITLinear" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 0) "0"
      kf.interpolation `shouldEqual` ITLinear

    it "should default controlMode to CMSmooth" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 0) "0"
      kf.controlMode `shouldEqual` CMSmooth

    it "should set inHandle with frame -5" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 0) "0"
      shouldBeCloseTo (unFiniteFloat kf.inHandle.frame) (-5.0) 0.01

    it "should set outHandle with frame +5" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 0) "0"
      shouldBeCloseTo (unFiniteFloat kf.outHandle.frame) 5.0 0.01

    it "should set handle values to 0" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 0) "0"
      shouldBeCloseTo (unFiniteFloat kf.inHandle.value) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat kf.outHandle.value) 0.0 0.01

    it "should set handles as enabled" do
      let kf = mkKeyframe (nes "kf_1") (FrameNumber 0) "0"
      kf.inHandle.enabled `shouldEqual` true
      kf.outHandle.enabled `shouldEqual` true

--------------------------------------------------------------------------------
-- 3. Default handles
--------------------------------------------------------------------------------

defaultHandleTests :: Spec Unit
defaultHandleTests = do
  describe "default bezier handles" do

    it "defaultInHandle should have frame -5" do
      shouldBeCloseTo (unFiniteFloat defaultInHandle.frame) (-5.0) 0.01

    it "defaultOutHandle should have frame +5" do
      shouldBeCloseTo (unFiniteFloat defaultOutHandle.frame) 5.0 0.01

    it "both handles should have value 0" do
      shouldBeCloseTo (unFiniteFloat defaultInHandle.value) 0.0 0.01
      shouldBeCloseTo (unFiniteFloat defaultOutHandle.value) 0.0 0.01

    it "both handles should be enabled" do
      defaultInHandle.enabled `shouldEqual` true
      defaultOutHandle.enabled `shouldEqual` true

--------------------------------------------------------------------------------
-- 4. InterpolationType from Enums
--------------------------------------------------------------------------------

interpolationTypeTests :: Spec Unit
interpolationTypeTests = do
  describe "InterpolationType" do

    it "should have all expected variants" do
      -- Verify each variant exists (compiler guarantees exhaustiveness)
      let _ = ITLinear
      let _ = ITBezier
      let _ = ITHold
      let _ = ITEaseIn
      let _ = ITEaseOut
      let _ = ITEaseInOut
      let _ = ITCustom
      pure unit

--------------------------------------------------------------------------------
-- 5. FullInterpolationType classification
--------------------------------------------------------------------------------

fullInterpolationTypeTests :: Spec Unit
fullInterpolationTypeTests = do
  describe "FullInterpolationType" do

    it "should classify base interpolations correctly" do
      isBaseInterpolation FITLinear `shouldEqual` true
      isBaseInterpolation FITBezier `shouldEqual` true
      isBaseInterpolation FITHold `shouldEqual` true

    it "should classify easing interpolations as non-base" do
      isBaseInterpolation FITEaseInSine `shouldEqual` false
      isBaseInterpolation FITEaseOutBounce `shouldEqual` false
      isBaseInterpolation FITEaseInOutElastic `shouldEqual` false

    it "isEasingInterpolation should be inverse of isBaseInterpolation" do
      isEasingInterpolation FITLinear `shouldEqual` false
      isEasingInterpolation FITEaseInSine `shouldEqual` true
      isEasingInterpolation FITEaseOutBounce `shouldEqual` true
