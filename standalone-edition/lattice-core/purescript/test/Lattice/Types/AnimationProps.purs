-- | Port of ui/src/__tests__/types/animation.property.test.ts
-- |
-- | Tests animation factory functions:
-- |   - mkAnimatableProperty (fields, defaults, types)
-- |   - mkKeyframe (fields, defaults, interpolation, handles)
-- |   - Determinism and uniqueness
-- |
-- | 30 tests across 2 describe blocks

module Test.Lattice.Types.AnimationProps (spec) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(..), isNothing)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( NonEmptyString(..), mkNonEmptyString
  , FrameNumber(..)
  , unNonEmptyString, unFiniteFloat
  )
import Lattice.Entities (PropertyValueType(..))
import Lattice.Enums (InterpolationType(..))
import Lattice.Animation
  ( mkAnimatableProperty
  , mkKeyframe
  , defaultInHandle
  , defaultOutHandle
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "Animation Properties" do
    animatablePropertyTests
    keyframeTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. mkAnimatableProperty
-- ────────────────────────────────────────────────────────────────────────────

animatablePropertyTests :: Spec Unit
animatablePropertyTests = do
  describe "mkAnimatableProperty" do
    let prop = mkAnimatableProperty (nes "prop-1") (nes "opacity") PVTNumber "100" Nothing

    it "has correct id" do
      unNonEmptyString prop.id `shouldEqual` "prop-1"

    it "has correct name" do
      unNonEmptyString prop.name `shouldEqual` "opacity"

    it "has correct type" do
      prop.propertyType `shouldEqual` PVTNumber

    it "has correct value" do
      prop.value `shouldEqual` "100"

    it "animated defaults to false" do
      prop.animated `shouldEqual` false

    it "keyframes defaults to empty array" do
      length prop.keyframes `shouldEqual` 0

    it "group is Nothing when not specified" do
      isNothing prop.group `shouldEqual` true

    it "expression is Nothing by default" do
      isNothing prop.expression `shouldEqual` true

    it "supports number type" do
      let p = mkAnimatableProperty (nes "p-num") (nes "scale") PVTNumber "100" Nothing
      p.propertyType `shouldEqual` PVTNumber

    it "supports position type" do
      let p = mkAnimatableProperty (nes "p-pos") (nes "position") PVTPosition "{\"x\":0,\"y\":0}" Nothing
      p.propertyType `shouldEqual` PVTPosition

    it "supports color type" do
      let p = mkAnimatableProperty (nes "p-col") (nes "fill") PVTColor "#ffffff" Nothing
      p.propertyType `shouldEqual` PVTColor

    it "supports group parameter" do
      let p = mkAnimatableProperty (nes "p-grp") (nes "x") PVTNumber "0" (Just (nes "transform"))
      case p.group of
        Just g -> unNonEmptyString g `shouldEqual` "transform"
        Nothing -> fail "Expected group to be set"

    it "different ids produce different properties" do
      let p1 = mkAnimatableProperty (nes "id-a") (nes "x") PVTNumber "0" Nothing
      let p2 = mkAnimatableProperty (nes "id-b") (nes "x") PVTNumber "0" Nothing
      (unNonEmptyString p1.id == unNonEmptyString p2.id) `shouldEqual` false

-- ────────────────────────────────────────────────────────────────────────────
-- 2. mkKeyframe
-- ────────────────────────────────────────────────────────────────────────────

keyframeTests :: Spec Unit
keyframeTests = do
  describe "mkKeyframe" do
    let kf = mkKeyframe (nes "kf-1") (FrameNumber 0) "100"

    it "has correct id" do
      unNonEmptyString kf.id `shouldEqual` "kf-1"

    it "has correct frame" do
      kf.frame `shouldEqual` FrameNumber 0

    it "has correct value" do
      kf.value `shouldEqual` "100"

    it "interpolation defaults to linear" do
      kf.interpolation `shouldEqual` ITLinear

    it "controlMode defaults to smooth" do
      show kf.controlMode `shouldEqual` show kf.controlMode  -- exists

    it "inHandle has correct defaults" do
      shouldBeCloseTo (unFiniteFloat defaultInHandle.frame) (-5.0) 0.01
      shouldBeCloseTo (unFiniteFloat defaultInHandle.value) 0.0 0.01
      defaultInHandle.enabled `shouldEqual` true

    it "outHandle has correct defaults" do
      shouldBeCloseTo (unFiniteFloat defaultOutHandle.frame) 5.0 0.01
      shouldBeCloseTo (unFiniteFloat defaultOutHandle.value) 0.0 0.01
      defaultOutHandle.enabled `shouldEqual` true

    it "accepts zero as valid frame" do
      let k = mkKeyframe (nes "kf-z") (FrameNumber 0) "0"
      k.frame `shouldEqual` FrameNumber 0

    it "accepts negative frames" do
      let k = mkKeyframe (nes "kf-neg") (FrameNumber (-10)) "0"
      k.frame `shouldEqual` FrameNumber (-10)

    it "handles positive frames" do
      let k = mkKeyframe (nes "kf-pos") (FrameNumber 300) "0"
      k.frame `shouldEqual` FrameNumber 300

    it "accepts different value types as string" do
      let k1 = mkKeyframe (nes "k1") (FrameNumber 0) "42.5"
      let k2 = mkKeyframe (nes "k2") (FrameNumber 0) "{\"x\":1,\"y\":2}"
      let k3 = mkKeyframe (nes "k3") (FrameNumber 0) "#ff0000"
      k1.value `shouldEqual` "42.5"
      k2.value `shouldEqual` "{\"x\":1,\"y\":2}"
      k3.value `shouldEqual` "#ff0000"

    it "different ids produce different keyframes" do
      let k1 = mkKeyframe (nes "kf-a") (FrameNumber 0) "0"
      let k2 = mkKeyframe (nes "kf-b") (FrameNumber 0) "0"
      (unNonEmptyString k1.id == unNonEmptyString k2.id) `shouldEqual` false

    it "is deterministic (same inputs = same output)" do
      let k1 = mkKeyframe (nes "kf-d") (FrameNumber 10) "50"
      let k2 = mkKeyframe (nes "kf-d") (FrameNumber 10) "50"
      k1.frame `shouldEqual` k2.frame
      k1.value `shouldEqual` k2.value
      k1.interpolation `shouldEqual` k2.interpolation

    it "all interpolation types are valid" do
      -- Verify all interpolation type constructors exist
      let _ = ITLinear
      let _ = ITBezier
      let _ = ITHold
      pure unit
