-- | Port of ui/src/__tests__/types/masks.property.test.ts
-- |
-- | Tests mask factory functions:
-- |   - createDefaultMask (fields, defaults, mode)
-- |   - createEllipseMask (fields, defaults, bezier)
-- |   - MaskVertex creation via mkMaskVertex
-- |   - Determinism
-- |
-- | 23 tests across 3 describe blocks

module Test.Lattice.Types.MasksProps (spec) where

import Prelude

import Data.Maybe (Maybe(..), isNothing)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( NonEmptyString(..), mkNonEmptyString
  , unNonEmptyString, unFiniteFloat
  )
import Lattice.Masks
  ( createDefaultMask
  , createEllipseMask
  , mkMaskVertex
  , MaskModeCombine(..)
  , bezierKappa
  , defaultMaskColor
  , defaultEllipseMaskColor
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

defaultPropIds :: { pathPropId :: NonEmptyString
                  , opacityPropId :: NonEmptyString
                  , featherPropId :: NonEmptyString
                  , expansionPropId :: NonEmptyString
                  }
defaultPropIds =
  { pathPropId: nes "path-1"
  , opacityPropId: nes "opacity-1"
  , featherPropId: nes "feather-1"
  , expansionPropId: nes "expansion-1"
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "Masks Properties" do
    defaultMaskTests
    ellipseMaskTests
    vertexTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. createDefaultMask
-- ────────────────────────────────────────────────────────────────────────────

defaultMaskTests :: Spec Unit
defaultMaskTests = do
  describe "createDefaultMask" do
    let mask = createDefaultMask (nes "mask-1") defaultPropIds

    it "has correct id" do
      unNonEmptyString mask.id `shouldEqual` "mask-1"

    it "name is 'Mask 1'" do
      unNonEmptyString mask.name `shouldEqual` "Mask 1"

    it "enabled by default" do
      mask.enabled `shouldEqual` true

    it "not locked by default" do
      mask.locked `shouldEqual` false

    it "mode is add by default" do
      mask.mode `shouldEqual` MMAdd

    it "not inverted by default" do
      mask.inverted `shouldEqual` false

    it "has correct pathPropertyId" do
      unNonEmptyString mask.pathPropertyId `shouldEqual` "path-1"

    it "has correct opacityPropertyId" do
      unNonEmptyString mask.opacityPropertyId `shouldEqual` "opacity-1"

    it "has correct featherPropertyId" do
      unNonEmptyString mask.featherPropertyId `shouldEqual` "feather-1"

    it "featherX is Nothing by default" do
      isNothing mask.featherXPropertyId `shouldEqual` true

    it "featherY is Nothing by default" do
      isNothing mask.featherYPropertyId `shouldEqual` true

    it "has correct expansionPropertyId" do
      unNonEmptyString mask.expansionPropertyId `shouldEqual` "expansion-1"

    it "color is default mask color (yellow)" do
      unNonEmptyString mask.color `shouldEqual` defaultMaskColor

    it "is deterministic" do
      let m1 = createDefaultMask (nes "mask-d") defaultPropIds
      let m2 = createDefaultMask (nes "mask-d") defaultPropIds
      unNonEmptyString m1.name `shouldEqual` unNonEmptyString m2.name
      m1.enabled `shouldEqual` m2.enabled
      m1.mode `shouldEqual` m2.mode

-- ────────────────────────────────────────────────────────────────────────────
-- 2. createEllipseMask
-- ────────────────────────────────────────────────────────────────────────────

ellipseMaskTests :: Spec Unit
ellipseMaskTests = do
  describe "createEllipseMask" do
    let mask = createEllipseMask (nes "emask-1") defaultPropIds 100.0 80.0 200.0 150.0

    it "has correct id" do
      unNonEmptyString mask.id `shouldEqual` "emask-1"

    it "enabled by default" do
      mask.enabled `shouldEqual` true

    it "mode is add" do
      mask.mode `shouldEqual` MMAdd

    it "color is ellipse mask color (cyan)" do
      unNonEmptyString mask.color `shouldEqual` defaultEllipseMaskColor

    it "is deterministic" do
      let m1 = createEllipseMask (nes "em-d") defaultPropIds 100.0 80.0 200.0 150.0
      let m2 = createEllipseMask (nes "em-d") defaultPropIds 100.0 80.0 200.0 150.0
      unNonEmptyString m1.name `shouldEqual` unNonEmptyString m2.name
      m1.mode `shouldEqual` m2.mode

-- ────────────────────────────────────────────────────────────────────────────
-- 3. MaskVertex
-- ────────────────────────────────────────────────────────────────────────────

vertexTests :: Spec Unit
vertexTests = do
  describe "MaskVertex (mkMaskVertex)" do

    it "creates vertex at specified position" do
      let v = mkMaskVertex 100.0 200.0 0.0 0.0 0.0 0.0
      shouldBeCloseTo (unFiniteFloat v.x) 100.0 0.01
      shouldBeCloseTo (unFiniteFloat v.y) 200.0 0.01

    it "creates vertex with tangent handles" do
      let v = mkMaskVertex 0.0 0.0 (-10.0) (-5.0) 10.0 5.0
      shouldBeCloseTo (unFiniteFloat v.inTangentX) (-10.0) 0.01
      shouldBeCloseTo (unFiniteFloat v.inTangentY) (-5.0) 0.01
      shouldBeCloseTo (unFiniteFloat v.outTangentX) 10.0 0.01
      shouldBeCloseTo (unFiniteFloat v.outTangentY) 5.0 0.01

    it "bezierKappa is approximately 0.5523" do
      shouldBeCloseTo bezierKappa 0.5523 0.001

    it "is deterministic" do
      let v1 = mkMaskVertex 50.0 60.0 1.0 2.0 3.0 4.0
      let v2 = mkMaskVertex 50.0 60.0 1.0 2.0 3.0 4.0
      unFiniteFloat v1.x `shouldEqual` unFiniteFloat v2.x
      unFiniteFloat v1.outTangentX `shouldEqual` unFiniteFloat v2.outTangentX
