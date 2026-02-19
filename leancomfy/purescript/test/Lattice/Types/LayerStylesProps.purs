-- | Port of ui/src/__tests__/types/layerStyles.property.test.ts (partial)
-- |
-- | Tests layer styles type structure:
-- |   - createDefaultLayerStyles factory
-- |   - GlowTechnique, InnerGlowSource, BevelStyle, BevelTechnique
-- |   - StrokePosition, StrokeFillType, GradientOverlayType
-- |   - Structure validation
-- |
-- | Note: Individual style factory tests (createDefaultDropShadow,
-- | createDefaultInnerShadow, etc.) are deferred - they require
-- | creating AnimatableProperty-based style records.
-- |
-- | 15 tests across 3 describe blocks

module Test.Lattice.Types.LayerStylesProps (spec) where

import Prelude

import Data.Array (length, nub)
import Data.Maybe (isNothing)
import Lattice.LayerStyles
  ( createDefaultLayerStyles
  , GlowTechnique(..)
  , InnerGlowSource(..)
  , BevelStyle(..)
  , BevelTechnique(..)
  , BevelDirection(..)
  , GradientOverlayType(..)
  , StrokePosition(..)
  , StrokeFillType(..)
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "LayerStyles Properties" do
    defaultStylesTests
    enumTests
    structureTests

--------------------------------------------------------------------------------
-- 1. createDefaultLayerStyles
--------------------------------------------------------------------------------

defaultStylesTests :: Spec Unit
defaultStylesTests = do
  describe "createDefaultLayerStyles" do
    let styles = createDefaultLayerStyles

    it "enabled defaults to false" do
      styles.enabled `shouldEqual` false

    it "blendingOptions defaults to Nothing" do
      isNothing styles.blendingOptions `shouldEqual` true

    it "dropShadow defaults to Nothing" do
      isNothing styles.dropShadow `shouldEqual` true

    it "innerShadow defaults to Nothing" do
      isNothing styles.innerShadow `shouldEqual` true

    it "outerGlow defaults to Nothing" do
      isNothing styles.outerGlow `shouldEqual` true

    it "innerGlow defaults to Nothing" do
      isNothing styles.innerGlow `shouldEqual` true

    it "bevelEmboss defaults to Nothing" do
      isNothing styles.bevelEmboss `shouldEqual` true

    it "all optional styles default to Nothing" do
      isNothing styles.satin `shouldEqual` true
      isNothing styles.colorOverlay `shouldEqual` true
      isNothing styles.gradientOverlay `shouldEqual` true
      isNothing styles.patternOverlay `shouldEqual` true
      isNothing styles.stroke `shouldEqual` true

    it "is deterministic" do
      let s1 = createDefaultLayerStyles
      let s2 = createDefaultLayerStyles
      s1.enabled `shouldEqual` s2.enabled

--------------------------------------------------------------------------------
-- 2. Enum exhaustiveness
--------------------------------------------------------------------------------

enumTests :: Spec Unit
enumTests = do
  describe "style enums" do

    it "GlowTechnique has 2 variants" do
      let types = [GTSofter, GTPrecise]
      length types `shouldEqual` 2

    it "InnerGlowSource has 2 variants" do
      let sources = [IGSCenter, IGSEdge]
      length sources `shouldEqual` 2

    it "BevelStyle has 5 variants" do
      let styles = [BSOuterBevel, BSInnerBevel, BSEmboss, BSPillowEmboss, BSStrokeEmboss]
      length styles `shouldEqual` 5
      length (nub (map show styles)) `shouldEqual` 5

    it "BevelTechnique has 3 variants" do
      let techs = [BTSmooth, BTChiselHard, BTChiselSoft]
      length techs `shouldEqual` 3

    it "BevelDirection has 2 variants" do
      let dirs = [BDUp, BDDown]
      length dirs `shouldEqual` 2

    it "GradientOverlayType has 5 variants" do
      let types = [GOTLinear, GOTRadial, GOTAngle, GOTReflected, GOTDiamond]
      length types `shouldEqual` 5

    it "StrokePosition has 3 variants" do
      let positions = [SPOutside, SPInside, SPCenter]
      length positions `shouldEqual` 3

    it "StrokeFillType has 3 variants" do
      let types = [SFTColor, SFTGradient, SFTPattern]
      length types `shouldEqual` 3

--------------------------------------------------------------------------------
-- 3. Structure validation
--------------------------------------------------------------------------------

structureTests :: Spec Unit
structureTests = do
  describe "structure validation" do

    it "style disabled by default = no rendering cost" do
      let styles = createDefaultLayerStyles
      styles.enabled `shouldEqual` false
      isNothing styles.dropShadow `shouldEqual` true
