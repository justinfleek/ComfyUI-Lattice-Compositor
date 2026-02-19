-- | Port of ui/src/__tests__/types/layerStyles.property.test.ts (partial)
-- |
-- | Tests createDefaultLayerStyles:
-- |   - enabled defaults to false
-- |   - All style slots are Nothing
-- |   - Determinism
-- |
-- | Note: Individual style factory tests (createDefaultDropShadow, etc.)
-- | would require PS factories that generate property IDs, which differs
-- | architecturally from TS. Those are deferred.
-- |
-- | 5 tests across 1 describe block

module Test.Lattice.Types.LayerStyles (spec) where

import Prelude

import Data.Maybe (isNothing)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)

import Lattice.LayerStyles (createDefaultLayerStyles)

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "LayerStyles - Type Tests" do
    createDefaultLayerStylesTests

createDefaultLayerStylesTests :: Spec Unit
createDefaultLayerStylesTests = do
  describe "createDefaultLayerStyles" do

    it "should have enabled false" do
      createDefaultLayerStyles.enabled `shouldEqual` false

    it "should have no drop shadow" do
      isNothing createDefaultLayerStyles.dropShadow `shouldEqual` true

    it "should have no inner shadow, glows, or bevel" do
      isNothing createDefaultLayerStyles.innerShadow `shouldEqual` true
      isNothing createDefaultLayerStyles.outerGlow `shouldEqual` true
      isNothing createDefaultLayerStyles.innerGlow `shouldEqual` true
      isNothing createDefaultLayerStyles.bevelEmboss `shouldEqual` true

    it "should have no satin, overlays, or stroke" do
      isNothing createDefaultLayerStyles.satin `shouldEqual` true
      isNothing createDefaultLayerStyles.colorOverlay `shouldEqual` true
      isNothing createDefaultLayerStyles.gradientOverlay `shouldEqual` true
      isNothing createDefaultLayerStyles.patternOverlay `shouldEqual` true
      isNothing createDefaultLayerStyles.stroke `shouldEqual` true

    it "should have no blending options" do
      isNothing createDefaultLayerStyles.blendingOptions `shouldEqual` true
