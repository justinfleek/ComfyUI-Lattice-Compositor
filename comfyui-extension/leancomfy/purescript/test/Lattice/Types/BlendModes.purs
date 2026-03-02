-- | Port of ui/src/__tests__/types/blendModes.property.test.ts
-- |
-- | Tests blend mode utilities:
-- |   - blendModeCategory mapping
-- |   - categoryModes retrieval
-- |   - allBlendModes enumeration
-- |   - String conversion roundtrips
-- |
-- | 15 tests across 4 describe blocks

module Test.Lattice.Types.BlendModes (spec) where

import Prelude

import Data.Array (length, nub, all, elem, concatMap)
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.BlendModes
  ( BlendMode(..)
  , BlendModeCategory(..)
  , blendModeCategory
  , categoryModes
  , allBlendModes
  , blendModeToString
  , blendModeFromString
  )

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "BlendModes - Type Tests" do
    blendModeCategoryTests
    categoryModesTests
    allBlendModesTests
    stringConversionTests

--------------------------------------------------------------------------------
-- 1. blendModeCategory
--------------------------------------------------------------------------------

blendModeCategoryTests :: Spec Unit
blendModeCategoryTests = do
  describe "blendModeCategory" do

    it "should categorize Normal modes correctly" do
      blendModeCategory BMNormal `shouldEqual` BMCNormal
      blendModeCategory BMDissolve `shouldEqual` BMCNormal

    it "should categorize Darken modes correctly" do
      blendModeCategory BMDarken `shouldEqual` BMCDarken
      blendModeCategory BMMultiply `shouldEqual` BMCDarken
      blendModeCategory BMColorBurn `shouldEqual` BMCDarken
      blendModeCategory BMLinearBurn `shouldEqual` BMCDarken
      blendModeCategory BMDarkerColor `shouldEqual` BMCDarken

    it "should categorize Lighten modes correctly" do
      blendModeCategory BMLighten `shouldEqual` BMCLighten
      blendModeCategory BMScreen `shouldEqual` BMCLighten
      blendModeCategory BMColorDodge `shouldEqual` BMCLighten
      blendModeCategory BMLinearDodge `shouldEqual` BMCLighten
      blendModeCategory BMAdd `shouldEqual` BMCLighten

    it "should categorize Contrast modes correctly" do
      blendModeCategory BMOverlay `shouldEqual` BMCContrast
      blendModeCategory BMSoftLight `shouldEqual` BMCContrast
      blendModeCategory BMHardLight `shouldEqual` BMCContrast
      blendModeCategory BMHardMix `shouldEqual` BMCContrast

    it "should categorize Inversion modes correctly" do
      blendModeCategory BMDifference `shouldEqual` BMCInversion
      blendModeCategory BMExclusion `shouldEqual` BMCInversion
      blendModeCategory BMSubtract `shouldEqual` BMCInversion
      blendModeCategory BMDivide `shouldEqual` BMCInversion

    it "should categorize Component modes correctly" do
      blendModeCategory BMHue `shouldEqual` BMCComponent
      blendModeCategory BMSaturation `shouldEqual` BMCComponent
      blendModeCategory BMColor `shouldEqual` BMCComponent
      blendModeCategory BMLuminosity `shouldEqual` BMCComponent

    it "should categorize Utility modes correctly" do
      blendModeCategory BMStencilAlpha `shouldEqual` BMCUtility
      blendModeCategory BMStencilLuma `shouldEqual` BMCUtility
      blendModeCategory BMAlphaAdd `shouldEqual` BMCUtility

    it "should categorize classic modes to parent categories" do
      blendModeCategory BMClassicColorBurn `shouldEqual` BMCDarken
      blendModeCategory BMClassicColorDodge `shouldEqual` BMCLighten

--------------------------------------------------------------------------------
-- 2. categoryModes
--------------------------------------------------------------------------------

categoryModesTests :: Spec Unit
categoryModesTests = do
  describe "categoryModes" do

    it "should return correct number of modes per category" do
      length (categoryModes BMCNormal) `shouldEqual` 2
      length (categoryModes BMCDarken) `shouldEqual` 5
      length (categoryModes BMCLighten) `shouldEqual` 6
      length (categoryModes BMCContrast) `shouldEqual` 7
      length (categoryModes BMCInversion) `shouldEqual` 4
      length (categoryModes BMCComponent) `shouldEqual` 4
      length (categoryModes BMCUtility) `shouldEqual` 6

    it "should not have duplicates within a category" do
      let categories = [BMCNormal, BMCDarken, BMCLighten, BMCContrast, BMCInversion, BMCComponent, BMCUtility]
      for_ categories \cat -> do
        let modes = categoryModes cat
        let unique = nub modes
        length unique `shouldEqual` length modes

    it "should return modes that map back to the same category" do
      let categories = [BMCNormal, BMCDarken, BMCLighten, BMCContrast, BMCInversion, BMCComponent, BMCUtility]
      for_ categories \cat -> do
        let modes = categoryModes cat
        for_ modes \mode -> do
          blendModeCategory mode `shouldEqual` cat

--------------------------------------------------------------------------------
-- 3. allBlendModes
--------------------------------------------------------------------------------

allBlendModesTests :: Spec Unit
allBlendModesTests = do
  describe "allBlendModes" do

    it "should contain all blend modes (36 total)" do
      length allBlendModes `shouldEqual` 36

    it "should have no duplicates" do
      let unique = nub allBlendModes
      length unique `shouldEqual` length allBlendModes

    it "should contain all category modes" do
      let categories = [BMCNormal, BMCDarken, BMCLighten, BMCContrast, BMCInversion, BMCComponent, BMCUtility]
      let allFromCategories = concatMap categoryModes categories
      for_ allFromCategories \mode ->
        if elem mode allBlendModes
          then pure unit
          else fail ("Expected allBlendModes to contain " <> show mode)

--------------------------------------------------------------------------------
-- 4. String conversion
--------------------------------------------------------------------------------

stringConversionTests :: Spec Unit
stringConversionTests = do
  describe "blendModeToString / blendModeFromString" do

    it "should roundtrip all blend modes through string conversion" do
      for_ allBlendModes \mode -> do
        let str = blendModeToString mode
        case blendModeFromString str of
          Just parsed -> parsed `shouldEqual` mode
          Nothing -> fail ("Failed to parse string: " <> str <> " for mode " <> show mode)

    it "should return Nothing for unknown strings" do
      isNothing (blendModeFromString "unknown-mode") `shouldEqual` true
      isNothing (blendModeFromString "") `shouldEqual` true
      isNothing (blendModeFromString "Normal") `shouldEqual` true  -- case sensitive

    it "should produce kebab-case strings" do
      blendModeToString BMColorBurn `shouldEqual` "color-burn"
      blendModeToString BMSoftLight `shouldEqual` "soft-light"
      blendModeToString BMNormal `shouldEqual` "normal"

    it "should parse all known strings successfully" do
      let knownStrings =
            [ "normal", "dissolve", "darken", "multiply", "color-burn"
            , "lighten", "screen", "overlay", "soft-light", "hard-light"
            , "difference", "exclusion", "hue", "saturation", "color", "luminosity"
            ]
      for_ knownStrings \str ->
        isJust (blendModeFromString str) `shouldEqual` true
