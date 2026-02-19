-- | Port of ui/src/__tests__/types/text.property.test.ts
-- |
-- | Tests createDefaultTextData:
-- |   - Core text properties (text, font, fill, stroke)
-- |   - Character properties (tracking, lineSpacing, blur)
-- |   - Paragraph properties (letterSpacing, lineHeight, textAlign)
-- |   - Path options (pathLayerId, pathReversed, etc.)
-- |   - Advanced options (anchorPointGrouping, fillAndStroke, etc.)
-- |   - Determinism and immutability
-- |
-- | 30 tests across 7 describe blocks

module Test.Lattice.Types.Text (spec) where

import Prelude

import Data.Maybe (Maybe(..), isNothing)
import Data.Array (length)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( unNonEmptyString, unPositiveFloat, unNonNegativeFloat
  , unFiniteFloat, unPercentage, unHexColor
  )
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)

import Lattice.Text
  ( TextAlign(..)
  , FontStyle(..)
  , AnchorPointGrouping(..)
  , FillAndStroke(..)
  , InterCharacterBlending(..)
  , createDefaultTextData
  )

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

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "TextData - Type Tests" do
    coreTextTests
    characterTests
    paragraphTests
    pathOptionTests
    advancedOptionTests
    optionalFieldTests
    determinismTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Core text properties
-- ────────────────────────────────────────────────────────────────────────────

coreTextTests :: Spec Unit
coreTextTests = do
  describe "core text properties" do

    it "should have default text 'Text'" do
      createDefaultTextData.text `shouldEqual` "Text"

    it "should have fontFamily 'Arial'" do
      unNonEmptyString createDefaultTextData.fontFamily `shouldEqual` "Arial"

    it "should have fontSize 72" do
      shouldBeCloseTo (unPositiveFloat createDefaultTextData.fontSize) 72.0 0.01

    it "should have fontWeight 'normal'" do
      unNonEmptyString createDefaultTextData.fontWeight `shouldEqual` "normal"

    it "should have fontStyle FSNormal" do
      createDefaultTextData.fontStyle `shouldEqual` FSNormal

    it "should have fill '#ffffff'" do
      unHexColor createDefaultTextData.fill `shouldEqual` "#ffffff"

    it "should have empty stroke" do
      createDefaultTextData.stroke `shouldEqual` ""

    it "should have strokeWidth 0" do
      shouldBeCloseTo (unNonNegativeFloat createDefaultTextData.strokeWidth) 0.0 0.01

-- ────────────────────────────────────────────────────────────────────────────
-- 2. Character properties
-- ────────────────────────────────────────────────────────────────────────────

characterTests :: Spec Unit
characterTests = do
  describe "character properties" do

    it "should have tracking 0" do
      shouldBeCloseTo (unFiniteFloat createDefaultTextData.tracking) 0.0 0.01

    it "should have lineSpacing 1.2" do
      shouldBeCloseTo (unPositiveFloat createDefaultTextData.lineSpacing) 1.2 0.01

    it "should have lineAnchor 50" do
      shouldBeCloseTo (unPercentage createDefaultTextData.lineAnchor) 50.0 0.01

    it "should have characterOffset 0" do
      createDefaultTextData.characterOffset `shouldEqual` 0

    it "should have characterValue 0" do
      createDefaultTextData.characterValue `shouldEqual` 0

    it "should have blur {x: 0, y: 0}" do
      shouldBeCloseTo (unNonNegativeFloat createDefaultTextData.blur.x) 0.0 0.01
      shouldBeCloseTo (unNonNegativeFloat createDefaultTextData.blur.y) 0.0 0.01

-- ────────────────────────────────────────────────────────────────────────────
-- 3. Paragraph properties
-- ────────────────────────────────────────────────────────────────────────────

paragraphTests :: Spec Unit
paragraphTests = do
  describe "paragraph properties" do

    it "should have letterSpacing 0" do
      shouldBeCloseTo (unFiniteFloat createDefaultTextData.letterSpacing) 0.0 0.01

    it "should have lineHeight 1.2" do
      shouldBeCloseTo (unPositiveFloat createDefaultTextData.lineHeight) 1.2 0.01

    it "should have textAlign center" do
      createDefaultTextData.textAlign `shouldEqual` TACenter

-- ────────────────────────────────────────────────────────────────────────────
-- 4. Path options
-- ────────────────────────────────────────────────────────────────────────────

pathOptionTests :: Spec Unit
pathOptionTests = do
  describe "path options" do

    it "should have empty pathLayerId (no path)" do
      createDefaultTextData.pathLayerId `shouldEqual` ""

    it "should have pathReversed false" do
      createDefaultTextData.pathReversed `shouldEqual` false

    it "should have pathPerpendicularToPath true" do
      createDefaultTextData.pathPerpendicularToPath `shouldEqual` true

    it "should have pathForceAlignment false" do
      createDefaultTextData.pathForceAlignment `shouldEqual` false

    it "should have zero path margins" do
      shouldBeCloseTo (unNonNegativeFloat createDefaultTextData.pathFirstMargin) 0.0 0.01
      shouldBeCloseTo (unNonNegativeFloat createDefaultTextData.pathLastMargin) 0.0 0.01

    it "should have pathAlign center" do
      createDefaultTextData.pathAlign `shouldEqual` TACenter

-- ────────────────────────────────────────────────────────────────────────────
-- 5. Advanced options
-- ────────────────────────────────────────────────────────────────────────────

advancedOptionTests :: Spec Unit
advancedOptionTests = do
  describe "advanced options" do

    it "should have anchorPointGrouping character" do
      createDefaultTextData.anchorPointGrouping `shouldEqual` Just APGCharacter

    it "should have groupingAlignment at center" do
      case createDefaultTextData.groupingAlignment of
        Just ga -> do
          shouldBeCloseTo (unPercentage ga.x) 50.0 0.01
          shouldBeCloseTo (unPercentage ga.y) 50.0 0.01
        Nothing -> fail "Expected groupingAlignment to be Just"

    it "should have fillAndStroke fill-over-stroke" do
      createDefaultTextData.fillAndStroke `shouldEqual` Just FASOFillOverStroke

    it "should have interCharacterBlending normal" do
      createDefaultTextData.interCharacterBlending `shouldEqual` Just ICBNormal

    it "should have perCharacter3D false" do
      createDefaultTextData.perCharacter3D `shouldEqual` false

-- ────────────────────────────────────────────────────────────────────────────
-- 6. Optional fields
-- ────────────────────────────────────────────────────────────────────────────

optionalFieldTests :: Spec Unit
optionalFieldTests = do
  describe "optional fields (not in TS defaults)" do

    it "should have baselineShift Nothing" do
      isNothing createDefaultTextData.baselineShift `shouldEqual` true

    it "should have empty animators" do
      length createDefaultTextData.animators `shouldEqual` 0

-- ────────────────────────────────────────────────────────────────────────────
-- 7. Determinism
-- ────────────────────────────────────────────────────────────────────────────

determinismTests :: Spec Unit
determinismTests = do
  describe "determinism" do

    it "should be deterministic (same values every call)" do
      let td1 = createDefaultTextData
      let td2 = createDefaultTextData
      td1.text `shouldEqual` td2.text
      td1.fontStyle `shouldEqual` td2.fontStyle
      td1.textAlign `shouldEqual` td2.textAlign
