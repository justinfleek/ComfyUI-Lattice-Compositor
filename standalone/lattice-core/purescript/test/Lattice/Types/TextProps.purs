-- | Port of ui/src/__tests__/types/text.property.test.ts
-- |
-- | Tests createDefaultTextData property-based assertions:
-- |   - Core text properties (text, fontFamily, fontSize, fill, stroke)
-- |   - Character properties (tracking, lineSpacing, blur)
-- |   - Paragraph properties (letterSpacing, lineHeight, textAlign)
-- |   - Path text options
-- |   - Advanced options (anchorPointGrouping, fillAndStroke)
-- |   - Determinism
-- |
-- | 21 tests across 6 describe blocks

module Test.Lattice.Types.TextProps (spec) where

import Prelude

import Data.Maybe (Maybe(..), isNothing, isJust)
import Effect.Aff (Aff)
import Lattice.Primitives
  ( unNonEmptyString, unPositiveFloat, unNonNegativeFloat
  , unFiniteFloat, unPercentage, unHexColor
  )
import Lattice.Text
  ( createDefaultTextData
  , FontStyle(..)
  , TextAlign(..)
  , AnchorPointGrouping(..)
  , FillAndStroke(..)
  , InterCharacterBlending(..)
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

-- ────────────────────────────────────────────────────────────────────────────
-- Test Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "TextData Properties" do
    coreTextTests
    characterTests
    paragraphTests
    pathTests
    advancedTests
    determinismTests

-- ────────────────────────────────────────────────────────────────────────────
-- 1. Core text properties
-- ────────────────────────────────────────────────────────────────────────────

coreTextTests :: Spec Unit
coreTextTests = do
  describe "core text properties" do
    let td = createDefaultTextData

    it "text defaults to 'Text'" do
      td.text `shouldEqual` "Text"

    it "fontFamily defaults to 'Arial'" do
      unNonEmptyString td.fontFamily `shouldEqual` "Arial"

    it "fontSize defaults to 72" do
      shouldBeCloseTo (unPositiveFloat td.fontSize) 72.0 0.01

    it "fontWeight defaults to 'normal'" do
      unNonEmptyString td.fontWeight `shouldEqual` "normal"

    it "fontStyle defaults to FSNormal" do
      td.fontStyle `shouldEqual` FSNormal

    it "fill defaults to white" do
      unHexColor td.fill `shouldEqual` "#ffffff"

    it "stroke defaults to empty" do
      td.stroke `shouldEqual` ""

    it "strokeWidth defaults to 0" do
      shouldBeCloseTo (unNonNegativeFloat td.strokeWidth) 0.0 0.01

-- ────────────────────────────────────────────────────────────────────────────
-- 2. Character properties
-- ────────────────────────────────────────────────────────────────────────────

characterTests :: Spec Unit
characterTests = do
  describe "character properties" do
    let td = createDefaultTextData

    it "tracking defaults to 0" do
      shouldBeCloseTo (unFiniteFloat td.tracking) 0.0 0.01

    it "lineSpacing defaults to 1.2" do
      shouldBeCloseTo (unPositiveFloat td.lineSpacing) 1.2 0.01

    it "characterOffset defaults to 0" do
      td.characterOffset `shouldEqual` 0

    it "characterValue defaults to 0" do
      td.characterValue `shouldEqual` 0

-- ────────────────────────────────────────────────────────────────────────────
-- 3. Paragraph properties
-- ────────────────────────────────────────────────────────────────────────────

paragraphTests :: Spec Unit
paragraphTests = do
  describe "paragraph properties" do
    let td = createDefaultTextData

    it "letterSpacing defaults to 0" do
      shouldBeCloseTo (unFiniteFloat td.letterSpacing) 0.0 0.01

    it "lineHeight defaults to 1.2" do
      shouldBeCloseTo (unPositiveFloat td.lineHeight) 1.2 0.01

    it "textAlign defaults to TACenter" do
      td.textAlign `shouldEqual` TACenter

-- ────────────────────────────────────────────────────────────────────────────
-- 4. Path text options
-- ────────────────────────────────────────────────────────────────────────────

pathTests :: Spec Unit
pathTests = do
  describe "path text options" do
    let td = createDefaultTextData

    it "pathLayerId defaults to empty" do
      td.pathLayerId `shouldEqual` ""

    it "pathReversed defaults to false" do
      td.pathReversed `shouldEqual` false

    it "pathPerpendicularToPath defaults to true" do
      td.pathPerpendicularToPath `shouldEqual` true

-- ────────────────────────────────────────────────────────────────────────────
-- 5. Advanced options
-- ────────────────────────────────────────────────────────────────────────────

advancedTests :: Spec Unit
advancedTests = do
  describe "advanced options" do
    let td = createDefaultTextData

    it "anchorPointGrouping defaults to APGCharacter" do
      td.anchorPointGrouping `shouldEqual` Just APGCharacter

    it "fillAndStroke defaults to FASOFillOverStroke" do
      td.fillAndStroke `shouldEqual` Just FASOFillOverStroke

    it "interCharacterBlending defaults to ICBNormal" do
      td.interCharacterBlending `shouldEqual` Just ICBNormal

-- ────────────────────────────────────────────────────────────────────────────
-- 6. Determinism
-- ────────────────────────────────────────────────────────────────────────────

determinismTests :: Spec Unit
determinismTests = do
  describe "determinism" do

    it "createDefaultTextData is deterministic" do
      let td1 = createDefaultTextData
      let td2 = createDefaultTextData
      td1.text `shouldEqual` td2.text
      td1.fontStyle `shouldEqual` td2.fontStyle
      td1.textAlign `shouldEqual` td2.textAlign
      td1.pathReversed `shouldEqual` td2.pathReversed
