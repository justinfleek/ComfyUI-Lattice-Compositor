-- |
-- Module      : Lattice.Types.LayerDataText
-- Description : Text layer data types and animators
-- 
-- Migrated from ui/src/types/text.ts
-- These types depend heavily on AnimatableProperty
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.LayerDataText
  ( -- Text data
    TextData(..)
  , TextFontStyle(..)
  , TextAlign(..)
  , TextAnchorPointGrouping(..)
  , TextFillAndStroke(..)
  , TextInterCharacterBlending(..)
  , TextCase(..)
  , TextVerticalAlign(..)
  , TextPathAlign(..)
  -- Text animator
  , TextAnimator(..)
  , TextRangeSelector(..)
  , TextRangeSelectorMode(..)
  , TextRangeSelectorBasedOn(..)
  , TextRangeSelectorShape(..)
  , TextRangeSelectorSelectorMode(..)
  , TextWigglySelector(..)
  , TextExpressionSelector(..)
  , TextAnimatorProperties(..)
  , TextAnimatorPresetType(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  , Value(..)
  )
import Data.Aeson.Key (fromString)
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import qualified Data.Text as Text
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , validateFinite
  , validateNonNegative
  , validateNormalized01
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // text // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Font style
data TextFontStyle
  = TextFontStyleNormal
  | TextFontStyleItalic
  deriving (Eq, Show, Generic)

instance ToJSON TextFontStyle where
  toJSON TextFontStyleNormal = "normal"
  toJSON TextFontStyleItalic = "italic"

instance FromJSON TextFontStyle where
  parseJSON = withText "TextFontStyle" $ \s ->
    case s of
      t | t == Text.pack "normal" -> return TextFontStyleNormal
      t | t == Text.pack "italic" -> return TextFontStyleItalic
      _ -> fail "Invalid TextFontStyle"

-- | Text align
data TextAlign
  = TextAlignLeft
  | TextAlignCenter
  | TextAlignRight
  deriving (Eq, Show, Generic)

instance ToJSON TextAlign where
  toJSON TextAlignLeft = "left"
  toJSON TextAlignCenter = "center"
  toJSON TextAlignRight = "right"

instance FromJSON TextAlign where
  parseJSON = withText "TextAlign" $ \s ->
    case s of
      t | t == Text.pack "left" -> return TextAlignLeft
      t | t == Text.pack "center" -> return TextAlignCenter
      t | t == Text.pack "right" -> return TextAlignRight
      _ -> fail "Invalid TextAlign"

-- | Anchor point grouping
data TextAnchorPointGrouping
  = TextAnchorPointGroupingCharacter
  | TextAnchorPointGroupingWord
  | TextAnchorPointGroupingLine
  | TextAnchorPointGroupingAll
  deriving (Eq, Show, Generic)

instance ToJSON TextAnchorPointGrouping where
  toJSON TextAnchorPointGroupingCharacter = "character"
  toJSON TextAnchorPointGroupingWord = "word"
  toJSON TextAnchorPointGroupingLine = "line"
  toJSON TextAnchorPointGroupingAll = "all"

instance FromJSON TextAnchorPointGrouping where
  parseJSON = withText "TextAnchorPointGrouping" $ \s ->
    case s of
      t | t == Text.pack "character" -> return TextAnchorPointGroupingCharacter
      t | t == Text.pack "word" -> return TextAnchorPointGroupingWord
      t | t == Text.pack "line" -> return TextAnchorPointGroupingLine
      t | t == Text.pack "all" -> return TextAnchorPointGroupingAll
      _ -> fail "Invalid TextAnchorPointGrouping"

-- | Fill and stroke order
data TextFillAndStroke
  = TextFillAndStrokeFillOverStroke
  | TextFillAndStrokeStrokeOverFill
  deriving (Eq, Show, Generic)

instance ToJSON TextFillAndStroke where
  toJSON TextFillAndStrokeFillOverStroke = "fill-over-stroke"
  toJSON TextFillAndStrokeStrokeOverFill = "stroke-over-fill"

instance FromJSON TextFillAndStroke where
  parseJSON = withText "TextFillAndStroke" $ \s ->
    case s of
      t | t == Text.pack "fill-over-stroke" -> return TextFillAndStrokeFillOverStroke
      t | t == Text.pack "stroke-over-fill" -> return TextFillAndStrokeStrokeOverFill
      _ -> fail "Invalid TextFillAndStroke"

-- | Inter-character blending
data TextInterCharacterBlending
  = TextInterCharacterBlendingNormal
  | TextInterCharacterBlendingMultiply
  | TextInterCharacterBlendingScreen
  | TextInterCharacterBlendingOverlay
  deriving (Eq, Show, Generic)

instance ToJSON TextInterCharacterBlending where
  toJSON TextInterCharacterBlendingNormal = "normal"
  toJSON TextInterCharacterBlendingMultiply = "multiply"
  toJSON TextInterCharacterBlendingScreen = "screen"
  toJSON TextInterCharacterBlendingOverlay = "overlay"

instance FromJSON TextInterCharacterBlending where
  parseJSON = withText "TextInterCharacterBlending" $ \s ->
    case s of
      t | t == Text.pack "normal" -> return TextInterCharacterBlendingNormal
      t | t == Text.pack "multiply" -> return TextInterCharacterBlendingMultiply
      t | t == Text.pack "screen" -> return TextInterCharacterBlendingScreen
      t | t == Text.pack "overlay" -> return TextInterCharacterBlendingOverlay
      _ -> fail "Invalid TextInterCharacterBlending"

-- | Text case
data TextCase
  = TextCaseNormal
  | TextCaseUppercase
  | TextCaseLowercase
  | TextCaseSmallCaps
  deriving (Eq, Show, Generic)

instance ToJSON TextCase where
  toJSON TextCaseNormal = "normal"
  toJSON TextCaseUppercase = "uppercase"
  toJSON TextCaseLowercase = "lowercase"
  toJSON TextCaseSmallCaps = "smallCaps"

instance FromJSON TextCase where
  parseJSON = withText "TextCase" $ \s ->
    case s of
      t | t == Text.pack "normal" -> return TextCaseNormal
      t | t == Text.pack "uppercase" -> return TextCaseUppercase
      t | t == Text.pack "lowercase" -> return TextCaseLowercase
      t | t == Text.pack "smallCaps" -> return TextCaseSmallCaps
      _ -> fail "Invalid TextCase"

-- | Vertical align
data TextVerticalAlign
  = TextVerticalAlignNormal
  | TextVerticalAlignSuperscript
  | TextVerticalAlignSubscript
  deriving (Eq, Show, Generic)

instance ToJSON TextVerticalAlign where
  toJSON TextVerticalAlignNormal = "normal"
  toJSON TextVerticalAlignSuperscript = "superscript"
  toJSON TextVerticalAlignSubscript = "subscript"

instance FromJSON TextVerticalAlign where
  parseJSON = withText "TextVerticalAlign" $ \s ->
    case s of
      t | t == Text.pack "normal" -> return TextVerticalAlignNormal
      t | t == Text.pack "superscript" -> return TextVerticalAlignSuperscript
      t | t == Text.pack "subscript" -> return TextVerticalAlignSubscript
      _ -> fail "Invalid TextVerticalAlign"

-- | Path align
data TextPathAlign
  = TextPathAlignLeft
  | TextPathAlignCenter
  | TextPathAlignRight
  deriving (Eq, Show, Generic)

instance ToJSON TextPathAlign where
  toJSON TextPathAlignLeft = "left"
  toJSON TextPathAlignCenter = "center"
  toJSON TextPathAlignRight = "right"

instance FromJSON TextPathAlign where
  parseJSON = withText "TextPathAlign" $ \s ->
    case s of
      _ | s == Text.pack "left" -> return TextPathAlignLeft
      _ | s == Text.pack "center" -> return TextPathAlignCenter
      _ | s == Text.pack "right" -> return TextPathAlignRight
      _ -> fail "Invalid TextPathAlign"

-- | Text data
data TextData = TextData
  { textDataText :: Text  -- Source Text
  , textDataFontFamily :: Text
  , textDataFontSize :: Double
  , textDataFontWeight :: Text
  , textDataFontStyle :: TextFontStyle
  , textDataFill :: Text  -- Color hex
  , textDataStroke :: Text  -- Color hex
  , textDataStrokeWidth :: Double
  , textDataTracking :: Double  -- Tracking (spacing)
  , textDataLineSpacing :: Double  -- Leading
  , textDataLineAnchor :: Double  -- 0% to 100%
  , textDataCharacterOffset :: Double  -- Integer shift
  , textDataCharacterValue :: Double  -- Unicode shift
  , textDataBlur :: Vec2  -- Per-character blur
  , textDataLetterSpacing :: Double  -- Alias for tracking
  , textDataLineHeight :: Double  -- Alias for lineSpacing
  , textDataTextAlign :: TextAlign
  , textDataPathLayerId :: Text  -- Path layer ID (empty string = no path)
  , textDataPathReversed :: Bool  -- Reverse Path direction
  , textDataPathPerpendicularToPath :: Bool  -- Characters perpendicular to path tangent
  , textDataPathForceAlignment :: Bool  -- Force alignment to path
  , textDataPathFirstMargin :: Double  -- First Margin (pixels from path start)
  , textDataPathLastMargin :: Double  -- Last Margin (pixels from path end)
  , textDataPathOffset :: Double  -- 0-100%, animatable - shifts all characters along path
  , textDataPathAlign :: TextPathAlign  -- Baseline alignment
  , textDataAnchorPointGrouping :: Maybe TextAnchorPointGrouping
  , textDataGroupingAlignment :: Maybe Vec2  -- Percentages
  , textDataFillAndStroke :: Maybe TextFillAndStroke
  , textDataInterCharacterBlending :: Maybe TextInterCharacterBlending
  , textDataPerCharacter3D :: Maybe Bool
  , textDataBaselineShift :: Maybe Double  -- Vertical shift in pixels
  , textDataTextCase :: Maybe TextCase
  , textDataVerticalAlign :: Maybe TextVerticalAlign
  , textDataKerning :: Maybe Bool  -- Enable/disable kerning (default: true)
  , textDataLigatures :: Maybe Bool  -- Enable standard ligatures (default: true)
  , textDataDiscretionaryLigatures :: Maybe Bool  -- Enable discretionary ligatures (default: false)
  , textDataSmallCapsFeature :: Maybe Bool  -- Use OpenType small caps (default: false)
  , textDataStylisticSet :: Maybe Double  -- Stylistic set 1-20 (0 = none)
  , textDataFirstLineIndent :: Maybe Double  -- Pixels
  , textDataSpaceBefore :: Maybe Double  -- Pixels before paragraph
  , textDataSpaceAfter :: Maybe Double  -- Pixels after paragraph
  , textDataAnimators :: Maybe [TextAnimator]  -- Text Animators (per-character animation)
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextData where
  toJSON (TextData text fontFamily fontSize fontWeight fontStyle fill stroke strokeWidth tracking lineSpacing lineAnchor charOffset charValue blur letterSpacing lineHeight textAlign pathLayerId pathReversed pathPerp pathForce pathFirstMargin pathLastMargin pathOffset pathAlign mAnchorGroup mGroupAlign mFillStroke mInterChar mPerChar3D mBaselineShift mTextCase mVertAlign mKerning mLigatures mDiscLigatures mSmallCaps mStylisticSet mFirstIndent mSpaceBefore mSpaceAfter mAnimators) =
    let
      baseFields = ["text" .= text, "fontFamily" .= fontFamily, "fontSize" .= fontSize, "fontWeight" .= fontWeight, "fontStyle" .= fontStyle, "fill" .= fill, "stroke" .= stroke, "strokeWidth" .= strokeWidth, "tracking" .= tracking, "lineSpacing" .= lineSpacing, "lineAnchor" .= lineAnchor, "characterOffset" .= charOffset, "characterValue" .= charValue, "blur" .= blur, "letterSpacing" .= letterSpacing, "lineHeight" .= lineHeight, "textAlign" .= textAlign, "pathLayerId" .= pathLayerId, "pathReversed" .= pathReversed, "pathPerpendicularToPath" .= pathPerp, "pathForceAlignment" .= pathForce, "pathFirstMargin" .= pathFirstMargin, "pathLastMargin" .= pathLastMargin, "pathOffset" .= pathOffset, "pathAlign" .= pathAlign]
      f1 = case mAnchorGroup of Just g -> ("anchorPointGrouping" .= g) : baseFields; Nothing -> baseFields
      f2 = case mGroupAlign of Just a -> ("groupingAlignment" .= a) : f1; Nothing -> f1
      f3 = case mFillStroke of Just f -> ("fillAndStroke" .= f) : f2; Nothing -> f2
      f4 = case mInterChar of Just i -> ("interCharacterBlending" .= i) : f3; Nothing -> f3
      f5 = case mPerChar3D of Just p -> ("perCharacter3D" .= p) : f4; Nothing -> f4
      f6 = case mBaselineShift of Just b -> ("baselineShift" .= b) : f5; Nothing -> f5
      f7 = case mTextCase of Just c -> ("textCase" .= c) : f6; Nothing -> f6
      f8 = case mVertAlign of Just v -> ("verticalAlign" .= v) : f7; Nothing -> f7
      f9 = case mKerning of Just k -> ("kerning" .= k) : f8; Nothing -> f8
      f10 = case mLigatures of Just l -> ("ligatures" .= l) : f9; Nothing -> f9
      f11 = case mDiscLigatures of Just d -> ("discretionaryLigatures" .= d) : f10; Nothing -> f10
      f12 = case mSmallCaps of Just s -> ("smallCapsFeature" .= s) : f11; Nothing -> f11
      f13 = case mStylisticSet of Just st -> ("stylisticSet" .= st) : f12; Nothing -> f12
      f14 = case mFirstIndent of Just f -> ("firstLineIndent" .= f) : f13; Nothing -> f13
      f15 = case mSpaceBefore of Just s -> ("spaceBefore" .= s) : f14; Nothing -> f14
      f16 = case mSpaceAfter of Just s -> ("spaceAfter" .= s) : f15; Nothing -> f15
      f17 = case mAnimators of Just a -> ("animators" .= a) : f16; Nothing -> f16
    in object f17

instance FromJSON TextData where
  parseJSON = withObject "TextData" $ \o -> do
    text <- o .: "text"
    fontFamily <- o .: "fontFamily"
    fontSize <- o .: "fontSize"
    fontWeight <- o .: "fontWeight"
    fontStyle <- o .: "fontStyle"
    fill <- o .: "fill"
    stroke <- o .: "stroke"
    strokeWidth <- o .: "strokeWidth"
    tracking <- o .: "tracking"
    lineSpacing <- o .: "lineSpacing"
    lineAnchor <- o .: "lineAnchor"
    charOffset <- o .: "characterOffset"
    charValue <- o .: "characterValue"
    blur <- o .: "blur"
    letterSpacing <- o .: "letterSpacing"
    lineHeight <- o .: "lineHeight"
    textAlign <- o .: "textAlign"
    pathLayerId <- o .: "pathLayerId"
    pathReversed <- o .: "pathReversed"
    pathPerp <- o .: "pathPerpendicularToPath"
    pathForce <- o .: "pathForceAlignment"
    pathFirstMargin <- o .: "pathFirstMargin"
    pathLastMargin <- o .: "pathLastMargin"
    pathOffset <- o .: "pathOffset"
    pathAlign <- o .: "pathAlign"
    mAnchorGroup <- o .:? "anchorPointGrouping"
    mGroupAlign <- o .:? "groupingAlignment"
    mFillStroke <- o .:? "fillAndStroke"
    mInterChar <- o .:? "interCharacterBlending"
    mPerChar3D <- o .:? "perCharacter3D"
    mBaselineShift <- o .:? "baselineShift"
    mTextCase <- o .:? "textCase"
    mVertAlign <- o .:? "verticalAlign"
    mKerning <- o .:? "kerning"
    mLigatures <- o .:? "ligatures"
    mDiscLigatures <- o .:? "discretionaryLigatures"
    mSmallCaps <- o .:? "smallCapsFeature"
    mStylisticSet <- o .:? "stylisticSet"
    mFirstIndent <- o .:? "firstLineIndent"
    mSpaceBefore <- o .:? "spaceBefore"
    mSpaceAfter <- o .:? "spaceAfter"
    mAnimators <- o .:? "animators"
    -- Validate numeric values
    if validateFinite fontSize && validateFinite strokeWidth && validateFinite tracking &&
       validateFinite lineSpacing && validateFinite lineAnchor && validateFinite charOffset &&
       validateFinite charValue && validateFinite letterSpacing && validateFinite lineHeight &&
       validateFinite pathFirstMargin && validateFinite pathLastMargin && validateFinite pathOffset &&
       validateNonNegative fontSize && validateNonNegative strokeWidth &&
       validateNormalized01 (lineAnchor / 100) && validateNormalized01 (pathOffset / 100) &&
       maybe True (\s -> validateFinite s && validateNormalized01 (s / 20) && s >= 0 && s <= 20) mStylisticSet &&
       maybe True (\b -> validateFinite b) mBaselineShift &&
       maybe True (\f -> validateFinite f) mFirstIndent &&
       maybe True (\s -> validateFinite s) mSpaceBefore &&
       maybe True (\s -> validateFinite s) mSpaceAfter
      then return (TextData text fontFamily fontSize fontWeight fontStyle fill stroke strokeWidth tracking lineSpacing lineAnchor charOffset charValue blur letterSpacing lineHeight textAlign pathLayerId pathReversed pathPerp pathForce pathFirstMargin pathLastMargin pathOffset pathAlign mAnchorGroup mGroupAlign mFillStroke mInterChar mPerChar3D mBaselineShift mTextCase mVertAlign mKerning mLigatures mDiscLigatures mSmallCaps mStylisticSet mFirstIndent mSpaceBefore mSpaceAfter mAnimators)
      else fail "TextData: numeric values must be finite and within valid ranges"

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // text // animator
-- ════════════════════════════════════════════════════════════════════════════

-- | Range selector mode
data TextRangeSelectorMode
  = TextRangeSelectorModePercent
  | TextRangeSelectorModeIndex
  deriving (Eq, Show, Generic)

instance ToJSON TextRangeSelectorMode where
  toJSON TextRangeSelectorModePercent = "percent"
  toJSON TextRangeSelectorModeIndex = "index"

instance FromJSON TextRangeSelectorMode where
  parseJSON = withText "TextRangeSelectorMode" $ \s ->
    case s of
      t | t == Text.pack "percent" -> return TextRangeSelectorModePercent
      t | t == Text.pack "index" -> return TextRangeSelectorModeIndex
      _ -> fail "Invalid TextRangeSelectorMode"

-- | Range selector based on
data TextRangeSelectorBasedOn
  = TextRangeSelectorBasedOnCharacters
  | TextRangeSelectorBasedOnCharactersExcludingSpaces
  | TextRangeSelectorBasedOnWords
  | TextRangeSelectorBasedOnLines
  deriving (Eq, Show, Generic)

instance ToJSON TextRangeSelectorBasedOn where
  toJSON TextRangeSelectorBasedOnCharacters = "characters"
  toJSON TextRangeSelectorBasedOnCharactersExcludingSpaces = "characters_excluding_spaces"
  toJSON TextRangeSelectorBasedOnWords = "words"
  toJSON TextRangeSelectorBasedOnLines = "lines"

instance FromJSON TextRangeSelectorBasedOn where
  parseJSON = withText "TextRangeSelectorBasedOn" $ \s ->
    case s of
      t | t == Text.pack "characters" -> return TextRangeSelectorBasedOnCharacters
      t | t == Text.pack "characters_excluding_spaces" -> return TextRangeSelectorBasedOnCharactersExcludingSpaces
      t | t == Text.pack "words" -> return TextRangeSelectorBasedOnWords
      t | t == Text.pack "lines" -> return TextRangeSelectorBasedOnLines
      _ -> fail "Invalid TextRangeSelectorBasedOn"

-- | Range selector shape
data TextRangeSelectorShape
  = TextRangeSelectorShapeSquare
  | TextRangeSelectorShapeRampUp
  | TextRangeSelectorShapeRampDown
  | TextRangeSelectorShapeTriangle
  | TextRangeSelectorShapeRound
  | TextRangeSelectorShapeSmooth
  deriving (Eq, Show, Generic)

instance ToJSON TextRangeSelectorShape where
  toJSON TextRangeSelectorShapeSquare = "square"
  toJSON TextRangeSelectorShapeRampUp = "ramp_up"
  toJSON TextRangeSelectorShapeRampDown = "ramp_down"
  toJSON TextRangeSelectorShapeTriangle = "triangle"
  toJSON TextRangeSelectorShapeRound = "round"
  toJSON TextRangeSelectorShapeSmooth = "smooth"

instance FromJSON TextRangeSelectorShape where
  parseJSON = withText "TextRangeSelectorShape" $ \s ->
    case s of
      t | t == Text.pack "square" -> return TextRangeSelectorShapeSquare
      t | t == Text.pack "ramp_up" -> return TextRangeSelectorShapeRampUp
      t | t == Text.pack "ramp_down" -> return TextRangeSelectorShapeRampDown
      t | t == Text.pack "triangle" -> return TextRangeSelectorShapeTriangle
      t | t == Text.pack "round" -> return TextRangeSelectorShapeRound
      t | t == Text.pack "smooth" -> return TextRangeSelectorShapeSmooth
      _ -> fail "Invalid TextRangeSelectorShape"

-- | Range selector selector mode
data TextRangeSelectorSelectorMode
  = TextRangeSelectorSelectorModeAdd
  | TextRangeSelectorSelectorModeSubtract
  | TextRangeSelectorSelectorModeIntersect
  | TextRangeSelectorSelectorModeMin
  | TextRangeSelectorSelectorModeMax
  | TextRangeSelectorSelectorModeDifference
  deriving (Eq, Show, Generic)

instance ToJSON TextRangeSelectorSelectorMode where
  toJSON TextRangeSelectorSelectorModeAdd = "add"
  toJSON TextRangeSelectorSelectorModeSubtract = "subtract"
  toJSON TextRangeSelectorSelectorModeIntersect = "intersect"
  toJSON TextRangeSelectorSelectorModeMin = "min"
  toJSON TextRangeSelectorSelectorModeMax = "max"
  toJSON TextRangeSelectorSelectorModeDifference = "difference"

instance FromJSON TextRangeSelectorSelectorMode where
  parseJSON = withText "TextRangeSelectorSelectorMode" $ \s ->
    case s of
      t | t == Text.pack "add" -> return TextRangeSelectorSelectorModeAdd
      t | t == Text.pack "subtract" -> return TextRangeSelectorSelectorModeSubtract
      t | t == Text.pack "intersect" -> return TextRangeSelectorSelectorModeIntersect
      t | t == Text.pack "min" -> return TextRangeSelectorSelectorModeMin
      t | t == Text.pack "max" -> return TextRangeSelectorSelectorModeMax
      t | t == Text.pack "difference" -> return TextRangeSelectorSelectorModeDifference
      _ -> fail "Invalid TextRangeSelectorSelectorMode"

-- | Range selector
data TextRangeSelector = TextRangeSelector
  { textRangeSelectorMode :: TextRangeSelectorMode  -- Units mode
  , textRangeSelectorStart :: AnimatableProperty Double  -- Selection range (0-100 for percent, integers for index)
  , textRangeSelectorEnd :: AnimatableProperty Double
  , textRangeSelectorOffset :: AnimatableProperty Double
  , textRangeSelectorBasedOn :: TextRangeSelectorBasedOn  -- Selection unit
  , textRangeSelectorShape :: TextRangeSelectorShape  -- Shape for selection falloff
  , textRangeSelectorSelectorMode :: Maybe TextRangeSelectorSelectorMode  -- Selector Mode (how multiple selectors combine)
  , textRangeSelectorAmount :: Maybe Double  -- 0-100%, overall influence of this selector
  , textRangeSelectorSmoothness :: Maybe Double  -- 0-100%, smoothing of selection edges
  , textRangeSelectorRandomizeOrder :: Bool  -- Randomness
  , textRangeSelectorRandomSeed :: Double
  , textRangeSelectorEase :: (Double, Double)  -- Easing { high, low } 0-100
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextRangeSelector where
  toJSON (TextRangeSelector mode start end offset basedOn shape mSelectorMode mAmount mSmoothness randomizeOrder randomSeed (easeHigh, easeLow)) =
    let
      baseFields = ["mode" .= mode, "start" .= start, "end" .= end, "offset" .= offset, "basedOn" .= basedOn, "shape" .= shape, "randomizeOrder" .= randomizeOrder, "randomSeed" .= randomSeed, "ease" .= object ["high" .= easeHigh, "low" .= easeLow]]
      withSelectorMode = case mSelectorMode of Just m -> ("selectorMode" .= m) : baseFields; Nothing -> baseFields
      withAmount = case mAmount of Just a -> ("amount" .= a) : withSelectorMode; Nothing -> withSelectorMode
      withSmoothness = case mSmoothness of Just s -> ("smoothness" .= s) : withAmount; Nothing -> withAmount
    in object withSmoothness

instance FromJSON TextRangeSelector where
  parseJSON = withObject "TextRangeSelector" $ \o -> do
    mode <- o .: "mode"
    start <- o .: "start"
    end <- o .: "end"
    offset <- o .: "offset"
    basedOn <- o .: "basedOn"
    shape <- o .: "shape"
    mSelectorMode <- o .:? "selectorMode"
    mAmount <- o .:? "amount"
    mSmoothness <- o .:? "smoothness"
    randomizeOrder <- o .: "randomizeOrder"
    randomSeed <- o .: "randomSeed"
    easeObj <- o .: "ease"
    easeHigh <- easeObj .: "high"
    easeLow <- easeObj .: "low"
    if validateFinite randomSeed &&
       maybe True (\a -> validateFinite a && validateNormalized01 (a / 100)) mAmount &&
       maybe True (\s -> validateFinite s && validateNormalized01 (s / 100)) mSmoothness &&
       validateFinite easeHigh && validateFinite easeLow &&
       validateNormalized01 (easeHigh / 100) && validateNormalized01 (easeLow / 100)
      then return (TextRangeSelector mode start end offset basedOn shape mSelectorMode mAmount mSmoothness randomizeOrder randomSeed (easeHigh, easeLow))
      else fail "TextRangeSelector: numeric values must be finite and within valid ranges"

-- | Wiggly selector mode
data TextWigglySelectorMode
  = TextWigglySelectorModeAdd
  | TextWigglySelectorModeSubtract
  | TextWigglySelectorModeIntersect
  | TextWigglySelectorModeMin
  | TextWigglySelectorModeMax
  | TextWigglySelectorModeDifference
  deriving (Eq, Show, Generic)

instance ToJSON TextWigglySelectorMode where
  toJSON TextWigglySelectorModeAdd = "add"
  toJSON TextWigglySelectorModeSubtract = "subtract"
  toJSON TextWigglySelectorModeIntersect = "intersect"
  toJSON TextWigglySelectorModeMin = "min"
  toJSON TextWigglySelectorModeMax = "max"
  toJSON TextWigglySelectorModeDifference = "difference"

instance FromJSON TextWigglySelectorMode where
  parseJSON = withText "TextWigglySelectorMode" $ \s ->
    case s of
      t | t == Text.pack "add" -> return TextWigglySelectorModeAdd
      t | t == Text.pack "subtract" -> return TextWigglySelectorModeSubtract
      t | t == Text.pack "intersect" -> return TextWigglySelectorModeIntersect
      t | t == Text.pack "min" -> return TextWigglySelectorModeMin
      t | t == Text.pack "max" -> return TextWigglySelectorModeMax
      t | t == Text.pack "difference" -> return TextWigglySelectorModeDifference
      _ -> fail "Invalid TextWigglySelectorMode"

-- | Wiggly Selector - adds randomization to property values
data TextWigglySelector = TextWigglySelector
  { textWigglySelectorEnabled :: Bool
  , textWigglySelectorMode :: TextWigglySelectorMode  -- Mode for combining with other selectors
  , textWigglySelectorMaxAmount :: Double  -- 0-100%
  , textWigglySelectorMinAmount :: Double  -- 0-100%
  , textWigglySelectorWigglesPerSecond :: Double  -- How fast values change
  , textWigglySelectorCorrelation :: Double  -- 0% = fully random per character, 100% = all move together (wave)
  , textWigglySelectorLockDimensions :: Bool  -- X and Y wiggle together
  , textWigglySelectorBasedOn :: TextRangeSelectorBasedOn  -- Spatial settings
  , textWigglySelectorRandomSeed :: Double  -- Random seed for deterministic results
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextWigglySelector where
  toJSON (TextWigglySelector enabled mode maxAmount minAmount wigglesPerSecond correlation lockDimensions basedOn randomSeed) =
    object
      [ "enabled" .= enabled
      , "mode" .= mode
      , "maxAmount" .= maxAmount
      , "minAmount" .= minAmount
      , "wigglesPerSecond" .= wigglesPerSecond
      , "correlation" .= correlation
      , "lockDimensions" .= lockDimensions
      , "basedOn" .= basedOn
      , "randomSeed" .= randomSeed
      ]

instance FromJSON TextWigglySelector where
  parseJSON = withObject "TextWigglySelector" $ \o -> do
    enabled <- o .: "enabled"
    mode <- o .: "mode"
    maxAmount <- o .: "maxAmount"
    minAmount <- o .: "minAmount"
    wigglesPerSecond <- o .: "wigglesPerSecond"
    correlation <- o .: "correlation"
    lockDimensions <- o .: "lockDimensions"
    basedOn <- o .: "basedOn"
    randomSeed <- o .: "randomSeed"
    if validateFinite maxAmount && validateFinite minAmount && validateFinite wigglesPerSecond &&
       validateFinite correlation && validateFinite randomSeed &&
       validateNormalized01 (maxAmount / 100) && validateNormalized01 (minAmount / 100) &&
       validateNormalized01 (correlation / 100) && validateNonNegative wigglesPerSecond &&
       minAmount <= maxAmount
      then return (TextWigglySelector enabled mode maxAmount minAmount wigglesPerSecond correlation lockDimensions basedOn randomSeed)
      else fail "TextWigglySelector: numeric values must be finite and within valid ranges"

-- | Expression selector mode
data TextExpressionSelectorMode
  = TextExpressionSelectorModeAdd
  | TextExpressionSelectorModeSubtract
  | TextExpressionSelectorModeIntersect
  | TextExpressionSelectorModeMin
  | TextExpressionSelectorModeMax
  | TextExpressionSelectorModeDifference
  deriving (Eq, Show, Generic)

instance ToJSON TextExpressionSelectorMode where
  toJSON TextExpressionSelectorModeAdd = "add"
  toJSON TextExpressionSelectorModeSubtract = "subtract"
  toJSON TextExpressionSelectorModeIntersect = "intersect"
  toJSON TextExpressionSelectorModeMin = "min"
  toJSON TextExpressionSelectorModeMax = "max"
  toJSON TextExpressionSelectorModeDifference = "difference"

instance FromJSON TextExpressionSelectorMode where
  parseJSON = withText "TextExpressionSelectorMode" $ \s ->
    case s of
      t | t == Text.pack "add" -> return TextExpressionSelectorModeAdd
      t | t == Text.pack "subtract" -> return TextExpressionSelectorModeSubtract
      t | t == Text.pack "intersect" -> return TextExpressionSelectorModeIntersect
      t | t == Text.pack "min" -> return TextExpressionSelectorModeMin
      t | t == Text.pack "max" -> return TextExpressionSelectorModeMax
      t | t == Text.pack "difference" -> return TextExpressionSelectorModeDifference
      _ -> fail "Invalid TextExpressionSelectorMode"

-- | Expression Selector - programmatic control via expressions
data TextExpressionSelector = TextExpressionSelector
  { textExpressionSelectorEnabled :: Bool
  , textExpressionSelectorMode :: TextExpressionSelectorMode  -- Mode for combining with other selectors
  , textExpressionSelectorAmountExpression :: Text  -- The expression that calculates amount per character
  , textExpressionSelectorBasedOn :: TextRangeSelectorBasedOn  -- Based on unit
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextExpressionSelector where
  toJSON (TextExpressionSelector enabled mode amountExpression basedOn) =
    object
      [ "enabled" .= enabled
      , "mode" .= mode
      , "amountExpression" .= amountExpression
      , "basedOn" .= basedOn
      ]

instance FromJSON TextExpressionSelector where
  parseJSON = withObject "TextExpressionSelector" $ \o -> do
    enabled <- o .: "enabled"
    mode <- o .: "mode"
    amountExpression <- o .: "amountExpression"
    basedOn <- o .: "basedOn"
    return (TextExpressionSelector enabled mode amountExpression basedOn)

-- | Text animator properties
-- Note: In TypeScript this uses an index signature, but in Haskell we'll use a HashMap
-- For JSON serialization, we'll serialize as an object with known properties
data TextAnimatorProperties = TextAnimatorProperties
  { textAnimatorPropertiesPosition :: Maybe (AnimatableProperty Vec2)
  , textAnimatorPropertiesAnchorPoint :: Maybe (AnimatableProperty Vec2)
  , textAnimatorPropertiesScale :: Maybe (AnimatableProperty Vec2)
  , textAnimatorPropertiesRotation :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesSkew :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesSkewAxis :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesOpacity :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesFillColor :: Maybe (AnimatableProperty Text)
  , textAnimatorPropertiesFillBrightness :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesFillSaturation :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesFillHue :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesStrokeColor :: Maybe (AnimatableProperty Text)
  , textAnimatorPropertiesStrokeWidth :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesTracking :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesLineAnchor :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesLineSpacing :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesCharacterOffset :: Maybe (AnimatableProperty Double)
  , textAnimatorPropertiesBlur :: Maybe (AnimatableProperty Vec2)
  , textAnimatorPropertiesCustom :: HashMap.HashMap Text Value  -- For dynamic properties
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextAnimatorProperties where
  toJSON (TextAnimatorProperties mPos mAnchor mScale mRot mSkew mSkewAxis mOpacity mFillColor mFillBright mFillSat mFillHue mStrokeColor mStrokeWidth mTracking mLineAnchor mLineSpacing mCharOffset mBlur custom) =
    let
      baseFields = map (\(k, v) -> fromString (Text.unpack k) .= v) (HashMap.toList custom)
      f1 = case mPos of Just p -> (fromString "position" .= p) : baseFields; Nothing -> baseFields
      f2 = case mAnchor of Just a -> (fromString "anchorPoint" .= a) : f1; Nothing -> f1
      f3 = case mScale of Just s -> (fromString "scale" .= s) : f2; Nothing -> f2
      f4 = case mRot of Just r -> (fromString "rotation" .= r) : f3; Nothing -> f3
      f5 = case mSkew of Just s -> (fromString "skew" .= s) : f4; Nothing -> f4
      f6 = case mSkewAxis of Just s -> (fromString "skewAxis" .= s) : f5; Nothing -> f5
      f7 = case mOpacity of Just o -> (fromString "opacity" .= o) : f6; Nothing -> f6
      f8 = case mFillColor of Just c -> (fromString "fillColor" .= c) : f7; Nothing -> f7
      f9 = case mFillBright of Just b -> (fromString "fillBrightness" .= b) : f8; Nothing -> f8
      f10 = case mFillSat of Just s -> (fromString "fillSaturation" .= s) : f9; Nothing -> f9
      f11 = case mFillHue of Just h -> (fromString "fillHue" .= h) : f10; Nothing -> f10
      f12 = case mStrokeColor of Just c -> (fromString "strokeColor" .= c) : f11; Nothing -> f11
      f13 = case mStrokeWidth of Just w -> (fromString "strokeWidth" .= w) : f12; Nothing -> f12
      f14 = case mTracking of Just t -> (fromString "tracking" .= t) : f13; Nothing -> f13
      f15 = case mLineAnchor of Just a -> (fromString "lineAnchor" .= a) : f14; Nothing -> f14
      f16 = case mLineSpacing of Just s -> (fromString "lineSpacing" .= s) : f15; Nothing -> f15
      f17 = case mCharOffset of Just o -> (fromString "characterOffset" .= o) : f16; Nothing -> f16
      f18 = case mBlur of Just b -> (fromString "blur" .= b) : f17; Nothing -> f17
    in object f18

instance FromJSON TextAnimatorProperties where
  parseJSON = withObject "TextAnimatorProperties" $ \o -> do
    mPos <- o .:? "position"
    mAnchor <- o .:? "anchorPoint"
    mScale <- o .:? "scale"
    mRot <- o .:? "rotation"
    mSkew <- o .:? "skew"
    mSkewAxis <- o .:? "skewAxis"
    mOpacity <- o .:? "opacity"
    mFillColor <- o .:? "fillColor"
    mFillBright <- o .:? "fillBrightness"
    mFillSat <- o .:? "fillSaturation"
    mFillHue <- o .:? "fillHue"
    mStrokeColor <- o .:? "strokeColor"
    mStrokeWidth <- o .:? "strokeWidth"
    mTracking <- o .:? "tracking"
    mLineAnchor <- o .:? "lineAnchor"
    mLineSpacing <- o .:? "lineSpacing"
    mCharOffset <- o .:? "characterOffset"
    mBlur <- o .:? "blur"
    -- Extract remaining properties as custom (all key-value pairs not in known keys)
    -- In TypeScript, TextAnimatorProperties uses an index signature for dynamic properties
    -- In Haskell, we parse known properties explicitly and store the rest in custom HashMap
    -- For now, we'll leave custom empty - full implementation would require parsing all remaining keys
    let custom = HashMap.empty
    return (TextAnimatorProperties mPos mAnchor mScale mRot mSkew mSkewAxis mOpacity mFillColor mFillBright mFillSat mFillHue mStrokeColor mStrokeWidth mTracking mLineAnchor mLineSpacing mCharOffset mBlur custom)

-- | Text animator preset type
data TextAnimatorPresetType
  = TextAnimatorPresetTypeTypewriter
  | TextAnimatorPresetTypeFadeInByCharacter
  | TextAnimatorPresetTypeFadeInByWord
  | TextAnimatorPresetTypeBounceIn
  | TextAnimatorPresetTypeWave
  | TextAnimatorPresetTypeScaleIn
  | TextAnimatorPresetTypeRotateIn
  | TextAnimatorPresetTypeSlideInLeft
  | TextAnimatorPresetTypeSlideInRight
  | TextAnimatorPresetTypeBlurIn
  | TextAnimatorPresetTypeRandomFade
  deriving (Eq, Show, Generic)

instance ToJSON TextAnimatorPresetType where
  toJSON TextAnimatorPresetTypeTypewriter = "typewriter"
  toJSON TextAnimatorPresetTypeFadeInByCharacter = "fade_in_by_character"
  toJSON TextAnimatorPresetTypeFadeInByWord = "fade_in_by_word"
  toJSON TextAnimatorPresetTypeBounceIn = "bounce_in"
  toJSON TextAnimatorPresetTypeWave = "wave"
  toJSON TextAnimatorPresetTypeScaleIn = "scale_in"
  toJSON TextAnimatorPresetTypeRotateIn = "rotate_in"
  toJSON TextAnimatorPresetTypeSlideInLeft = "slide_in_left"
  toJSON TextAnimatorPresetTypeSlideInRight = "slide_in_right"
  toJSON TextAnimatorPresetTypeBlurIn = "blur_in"
  toJSON TextAnimatorPresetTypeRandomFade = "random_fade"

instance FromJSON TextAnimatorPresetType where
  parseJSON = withText "TextAnimatorPresetType" $ \s ->
    case s of
      t | t == Text.pack "typewriter" -> return TextAnimatorPresetTypeTypewriter
      t | t == Text.pack "fade_in_by_character" -> return TextAnimatorPresetTypeFadeInByCharacter
      t | t == Text.pack "fade_in_by_word" -> return TextAnimatorPresetTypeFadeInByWord
      t | t == Text.pack "bounce_in" -> return TextAnimatorPresetTypeBounceIn
      t | t == Text.pack "wave" -> return TextAnimatorPresetTypeWave
      t | t == Text.pack "scale_in" -> return TextAnimatorPresetTypeScaleIn
      t | t == Text.pack "rotate_in" -> return TextAnimatorPresetTypeRotateIn
      t | t == Text.pack "slide_in_left" -> return TextAnimatorPresetTypeSlideInLeft
      t | t == Text.pack "slide_in_right" -> return TextAnimatorPresetTypeSlideInRight
      t | t == Text.pack "blur_in" -> return TextAnimatorPresetTypeBlurIn
      t | t == Text.pack "random_fade" -> return TextAnimatorPresetTypeRandomFade
      _ -> fail "Invalid TextAnimatorPresetType"

-- | Text animator (per-character animation)
data TextAnimator = TextAnimator
  { textAnimatorId :: Text
  , textAnimatorName :: Text
  , textAnimatorEnabled :: Bool
  , textAnimatorRangeSelector :: TextRangeSelector  -- Selectors (can have multiple - Range, Wiggly, Expression)
  , textAnimatorWigglySelector :: Maybe TextWigglySelector
  , textAnimatorExpressionSelector :: Maybe TextExpressionSelector
  , textAnimatorProperties :: TextAnimatorProperties  -- Animatable Properties
  }
  deriving (Eq, Show, Generic)

instance ToJSON TextAnimator where
  toJSON (TextAnimator id_ name enabled rangeSelector mWiggly mExpression properties) =
    let
      baseFields = ["id" .= id_, "name" .= name, "enabled" .= enabled, "rangeSelector" .= rangeSelector, "properties" .= properties]
      withWiggly = case mWiggly of Just w -> ("wigglySelector" .= w) : baseFields; Nothing -> baseFields
      withExpression = case mExpression of Just e -> ("expressionSelector" .= e) : withWiggly; Nothing -> withWiggly
    in object withExpression

instance FromJSON TextAnimator where
  parseJSON = withObject "TextAnimator" $ \o -> do
    id_ <- o .: "id"
    name <- o .: "name"
    enabled <- o .: "enabled"
    rangeSelector <- o .: "rangeSelector"
    mWiggly <- o .:? "wigglySelector"
    mExpression <- o .:? "expressionSelector"
    properties <- o .: "properties"
    return (TextAnimator id_ name enabled rangeSelector mWiggly mExpression properties)
