{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Text
Description : Text layer types and animators
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Text.lean
-}

module Lattice.Text
  ( -- * Enumerations
    FontStyle(..)
  , TextAlign(..)
  , AnchorPointGrouping(..)
  , FillAndStroke(..)
  , InterCharacterBlending(..)
  , TextCase(..)
  , VerticalAlign(..)
  , RangeSelectorMode(..)
  , SelectionBasedOn(..)
  , SelectionShape(..)
  , SelectorMode(..)
  , TextAnimatorPresetType(..)
    -- * Character Blur
  , CharacterBlur(..)
    -- * Grouping
  , GroupingAlignment(..)
  , EaseSettings(..)
    -- * Selectors
  , TextRangeSelector(..)
  , TextWigglySelector(..)
  , TextExpressionSelector(..)
    -- * Animator
  , TextAnimatorProperties(..)
  , TextAnimator(..)
    -- * Text Data
  , TextData(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data FontStyle = FSNormal | FSItalic
  deriving stock (Eq, Show, Generic)

data TextAlign = TALeft | TACenter | TARight
  deriving stock (Eq, Show, Generic)

data AnchorPointGrouping = APGCharacter | APGWord | APGLine | APGAll
  deriving stock (Eq, Show, Generic)

data FillAndStroke = FASOFillOverStroke | FASOStrokeOverFill
  deriving stock (Eq, Show, Generic)

data InterCharacterBlending = ICBNormal | ICBMultiply | ICBScreen | ICBOverlay
  deriving stock (Eq, Show, Generic)

data TextCase = TCNormal | TCUppercase | TCLowercase | TCSmallCaps
  deriving stock (Eq, Show, Generic)

data VerticalAlign = VANormal | VASuperscript | VASubscript
  deriving stock (Eq, Show, Generic)

data RangeSelectorMode = RSMPercent | RSMIndex
  deriving stock (Eq, Show, Generic)

data SelectionBasedOn
  = SBOCharacters | SBOCharactersExcludingSpaces | SBOWords | SBOLines
  deriving stock (Eq, Show, Generic)

data SelectionShape
  = SSSquare | SSRampUp | SSRampDown | SSTriangle | SSRound | SSSmooth
  deriving stock (Eq, Show, Generic)

data SelectorMode
  = SMAdd | SMSubtract | SMIntersect | SMMin | SMMax | SMDifference
  deriving stock (Eq, Show, Generic)

data TextAnimatorPresetType
  = TAPTypewriter | TAPFadeInByCharacter | TAPFadeInByWord
  | TAPBounceIn | TAPWave | TAPScaleIn | TAPRotateIn
  | TAPSlideInLeft | TAPSlideInRight | TAPBlurIn | TAPRandomFade
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Character Blur
--------------------------------------------------------------------------------

data CharacterBlur = CharacterBlur
  { cbX :: !NonNegativeFloat
  , cbY :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Grouping
--------------------------------------------------------------------------------

data GroupingAlignment = GroupingAlignment
  { gaX :: !Percentage  -- 0-100%
  , gaY :: !Percentage  -- 0-100%
  } deriving stock (Eq, Show, Generic)

data EaseSettings = EaseSettings
  { esHigh :: !Percentage  -- 0-100
  , esLow  :: !Percentage  -- 0-100
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Selectors
--------------------------------------------------------------------------------

data TextRangeSelector = TextRangeSelector
  { trsMode            :: !RangeSelectorMode
  , trsStartPropertyId :: !NonEmptyString
  , trsEndPropertyId   :: !NonEmptyString
  , trsOffsetPropertyId :: !NonEmptyString
  , trsBasedOn         :: !SelectionBasedOn
  , trsShape           :: !SelectionShape
  , trsSelectorMode    :: !(Maybe SelectorMode)
  , trsAmount          :: !Percentage
  , trsSmoothness      :: !Percentage
  , trsRandomizeOrder  :: !Bool
  , trsRandomSeed      :: !Int
  , trsEase            :: !EaseSettings
  } deriving stock (Eq, Show, Generic)

data TextWigglySelector = TextWigglySelector
  { twsEnabled          :: !Bool
  , twsMode             :: !SelectorMode
  , twsMaxAmount        :: !Percentage
  , twsMinAmount        :: !Percentage
  , twsWigglesPerSecond :: !NonNegativeFloat
  , twsCorrelation      :: !Percentage
  , twsLockDimensions   :: !Bool
  , twsBasedOn          :: !SelectionBasedOn
  , twsRandomSeed       :: !Int
  } deriving stock (Eq, Show, Generic)

data TextExpressionSelector = TextExpressionSelector
  { tesEnabled          :: !Bool
  , tesMode             :: !SelectorMode
  , tesAmountExpression :: !Text
  , tesBasedOn          :: !SelectionBasedOn
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Animator
--------------------------------------------------------------------------------

data TextAnimatorProperties = TextAnimatorProperties
  { tapPositionPropertyId         :: !(Maybe NonEmptyString)
  , tapAnchorPointPropertyId      :: !(Maybe NonEmptyString)
  , tapScalePropertyId            :: !(Maybe NonEmptyString)
  , tapRotationPropertyId         :: !(Maybe NonEmptyString)
  , tapSkewPropertyId             :: !(Maybe NonEmptyString)
  , tapSkewAxisPropertyId         :: !(Maybe NonEmptyString)
  , tapOpacityPropertyId          :: !(Maybe NonEmptyString)
  , tapFillColorPropertyId        :: !(Maybe NonEmptyString)
  , tapFillBrightnessPropertyId   :: !(Maybe NonEmptyString)
  , tapFillSaturationPropertyId   :: !(Maybe NonEmptyString)
  , tapFillHuePropertyId          :: !(Maybe NonEmptyString)
  , tapStrokeColorPropertyId      :: !(Maybe NonEmptyString)
  , tapStrokeWidthPropertyId      :: !(Maybe NonEmptyString)
  , tapTrackingPropertyId         :: !(Maybe NonEmptyString)
  , tapLineAnchorPropertyId       :: !(Maybe NonEmptyString)
  , tapLineSpacingPropertyId      :: !(Maybe NonEmptyString)
  , tapCharacterOffsetPropertyId  :: !(Maybe NonEmptyString)
  , tapBlurPropertyId             :: !(Maybe NonEmptyString)
  } deriving stock (Eq, Show, Generic)

data TextAnimator = TextAnimator
  { taId                 :: !NonEmptyString
  , taName               :: !NonEmptyString
  , taEnabled            :: !Bool
  , taRangeSelector      :: !TextRangeSelector
  , taWigglySelector     :: !(Maybe TextWigglySelector)
  , taExpressionSelector :: !(Maybe TextExpressionSelector)
  , taProperties         :: !TextAnimatorProperties
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Text Data
--------------------------------------------------------------------------------

data TextData = TextData
  { tdText                    :: !Text
  , tdFontFamily              :: !NonEmptyString
  , tdFontSize                :: !PositiveFloat
  , tdFontWeight              :: !NonEmptyString
  , tdFontStyle               :: !FontStyle
  , tdFill                    :: !HexColor
  , tdStroke                  :: !Text
  , tdStrokeWidth             :: !NonNegativeFloat
  , tdTracking                :: !FiniteFloat
  , tdLineSpacing             :: !PositiveFloat
  , tdLineAnchor              :: !Percentage
  , tdCharacterOffset         :: !Int
  , tdCharacterValue          :: !Int
  , tdBlur                    :: !CharacterBlur
  , tdLetterSpacing           :: !FiniteFloat
  , tdLineHeight              :: !PositiveFloat
  , tdTextAlign               :: !TextAlign
  , tdPathLayerId             :: !Text
  , tdPathReversed            :: !Bool
  , tdPathPerpendicularToPath :: !Bool
  , tdPathForceAlignment      :: !Bool
  , tdPathFirstMargin         :: !NonNegativeFloat
  , tdPathLastMargin          :: !NonNegativeFloat
  , tdPathOffset              :: !Percentage
  , tdPathAlign               :: !TextAlign
  , tdAnchorPointGrouping     :: !(Maybe AnchorPointGrouping)
  , tdGroupingAlignment       :: !(Maybe GroupingAlignment)
  , tdFillAndStroke           :: !(Maybe FillAndStroke)
  , tdInterCharacterBlending  :: !(Maybe InterCharacterBlending)
  , tdPerCharacter3D          :: !Bool
  , tdBaselineShift           :: !(Maybe FiniteFloat)
  , tdTextCase                :: !(Maybe TextCase)
  , tdVerticalAlign           :: !(Maybe VerticalAlign)
  , tdKerning                 :: !Bool
  , tdLigatures               :: !Bool
  , tdDiscretionaryLigatures  :: !Bool
  , tdSmallCapsFeature        :: !Bool
  , tdStylisticSet            :: !Int  -- 0-20
  , tdFirstLineIndent         :: !(Maybe FiniteFloat)
  , tdSpaceBefore             :: !(Maybe FiniteFloat)
  , tdSpaceAfter              :: !(Maybe FiniteFloat)
  , tdAnimators               :: !(Vector TextAnimator)
  } deriving stock (Eq, Show, Generic)
