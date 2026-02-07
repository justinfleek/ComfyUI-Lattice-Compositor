-- | Lattice.Text - Text layer types and animators
-- |
-- | Source: leancomfy/lean/Lattice/Text.lean

module Lattice.Text
  ( FontStyle(..)
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
  , CharacterBlur
  , GroupingAlignment
  , EaseSettings
  , TextRangeSelector
  , TextWigglySelector
  , TextExpressionSelector
  , TextAnimatorProperties
  , TextAnimator
  , TextData
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

data FontStyle = FSNormal | FSItalic

derive instance Eq FontStyle
derive instance Generic FontStyle _
instance Show FontStyle where show = genericShow

data TextAlign = TALeft | TACenter | TARight

derive instance Eq TextAlign
derive instance Generic TextAlign _
instance Show TextAlign where show = genericShow

data AnchorPointGrouping = APGCharacter | APGWord | APGLine | APGAll

derive instance Eq AnchorPointGrouping
derive instance Generic AnchorPointGrouping _
instance Show AnchorPointGrouping where show = genericShow

data FillAndStroke = FASOFillOverStroke | FASOStrokeOverFill

derive instance Eq FillAndStroke
derive instance Generic FillAndStroke _
instance Show FillAndStroke where show = genericShow

data InterCharacterBlending = ICBNormal | ICBMultiply | ICBScreen | ICBOverlay

derive instance Eq InterCharacterBlending
derive instance Generic InterCharacterBlending _
instance Show InterCharacterBlending where show = genericShow

data TextCase = TCNormal | TCUppercase | TCLowercase | TCSmallCaps

derive instance Eq TextCase
derive instance Generic TextCase _
instance Show TextCase where show = genericShow

data VerticalAlign = VANormal | VASuperscript | VASubscript

derive instance Eq VerticalAlign
derive instance Generic VerticalAlign _
instance Show VerticalAlign where show = genericShow

data RangeSelectorMode = RSMPercent | RSMIndex

derive instance Eq RangeSelectorMode
derive instance Generic RangeSelectorMode _
instance Show RangeSelectorMode where show = genericShow

data SelectionBasedOn
  = SBOCharacters | SBOCharactersExcludingSpaces | SBOWords | SBOLines

derive instance Eq SelectionBasedOn
derive instance Generic SelectionBasedOn _
instance Show SelectionBasedOn where show = genericShow

data SelectionShape
  = SSSquare | SSRampUp | SSRampDown | SSTriangle | SSRound | SSSmooth

derive instance Eq SelectionShape
derive instance Generic SelectionShape _
instance Show SelectionShape where show = genericShow

data SelectorMode
  = SMAdd | SMSubtract | SMIntersect | SMMin | SMMax | SMDifference

derive instance Eq SelectorMode
derive instance Generic SelectorMode _
instance Show SelectorMode where show = genericShow

data TextAnimatorPresetType
  = TAPTypewriter | TAPFadeInByCharacter | TAPFadeInByWord
  | TAPBounceIn | TAPWave | TAPScaleIn | TAPRotateIn
  | TAPSlideInLeft | TAPSlideInRight | TAPBlurIn | TAPRandomFade

derive instance Eq TextAnimatorPresetType
derive instance Generic TextAnimatorPresetType _
instance Show TextAnimatorPresetType where show = genericShow

--------------------------------------------------------------------------------
-- Character Blur
--------------------------------------------------------------------------------

type CharacterBlur =
  { x :: NonNegativeFloat
  , y :: NonNegativeFloat
  }

--------------------------------------------------------------------------------
-- Grouping
--------------------------------------------------------------------------------

type GroupingAlignment =
  { x :: Percentage  -- 0-100%
  , y :: Percentage  -- 0-100%
  }

type EaseSettings =
  { high :: Percentage  -- 0-100
  , low  :: Percentage  -- 0-100
  }

--------------------------------------------------------------------------------
-- Selectors
--------------------------------------------------------------------------------

type TextRangeSelector =
  { mode            :: RangeSelectorMode
  , startPropertyId :: NonEmptyString
  , endPropertyId   :: NonEmptyString
  , offsetPropertyId :: NonEmptyString
  , basedOn         :: SelectionBasedOn
  , shape           :: SelectionShape
  , selectorMode    :: Maybe SelectorMode
  , amount          :: Percentage
  , smoothness      :: Percentage
  , randomizeOrder  :: Boolean
  , randomSeed      :: Int
  , ease            :: EaseSettings
  }

type TextWigglySelector =
  { enabled          :: Boolean
  , mode             :: SelectorMode
  , maxAmount        :: Percentage
  , minAmount        :: Percentage
  , wigglesPerSecond :: NonNegativeFloat
  , correlation      :: Percentage
  , lockDimensions   :: Boolean
  , basedOn          :: SelectionBasedOn
  , randomSeed       :: Int
  }

type TextExpressionSelector =
  { enabled          :: Boolean
  , mode             :: SelectorMode
  , amountExpression :: String
  , basedOn          :: SelectionBasedOn
  }

--------------------------------------------------------------------------------
-- Animator
--------------------------------------------------------------------------------

type TextAnimatorProperties =
  { positionPropertyId         :: Maybe NonEmptyString
  , anchorPointPropertyId      :: Maybe NonEmptyString
  , scalePropertyId            :: Maybe NonEmptyString
  , rotationPropertyId         :: Maybe NonEmptyString
  , skewPropertyId             :: Maybe NonEmptyString
  , skewAxisPropertyId         :: Maybe NonEmptyString
  , opacityPropertyId          :: Maybe NonEmptyString
  , fillColorPropertyId        :: Maybe NonEmptyString
  , fillBrightnessPropertyId   :: Maybe NonEmptyString
  , fillSaturationPropertyId   :: Maybe NonEmptyString
  , fillHuePropertyId          :: Maybe NonEmptyString
  , strokeColorPropertyId      :: Maybe NonEmptyString
  , strokeWidthPropertyId      :: Maybe NonEmptyString
  , trackingPropertyId         :: Maybe NonEmptyString
  , lineAnchorPropertyId       :: Maybe NonEmptyString
  , lineSpacingPropertyId      :: Maybe NonEmptyString
  , characterOffsetPropertyId  :: Maybe NonEmptyString
  , blurPropertyId             :: Maybe NonEmptyString
  }

type TextAnimator =
  { id                 :: NonEmptyString
  , name               :: NonEmptyString
  , enabled            :: Boolean
  , rangeSelector      :: TextRangeSelector
  , wigglySelector     :: Maybe TextWigglySelector
  , expressionSelector :: Maybe TextExpressionSelector
  , properties         :: TextAnimatorProperties
  }

--------------------------------------------------------------------------------
-- Text Data
--------------------------------------------------------------------------------

type TextData =
  { text                    :: String
  , fontFamily              :: NonEmptyString
  , fontSize                :: PositiveFloat
  , fontWeight              :: NonEmptyString
  , fontStyle               :: FontStyle
  , fill                    :: HexColor
  , stroke                  :: String
  , strokeWidth             :: NonNegativeFloat
  , tracking                :: FiniteFloat
  , lineSpacing             :: PositiveFloat
  , lineAnchor              :: Percentage
  , characterOffset         :: Int
  , characterValue          :: Int
  , blur                    :: CharacterBlur
  , letterSpacing           :: FiniteFloat
  , lineHeight              :: PositiveFloat
  , textAlign               :: TextAlign
  , pathLayerId             :: String
  , pathReversed            :: Boolean
  , pathPerpendicularToPath :: Boolean
  , pathForceAlignment      :: Boolean
  , pathFirstMargin         :: NonNegativeFloat
  , pathLastMargin          :: NonNegativeFloat
  , pathOffset              :: Percentage
  , pathAlign               :: TextAlign
  , anchorPointGrouping     :: Maybe AnchorPointGrouping
  , groupingAlignment       :: Maybe GroupingAlignment
  , fillAndStroke           :: Maybe FillAndStroke
  , interCharacterBlending  :: Maybe InterCharacterBlending
  , perCharacter3D          :: Boolean
  , baselineShift           :: Maybe FiniteFloat
  , textCase                :: Maybe TextCase
  , verticalAlign           :: Maybe VerticalAlign
  , kerning                 :: Boolean
  , ligatures               :: Boolean
  , discretionaryLigatures  :: Boolean
  , smallCapsFeature        :: Boolean
  , stylisticSet            :: Int  -- 0-20
  , firstLineIndent         :: Maybe FiniteFloat
  , spaceBefore             :: Maybe FiniteFloat
  , spaceAfter              :: Maybe FiniteFloat
  , animators               :: Array TextAnimator
  }
