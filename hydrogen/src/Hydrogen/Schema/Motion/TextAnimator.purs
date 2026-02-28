-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // motion // text-animator
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Text animation types for per-character motion effects.
-- |
-- | Text animators allow After Effects-style per-character animation
-- | with range selectors, wiggly selectors, and expression selectors.
-- |
-- | ## Architecture
-- |
-- | Mirrors `Lattice.Text` from the Haskell backend.
-- |
-- | ## Features
-- |
-- | - Range selectors with start/end/offset
-- | - Wiggly selectors for organic movement
-- | - Expression selectors for procedural animation
-- | - Per-character transform properties

module Hydrogen.Schema.Motion.TextAnimator
  ( -- * Enumerations
    FontStyle(..)
  , fontStyleToString
  , fontStyleFromString
  
  , TextAlign(..)
  , textAlignToString
  , textAlignFromString
  
  , AnchorPointGrouping(..)
  , anchorPointGroupingToString
  , anchorPointGroupingFromString
  
  , FillAndStroke(..)
  , fillAndStrokeToString
  , fillAndStrokeFromString
  
  , InterCharacterBlending(..)
  , interCharacterBlendingToString
  , interCharacterBlendingFromString
  
  , TextCase(..)
  , textCaseToString
  , textCaseFromString
  
  , VerticalAlign(..)
  , verticalAlignToString
  , verticalAlignFromString
  
  , RangeSelectorMode(..)
  , rangeSelectorModeToString
  , rangeSelectorModeFromString
  
  , SelectionBasedOn(..)
  , selectionBasedOnToString
  , selectionBasedOnFromString
  
  , SelectionShape(..)
  , selectionShapeToString
  , selectionShapeFromString
  
  , SelectorMode(..)
  , selectorModeToString
  , selectorModeFromString
  
  , TextAnimatorPresetType(..)
  , textAnimatorPresetTypeToString
  , textAnimatorPresetTypeFromString
  
  -- * Character Blur
  , CharacterBlur(..)
  , mkCharacterBlur
  
  -- * Grouping
  , GroupingAlignment(..)
  , mkGroupingAlignment
  
  , EaseSettings(..)
  , mkEaseSettings
  , defaultEaseSettings
  
  -- * Selectors
  , TextRangeSelector(..)
  , defaultTextRangeSelector
  
  , TextWigglySelector(..)
  , defaultTextWigglySelector
  
  , TextExpressionSelector(..)
  , defaultTextExpressionSelector
  
  -- * Animator
  , TextAnimatorProperties(..)
  , defaultTextAnimatorProperties
  
  , TextAnimatorId(..)
  , mkTextAnimatorId
  
  , TextAnimator(..)
  , defaultTextAnimator
  
  -- * Per-Character 3D
  , PerCharacter3DProperties(..)
  , defaultPerCharacter3DProperties
  , CharacterOrientation(..)
  , characterOrientationToString
  , characterOrientationFromString
  
  -- * 3D Text Animator Properties
  , TextAnimator3DProperties(..)
  , defaultTextAnimator3DProperties
  
  -- * Combined 3D Text Animator
  , TextAnimator3D(..)
  , defaultTextAnimator3D
  
  -- * 3D Queries
  , hasAny3DProperties
  , count3DProperties
  , describe3DOrientation
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Motion.Property (AnimatablePropertyId)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // font // style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Font style variant.
data FontStyle
  = FSNormal  -- ^ Normal/regular style
  | FSItalic  -- ^ Italic style

derive instance eqFontStyle :: Eq FontStyle
derive instance ordFontStyle :: Ord FontStyle

instance showFontStyle :: Show FontStyle where
  show FSNormal = "FSNormal"
  show FSItalic = "FSItalic"

fontStyleToString :: FontStyle -> String
fontStyleToString FSNormal = "normal"
fontStyleToString FSItalic = "italic"

fontStyleFromString :: String -> Maybe FontStyle
fontStyleFromString "normal" = Just FSNormal
fontStyleFromString "italic" = Just FSItalic
fontStyleFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // text // align
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text horizontal alignment.
data TextAlign
  = TALeft    -- ^ Left aligned
  | TACenter  -- ^ Center aligned
  | TARight   -- ^ Right aligned

derive instance eqTextAlign :: Eq TextAlign
derive instance ordTextAlign :: Ord TextAlign

instance showTextAlign :: Show TextAlign where
  show TALeft = "TALeft"
  show TACenter = "TACenter"
  show TARight = "TARight"

textAlignToString :: TextAlign -> String
textAlignToString TALeft = "left"
textAlignToString TACenter = "center"
textAlignToString TARight = "right"

textAlignFromString :: String -> Maybe TextAlign
textAlignFromString "left" = Just TALeft
textAlignFromString "center" = Just TACenter
textAlignFromString "right" = Just TARight
textAlignFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // anchor // point // grouping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Grouping for anchor point calculations.
data AnchorPointGrouping
  = APGCharacter  -- ^ Per character
  | APGWord       -- ^ Per word
  | APGLine       -- ^ Per line
  | APGAll        -- ^ All text as one

derive instance eqAnchorPointGrouping :: Eq AnchorPointGrouping
derive instance ordAnchorPointGrouping :: Ord AnchorPointGrouping

instance showAnchorPointGrouping :: Show AnchorPointGrouping where
  show APGCharacter = "APGCharacter"
  show APGWord = "APGWord"
  show APGLine = "APGLine"
  show APGAll = "APGAll"

anchorPointGroupingToString :: AnchorPointGrouping -> String
anchorPointGroupingToString APGCharacter = "character"
anchorPointGroupingToString APGWord = "word"
anchorPointGroupingToString APGLine = "line"
anchorPointGroupingToString APGAll = "all"

anchorPointGroupingFromString :: String -> Maybe AnchorPointGrouping
anchorPointGroupingFromString "character" = Just APGCharacter
anchorPointGroupingFromString "word" = Just APGWord
anchorPointGroupingFromString "line" = Just APGLine
anchorPointGroupingFromString "all" = Just APGAll
anchorPointGroupingFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // fill // and // stroke
-- ═════════════════════════════════════════════════════════════════════════════

-- | Order of fill and stroke rendering.
data FillAndStroke
  = FASOFillOverStroke  -- ^ Fill drawn over stroke
  | FASOStrokeOverFill  -- ^ Stroke drawn over fill

derive instance eqFillAndStroke :: Eq FillAndStroke
derive instance ordFillAndStroke :: Ord FillAndStroke

instance showFillAndStroke :: Show FillAndStroke where
  show FASOFillOverStroke = "FASOFillOverStroke"
  show FASOStrokeOverFill = "FASOStrokeOverFill"

fillAndStrokeToString :: FillAndStroke -> String
fillAndStrokeToString FASOFillOverStroke = "fill-over-stroke"
fillAndStrokeToString FASOStrokeOverFill = "stroke-over-fill"

fillAndStrokeFromString :: String -> Maybe FillAndStroke
fillAndStrokeFromString "fill-over-stroke" = Just FASOFillOverStroke
fillAndStrokeFromString "stroke-over-fill" = Just FASOStrokeOverFill
fillAndStrokeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // inter // character // blending
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend mode between overlapping characters.
data InterCharacterBlending
  = ICBNormal    -- ^ Normal blending
  | ICBMultiply  -- ^ Multiply blend
  | ICBScreen    -- ^ Screen blend
  | ICBOverlay   -- ^ Overlay blend

derive instance eqInterCharacterBlending :: Eq InterCharacterBlending
derive instance ordInterCharacterBlending :: Ord InterCharacterBlending

instance showInterCharacterBlending :: Show InterCharacterBlending where
  show ICBNormal = "ICBNormal"
  show ICBMultiply = "ICBMultiply"
  show ICBScreen = "ICBScreen"
  show ICBOverlay = "ICBOverlay"

interCharacterBlendingToString :: InterCharacterBlending -> String
interCharacterBlendingToString ICBNormal = "normal"
interCharacterBlendingToString ICBMultiply = "multiply"
interCharacterBlendingToString ICBScreen = "screen"
interCharacterBlendingToString ICBOverlay = "overlay"

interCharacterBlendingFromString :: String -> Maybe InterCharacterBlending
interCharacterBlendingFromString "normal" = Just ICBNormal
interCharacterBlendingFromString "multiply" = Just ICBMultiply
interCharacterBlendingFromString "screen" = Just ICBScreen
interCharacterBlendingFromString "overlay" = Just ICBOverlay
interCharacterBlendingFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // text // case
-- ═════════════════════════════════════════════════════════════════════════════

-- | Text case transformation.
data TextCase
  = TCNormal     -- ^ No transformation
  | TCUppercase  -- ^ All uppercase
  | TCLowercase  -- ^ All lowercase
  | TCSmallCaps  -- ^ Small capitals

derive instance eqTextCase :: Eq TextCase
derive instance ordTextCase :: Ord TextCase

instance showTextCase :: Show TextCase where
  show TCNormal = "TCNormal"
  show TCUppercase = "TCUppercase"
  show TCLowercase = "TCLowercase"
  show TCSmallCaps = "TCSmallCaps"

textCaseToString :: TextCase -> String
textCaseToString TCNormal = "normal"
textCaseToString TCUppercase = "uppercase"
textCaseToString TCLowercase = "lowercase"
textCaseToString TCSmallCaps = "small-caps"

textCaseFromString :: String -> Maybe TextCase
textCaseFromString "normal" = Just TCNormal
textCaseFromString "uppercase" = Just TCUppercase
textCaseFromString "lowercase" = Just TCLowercase
textCaseFromString "small-caps" = Just TCSmallCaps
textCaseFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // vertical // align
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vertical alignment for text.
data VerticalAlign
  = VANormal      -- ^ Normal baseline
  | VASuperscript -- ^ Superscript position
  | VASubscript   -- ^ Subscript position

derive instance eqVerticalAlign :: Eq VerticalAlign
derive instance ordVerticalAlign :: Ord VerticalAlign

instance showVerticalAlign :: Show VerticalAlign where
  show VANormal = "VANormal"
  show VASuperscript = "VASuperscript"
  show VASubscript = "VASubscript"

verticalAlignToString :: VerticalAlign -> String
verticalAlignToString VANormal = "normal"
verticalAlignToString VASuperscript = "superscript"
verticalAlignToString VASubscript = "subscript"

verticalAlignFromString :: String -> Maybe VerticalAlign
verticalAlignFromString "normal" = Just VANormal
verticalAlignFromString "superscript" = Just VASuperscript
verticalAlignFromString "subscript" = Just VASubscript
verticalAlignFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // range // selector // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode for range selector values.
data RangeSelectorMode
  = RSMPercent  -- ^ Percentage-based (0-100)
  | RSMIndex    -- ^ Index-based (character index)

derive instance eqRangeSelectorMode :: Eq RangeSelectorMode
derive instance ordRangeSelectorMode :: Ord RangeSelectorMode

instance showRangeSelectorMode :: Show RangeSelectorMode where
  show RSMPercent = "RSMPercent"
  show RSMIndex = "RSMIndex"

rangeSelectorModeToString :: RangeSelectorMode -> String
rangeSelectorModeToString RSMPercent = "percent"
rangeSelectorModeToString RSMIndex = "index"

rangeSelectorModeFromString :: String -> Maybe RangeSelectorMode
rangeSelectorModeFromString "percent" = Just RSMPercent
rangeSelectorModeFromString "index" = Just RSMIndex
rangeSelectorModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // selection // based // on
-- ═════════════════════════════════════════════════════════════════════════════

-- | What the selection is based on.
data SelectionBasedOn
  = SBOCharacters                 -- ^ All characters
  | SBOCharactersExcludingSpaces  -- ^ Characters excluding spaces
  | SBOWords                      -- ^ Words
  | SBOLines                      -- ^ Lines

derive instance eqSelectionBasedOn :: Eq SelectionBasedOn
derive instance ordSelectionBasedOn :: Ord SelectionBasedOn

instance showSelectionBasedOn :: Show SelectionBasedOn where
  show SBOCharacters = "SBOCharacters"
  show SBOCharactersExcludingSpaces = "SBOCharactersExcludingSpaces"
  show SBOWords = "SBOWords"
  show SBOLines = "SBOLines"

selectionBasedOnToString :: SelectionBasedOn -> String
selectionBasedOnToString SBOCharacters = "characters"
selectionBasedOnToString SBOCharactersExcludingSpaces = "characters-excluding-spaces"
selectionBasedOnToString SBOWords = "words"
selectionBasedOnToString SBOLines = "lines"

selectionBasedOnFromString :: String -> Maybe SelectionBasedOn
selectionBasedOnFromString "characters" = Just SBOCharacters
selectionBasedOnFromString "characters-excluding-spaces" = Just SBOCharactersExcludingSpaces
selectionBasedOnFromString "words" = Just SBOWords
selectionBasedOnFromString "lines" = Just SBOLines
selectionBasedOnFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // selection // shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of the selection falloff.
data SelectionShape
  = SSSquare    -- ^ Square/flat selection
  | SSRampUp    -- ^ Ramp up from 0 to 1
  | SSRampDown  -- ^ Ramp down from 1 to 0
  | SSTriangle  -- ^ Triangle peak
  | SSRound     -- ^ Rounded/circular
  | SSSmooth    -- ^ Smooth easing

derive instance eqSelectionShape :: Eq SelectionShape
derive instance ordSelectionShape :: Ord SelectionShape

instance showSelectionShape :: Show SelectionShape where
  show SSSquare = "SSSquare"
  show SSRampUp = "SSRampUp"
  show SSRampDown = "SSRampDown"
  show SSTriangle = "SSTriangle"
  show SSRound = "SSRound"
  show SSSmooth = "SSSmooth"

selectionShapeToString :: SelectionShape -> String
selectionShapeToString SSSquare = "square"
selectionShapeToString SSRampUp = "ramp-up"
selectionShapeToString SSRampDown = "ramp-down"
selectionShapeToString SSTriangle = "triangle"
selectionShapeToString SSRound = "round"
selectionShapeToString SSSmooth = "smooth"

selectionShapeFromString :: String -> Maybe SelectionShape
selectionShapeFromString "square" = Just SSSquare
selectionShapeFromString "ramp-up" = Just SSRampUp
selectionShapeFromString "ramp-down" = Just SSRampDown
selectionShapeFromString "triangle" = Just SSTriangle
selectionShapeFromString "round" = Just SSRound
selectionShapeFromString "smooth" = Just SSSmooth
selectionShapeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // selector // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How multiple selectors combine.
data SelectorMode
  = SMAdd         -- ^ Add amounts
  | SMSubtract    -- ^ Subtract amounts
  | SMIntersect   -- ^ Minimum of amounts
  | SMMin         -- ^ Minimum value
  | SMMax         -- ^ Maximum value
  | SMDifference  -- ^ Absolute difference

derive instance eqSelectorMode :: Eq SelectorMode
derive instance ordSelectorMode :: Ord SelectorMode

instance showSelectorMode :: Show SelectorMode where
  show SMAdd = "SMAdd"
  show SMSubtract = "SMSubtract"
  show SMIntersect = "SMIntersect"
  show SMMin = "SMMin"
  show SMMax = "SMMax"
  show SMDifference = "SMDifference"

selectorModeToString :: SelectorMode -> String
selectorModeToString SMAdd = "add"
selectorModeToString SMSubtract = "subtract"
selectorModeToString SMIntersect = "intersect"
selectorModeToString SMMin = "min"
selectorModeToString SMMax = "max"
selectorModeToString SMDifference = "difference"

selectorModeFromString :: String -> Maybe SelectorMode
selectorModeFromString "add" = Just SMAdd
selectorModeFromString "subtract" = Just SMSubtract
selectorModeFromString "intersect" = Just SMIntersect
selectorModeFromString "min" = Just SMMin
selectorModeFromString "max" = Just SMMax
selectorModeFromString "difference" = Just SMDifference
selectorModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                         // text // animator // preset // type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preset animation types for text.
data TextAnimatorPresetType
  = TAPTypewriter          -- ^ Typewriter reveal
  | TAPFadeInByCharacter   -- ^ Fade in character by character
  | TAPFadeInByWord        -- ^ Fade in word by word
  | TAPBounceIn            -- ^ Bouncy entrance
  | TAPWave                -- ^ Wave motion
  | TAPScaleIn             -- ^ Scale up entrance
  | TAPRotateIn            -- ^ Rotation entrance
  | TAPSlideInLeft         -- ^ Slide from left
  | TAPSlideInRight        -- ^ Slide from right
  | TAPBlurIn              -- ^ Blur to clear
  | TAPRandomFade          -- ^ Random character fade

derive instance eqTextAnimatorPresetType :: Eq TextAnimatorPresetType
derive instance ordTextAnimatorPresetType :: Ord TextAnimatorPresetType

instance showTextAnimatorPresetType :: Show TextAnimatorPresetType where
  show TAPTypewriter = "TAPTypewriter"
  show TAPFadeInByCharacter = "TAPFadeInByCharacter"
  show TAPFadeInByWord = "TAPFadeInByWord"
  show TAPBounceIn = "TAPBounceIn"
  show TAPWave = "TAPWave"
  show TAPScaleIn = "TAPScaleIn"
  show TAPRotateIn = "TAPRotateIn"
  show TAPSlideInLeft = "TAPSlideInLeft"
  show TAPSlideInRight = "TAPSlideInRight"
  show TAPBlurIn = "TAPBlurIn"
  show TAPRandomFade = "TAPRandomFade"

textAnimatorPresetTypeToString :: TextAnimatorPresetType -> String
textAnimatorPresetTypeToString TAPTypewriter = "typewriter"
textAnimatorPresetTypeToString TAPFadeInByCharacter = "fade-in-by-character"
textAnimatorPresetTypeToString TAPFadeInByWord = "fade-in-by-word"
textAnimatorPresetTypeToString TAPBounceIn = "bounce-in"
textAnimatorPresetTypeToString TAPWave = "wave"
textAnimatorPresetTypeToString TAPScaleIn = "scale-in"
textAnimatorPresetTypeToString TAPRotateIn = "rotate-in"
textAnimatorPresetTypeToString TAPSlideInLeft = "slide-in-left"
textAnimatorPresetTypeToString TAPSlideInRight = "slide-in-right"
textAnimatorPresetTypeToString TAPBlurIn = "blur-in"
textAnimatorPresetTypeToString TAPRandomFade = "random-fade"

textAnimatorPresetTypeFromString :: String -> Maybe TextAnimatorPresetType
textAnimatorPresetTypeFromString "typewriter" = Just TAPTypewriter
textAnimatorPresetTypeFromString "fade-in-by-character" = Just TAPFadeInByCharacter
textAnimatorPresetTypeFromString "fade-in-by-word" = Just TAPFadeInByWord
textAnimatorPresetTypeFromString "bounce-in" = Just TAPBounceIn
textAnimatorPresetTypeFromString "wave" = Just TAPWave
textAnimatorPresetTypeFromString "scale-in" = Just TAPScaleIn
textAnimatorPresetTypeFromString "rotate-in" = Just TAPRotateIn
textAnimatorPresetTypeFromString "slide-in-left" = Just TAPSlideInLeft
textAnimatorPresetTypeFromString "slide-in-right" = Just TAPSlideInRight
textAnimatorPresetTypeFromString "blur-in" = Just TAPBlurIn
textAnimatorPresetTypeFromString "random-fade" = Just TAPRandomFade
textAnimatorPresetTypeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // character // blur
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-character blur amount.
type CharacterBlur =
  { x :: Number  -- ^ Horizontal blur (non-negative)
  , y :: Number  -- ^ Vertical blur (non-negative)
  }

-- | Create a character blur value.
mkCharacterBlur :: Number -> Number -> CharacterBlur
mkCharacterBlur x y = { x, y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // grouping // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alignment within a grouping (percentages 0-100).
type GroupingAlignment =
  { x :: Number  -- ^ X alignment (0-100%)
  , y :: Number  -- ^ Y alignment (0-100%)
  }

-- | Create a grouping alignment.
mkGroupingAlignment :: Number -> Number -> GroupingAlignment
mkGroupingAlignment x y = { x, y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // ease // settings
-- ═════════════════════════════════════════════════════════════════════════════

-- | Ease high/low settings for range selector.
type EaseSettings =
  { high :: Number  -- ^ High ease percentage (0-100)
  , low :: Number   -- ^ Low ease percentage (0-100)
  }

-- | Create ease settings.
mkEaseSettings :: Number -> Number -> EaseSettings
mkEaseSettings high low = { high, low }

-- | Default ease settings (no easing).
defaultEaseSettings :: EaseSettings
defaultEaseSettings = { high: 0.0, low: 0.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // text // range // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Range selector for text animation.
-- |
-- | Defines which characters are affected based on start/end/offset.
type TextRangeSelector =
  { mode :: RangeSelectorMode
  , startPropertyId :: AnimatablePropertyId
  , endPropertyId :: AnimatablePropertyId
  , offsetPropertyId :: AnimatablePropertyId
  , basedOn :: SelectionBasedOn
  , shape :: SelectionShape
  , selectorMode :: Maybe SelectorMode
  , amount :: Number           -- ^ Percentage (0-100)
  , smoothness :: Number       -- ^ Percentage (0-100)
  , randomizeOrder :: Boolean
  , randomSeed :: Int
  , ease :: EaseSettings
  }

-- | Default text range selector.
defaultTextRangeSelector 
  :: AnimatablePropertyId 
  -> AnimatablePropertyId 
  -> AnimatablePropertyId 
  -> TextRangeSelector
defaultTextRangeSelector startId endId offsetId =
  { mode: RSMPercent
  , startPropertyId: startId
  , endPropertyId: endId
  , offsetPropertyId: offsetId
  , basedOn: SBOCharacters
  , shape: SSSquare
  , selectorMode: Nothing
  , amount: 100.0
  , smoothness: 0.0
  , randomizeOrder: false
  , randomSeed: 0
  , ease: defaultEaseSettings
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // text // wiggly // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Wiggly selector for organic text animation.
type TextWigglySelector =
  { enabled :: Boolean
  , mode :: SelectorMode
  , maxAmount :: Number         -- ^ Maximum percentage
  , minAmount :: Number         -- ^ Minimum percentage
  , wigglesPerSecond :: Number  -- ^ Frequency (non-negative)
  , correlation :: Number       -- ^ How correlated between characters (0-100%)
  , lockDimensions :: Boolean
  , basedOn :: SelectionBasedOn
  , randomSeed :: Int
  }

-- | Default wiggly selector (disabled).
defaultTextWigglySelector :: TextWigglySelector
defaultTextWigglySelector =
  { enabled: false
  , mode: SMAdd
  , maxAmount: 100.0
  , minAmount: 0.0
  , wigglesPerSecond: 2.0
  , correlation: 50.0
  , lockDimensions: false
  , basedOn: SBOCharacters
  , randomSeed: 0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // text // expression // selector
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expression selector for procedural text animation.
type TextExpressionSelector =
  { enabled :: Boolean
  , mode :: SelectorMode
  , amountExpression :: String   -- ^ Expression code
  , basedOn :: SelectionBasedOn
  }

-- | Default expression selector (disabled).
defaultTextExpressionSelector :: TextExpressionSelector
defaultTextExpressionSelector =
  { enabled: false
  , mode: SMAdd
  , amountExpression: "100"
  , basedOn: SBOCharacters
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // text // animator // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animatable properties for text animator.
-- |
-- | Each field is an optional property ID that can be animated.
type TextAnimatorProperties =
  { positionPropertyId :: Maybe AnimatablePropertyId
  , anchorPointPropertyId :: Maybe AnimatablePropertyId
  , scalePropertyId :: Maybe AnimatablePropertyId
  , rotationPropertyId :: Maybe AnimatablePropertyId
  , skewPropertyId :: Maybe AnimatablePropertyId
  , skewAxisPropertyId :: Maybe AnimatablePropertyId
  , opacityPropertyId :: Maybe AnimatablePropertyId
  , fillColorPropertyId :: Maybe AnimatablePropertyId
  , fillBrightnessPropertyId :: Maybe AnimatablePropertyId
  , fillSaturationPropertyId :: Maybe AnimatablePropertyId
  , fillHuePropertyId :: Maybe AnimatablePropertyId
  , strokeColorPropertyId :: Maybe AnimatablePropertyId
  , strokeWidthPropertyId :: Maybe AnimatablePropertyId
  , trackingPropertyId :: Maybe AnimatablePropertyId
  , lineAnchorPropertyId :: Maybe AnimatablePropertyId
  , lineSpacingPropertyId :: Maybe AnimatablePropertyId
  , characterOffsetPropertyId :: Maybe AnimatablePropertyId
  , blurPropertyId :: Maybe AnimatablePropertyId
  }

-- | Default animator properties (all empty).
defaultTextAnimatorProperties :: TextAnimatorProperties
defaultTextAnimatorProperties =
  { positionPropertyId: Nothing
  , anchorPointPropertyId: Nothing
  , scalePropertyId: Nothing
  , rotationPropertyId: Nothing
  , skewPropertyId: Nothing
  , skewAxisPropertyId: Nothing
  , opacityPropertyId: Nothing
  , fillColorPropertyId: Nothing
  , fillBrightnessPropertyId: Nothing
  , fillSaturationPropertyId: Nothing
  , fillHuePropertyId: Nothing
  , strokeColorPropertyId: Nothing
  , strokeWidthPropertyId: Nothing
  , trackingPropertyId: Nothing
  , lineAnchorPropertyId: Nothing
  , lineSpacingPropertyId: Nothing
  , characterOffsetPropertyId: Nothing
  , blurPropertyId: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // text // animator // id
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a text animator.
newtype TextAnimatorId = TextAnimatorId String

derive instance eqTextAnimatorId :: Eq TextAnimatorId
derive instance ordTextAnimatorId :: Ord TextAnimatorId

instance showTextAnimatorId :: Show TextAnimatorId where
  show (TextAnimatorId s) = "(TextAnimatorId " <> s <> ")"

-- | Smart constructor for TextAnimatorId.
mkTextAnimatorId :: String -> Maybe TextAnimatorId
mkTextAnimatorId "" = Nothing
mkTextAnimatorId s = Just (TextAnimatorId s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // text // animator
-- ═════════════════════════════════════════════════════════════════════════════

-- | A text animator with selectors and properties.
type TextAnimator =
  { id :: TextAnimatorId
  , name :: String
  , enabled :: Boolean
  , rangeSelector :: TextRangeSelector
  , wigglySelector :: Maybe TextWigglySelector
  , expressionSelector :: Maybe TextExpressionSelector
  , properties :: TextAnimatorProperties
  }

-- | Default text animator.
defaultTextAnimator 
  :: TextAnimatorId 
  -> String 
  -> TextRangeSelector 
  -> TextAnimator
defaultTextAnimator animId name rangeSelector =
  { id: animId
  , name
  , enabled: true
  , rangeSelector
  , wigglySelector: Nothing
  , expressionSelector: Nothing
  , properties: defaultTextAnimatorProperties
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                             // per // character // 3d // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Character orientation mode for per-character 3D.
-- |
-- | Determines how characters orient themselves in 3D space.
data CharacterOrientation
  = COOff                -- ^ No auto-orientation
  | COOrientAlongPath    -- ^ Orient along text path/baseline
  | COOrientTowardsCamera -- ^ Always face camera (billboard)
  | COOrientToPoint      -- ^ Orient towards specific point

derive instance eqCharacterOrientation :: Eq CharacterOrientation
derive instance ordCharacterOrientation :: Ord CharacterOrientation

instance showCharacterOrientation :: Show CharacterOrientation where
  show COOff = "COOff"
  show COOrientAlongPath = "COOrientAlongPath"
  show COOrientTowardsCamera = "COOrientTowardsCamera"
  show COOrientToPoint = "COOrientToPoint"

characterOrientationToString :: CharacterOrientation -> String
characterOrientationToString COOff = "off"
characterOrientationToString COOrientAlongPath = "orient-along-path"
characterOrientationToString COOrientTowardsCamera = "orient-towards-camera"
characterOrientationToString COOrientToPoint = "orient-to-point"

characterOrientationFromString :: String -> Maybe CharacterOrientation
characterOrientationFromString "off" = Just COOff
characterOrientationFromString "orient-along-path" = Just COOrientAlongPath
characterOrientationFromString "orient-towards-camera" = Just COOrientTowardsCamera
characterOrientationFromString "orient-to-point" = Just COOrientToPoint
characterOrientationFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                         // per // character // 3d // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Per-Character 3D Properties — After Effects-style 3D text animation.
-- |
-- | ## AE Properties
-- |
-- | When "Enable Per-character 3D" is enabled on a text layer,
-- | each character can have independent 3D transforms:
-- |
-- | - **Position X/Y/Z**: 3D position offset
-- | - **Anchor Point X/Y/Z**: 3D anchor for rotation/scale
-- | - **Scale X/Y/Z**: Non-uniform 3D scale
-- | - **Rotation X/Y/Z**: Rotation around each axis (degrees)
-- | - **Orientation**: Auto-orient behavior
-- |
-- | These properties are animated via Text Animator selectors.
type PerCharacter3DProperties =
  { positionX :: Maybe AnimatablePropertyId       -- ^ X position offset
  , positionY :: Maybe AnimatablePropertyId       -- ^ Y position offset
  , positionZ :: Maybe AnimatablePropertyId       -- ^ Z position (depth)
  , anchorPointX :: Maybe AnimatablePropertyId    -- ^ X anchor
  , anchorPointY :: Maybe AnimatablePropertyId    -- ^ Y anchor
  , anchorPointZ :: Maybe AnimatablePropertyId    -- ^ Z anchor
  , scaleX :: Maybe AnimatablePropertyId          -- ^ X scale (0-1000%)
  , scaleY :: Maybe AnimatablePropertyId          -- ^ Y scale (0-1000%)
  , scaleZ :: Maybe AnimatablePropertyId          -- ^ Z scale (0-1000%)
  , rotationX :: Maybe AnimatablePropertyId       -- ^ X rotation (degrees)
  , rotationY :: Maybe AnimatablePropertyId       -- ^ Y rotation (degrees)
  , rotationZ :: Maybe AnimatablePropertyId       -- ^ Z rotation (degrees)
  , orientation :: CharacterOrientation           -- ^ Auto-orient mode
  , orientTowardsPoint :: Maybe AnimatablePropertyId  -- ^ Point for orient-to-point
  }

-- | Default per-character 3D properties (all empty/off).
defaultPerCharacter3DProperties :: PerCharacter3DProperties
defaultPerCharacter3DProperties =
  { positionX: Nothing
  , positionY: Nothing
  , positionZ: Nothing
  , anchorPointX: Nothing
  , anchorPointY: Nothing
  , anchorPointZ: Nothing
  , scaleX: Nothing
  , scaleY: Nothing
  , scaleZ: Nothing
  , rotationX: Nothing
  , rotationY: Nothing
  , rotationZ: Nothing
  , orientation: COOff
  , orientTowardsPoint: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                          // text // animator // 3d // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Text Animator Properties — Combined 2D and 3D properties.
-- |
-- | ## AE Architecture
-- |
-- | In After Effects, when per-character 3D is enabled, the Text Animator
-- | expands to include full 3D transform properties. This type combines:
-- |
-- | - Standard 2D text animator properties (position, scale, rotation, opacity)
-- | - Per-character 3D properties (individual X/Y/Z transforms)
-- | - 3D-specific properties (extrusion, bevel, material options)
-- |
-- | ## Use Cases
-- |
-- | - 3D text reveals with per-character depth
-- | - Character rotation around individual axes
-- | - Cinematic text animations with depth
type TextAnimator3DProperties =
  { -- Standard 2D properties
    position2D :: Maybe AnimatablePropertyId      -- ^ 2D position (X/Y only)
  , anchorPoint2D :: Maybe AnimatablePropertyId   -- ^ 2D anchor point
  , scale2D :: Maybe AnimatablePropertyId         -- ^ Uniform scale (%)
  , rotation2D :: Maybe AnimatablePropertyId      -- ^ Z rotation only
  , opacity :: Maybe AnimatablePropertyId         -- ^ Opacity (0-100%)
  , skew :: Maybe AnimatablePropertyId            -- ^ Skew amount
  , skewAxis :: Maybe AnimatablePropertyId        -- ^ Skew axis angle
  
    -- 3D position/anchor (overrides 2D when enabled)
  , position3D :: PerCharacter3DProperties        -- ^ Full 3D position data
  
    -- Fill/stroke properties
  , fillColor :: Maybe AnimatablePropertyId       -- ^ Fill color
  , fillHue :: Maybe AnimatablePropertyId         -- ^ Hue shift
  , fillSaturation :: Maybe AnimatablePropertyId  -- ^ Saturation adjustment
  , fillBrightness :: Maybe AnimatablePropertyId  -- ^ Brightness adjustment
  , strokeColor :: Maybe AnimatablePropertyId     -- ^ Stroke color
  , strokeWidth :: Maybe AnimatablePropertyId     -- ^ Stroke width
  
    -- Spacing/tracking
  , tracking :: Maybe AnimatablePropertyId        -- ^ Letter spacing
  , lineAnchor :: Maybe AnimatablePropertyId      -- ^ Line anchor position
  , lineSpacing :: Maybe AnimatablePropertyId     -- ^ Line spacing
  , characterOffset :: Maybe AnimatablePropertyId -- ^ Character offset
  , characterBlur :: Maybe AnimatablePropertyId   -- ^ Per-character blur
  }

-- | Default 3D text animator properties.
defaultTextAnimator3DProperties :: TextAnimator3DProperties
defaultTextAnimator3DProperties =
  { position2D: Nothing
  , anchorPoint2D: Nothing
  , scale2D: Nothing
  , rotation2D: Nothing
  , opacity: Nothing
  , skew: Nothing
  , skewAxis: Nothing
  , position3D: defaultPerCharacter3DProperties
  , fillColor: Nothing
  , fillHue: Nothing
  , fillSaturation: Nothing
  , fillBrightness: Nothing
  , strokeColor: Nothing
  , strokeWidth: Nothing
  , tracking: Nothing
  , lineAnchor: Nothing
  , lineSpacing: Nothing
  , characterOffset: Nothing
  , characterBlur: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // text // animator // 3d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 3D Text Animator — Full 3D-capable text animation.
-- |
-- | ## AE Feature Parity
-- |
-- | This type provides complete After Effects text animator functionality
-- | with per-character 3D support:
-- |
-- | - Range, Wiggly, and Expression selectors
-- | - Full 2D + 3D transform properties
-- | - Independent X/Y/Z rotation and position per character
-- | - Auto-orientation modes
-- |
-- | ## Usage
-- |
-- | Enable per-character 3D by populating the `properties3D.position3D` fields.
-- | When any 3D property is set, the renderer enables 3D mode for text.
type TextAnimator3D =
  { id :: TextAnimatorId
  , name :: String
  , enabled :: Boolean
  , perCharacter3DEnabled :: Boolean              -- ^ Master 3D toggle
  , rangeSelector :: TextRangeSelector
  , wigglySelector :: Maybe TextWigglySelector
  , expressionSelector :: Maybe TextExpressionSelector
  , properties :: TextAnimator3DProperties        -- ^ Full 2D+3D properties
  }

-- | Default 3D text animator.
defaultTextAnimator3D
  :: TextAnimatorId
  -> String
  -> TextRangeSelector
  -> TextAnimator3D
defaultTextAnimator3D animId name rangeSelector =
  { id: animId
  , name
  , enabled: true
  , perCharacter3DEnabled: false
  , rangeSelector
  , wigglySelector: Nothing
  , expressionSelector: Nothing
  , properties: defaultTextAnimator3DProperties
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if any 3D properties are set.
hasAny3DProperties :: PerCharacter3DProperties -> Boolean
hasAny3DProperties p =
  case p.positionZ of
    Just _ -> true
    Nothing -> case p.rotationX of
      Just _ -> true
      Nothing -> case p.rotationY of
        Just _ -> true
        Nothing -> case p.anchorPointZ of
          Just _ -> true
          Nothing -> case p.scaleZ of
            Just _ -> true
            Nothing -> false

-- | Count how many 3D properties are set.
count3DProperties :: PerCharacter3DProperties -> Int
count3DProperties p =
  countMaybe p.positionX
  + countMaybe p.positionY
  + countMaybe p.positionZ
  + countMaybe p.anchorPointX
  + countMaybe p.anchorPointY
  + countMaybe p.anchorPointZ
  + countMaybe p.scaleX
  + countMaybe p.scaleY
  + countMaybe p.scaleZ
  + countMaybe p.rotationX
  + countMaybe p.rotationY
  + countMaybe p.rotationZ
  where
    countMaybe :: forall a. Maybe a -> Int
    countMaybe (Just _) = 1
    countMaybe Nothing = 0

-- | Describe the 3D orientation mode.
describe3DOrientation :: PerCharacter3DProperties -> String
describe3DOrientation p =
  "Orientation: " <> show p.orientation
