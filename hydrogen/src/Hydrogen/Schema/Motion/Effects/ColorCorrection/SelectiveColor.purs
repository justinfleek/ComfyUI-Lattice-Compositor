-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--          // hydrogen // schema // motion // effects // color // selectivecolor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Selective Color — Per-color-range CMYK adjustments.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Selective Color effect which allows independent
-- | adjustment of nine color ranges using CMYK sliders:
-- |
-- | - **Reds, Yellows, Greens, Cyans, Blues, Magentas**: Primary colors
-- | - **Whites, Neutrals, Blacks**: Luminance ranges
-- |
-- | Each range has four CMYK adjustments:
-- | - Cyan: Adds cyan (negative) or red (positive)
-- | - Magenta: Adds magenta (negative) or green (positive)
-- | - Yellow: Adds yellow (negative) or blue (positive)
-- | - Black: Darkens (positive) or lightens (negative)
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | cyan | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | magenta | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | yellow | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | black | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | method | CorrectionMethod | — | — | enum | Relative |
-- |
-- | ## Correction Methods
-- |
-- | - **Relative**: Percentages are relative to existing color amounts
-- | - **Absolute**: Percentages are absolute additions

module Hydrogen.Schema.Motion.Effects.ColorCorrection.SelectiveColor
  ( -- * Color Range
    ColorRange(..)
  , colorRangeToString
  , colorRangeFromString
  , allColorRanges
  
  -- * Correction Method
  , CorrectionMethod(..)
  , correctionMethodToString
  , correctionMethodFromString
  
  -- * CMYK Adjustment
  , CMYKAdjustment(..)
  , defaultCMYKAdjustment
  , mkCMYKAdjustment
  
  -- * Selective Color Effect
  , SelectiveColorEffect(..)
  , defaultSelectiveColorEffect
  , mkSelectiveColorEffect
  
  -- * Accessors
  , getAdjustment
  , correctionMethod
  , cyan
  , magenta
  , yellow
  , black
  
  -- * Operations
  , setAdjustment
  , setCorrectionMethod
  , setCyan
  , setMagenta
  , setYellow
  , setBlack
  , resetRange
  , resetEffect
  
  -- * Presets
  , scSkinToneCorrection
  , scEnhanceBlues
  , scEnhanceGreens
  , scCrossPro
  , scTealOrange
  
  -- * Queries
  , isAdjustmentNeutral
  , isEffectNeutral
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semigroup
  , show
  , (<>)
  , (&&)
  , (||)
  , not
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , otherwise
  , compare
  , map
  , pure
  , bind
  )

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color // range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color ranges for selective adjustment.
data ColorRange
  = RangeReds       -- ^ Red hue range
  | RangeYellows    -- ^ Yellow hue range
  | RangeGreens     -- ^ Green hue range
  | RangeCyans      -- ^ Cyan hue range
  | RangeBlues      -- ^ Blue hue range
  | RangeMagentas   -- ^ Magenta hue range
  | RangeWhites     -- ^ High luminance pixels
  | RangeNeutrals   -- ^ Mid luminance pixels
  | RangeBlacks     -- ^ Low luminance pixels

derive instance eqColorRange :: Eq ColorRange
derive instance ordColorRange :: Ord ColorRange

instance showColorRange :: Show ColorRange where
  show RangeReds = "Reds"
  show RangeYellows = "Yellows"
  show RangeGreens = "Greens"
  show RangeCyans = "Cyans"
  show RangeBlues = "Blues"
  show RangeMagentas = "Magentas"
  show RangeWhites = "Whites"
  show RangeNeutrals = "Neutrals"
  show RangeBlacks = "Blacks"

colorRangeToString :: ColorRange -> String
colorRangeToString = show

colorRangeFromString :: String -> Maybe ColorRange
colorRangeFromString "Reds" = Just RangeReds
colorRangeFromString "Yellows" = Just RangeYellows
colorRangeFromString "Greens" = Just RangeGreens
colorRangeFromString "Cyans" = Just RangeCyans
colorRangeFromString "Blues" = Just RangeBlues
colorRangeFromString "Magentas" = Just RangeMagentas
colorRangeFromString "Whites" = Just RangeWhites
colorRangeFromString "Neutrals" = Just RangeNeutrals
colorRangeFromString "Blacks" = Just RangeBlacks
colorRangeFromString _ = Nothing

-- | All color ranges in order.
allColorRanges :: Array ColorRange
allColorRanges = 
  [ RangeReds
  , RangeYellows
  , RangeGreens
  , RangeCyans
  , RangeBlues
  , RangeMagentas
  , RangeWhites
  , RangeNeutrals
  , RangeBlacks
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // correction // method
-- ═════════════════════════════════════════════════════════════════════════════

-- | Correction method for selective color.
data CorrectionMethod
  = Relative   -- ^ Percentages relative to existing amounts
  | Absolute   -- ^ Percentages as absolute additions

derive instance eqCorrectionMethod :: Eq CorrectionMethod
derive instance ordCorrectionMethod :: Ord CorrectionMethod

instance showCorrectionMethod :: Show CorrectionMethod where
  show Relative = "Relative"
  show Absolute = "Absolute"

correctionMethodToString :: CorrectionMethod -> String
correctionMethodToString = show

correctionMethodFromString :: String -> Maybe CorrectionMethod
correctionMethodFromString "Relative" = Just Relative
correctionMethodFromString "Absolute" = Just Absolute
correctionMethodFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // cmyk // adjustment
-- ═════════════════════════════════════════════════════════════════════════════

-- | CMYK adjustment for a color range.
type CMYKAdjustment =
  { cyan :: Number     -- ^ Cyan adjustment (-100 to 100)
  , magenta :: Number  -- ^ Magenta adjustment (-100 to 100)
  , yellow :: Number   -- ^ Yellow adjustment (-100 to 100)
  , black :: Number    -- ^ Black adjustment (-100 to 100)
  }

-- | Default neutral adjustment.
defaultCMYKAdjustment :: CMYKAdjustment
defaultCMYKAdjustment =
  { cyan: 0.0
  , magenta: 0.0
  , yellow: 0.0
  , black: 0.0
  }

-- | Create CMYK adjustment with clamped values.
mkCMYKAdjustment :: Number -> Number -> Number -> Number -> CMYKAdjustment
mkCMYKAdjustment c m y k =
  { cyan: clampNumber (negate 100.0) 100.0 c
  , magenta: clampNumber (negate 100.0) 100.0 m
  , yellow: clampNumber (negate 100.0) 100.0 y
  , black: clampNumber (negate 100.0) 100.0 k
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // selective color // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Selective Color effect with all nine ranges.
type SelectiveColorEffect =
  { reds :: CMYKAdjustment
  , yellows :: CMYKAdjustment
  , greens :: CMYKAdjustment
  , cyans :: CMYKAdjustment
  , blues :: CMYKAdjustment
  , magentas :: CMYKAdjustment
  , whites :: CMYKAdjustment
  , neutrals :: CMYKAdjustment
  , blacks :: CMYKAdjustment
  , method :: CorrectionMethod
  }

-- | Default neutral effect.
defaultSelectiveColorEffect :: SelectiveColorEffect
defaultSelectiveColorEffect =
  { reds: defaultCMYKAdjustment
  , yellows: defaultCMYKAdjustment
  , greens: defaultCMYKAdjustment
  , cyans: defaultCMYKAdjustment
  , blues: defaultCMYKAdjustment
  , magentas: defaultCMYKAdjustment
  , whites: defaultCMYKAdjustment
  , neutrals: defaultCMYKAdjustment
  , blacks: defaultCMYKAdjustment
  , method: Relative
  }

-- | Create effect from all adjustments.
mkSelectiveColorEffect 
  :: CMYKAdjustment -> CMYKAdjustment -> CMYKAdjustment
  -> CMYKAdjustment -> CMYKAdjustment -> CMYKAdjustment
  -> CMYKAdjustment -> CMYKAdjustment -> CMYKAdjustment
  -> CorrectionMethod
  -> SelectiveColorEffect
mkSelectiveColorEffect r y g c b m w n bl meth =
  { reds: r
  , yellows: y
  , greens: g
  , cyans: c
  , blues: b
  , magentas: m
  , whites: w
  , neutrals: n
  , blacks: bl
  , method: meth
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get adjustment for a color range.
getAdjustment :: ColorRange -> SelectiveColorEffect -> CMYKAdjustment
getAdjustment RangeReds effect = effect.reds
getAdjustment RangeYellows effect = effect.yellows
getAdjustment RangeGreens effect = effect.greens
getAdjustment RangeCyans effect = effect.cyans
getAdjustment RangeBlues effect = effect.blues
getAdjustment RangeMagentas effect = effect.magentas
getAdjustment RangeWhites effect = effect.whites
getAdjustment RangeNeutrals effect = effect.neutrals
getAdjustment RangeBlacks effect = effect.blacks

-- | Get correction method.
correctionMethod :: SelectiveColorEffect -> CorrectionMethod
correctionMethod effect = effect.method

-- | Get cyan value from adjustment.
cyan :: CMYKAdjustment -> Number
cyan adj = adj.cyan

-- | Get magenta value from adjustment.
magenta :: CMYKAdjustment -> Number
magenta adj = adj.magenta

-- | Get yellow value from adjustment.
yellow :: CMYKAdjustment -> Number
yellow adj = adj.yellow

-- | Get black value from adjustment.
black :: CMYKAdjustment -> Number
black adj = adj.black

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set adjustment for a color range.
setAdjustment :: ColorRange -> CMYKAdjustment -> SelectiveColorEffect -> SelectiveColorEffect
setAdjustment RangeReds adj effect = effect { reds = adj }
setAdjustment RangeYellows adj effect = effect { yellows = adj }
setAdjustment RangeGreens adj effect = effect { greens = adj }
setAdjustment RangeCyans adj effect = effect { cyans = adj }
setAdjustment RangeBlues adj effect = effect { blues = adj }
setAdjustment RangeMagentas adj effect = effect { magentas = adj }
setAdjustment RangeWhites adj effect = effect { whites = adj }
setAdjustment RangeNeutrals adj effect = effect { neutrals = adj }
setAdjustment RangeBlacks adj effect = effect { blacks = adj }

-- | Set correction method.
setCorrectionMethod :: CorrectionMethod -> SelectiveColorEffect -> SelectiveColorEffect
setCorrectionMethod meth effect = effect { method = meth }

-- | Set cyan on an adjustment.
setCyan :: Number -> CMYKAdjustment -> CMYKAdjustment
setCyan val adj = adj { cyan = clampNumber (negate 100.0) 100.0 val }

-- | Set magenta on an adjustment.
setMagenta :: Number -> CMYKAdjustment -> CMYKAdjustment
setMagenta val adj = adj { magenta = clampNumber (negate 100.0) 100.0 val }

-- | Set yellow on an adjustment.
setYellow :: Number -> CMYKAdjustment -> CMYKAdjustment
setYellow val adj = adj { yellow = clampNumber (negate 100.0) 100.0 val }

-- | Set black on an adjustment.
setBlack :: Number -> CMYKAdjustment -> CMYKAdjustment
setBlack val adj = adj { black = clampNumber (negate 100.0) 100.0 val }

-- | Reset a color range to neutral.
resetRange :: ColorRange -> SelectiveColorEffect -> SelectiveColorEffect
resetRange range effect = setAdjustment range defaultCMYKAdjustment effect

-- | Reset entire effect to neutral.
resetEffect :: SelectiveColorEffect -> SelectiveColorEffect
resetEffect _ = defaultSelectiveColorEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Skin tone correction — reduces red and magenta in reds/yellows.
scSkinToneCorrection :: SelectiveColorEffect
scSkinToneCorrection = defaultSelectiveColorEffect
  { reds = mkCMYKAdjustment 10.0 (negate 15.0) 5.0 0.0
  , yellows = mkCMYKAdjustment 5.0 (negate 10.0) 0.0 0.0
  }

-- | Enhance blues — makes blues more vibrant.
scEnhanceBlues :: SelectiveColorEffect
scEnhanceBlues = defaultSelectiveColorEffect
  { blues = mkCMYKAdjustment 20.0 10.0 (negate 30.0) 0.0
  , cyans = mkCMYKAdjustment 15.0 0.0 (negate 20.0) 0.0
  }

-- | Enhance greens — makes foliage more vibrant.
scEnhanceGreens :: SelectiveColorEffect
scEnhanceGreens = defaultSelectiveColorEffect
  { greens = mkCMYKAdjustment (negate 10.0) (negate 20.0) 30.0 0.0
  , yellows = mkCMYKAdjustment 10.0 (negate 15.0) 20.0 0.0
  }

-- | Cross-processing look.
scCrossPro :: SelectiveColorEffect
scCrossPro = defaultSelectiveColorEffect
  { reds = mkCMYKAdjustment (negate 20.0) 10.0 20.0 0.0
  , yellows = mkCMYKAdjustment 10.0 (negate 15.0) 30.0 0.0
  , blues = mkCMYKAdjustment 30.0 20.0 (negate 20.0) 0.0
  , blacks = mkCMYKAdjustment 10.0 5.0 (negate 10.0) 0.0
  }

-- | Teal and orange cinematic grade.
scTealOrange :: SelectiveColorEffect
scTealOrange = defaultSelectiveColorEffect
  { reds = mkCMYKAdjustment (negate 15.0) 10.0 20.0 0.0
  , yellows = mkCMYKAdjustment (negate 10.0) 5.0 15.0 0.0
  , cyans = mkCMYKAdjustment 20.0 (negate 5.0) (negate 25.0) 0.0
  , blues = mkCMYKAdjustment 25.0 0.0 (negate 30.0) 0.0
  , blacks = mkCMYKAdjustment 15.0 5.0 (negate 10.0) 5.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a CMYK adjustment is neutral.
isAdjustmentNeutral :: CMYKAdjustment -> Boolean
isAdjustmentNeutral adj =
  adj.cyan == 0.0 &&
  adj.magenta == 0.0 &&
  adj.yellow == 0.0 &&
  adj.black == 0.0

-- | Check if entire effect is neutral.
isEffectNeutral :: SelectiveColorEffect -> Boolean
isEffectNeutral effect =
  isAdjustmentNeutral effect.reds &&
  isAdjustmentNeutral effect.yellows &&
  isAdjustmentNeutral effect.greens &&
  isAdjustmentNeutral effect.cyans &&
  isAdjustmentNeutral effect.blues &&
  isAdjustmentNeutral effect.magentas &&
  isAdjustmentNeutral effect.whites &&
  isAdjustmentNeutral effect.neutrals &&
  isAdjustmentNeutral effect.blacks
