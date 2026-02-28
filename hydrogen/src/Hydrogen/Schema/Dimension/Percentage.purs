-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // dimension // percentage
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Percentage and ratio types - normalized values for proportional design.
-- |
-- | These types represent normalized values used throughout CSS:
-- | - Percent: 0-100 percentage
-- | - Ratio: 0.0-1.0 normalized value
-- | - Proportion: unbounded ratio for aspect ratios (e.g., 16:9)
-- |
-- | ## Type Safety
-- |
-- | Each unit is distinct. You cannot use Percent where Ratio is expected.
-- | This prevents subtle bugs in responsive calculations.
-- |
-- | ## Dependencies
-- | - Prelude
-- | - Hydrogen.Math.Core (clamp)

module Hydrogen.Schema.Dimension.Percentage
  ( -- * Percentage (0-100)
    Percent(Percent)
  , percent
  , percents
  , unwrapPercent
  , toPercent
  , percentOf
  
  -- * SignedPercent (-100 to 100)
  , SignedPercent(SignedPercent)
  , signedPercent
  , unwrapSignedPercent
  , signedPercentBounds
  , negateSignedPercent
  , zeroSignedPercent
  
  -- * IntensityPercent (0-400)
  -- For AE light intensity (allows overbright)
  , IntensityPercent(IntensityPercent)
  , intensityPercent
  , unwrapIntensityPercent
  , intensityPercentBounds
  , fullIntensity
  , doubleIntensity
  
  -- * Ratio (0.0-1.0)
  , Ratio(Ratio)
  , ratio
  , ratios
  , unwrapRatio
  , toRatio
  , half
  , quarter
  , full
  
  -- * SignedRatio (-1.0 to 1.0)
  , SignedRatio(SignedRatio)
  , signedRatio
  , unwrapSignedRatio
  , signedRatioBounds
  , negateSignedRatio
  , zeroSignedRatio
  
  -- * Proportion (unbounded)
    -- For aspect ratios like 16:9, 4:3
  , Proportion(Proportion)
  , proportion
  , proportions
  , unwrapProportion
  , aspect16x9
  , aspect4x3
  , aspect21x9
  , aspect1x1
  , aspect9x16
  , aspect3x4
  
  -- * Bounds
  , percentBounds
  , ratioBounds
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (*)
  , (/)
  , (<>)
  , (<<<)
  )

import Hydrogen.Math.Core as Math
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // percent // 0 100
-- ═════════════════════════════════════════════════════════════════════════════

-- | Percentage value - 0 to 100.
-- |
-- | Used for opacity, progress, completion, etc.
-- | Automatically clamped to 0-100 range.
newtype Percent = Percent Number

derive instance eqPercent :: Eq Percent
derive instance ordPercent :: Ord Percent

instance showPercent :: Show Percent where
  show (Percent v) = show v <> "%"

-- | Create Percent from Number (clamped 0-100)
percent :: Number -> Percent
percent = Percent <<< Math.clamp 0.0 100.0

-- | Create Percent (plural alias)
percents :: Number -> Percent
percents = percent

-- | Unwrap Percent to raw Number
unwrapPercent :: Percent -> Number
unwrapPercent (Percent v) = v

-- | Convert Ratio to Percent
toPercent :: Ratio -> Percent
toPercent r = Percent (unwrapRatio r * 100.0)

-- | Calculate percentage of a value
percentOf :: Percent -> Number -> Number
percentOf p v = v * (unwrapPercent p / 100.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // signed percent // ±100
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed percentage value - -100 to 100.
-- |
-- | Used for adjustments that can go positive or negative:
-- | - Saturation adjustment (-100 = full desaturation, +100 = double saturation)
-- | - Lightness adjustment (-100 = full darken, +100 = full lighten)
-- | - Contrast adjustment
-- | - Exposure adjustment
-- |
-- | Automatically clamped to -100 to 100 range.
newtype SignedPercent = SignedPercent Number

derive instance eqSignedPercent :: Eq SignedPercent
derive instance ordSignedPercent :: Ord SignedPercent

instance showSignedPercent :: Show SignedPercent where
  show (SignedPercent v) = show v <> "%"

-- | Create SignedPercent from Number (clamped -100 to 100)
signedPercent :: Number -> SignedPercent
signedPercent = SignedPercent <<< Math.clamp (-100.0) 100.0

-- | Unwrap SignedPercent to raw Number
unwrapSignedPercent :: SignedPercent -> Number
unwrapSignedPercent (SignedPercent v) = v

-- | Negate a signed percent
negateSignedPercent :: SignedPercent -> SignedPercent
negateSignedPercent (SignedPercent v) = SignedPercent (negate v)

-- | Zero adjustment (no change)
zeroSignedPercent :: SignedPercent
zeroSignedPercent = SignedPercent 0.0

-- | Bounds for SignedPercent
signedPercentBounds :: Bounded.NumberBounds
signedPercentBounds = Bounded.numberBounds (-100.0) 100.0 "signedPercent" 
  "Signed percentage adjustment (-100 to 100)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // intensity percent // 0 to 400
-- ═════════════════════════════════════════════════════════════════════════════

-- | Intensity percentage - 0 to 400.
-- |
-- | Used for light intensity in After Effects where values can exceed 100%:
-- | - 0%: No light (off)
-- | - 100%: Normal intensity
-- | - 200%: Double intensity (overbright)
-- | - 400%: Maximum intensity
-- |
-- | Automatically clamped to 0-400 range.
newtype IntensityPercent = IntensityPercent Number

derive instance eqIntensityPercent :: Eq IntensityPercent
derive instance ordIntensityPercent :: Ord IntensityPercent

instance showIntensityPercent :: Show IntensityPercent where
  show (IntensityPercent v) = show v <> "%"

-- | Create IntensityPercent from Number (clamped 0-400)
intensityPercent :: Number -> IntensityPercent
intensityPercent = IntensityPercent <<< Math.clamp 0.0 400.0

-- | Unwrap IntensityPercent to raw Number
unwrapIntensityPercent :: IntensityPercent -> Number
unwrapIntensityPercent (IntensityPercent v) = v

-- | Full intensity (100%)
fullIntensity :: IntensityPercent
fullIntensity = IntensityPercent 100.0

-- | Double intensity (200%)
doubleIntensity :: IntensityPercent
doubleIntensity = IntensityPercent 200.0

-- | Bounds for IntensityPercent
intensityPercentBounds :: Bounded.NumberBounds
intensityPercentBounds = Bounded.numberBounds 0.0 400.0 "intensityPercent"
  "Intensity percentage (0-400%, allows overbright)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // ratio // 0 1
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normalized ratio - 0.0 to 1.0.
-- |
-- | Used for alpha, progress, flex-grow, etc.
-- | Automatically clamped to 0.0-1.0 range.
newtype Ratio = Ratio Number

derive instance eqRatio :: Eq Ratio
derive instance ordRatio :: Ord Ratio

instance showRatio :: Show Ratio where
  show (Ratio v) = show v

-- | Create Ratio from Number (clamped 0.0-1.0)
ratio :: Number -> Ratio
ratio = Ratio <<< Math.clamp 0.0 1.0

-- | Create Ratio (plural alias)
ratios :: Number -> Ratio
ratios = ratio

-- | Unwrap Ratio to raw Number
unwrapRatio :: Ratio -> Number
unwrapRatio (Ratio v) = v

-- | Convert Percent to Ratio
toRatio :: Percent -> Ratio
toRatio p = Ratio (unwrapPercent p / 100.0)

-- | Half (0.5)
half :: Ratio
half = Ratio 0.5

-- | Quarter (0.25)
quarter :: Ratio
quarter = Ratio 0.25

-- | Full (1.0)
full :: Ratio
full = Ratio 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // signed ratio // ±1.0
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed normalized ratio - -1.0 to 1.0.
-- |
-- | Used for adjustments that can go positive or negative:
-- | - Color wheel offsets
-- | - Balance adjustments
-- | - Normalized deltas
-- |
-- | Automatically clamped to -1.0 to 1.0 range.
newtype SignedRatio = SignedRatio Number

derive instance eqSignedRatio :: Eq SignedRatio
derive instance ordSignedRatio :: Ord SignedRatio

instance showSignedRatio :: Show SignedRatio where
  show (SignedRatio v) = show v

-- | Create SignedRatio from Number (clamped -1.0 to 1.0)
signedRatio :: Number -> SignedRatio
signedRatio = SignedRatio <<< Math.clamp (-1.0) 1.0

-- | Unwrap SignedRatio to raw Number
unwrapSignedRatio :: SignedRatio -> Number
unwrapSignedRatio (SignedRatio v) = v

-- | Negate a signed ratio
negateSignedRatio :: SignedRatio -> SignedRatio
negateSignedRatio (SignedRatio v) = SignedRatio (negate v)

-- | Zero adjustment (no change)
zeroSignedRatio :: SignedRatio
zeroSignedRatio = SignedRatio 0.0

-- | Bounds for SignedRatio
signedRatioBounds :: Bounded.NumberBounds
signedRatioBounds = Bounded.numberBounds (-1.0) 1.0 "signedRatio"
  "Signed normalized ratio (-1.0 to 1.0)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // proportion // unbounded
-- ═════════════════════════════════════════════════════════════════════════════

-- | Proportion - unbounded ratio for aspect ratios.
-- |
-- | Unlike Percent and Ratio, Proportion has no upper bound.
-- | Used for aspect ratios like 16:9, 4:3, 21:9.
-- |
-- | Stores the ratio as a single Number (e.g., 16.0/9.0 = 1.777...)
newtype Proportion = Proportion Number

derive instance eqProportion :: Eq Proportion
derive instance ordProportion :: Ord Proportion

instance showProportion :: Show Proportion where
  show (Proportion v) = show v

-- | Create Proportion from Number (aspect ratio value)
proportion :: Number -> Proportion
proportion = Proportion

-- | Create Proportion (plural alias)
proportions :: Number -> Proportion
proportions = proportion

-- | Unwrap Proportion to raw Number
unwrapProportion :: Proportion -> Number
unwrapProportion (Proportion v) = v

-- | 16:9 widescreen aspect ratio (~1.778)
aspect16x9 :: Proportion
aspect16x9 = Proportion (16.0 / 9.0)

-- | 4:3 standard aspect ratio (~1.333)
aspect4x3 :: Proportion
aspect4x3 = Proportion (4.0 / 3.0)

-- | 21:9 ultrawide aspect ratio (~2.333)
aspect21x9 :: Proportion
aspect21x9 = Proportion (21.0 / 9.0)

-- | 1:1 square aspect ratio
aspect1x1 :: Proportion
aspect1x1 = Proportion 1.0

-- | 9:16 vertical video aspect ratio (~0.5625)
aspect9x16 :: Proportion
aspect9x16 = Proportion (9.0 / 16.0)

-- | 3:4 portrait aspect ratio (~0.75)
aspect3x4 :: Proportion
aspect3x4 = Proportion (3.0 / 4.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for Percent
-- |
-- | Min: 0.0
-- | Max: 100.0
percentBounds :: Bounded.NumberBounds
percentBounds = Bounded.numberBounds 0.0 100.0 "percent" "Percentage value (0-100)"

-- | Bounds for Ratio
-- |
-- | Min: 0.0
-- | Max: 1.0
ratioBounds :: Bounded.NumberBounds
ratioBounds = Bounded.numberBounds 0.0 1.0 "ratio" "Normalized ratio (0-1)"
