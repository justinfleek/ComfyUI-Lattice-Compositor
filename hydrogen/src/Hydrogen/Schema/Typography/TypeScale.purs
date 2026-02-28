-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // typography // type-scale
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TypeScale - mathematical foundation for typographic hierarchy.
-- |
-- | A type scale is defined by:
-- | - **Base size**: The reference size (typically body text, e.g., 16px)
-- | - **Ratio**: The multiplier between adjacent scale steps
-- |
-- | Sizes are calculated as: `base × ratio^step`
-- |
-- | Standard ratios derive from musical intervals:
-- | - **Minor Second** (1.067): 15/16 - subtle, conservative
-- | - **Major Second** (1.125): 8/9 - gentle progression
-- | - **Minor Third** (1.200): 5/6 - noticeable but not dramatic
-- | - **Major Third** (1.250): 4/5 - classic, balanced
-- | - **Perfect Fourth** (1.333): 3/4 - strong hierarchy
-- | - **Augmented Fourth** (1.414): √2 - geometric
-- | - **Perfect Fifth** (1.500): 2/3 - dramatic
-- | - **Golden Ratio** (1.618): φ - aesthetically pleasing
-- |
-- | Example: Base 16px with Major Third (1.250)
-- | - Step -2: 10.24px (small)
-- | - Step -1: 12.80px (footnote)
-- | - Step  0: 16.00px (body)
-- | - Step  1: 20.00px (h6)
-- | - Step  2: 25.00px (h5)
-- | - Step  3: 31.25px (h4)
-- | - Step  4: 39.06px (h3)
-- | - Step  5: 48.83px (h2)
-- | - Step  6: 61.04px (h1)
-- | - Step  7: 76.29px (hero)

module Hydrogen.Schema.Typography.TypeScale
  ( TypeScale
  , ScaleRatio
  , typeScale
  , base
  , ratio
  , sizeAt
  , sizeAtF
  -- Ratio accessors
  , ratioValue
  , ratioName
  -- Predefined ratios (musical intervals)
  , minorSecond
  , majorSecond
  , minorThird
  , majorThird
  , perfectFourth
  , augmentedFourth
  , perfectFifth
  , goldenRatio
  -- Custom ratio
  , customRatio
  -- Common scales
  , defaultScale
  , compactScale
  , dramaticScale
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (*)
  , (<>)
  )

import Data.Int (toNumber) as Int
import Hydrogen.Math.Core (pow)
import Hydrogen.Schema.Typography.FontSize (FontSize)
import Hydrogen.Schema.Typography.FontSize as FontSize

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // scale ratio
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale ratio — the multiplier between adjacent type sizes
-- |
-- | Named ratios derive from musical intervals, which produce
-- | naturally harmonious progressions.
data ScaleRatio
  = MinorSecond     -- ^ 1.067 (15:16) - subtle
  | MajorSecond     -- ^ 1.125 (8:9) - gentle
  | MinorThird      -- ^ 1.200 (5:6) - noticeable
  | MajorThird      -- ^ 1.250 (4:5) - classic
  | PerfectFourth   -- ^ 1.333 (3:4) - strong
  | AugmentedFourth -- ^ 1.414 (√2) - geometric
  | PerfectFifth    -- ^ 1.500 (2:3) - dramatic
  | GoldenRatio     -- ^ 1.618 (φ) - aesthetic
  | CustomRatio Number String -- ^ Any ratio with name

derive instance eqScaleRatio :: Eq ScaleRatio

instance showScaleRatio :: Show ScaleRatio where
  show r = ratioName r <> " (" <> show (ratioValue r) <> ")"

-- | Get the numeric value of a scale ratio
ratioValue :: ScaleRatio -> Number
ratioValue MinorSecond = 1.067
ratioValue MajorSecond = 1.125
ratioValue MinorThird = 1.200
ratioValue MajorThird = 1.250
ratioValue PerfectFourth = 1.333
ratioValue AugmentedFourth = 1.414
ratioValue PerfectFifth = 1.500
ratioValue GoldenRatio = 1.618
ratioValue (CustomRatio v _) = v

-- | Get the name of a scale ratio
ratioName :: ScaleRatio -> String
ratioName MinorSecond = "Minor Second"
ratioName MajorSecond = "Major Second"
ratioName MinorThird = "Minor Third"
ratioName MajorThird = "Major Third"
ratioName PerfectFourth = "Perfect Fourth"
ratioName AugmentedFourth = "Augmented Fourth"
ratioName PerfectFifth = "Perfect Fifth"
ratioName GoldenRatio = "Golden Ratio"
ratioName (CustomRatio _ name) = name

-- | Predefined ratio constants
minorSecond :: ScaleRatio
minorSecond = MinorSecond

majorSecond :: ScaleRatio
majorSecond = MajorSecond

minorThird :: ScaleRatio
minorThird = MinorThird

majorThird :: ScaleRatio
majorThird = MajorThird

perfectFourth :: ScaleRatio
perfectFourth = PerfectFourth

augmentedFourth :: ScaleRatio
augmentedFourth = AugmentedFourth

perfectFifth :: ScaleRatio
perfectFifth = PerfectFifth

goldenRatio :: ScaleRatio
goldenRatio = GoldenRatio

-- | Create a custom ratio
customRatio :: Number -> String -> ScaleRatio
customRatio = CustomRatio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // type scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type scale definition
-- |
-- | Combines a base size with a ratio to generate a complete scale.
-- | Sizes are calculated as: `base × ratio^step`
newtype TypeScale = TypeScale
  { base :: FontSize
  , ratio :: ScaleRatio
  }

derive instance eqTypeScale :: Eq TypeScale

instance showTypeScale :: Show TypeScale where
  show (TypeScale ts) = "TypeScale { base: " <> show ts.base 
    <> ", ratio: " <> show ts.ratio <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a type scale
typeScale :: FontSize -> ScaleRatio -> TypeScale
typeScale b r = TypeScale { base: b, ratio: r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the base size
base :: TypeScale -> FontSize
base (TypeScale ts) = ts.base

-- | Get the scale ratio
ratio :: TypeScale -> ScaleRatio
ratio (TypeScale ts) = ts.ratio

-- | Calculate size at a given step (integer)
-- |
-- | Step 0 = base size
-- | Positive steps = larger sizes
-- | Negative steps = smaller sizes
sizeAt :: Int -> TypeScale -> FontSize
sizeAt step (TypeScale ts) =
  FontSize.fontSize (FontSize.unwrap ts.base * pow (ratioValue ts.ratio) (Int.toNumber step))

-- | Calculate size at a given step (fractional)
-- |
-- | Allows interpolation between scale steps for fine-tuning.
sizeAtF :: Number -> TypeScale -> FontSize
sizeAtF step (TypeScale ts) =
  FontSize.fontSize (FontSize.unwrap ts.base * pow (ratioValue ts.ratio) step)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common scales
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default type scale: 16px base with Major Third ratio
-- |
-- | A balanced, widely applicable scale suitable for most interfaces.
defaultScale :: TypeScale
defaultScale = typeScale FontSize.browserDefault majorThird

-- | Compact type scale: 14px base with Major Second ratio
-- |
-- | For data-dense interfaces where space efficiency matters.
compactScale :: TypeScale
compactScale = typeScale FontSize.compact majorSecond

-- | Dramatic type scale: 18px base with Perfect Fourth ratio
-- |
-- | For editorial layouts and marketing pages with strong hierarchy.
dramaticScale :: TypeScale
dramaticScale = typeScale FontSize.readable perfectFourth
