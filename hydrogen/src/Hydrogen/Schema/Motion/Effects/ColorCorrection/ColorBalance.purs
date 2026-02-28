-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--            // hydrogen // schema // motion // effects // color // colorbalance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color Balance — Shift colors along complementary axes.
-- |
-- | ## After Effects Parity
-- |
-- | Mirrors AE's Color Balance effect with three tonal ranges:
-- |
-- | - **Shadows**: Affects dark regions (luminance < 0.33)
-- | - **Midtones**: Affects middle brightness (0.33 < luminance < 0.67)
-- | - **Highlights**: Affects bright regions (luminance > 0.67)
-- |
-- | Each range adjusts three complementary color axes:
-- | - Cyan ↔ Red
-- | - Magenta ↔ Green
-- | - Yellow ↔ Blue
-- |
-- | ## Properties (All Animatable)
-- |
-- | | Property | Type | Min | Max | Behavior | Default |
-- | |----------|------|-----|-----|----------|---------|
-- | | cyanRed | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | magentaGreen | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | yellowBlue | Number | -100.0 | 100.0 | clamps | 0.0 |
-- | | preserveLuminosity | Boolean | — | — | — | true |
-- |
-- | ## Mathematical Model
-- |
-- | Color shift is applied proportionally to tonal range:
-- | - Shadows: weighted by `1.0 - luminance` for dark pixels
-- | - Midtones: gaussian-weighted around middle luminance
-- | - Highlights: weighted by `luminance` for bright pixels
-- |
-- | When preserveLuminosity is true, the result is normalized to
-- | maintain the original pixel luminance.

module Hydrogen.Schema.Motion.Effects.ColorCorrection.ColorBalance
  ( -- * Tonal Range
    TonalRange(..)
  , defaultTonalRange
  , mkTonalRange
  
  -- * Color Balance Effect
  , ColorBalanceEffect(..)
  , defaultColorBalanceEffect
  , mkColorBalanceEffect
  
  -- * Accessors
  , shadowRange
  , midtoneRange
  , highlightRange
  , preserveLuminosity
  , cyanRed
  , magentaGreen
  , yellowBlue
  
  -- * Operations
  , setShadows
  , setMidtones
  , setHighlights
  , setPreserveLuminosity
  , setCyanRed
  , setMagentaGreen
  , setYellowBlue
  , resetRange
  , resetEffect
  
  -- * Presets
  , cbWarmSunlight
  , cbCoolMoonlight
  , cbSepia
  , cbCrossPro
  , cbTealOrange
  
  -- * Queries
  , isRangeNeutral
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

import Hydrogen.Schema.Bounded (clampNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // tonal // range
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color adjustment for a tonal range (shadows, midtones, or highlights).
-- |
-- | Each axis shifts between complementary colors:
-- | - Negative cyanRed = more cyan, Positive = more red
-- | - Negative magentaGreen = more magenta, Positive = more green
-- | - Negative yellowBlue = more yellow, Positive = more blue
type TonalRange =
  { cyanRed :: Number        -- ^ Cyan (-100) to Red (+100)
  , magentaGreen :: Number   -- ^ Magenta (-100) to Green (+100)
  , yellowBlue :: Number     -- ^ Yellow (-100) to Blue (+100)
  }

-- | Default neutral tonal range (no shift).
defaultTonalRange :: TonalRange
defaultTonalRange =
  { cyanRed: 0.0
  , magentaGreen: 0.0
  , yellowBlue: 0.0
  }

-- | Create tonal range with clamped values.
mkTonalRange :: Number -> Number -> Number -> TonalRange
mkTonalRange cr mg yb =
  { cyanRed: clampNumber (negate 100.0) 100.0 cr
  , magentaGreen: clampNumber (negate 100.0) 100.0 mg
  , yellowBlue: clampNumber (negate 100.0) 100.0 yb
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // color balance // effect
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Color Balance effect with three tonal ranges.
type ColorBalanceEffect =
  { shadows :: TonalRange      -- ^ Shadow color adjustment
  , midtones :: TonalRange     -- ^ Midtone color adjustment
  , highlights :: TonalRange   -- ^ Highlight color adjustment
  , preserveLuminosity :: Boolean  -- ^ Maintain original brightness
  }

-- | Default neutral effect.
defaultColorBalanceEffect :: ColorBalanceEffect
defaultColorBalanceEffect =
  { shadows: defaultTonalRange
  , midtones: defaultTonalRange
  , highlights: defaultTonalRange
  , preserveLuminosity: true
  }

-- | Create effect from three tonal ranges.
mkColorBalanceEffect :: TonalRange -> TonalRange -> TonalRange -> Boolean -> ColorBalanceEffect
mkColorBalanceEffect shad mid high preserveLum =
  { shadows: shad
  , midtones: mid
  , highlights: high
  , preserveLuminosity: preserveLum
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get shadow range.
shadowRange :: ColorBalanceEffect -> TonalRange
shadowRange effect = effect.shadows

-- | Get midtone range.
midtoneRange :: ColorBalanceEffect -> TonalRange
midtoneRange effect = effect.midtones

-- | Get highlight range.
highlightRange :: ColorBalanceEffect -> TonalRange
highlightRange effect = effect.highlights

-- | Get preserve luminosity flag.
preserveLuminosity :: ColorBalanceEffect -> Boolean
preserveLuminosity effect = effect.preserveLuminosity

-- | Get cyan/red value from a tonal range.
cyanRed :: TonalRange -> Number
cyanRed range = range.cyanRed

-- | Get magenta/green value from a tonal range.
magentaGreen :: TonalRange -> Number
magentaGreen range = range.magentaGreen

-- | Get yellow/blue value from a tonal range.
yellowBlue :: TonalRange -> Number
yellowBlue range = range.yellowBlue

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set shadow tonal range.
setShadows :: TonalRange -> ColorBalanceEffect -> ColorBalanceEffect
setShadows range effect = effect { shadows = range }

-- | Set midtone tonal range.
setMidtones :: TonalRange -> ColorBalanceEffect -> ColorBalanceEffect
setMidtones range effect = effect { midtones = range }

-- | Set highlight tonal range.
setHighlights :: TonalRange -> ColorBalanceEffect -> ColorBalanceEffect
setHighlights range effect = effect { highlights = range }

-- | Set preserve luminosity flag.
setPreserveLuminosity :: Boolean -> ColorBalanceEffect -> ColorBalanceEffect
setPreserveLuminosity flag effect = effect { preserveLuminosity = flag }

-- | Set cyan/red value on a tonal range.
setCyanRed :: Number -> TonalRange -> TonalRange
setCyanRed val range = range { cyanRed = clampNumber (negate 100.0) 100.0 val }

-- | Set magenta/green value on a tonal range.
setMagentaGreen :: Number -> TonalRange -> TonalRange
setMagentaGreen val range = range { magentaGreen = clampNumber (negate 100.0) 100.0 val }

-- | Set yellow/blue value on a tonal range.
setYellowBlue :: Number -> TonalRange -> TonalRange
setYellowBlue val range = range { yellowBlue = clampNumber (negate 100.0) 100.0 val }

-- | Reset a tonal range to neutral.
resetRange :: TonalRange -> TonalRange
resetRange _ = defaultTonalRange

-- | Reset entire effect to neutral.
resetEffect :: ColorBalanceEffect -> ColorBalanceEffect
resetEffect _ = defaultColorBalanceEffect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Warm sunlight — adds warmth throughout.
cbWarmSunlight :: ColorBalanceEffect
cbWarmSunlight =
  { shadows: mkTonalRange 10.0 0.0 (negate 15.0)      -- Warm shadows
  , midtones: mkTonalRange 5.0 5.0 (negate 10.0)      -- Warm mids
  , highlights: mkTonalRange 15.0 10.0 (negate 20.0)  -- Warm highlights
  , preserveLuminosity: true
  }

-- | Cool moonlight — adds cool blue tones.
cbCoolMoonlight :: ColorBalanceEffect
cbCoolMoonlight =
  { shadows: mkTonalRange (negate 10.0) 0.0 20.0      -- Blue shadows
  , midtones: mkTonalRange (negate 5.0) (negate 5.0) 10.0  -- Cool mids
  , highlights: mkTonalRange (negate 5.0) 0.0 15.0    -- Blue highlights
  , preserveLuminosity: true
  }

-- | Sepia tone — warm brown vintage look.
cbSepia :: ColorBalanceEffect
cbSepia =
  { shadows: mkTonalRange 15.0 5.0 (negate 20.0)
  , midtones: mkTonalRange 20.0 10.0 (negate 30.0)
  , highlights: mkTonalRange 10.0 5.0 (negate 15.0)
  , preserveLuminosity: true
  }

-- | Cross-processing look.
cbCrossPro :: ColorBalanceEffect
cbCrossPro =
  { shadows: mkTonalRange (negate 20.0) 10.0 30.0     -- Cyan/green/blue shadows
  , midtones: mkTonalRange 10.0 (negate 5.0) (negate 10.0)  -- Red/magenta mids
  , highlights: mkTonalRange 20.0 15.0 (negate 25.0)  -- Yellow/orange highlights
  , preserveLuminosity: false
  }

-- | Teal and orange — cinematic color grade.
cbTealOrange :: ColorBalanceEffect
cbTealOrange =
  { shadows: mkTonalRange (negate 15.0) 5.0 20.0      -- Teal shadows
  , midtones: mkTonalRange 5.0 0.0 (negate 5.0)       -- Slight warmth
  , highlights: mkTonalRange 20.0 10.0 (negate 15.0)  -- Orange highlights
  , preserveLuminosity: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a tonal range is neutral (no adjustment).
isRangeNeutral :: TonalRange -> Boolean
isRangeNeutral range =
  range.cyanRed == 0.0 &&
  range.magentaGreen == 0.0 &&
  range.yellowBlue == 0.0

-- | Check if entire effect is neutral.
isEffectNeutral :: ColorBalanceEffect -> Boolean
isEffectNeutral effect =
  isRangeNeutral effect.shadows &&
  isRangeNeutral effect.midtones &&
  isRangeNeutral effect.highlights
