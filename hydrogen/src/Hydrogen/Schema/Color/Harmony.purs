-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // color // harmony
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color harmony - relationships on the color wheel.
-- |
-- | Classic color theory for creating harmonious palettes:
-- | - **Complementary**: Opposite colors (180°)
-- | - **Triadic**: Three equidistant colors (120°)
-- | - **Analogous**: Adjacent colors (30°)
-- | - And more...

module Hydrogen.Schema.Color.Harmony
  ( Harmony(..)
  , HarmonyConfig
  , generateHarmony
  ) where

import Prelude
  ( class Eq
  , class Show
  , otherwise
  , mod
  , (+)
  , (-)
  , (<)
  , (>)
  )

import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color harmony
-- ═════════════════════════════════════════════════════════════════════════════

-- | Classic color harmony schemes based on the color wheel
data Harmony
  = Complementary        -- ^ Opposite on wheel (180°)
  | SplitComplementary   -- ^ Base + two adjacent to complement (150°, 210°)
  | Triadic              -- ^ Three equidistant (120° apart)
  | Tetradic             -- ^ Four colors, two complementary pairs
  | Square               -- ^ Four equidistant (90° apart)
  | Analogous            -- ^ Adjacent colors (30° apart)
  | AnalogousWide        -- ^ Wider analogous (60° apart)
  | DoubleSplit          -- ^ Split both the base and complement

derive instance eqHarmony :: Eq Harmony

instance showHarmony :: Show Harmony where
  show = case _ of
    Complementary -> "Complementary"
    SplitComplementary -> "Split Complementary"
    Triadic -> "Triadic"
    Tetradic -> "Tetradic"
    Square -> "Square"
    Analogous -> "Analogous"
    AnalogousWide -> "Analogous (Wide)"
    DoubleSplit -> "Double Split"

-- | Configuration for harmony generation
type HarmonyConfig =
  { baseColor :: HSL.HSL
  , harmony :: Harmony
  , saturationShift :: Int   -- ^ Adjust saturation (-100 to 100)
  , lightnessShift :: Int    -- ^ Adjust lightness (-100 to 100)
  }

-- | Generate colors based on harmony rules
generateHarmony :: HarmonyConfig -> Array HSL.HSL
generateHarmony { baseColor, harmony, saturationShift, lightnessShift } =
  let
    h = Hue.unwrap (HSL.hue baseColor)
    s = Sat.unwrap (HSL.saturation baseColor)
    l = Light.unwrap (HSL.lightness baseColor)
    s' = clamp100 (s + saturationShift)
    l' = clamp100 (l + lightnessShift)
    makeColor hue' = HSL.hsl (mod' hue' 360) s' l'
  in case harmony of
    Complementary -> 
      [ baseColor, makeColor (h + 180) ]
    SplitComplementary -> 
      [ baseColor, makeColor (h + 150), makeColor (h + 210) ]
    Triadic -> 
      [ baseColor, makeColor (h + 120), makeColor (h + 240) ]
    Tetradic -> 
      [ baseColor, makeColor (h + 90), makeColor (h + 180), makeColor (h + 270) ]
    Square -> 
      [ baseColor, makeColor (h + 90), makeColor (h + 180), makeColor (h + 270) ]
    Analogous -> 
      [ makeColor (h - 30), baseColor, makeColor (h + 30) ]
    AnalogousWide -> 
      [ makeColor (h - 60), baseColor, makeColor (h + 60) ]
    DoubleSplit ->
      [ makeColor (h - 30), makeColor (h + 30)
      , makeColor (h + 150), makeColor (h + 210) 
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

clamp100 :: Int -> Int
clamp100 n
  | n < 0 = 0
  | n > 100 = 100
  | otherwise = n

mod' :: Int -> Int -> Int
mod' a b = ((a `mod` b) + b) `mod` b
