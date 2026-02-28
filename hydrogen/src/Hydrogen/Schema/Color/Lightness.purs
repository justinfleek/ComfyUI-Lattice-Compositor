-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // color // lightness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Lightness - how light or dark a color is.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: Black (no light)
-- | - **50%**: Pure color (maximum saturation possible)
-- | - **100%**: White (full light)
-- |
-- | In HSL, lightness determines the amount of white or black mixed in.
-- | At 50% lightness, you get the most vivid version of the hue.

module Hydrogen.Schema.Color.Lightness
  ( Lightness
  , lightness
  , unsafeLightness
  , unwrap
  , lighten
  , darken
  , scale
  , isLight
  , isDark
  , bounds
  , toNumber
  , toUnitInterval
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>)
  , (<)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // lightness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lightness value as percentage (0-100)
-- |
-- | Represents how light or dark a color is. 0% is black, 100% is white.
-- | 50% gives the most saturated version of the hue.
newtype Lightness = Lightness Int

derive instance eqLightness :: Eq Lightness
derive instance ordLightness :: Ord Lightness

instance showLightness :: Show Lightness where
  show (Lightness l) = show l <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a lightness, clamping to 0-100
lightness :: Int -> Lightness
lightness n = Lightness (Bounded.clampInt 0 100 n)

-- | Create a lightness without clamping
-- |
-- | Use only when you know the value is valid.
unsafeLightness :: Int -> Lightness
unsafeLightness = Lightness

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Increase lightness (add white)
lighten :: Int -> Lightness -> Lightness
lighten amount (Lightness l) = lightness (l + amount)

-- | Decrease lightness (add black)
darken :: Int -> Lightness -> Lightness
darken amount (Lightness l) = lightness (l - amount)

-- | Scale lightness by a factor
scale :: Number -> Lightness -> Lightness
scale factor (Lightness l) = 
  lightness (Int.round (Int.toNumber l * factor))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if lightness is in the light range (> 60%)
-- |
-- | Useful for determining if dark text should be used on this background.
isLight :: Lightness -> Boolean
isLight (Lightness l) = l > 60

-- | Check if lightness is in the dark range (< 40%)
-- |
-- | Useful for determining if light text should be used on this background.
isDark :: Lightness -> Boolean
isDark (Lightness l) = l < 40

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Lightness -> Int
unwrap (Lightness l) = l

-- | Convert to Number for calculations
toNumber :: Lightness -> Number
toNumber (Lightness l) = Int.toNumber l

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Lightness -> Number
toUnitInterval (Lightness l) = Int.toNumber l / 100.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "lightness" "Light/dark level as percentage"
