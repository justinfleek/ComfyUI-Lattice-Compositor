-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // color // saturation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Saturation - color intensity/purity.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: Grayscale (no color)
-- | - **50%**: Muted, desaturated
-- | - **100%**: Fully saturated, vivid
-- |
-- | In HSL color space, saturation describes how much gray is mixed in.
-- | At 0% saturation, the hue is irrelevant - you get pure gray.

module Hydrogen.Schema.Color.Saturation
  ( Saturation
  , saturation
  , unsafeSaturation
  , unwrap
  , scale
  , increase
  , decrease
  -- Operations
  , blend
  , lerp
  , invert
  , fromUnitInterval
  -- Predicates
  , isGrayscale
  , isVivid
  , isMuted
  -- Constants
  , gray
  , muted
  , medium
  , vivid
  , full
  -- Accessors
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
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // saturation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Saturation value as percentage (0-100)
-- |
-- | Represents color purity/intensity. 0% is grayscale, 100% is fully vivid.
newtype Saturation = Saturation Int

derive instance eqSaturation :: Eq Saturation
derive instance ordSaturation :: Ord Saturation

instance showSaturation :: Show Saturation where
  show (Saturation s) = show s <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a saturation, clamping to 0-100
saturation :: Int -> Saturation
saturation n = Saturation (Bounded.clampInt 0 100 n)

-- | Create a saturation without clamping
-- |
-- | Use only when you know the value is valid.
unsafeSaturation :: Int -> Saturation
unsafeSaturation = Saturation

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale saturation by a factor (0.0 to 2.0 typical)
scale :: Number -> Saturation -> Saturation
scale factor (Saturation s) = 
  saturation (Int.round (Int.toNumber s * factor))

-- | Increase saturation by percentage points
increase :: Int -> Saturation -> Saturation
increase amount (Saturation s) = saturation (s + amount)

-- | Decrease saturation by percentage points
decrease :: Int -> Saturation -> Saturation
decrease amount (Saturation s) = saturation (s - amount)

-- | Blend two saturation values with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation for color transitions and gradients:
-- | ```purescript
-- | blend 0.0 gray full  -- Saturation 0%
-- | blend 0.5 gray full  -- Saturation 50%
-- | blend 1.0 gray full  -- Saturation 100%
-- | ```
blend :: Number -> Saturation -> Saturation -> Saturation
blend weight (Saturation a) (Saturation b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
      result = Int.toNumber a * (1.0 - w) + Int.toNumber b * w
  in saturation (Int.round result)

-- | Linear interpolation (standard lerp signature)
-- |
-- | ```purescript
-- | lerp gray full 0.5  -- Saturation 50%
-- | ```
lerp :: Saturation -> Saturation -> Number -> Saturation
lerp from to t = blend t from to

-- | Invert saturation (100 - value)
-- |
-- | Converts vivid to muted and vice versa:
-- | ```purescript
-- | invert (saturation 30)  -- Saturation 70%
-- | invert full             -- Saturation 0% (gray)
-- | invert gray             -- Saturation 100% (full)
-- | ```
invert :: Saturation -> Saturation
invert (Saturation s) = Saturation (100 - s)

-- | Create saturation from unit interval (0.0-1.0)
-- |
-- | Useful for converting from normalized values:
-- | ```purescript
-- | fromUnitInterval 0.0  -- Saturation 0%
-- | fromUnitInterval 0.5  -- Saturation 50%
-- | fromUnitInterval 1.0  -- Saturation 100%
-- | ```
fromUnitInterval :: Number -> Saturation
fromUnitInterval n = saturation (Int.round (Bounded.clampNumber 0.0 1.0 n * 100.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No saturation (grayscale) - 0%
gray :: Saturation
gray = Saturation 0

-- | Muted saturation - 25%
muted :: Saturation
muted = Saturation 25

-- | Medium saturation - 50%
medium :: Saturation
medium = Saturation 50

-- | Vivid saturation - 75%
vivid :: Saturation
vivid = Saturation 75

-- | Full saturation - 100%
full :: Saturation
full = Saturation 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if saturation is effectively grayscale (< 5%)
isGrayscale :: Saturation -> Boolean
isGrayscale (Saturation s) = s < 5

-- | Check if saturation is vivid (> 80%)
isVivid :: Saturation -> Boolean
isVivid (Saturation s) = s > 80

-- | Check if saturation is muted (5-50%)
-- |
-- | Muted colors have noticeable color but are subdued:
-- | ```purescript
-- | isMuted (saturation 30)  -- true
-- | isMuted gray             -- false
-- | isMuted full             -- false
-- | ```
isMuted :: Saturation -> Boolean
isMuted (Saturation s) = s >= 5 && s <= 50

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value
unwrap :: Saturation -> Int
unwrap (Saturation s) = s

-- | Convert to Number for calculations
toNumber :: Saturation -> Number
toNumber (Saturation s) = Int.toNumber s

-- | Convert to unit interval (0.0-1.0)
toUnitInterval :: Saturation -> Number
toUnitInterval (Saturation s) = Int.toNumber s / 100.0

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "saturation" "Color intensity as percentage"
