-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // color // opacity
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Opacity - alpha transparency value.
-- |
-- | Measured as a percentage from 0 to 100:
-- | - **0%**: Fully transparent (invisible)
-- | - **50%**: Half transparent
-- | - **100%**: Fully opaque (solid)
-- |
-- | Used in RGBA, HSLA, and other color spaces with alpha channels.
-- | Also known as alpha or transparency.

module Hydrogen.Schema.Color.Opacity
  ( Opacity
  , opacity
  , unsafeOpacity
  , unwrap
  , scale
  , increase
  , decrease
  , invert
  , multiply
  , blend
  , isTransparent
  , isOpaque
  , isSemiTransparent
  , bounds
  , toNumber
  , toUnitInterval
  , fromUnitInterval
  , toChannel
  , fromChannel
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
  , (==)
  , (>)
  , (<)
  , (&&)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // opacity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Opacity value as percentage (0-100)
-- |
-- | Represents alpha transparency. 0% is fully transparent, 100% is fully opaque.
-- | This matches the pattern of other percentage-based atoms like Saturation and
-- | Lightness for consistency across the Schema.
newtype Opacity = Opacity Int

derive instance eqOpacity :: Eq Opacity
derive instance ordOpacity :: Ord Opacity

instance showOpacity :: Show Opacity where
  show (Opacity o) = show o <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create an opacity value, clamping to 0-100
-- |
-- | Values outside the valid range are clamped:
-- | ```purescript
-- | opacity 50   -- Opacity 50%
-- | opacity 150  -- Opacity 100% (clamped)
-- | opacity (-20) -- Opacity 0% (clamped)
-- | ```
opacity :: Int -> Opacity
opacity n = Opacity (Bounded.clampInt 0 100 n)

-- | Create an opacity value without clamping
-- |
-- | Use only when you know the value is valid (0-100).
-- | Invalid values will break invariants.
unsafeOpacity :: Int -> Opacity
unsafeOpacity = Opacity

-- | Create opacity from unit interval (0.0-1.0)
-- |
-- | Useful for converting from graphics APIs that use normalized floats.
-- | ```purescript
-- | fromUnitInterval 0.0  -- Opacity 0%
-- | fromUnitInterval 0.5  -- Opacity 50%
-- | fromUnitInterval 1.0  -- Opacity 100%
-- | ```
fromUnitInterval :: Number -> Opacity
fromUnitInterval n = opacity (Int.round (Bounded.clampNumber 0.0 1.0 n * 100.0))

-- | Create opacity from 8-bit channel value (0-255)
-- |
-- | Useful for converting RGBA8 formats where alpha is stored as a byte.
-- | ```purescript
-- | fromChannel 0    -- Opacity 0%
-- | fromChannel 128  -- Opacity 50%
-- | fromChannel 255  -- Opacity 100%
-- | ```
fromChannel :: Int -> Opacity
fromChannel c = 
  let clamped = Bounded.clampInt 0 255 c
  in opacity (Int.round (Int.toNumber clamped * 100.0 / 255.0))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale opacity by a factor (0.0 to 2.0 typical)
-- |
-- | Useful for fading effects:
-- | ```purescript
-- | scale 0.5 (opacity 80)  -- Opacity 40%
-- | scale 2.0 (opacity 30)  -- Opacity 60%
-- | ```
scale :: Number -> Opacity -> Opacity
scale factor (Opacity o) = 
  opacity (Int.round (Int.toNumber o * factor))

-- | Increase opacity by percentage points
-- |
-- | Makes something more opaque:
-- | ```purescript
-- | increase 20 (opacity 30)  -- Opacity 50%
-- | increase 50 (opacity 80)  -- Opacity 100% (clamped)
-- | ```
increase :: Int -> Opacity -> Opacity
increase amount (Opacity o) = opacity (o + amount)

-- | Decrease opacity by percentage points
-- |
-- | Makes something more transparent:
-- | ```purescript
-- | decrease 20 (opacity 50)  -- Opacity 30%
-- | decrease 50 (opacity 30)  -- Opacity 0% (clamped)
-- | ```
decrease :: Int -> Opacity -> Opacity
decrease amount (Opacity o) = opacity (o - amount)

-- | Invert opacity (100 - value)
-- |
-- | Converts transparency to opacity and vice versa:
-- | ```purescript
-- | invert (opacity 30)   -- Opacity 70%
-- | invert (opacity 100)  -- Opacity 0%
-- | ```
invert :: Opacity -> Opacity
invert (Opacity o) = Opacity (100 - o)

-- | Multiply two opacity values
-- |
-- | Models layering of transparent surfaces. Result is always more transparent
-- | than either input (unless one is fully opaque):
-- | ```purescript
-- | multiply (opacity 50) (opacity 50)  -- Opacity 25%
-- | multiply (opacity 80) (opacity 90)  -- Opacity 72%
-- | ```
multiply :: Opacity -> Opacity -> Opacity
multiply (Opacity a) (Opacity b) = 
  opacity (Int.round (Int.toNumber a * Int.toNumber b / 100.0))

-- | Blend two opacity values with weight (0.0 = all first, 1.0 = all second)
-- |
-- | Linear interpolation between two alpha values:
-- | ```purescript
-- | blend 0.0 (opacity 20) (opacity 80)  -- Opacity 20%
-- | blend 0.5 (opacity 20) (opacity 80)  -- Opacity 50%
-- | blend 1.0 (opacity 20) (opacity 80)  -- Opacity 80%
-- | ```
blend :: Number -> Opacity -> Opacity -> Opacity
blend weight (Opacity a) (Opacity b) =
  let w = Bounded.clampNumber 0.0 1.0 weight
      result = Int.toNumber a * (1.0 - w) + Int.toNumber b * w
  in opacity (Int.round result)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if fully transparent (opacity = 0%)
-- |
-- | Useful for optimization - fully transparent layers don't need rendering:
-- | ```purescript
-- | isTransparent (opacity 0)  -- true
-- | isTransparent (opacity 1)  -- false
-- | ```
isTransparent :: Opacity -> Boolean
isTransparent (Opacity o) = o == 0

-- | Check if fully opaque (opacity = 100%)
-- |
-- | Useful for optimization - fully opaque layers can occlude layers behind:
-- | ```purescript
-- | isOpaque (opacity 100)  -- true
-- | isOpaque (opacity 99)   -- false
-- | ```
isOpaque :: Opacity -> Boolean
isOpaque (Opacity o) = o == 100

-- | Check if semi-transparent (0% < opacity < 100%)
-- |
-- | Detects cases requiring alpha blending:
-- | ```purescript
-- | isSemiTransparent (opacity 50)   -- true
-- | isSemiTransparent (opacity 0)    -- false
-- | isSemiTransparent (opacity 100)  -- false
-- | ```
isSemiTransparent :: Opacity -> Boolean
isSemiTransparent (Opacity o) = o > 0 && o < 100

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Int value (0-100)
unwrap :: Opacity -> Int
unwrap (Opacity o) = o

-- | Convert to Number for calculations
toNumber :: Opacity -> Number
toNumber (Opacity o) = Int.toNumber o

-- | Convert to unit interval (0.0-1.0)
-- |
-- | Useful for exporting to graphics APIs (CSS, WebGL, Canvas):
-- | ```purescript
-- | toUnitInterval (opacity 0)    -- 0.0
-- | toUnitInterval (opacity 50)   -- 0.5
-- | toUnitInterval (opacity 100)  -- 1.0
-- | ```
toUnitInterval :: Opacity -> Number
toUnitInterval (Opacity o) = Int.toNumber o / 100.0

-- | Convert to 8-bit channel value (0-255)
-- |
-- | Useful for serializing to RGBA8 formats:
-- | ```purescript
-- | toChannel (opacity 0)    -- 0
-- | toChannel (opacity 50)   -- 128
-- | toChannel (opacity 100)  -- 255
-- | ```
toChannel :: Opacity -> Int
toChannel (Opacity o) = Int.round (Int.toNumber o * 255.0 / 100.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds documentation for this type
bounds :: Bounded.IntBounds
bounds = Bounded.intBounds 0 100 "opacity" "Alpha transparency as percentage"
