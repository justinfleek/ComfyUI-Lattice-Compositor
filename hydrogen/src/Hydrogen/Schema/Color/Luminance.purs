-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // color // luminance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Luminance - absolute light emission intensity.
-- |
-- | Measured in candelas per square meter (cd/m², also called "nits"):
-- | - **0.0**: No light emission (black)
-- | - **80-200**: Typical SDR displays
-- | - **400-600**: Bright SDR displays
-- | - **1,000+**: HDR content (HDR10 standard)
-- | - **4,000+**: Peak HDR highlights
-- | - **10,000+**: Ultra HDR displays
-- |
-- | ## vs Lightness
-- |
-- | - **Lightness (HSL)**: Perceptual - "how light/dark does this look?"
-- | - **Luminance**: Physical - "how much light does this emit?"
-- |
-- | Luminance is for:
-- | - Emissive UI elements (glowing buttons, neon text)
-- | - HDR rendering (bloom effects, bright highlights)
-- | - Light source definitions (how bright is this light?)
-- | - Self-illuminating materials
-- |
-- | ## Use Cases
-- |
-- | - Glow effects (button with 200 nit glow)
-- | - HDR content (sunset at 4000 nits peak)
-- | - Light sources (LED panel at 500 nits)
-- | - Emissive materials (neon sign at 1000 nits)

module Hydrogen.Schema.Color.Luminance
  ( Luminance
  , luminance
  , fromInt
  , unsafeLuminance
  , unwrap
  , toInt
  , toNumber
  , scale
  , increase
  , decrease
  , bounds
  , isOff
  , isSubtle
  , isBright
  , isHDR
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (<>)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // luminance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Luminance value in nits (cd/m²)
-- |
-- | Represents absolute light emission intensity. 0 = no light, higher values
-- | = brighter emission. Unbounded to support HDR (can exceed 10,000 nits).
newtype Luminance = Luminance Number

derive instance eqLuminance :: Eq Luminance
derive instance ordLuminance :: Ord Luminance

instance showLuminance :: Show Luminance where
  show (Luminance l) = show l <> " nits"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a luminance value, clamping to >= 0.0
-- |
-- | Negative luminance is physically meaningless and is clamped to 0.
-- | Upper bound is unbounded to support HDR.
-- |
-- | ```purescript
-- | luminance 0.0      -- No emission (black)
-- | luminance 100.0    -- Typical display
-- | luminance 1000.0   -- HDR content
-- | luminance (-50.0)  -- Clamped to 0.0
-- | ```
luminance :: Number -> Luminance
luminance n = Luminance (Bounded.clampNumber 0.0 100000.0 n)

-- | Create luminance from integer nit value
-- |
-- | Common in display specifications and UI:
-- | ```purescript
-- | fromInt 100   -- 100 nits (typical display)
-- | fromInt 1000  -- 1000 nits (HDR)
-- | ```
fromInt :: Int -> Luminance
fromInt n = luminance (Int.toNumber n)

-- | Create a luminance value without clamping
-- |
-- | Use only when you know the value is valid (>= 0.0).
unsafeLuminance :: Number -> Luminance
unsafeLuminance = Luminance

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Scale luminance by a factor
-- |
-- | Useful for relative adjustments:
-- | ```purescript
-- | scale 2.0 (luminance 100.0)  -- Double brightness → 200 nits
-- | scale 0.5 (luminance 100.0)  -- Half brightness → 50 nits
-- | ```
scale :: Number -> Luminance -> Luminance
scale factor (Luminance l) = luminance (l * factor)

-- | Increase luminance by amount
-- |
-- | ```purescript
-- | increase 50.0 (luminance 100.0)  -- 150 nits
-- | ```
increase :: Number -> Luminance -> Luminance
increase amount (Luminance l) = luminance (l + amount)

-- | Decrease luminance by amount
-- |
-- | ```purescript
-- | decrease 50.0 (luminance 100.0)  -- 50 nits
-- | ```
decrease :: Number -> Luminance -> Luminance
decrease amount (Luminance l) = luminance (l - amount)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if luminance is effectively off (< 1.0 nit)
-- |
-- | Useful for optimization - non-emissive surfaces don't need glow rendering.
isOff :: Luminance -> Boolean
isOff (Luminance l) = l < 1.0

-- | Check if subtle glow (1-100 nits)
-- |
-- | Subtle glows: dim button highlights, ambient UI lighting
isSubtle :: Luminance -> Boolean
isSubtle (Luminance l) = l >= 1.0 && l <= 100.0

-- | Check if bright (100-1000 nits)
-- |
-- | Bright emissions: prominent buttons, active elements, LED indicators
isBright :: Luminance -> Boolean
isBright (Luminance l) = l > 100.0 && l <= 1000.0

-- | Check if HDR range (> 1000 nits)
-- |
-- | HDR content: peak highlights, sun reflections, neon signs, explosions
isHDR :: Luminance -> Boolean
isHDR (Luminance l) = l > 1000.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value (nits)
unwrap :: Luminance -> Number
unwrap (Luminance l) = l

-- | Round to nearest integer nit
-- |
-- | Useful for display and serialization:
-- | ```purescript
-- | toInt (luminance 147.3)  -- 147
-- | toInt (luminance 999.8)  -- 1000
-- | ```
toInt :: Luminance -> Int
toInt (Luminance l) = Int.round l

-- | Convert to Number (alias for unwrap)
toNumber :: Luminance -> Number
toNumber = unwrap

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 100000.0 "luminance" "Light emission intensity in nits (cd/m²)"
