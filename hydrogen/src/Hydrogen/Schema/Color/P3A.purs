-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                         // hydrogen // schema // color // p3a
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | P3A - Display P3 with alpha transparency.
-- |
-- | **WHY P3A?**
-- | P3A extends Display P3 with an opacity channel, enabling:
-- | - Wide gamut transparent colors for Apple devices
-- | - Proper alpha compositing in Display P3 space
-- | - Modern web with CSS `color(display-p3 r g b / a)` support
-- |
-- | **Components:**
-- | - **R** (Red): 0.0 to 1.0 (linear-light)
-- | - **G** (Green): 0.0 to 1.0 (linear-light)
-- | - **B** (Blue): 0.0 to 1.0 (linear-light)
-- | - **α** (Alpha): 0-100% opacity (0 = transparent, 100 = opaque)
-- |
-- | **Display P3 Characteristics:**
-- | - Primaries: Wider than sRGB, especially greens and reds
-- | - White point: D65 (same as sRGB)
-- | - Transfer function: sRGB-like gamma
-- | - Used by: Mac, iPhone, iPad, modern web browsers
-- |
-- | **Use cases:**
-- | - Wide gamut UI with transparency (Apple ecosystem)
-- | - HDR-aware web design
-- | - Photo overlays preserving wide gamut colors

module Hydrogen.Schema.Color.P3A
  ( -- * Types
    P3A
  
  -- * Constructors
  , p3a
  , p3aFromRecord
  , fromDisplayP3
  , withAlpha
  
  -- * Accessors
  , red
  , green
  , blue
  , alpha
  , toDisplayP3
  , p3aToRecord
  
  -- * Operations
  , blend
  , scale
  , lighten
  , darken
  , fadeIn
  , fadeOut
  , setAlpha
  
  -- * CSS Output
  , p3aToCss
  
  -- * Comparison
  , isEqual
  , isFullyOpaque
  , isFullyTransparent
  , isInGamut
  
  -- * Luminance
  , luminance
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>)
  , (>=)
  , (==)
  , (&&)
  , (<>)
  )

import Data.Int (round, toNumber) as Int
import Hydrogen.Schema.Color.WideGamut as WG
import Hydrogen.Schema.Color.Opacity as Op

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                        // p3a
-- ═════════════════════════════════════════════════════════════════════════════

-- | P3A color value — Display P3 with an alpha channel.
-- |
-- | Composes DisplayP3 (wide gamut RGB) with Opacity (0-100%).
-- | 0% = fully transparent, 100% = fully opaque.
newtype P3A = P3A
  { color :: WG.DisplayP3
  , alpha :: Op.Opacity
  }

derive instance eqP3A :: Eq P3A
derive instance ordP3A :: Ord P3A

instance showP3A :: Show P3A where
  show = p3aToCss

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a P3A color from raw values.
-- |
-- | - R, G, B: 0.0-1.0 (clamped)
-- | - α (Alpha): 0-100 (percentage): 0 = transparent, 100 = opaque
-- |
-- | ```purescript
-- | p3a 1.0 0.5 0.2 100  -- Vibrant orange, fully opaque
-- | p3a 0.0 0.8 0.2 50   -- Bright green, half transparent
-- | p3a 0.0 0.0 0.0 0    -- Black, fully transparent
-- | ```
p3a :: Number -> Number -> Number -> Int -> P3A
p3a r g b a = P3A
  { color: WG.displayP3 r g b
  , alpha: Op.opacity a
  }

-- | Create a P3A color from a record.
p3aFromRecord :: { r :: Number, g :: Number, b :: Number, a :: Int } -> P3A
p3aFromRecord { r, g, b, a } = p3a r g b a

-- | Create P3A from DisplayP3 with full opacity.
fromDisplayP3 :: WG.DisplayP3 -> P3A
fromDisplayP3 color = P3A
  { color: color
  , alpha: Op.opacity 100
  }

-- | Create P3A from DisplayP3 with specified alpha.
withAlpha :: WG.DisplayP3 -> Int -> P3A
withAlpha color a = P3A
  { color: color
  , alpha: Op.opacity a
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the red component.
red :: P3A -> Number
red (P3A p) = 
  let rec = WG.displayP3ToRecord p.color
  in rec.r

-- | Extract the green component.
green :: P3A -> Number
green (P3A p) = 
  let rec = WG.displayP3ToRecord p.color
  in rec.g

-- | Extract the blue component.
blue :: P3A -> Number
blue (P3A p) = 
  let rec = WG.displayP3ToRecord p.color
  in rec.b

-- | Extract the alpha (opacity).
alpha :: P3A -> Op.Opacity
alpha (P3A p) = p.alpha

-- | Extract the DisplayP3 portion (without alpha).
toDisplayP3 :: P3A -> WG.DisplayP3
toDisplayP3 (P3A p) = p.color

-- | Convert P3A to a record of raw values.
p3aToRecord :: P3A -> { r :: Number, g :: Number, b :: Number, a :: Int }
p3aToRecord (P3A p) =
  let rec = WG.displayP3ToRecord p.color
  in { r: rec.r
     , g: rec.g
     , b: rec.b
     , a: Op.unwrap p.alpha
     }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Blend two P3A colors.
-- |
-- | Uses linear interpolation: `blend c1 c2 0.5` is midpoint.
-- | Alpha is also blended.
blend :: P3A -> P3A -> Number -> P3A
blend (P3A a) (P3A b) t =
  let t' = clamp01 t
      oneMinusT = 1.0 - t'
      
      recA = WG.displayP3ToRecord a.color
      recB = WG.displayP3ToRecord b.color
      
      r = recA.r * oneMinusT + recB.r * t'
      g = recA.g * oneMinusT + recB.g * t'
      blu = recA.b * oneMinusT + recB.b * t'
      
      alphaA = Op.unwrap a.alpha
      alphaB = Op.unwrap b.alpha
      blendedAlpha = toInt (toNumber alphaA * oneMinusT + toNumber alphaB * t')
  in P3A
    { color: WG.displayP3 r g blu
    , alpha: Op.opacity blendedAlpha
    }

-- | Scale all RGB components by a factor.
-- |
-- | Alpha is unchanged.
scale :: Number -> P3A -> P3A
scale factor (P3A p) =
  let rec = WG.displayP3ToRecord p.color
      r = clamp01 (rec.r * factor)
      g = clamp01 (rec.g * factor)
      b = clamp01 (rec.b * factor)
  in P3A { color: WG.displayP3 r g b, alpha: p.alpha }

-- | Lighten the color by mixing with white.
-- |
-- | `lighten 0.2 color` mixes 20% white.
lighten :: Number -> P3A -> P3A
lighten amount (P3A p) =
  let rec = WG.displayP3ToRecord p.color
      amt = clamp01 amount
      r = rec.r + (1.0 - rec.r) * amt
      g = rec.g + (1.0 - rec.g) * amt
      b = rec.b + (1.0 - rec.b) * amt
  in P3A { color: WG.displayP3 r g b, alpha: p.alpha }

-- | Darken the color by mixing with black.
-- |
-- | `darken 0.2 color` mixes 20% black.
darken :: Number -> P3A -> P3A
darken amount (P3A p) =
  let rec = WG.displayP3ToRecord p.color
      amt = clamp01 amount
      r = rec.r * (1.0 - amt)
      g = rec.g * (1.0 - amt)
      b = rec.b * (1.0 - amt)
  in P3A { color: WG.displayP3 r g b, alpha: p.alpha }

-- | Increase opacity (make more opaque).
-- |
-- | ```purescript
-- | fadeIn 20 color  -- 20% more opaque
-- | ```
fadeIn :: Int -> P3A -> P3A
fadeIn amount (P3A p) =
  let current = Op.unwrap p.alpha
      new = current + amount
  in P3A { color: p.color, alpha: Op.opacity new }

-- | Decrease opacity (make more transparent).
-- |
-- | ```purescript
-- | fadeOut 20 color  -- 20% more transparent
-- | ```
fadeOut :: Int -> P3A -> P3A
fadeOut amount (P3A p) =
  let current = Op.unwrap p.alpha
      new = current - amount
  in P3A { color: p.color, alpha: Op.opacity new }

-- | Set alpha to a specific value.
setAlpha :: Int -> P3A -> P3A
setAlpha a (P3A p) = P3A { color: p.color, alpha: Op.opacity a }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert to CSS color() function with alpha.
-- |
-- | ```purescript
-- | p3aToCss (p3a 1.0 0.5 0.2 75)
-- | -- "color(display-p3 1 0.5 0.2 / 0.75)"
-- | ```
p3aToCss :: P3A -> String
p3aToCss (P3A p) =
  let rec = WG.displayP3ToRecord p.color
      a = Op.toUnitInterval p.alpha
  in "color(display-p3 " <> show rec.r <> " " 
     <> show rec.g <> " " <> show rec.b 
     <> " / " <> show a <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if two P3A colors are equal.
isEqual :: P3A -> P3A -> Boolean
isEqual (P3A a) (P3A b) =
  let recA = WG.displayP3ToRecord a.color
      recB = WG.displayP3ToRecord b.color
  in recA.r == recB.r &&
     recA.g == recB.g &&
     recA.b == recB.b &&
     Op.unwrap a.alpha == Op.unwrap b.alpha

-- | Check if color is fully opaque (alpha = 100%).
isFullyOpaque :: P3A -> Boolean
isFullyOpaque (P3A p) = Op.unwrap p.alpha == 100

-- | Check if color is fully transparent (alpha = 0%).
isFullyTransparent :: P3A -> Boolean
isFullyTransparent (P3A p) = Op.unwrap p.alpha == 0

-- | Check if color is within P3 gamut (all components 0-1).
isInGamut :: P3A -> Boolean
isInGamut (P3A p) =
  let rec = WG.displayP3ToRecord p.color
  in rec.r >= 0.0 && rec.r <= 1.0 &&
     rec.g >= 0.0 && rec.g <= 1.0 &&
     rec.b >= 0.0 && rec.b <= 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // luminance
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate relative luminance.
-- |
-- | Uses Display P3 coefficients (slightly different from sRGB).
-- | Y = 0.2627 R + 0.6780 G + 0.0593 B
luminance :: P3A -> Number
luminance (P3A p) =
  let rec = WG.displayP3ToRecord p.color
  in 0.2627 * rec.r + 0.6780 * rec.g + 0.0593 * rec.b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Convert Int to Number
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Convert Number to Int (rounds)
toInt :: Number -> Int
toInt = Int.round
