-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // schema // color // palette
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color palette generation and semantic roles.
-- |
-- | Tools for building systematic color palettes:
-- | - **Tints**: Lighter variations (add white)
-- | - **Shades**: Darker variations (add black)
-- | - **Tones**: Less saturated variations (add gray)
-- | - **Roles**: Semantic meaning in a design system

module Hydrogen.Schema.Color.Palette
  ( -- * Palette Type
    Palette
  , PaletteEntry
  
  -- * Semantic Roles
  , Role(..)
  
  -- * Palette Generation
  , tints
  , shades
  , tones
  , monochromatic
  
  -- * Palette Construction
  , emptyPalette
  , addColor
  , fromColors
  ) where

import Prelude
  ( class Eq
  , class Show
  , map
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  )

import Data.Array ((:), range)
import Data.Int (round, toNumber)
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // palette type
-- ═════════════════════════════════════════════════════════════════════════════

-- | A palette entry pairs a color with an optional role
type PaletteEntry = 
  { color :: HSL.HSL
  , role :: Role 
  }

-- | A palette is an array of color entries
type Palette = Array PaletteEntry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // semantic roles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic role of a color in a design system
data Role
  = Primary              -- ^ Main brand color
  | Secondary            -- ^ Supporting brand color
  | Accent               -- ^ Call-to-action, highlights
  | Background           -- ^ Page/section backgrounds
  | Surface              -- ^ Card/element backgrounds
  | OnPrimary            -- ^ Text/icons on primary
  | OnSecondary          -- ^ Text/icons on secondary
  | OnBackground         -- ^ Text/icons on background
  | OnSurface            -- ^ Text/icons on surface
  | Neutral              -- ^ Grays and muted colors
  | Success              -- ^ Positive feedback (green)
  | Warning              -- ^ Caution feedback (amber/yellow)
  | Error                -- ^ Negative feedback (red)
  | Info                 -- ^ Informational (blue)
  | Unassigned           -- ^ No specific role yet

derive instance eqRole :: Eq Role

instance showRole :: Show Role where
  show = case _ of
    Primary -> "primary"
    Secondary -> "secondary"
    Accent -> "accent"
    Background -> "background"
    Surface -> "surface"
    OnPrimary -> "on-primary"
    OnSecondary -> "on-secondary"
    OnBackground -> "on-background"
    OnSurface -> "on-surface"
    Neutral -> "neutral"
    Success -> "success"
    Warning -> "warning"
    Error -> "error"
    Info -> "info"
    Unassigned -> "unassigned"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // palette generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate tints (lighter versions) of a color
-- |
-- | Adds white to create progressively lighter variations.
tints :: Int -> HSL.HSL -> Array HSL.HSL
tints count color =
  let h = Hue.unwrap (HSL.hue color)
      s = Sat.unwrap (HSL.saturation color)
      l = Light.unwrap (HSL.lightness color)
      step = toNumber (100 - l) / toNumber (count + 1)
      makeColor i = HSL.hsl h s (l + round (step * toNumber i))
  in map makeColor (range 1 count)

-- | Generate shades (darker versions) of a color
-- |
-- | Adds black to create progressively darker variations.
shades :: Int -> HSL.HSL -> Array HSL.HSL
shades count color =
  let h = Hue.unwrap (HSL.hue color)
      s = Sat.unwrap (HSL.saturation color)
      l = Light.unwrap (HSL.lightness color)
      step = toNumber l / toNumber (count + 1)
      makeColor i = HSL.hsl h s (l - round (step * toNumber i))
  in map makeColor (range 1 count)

-- | Generate tones (less saturated versions) of a color
-- |
-- | Adds gray to create progressively more muted variations.
tones :: Int -> HSL.HSL -> Array HSL.HSL
tones count color =
  let h = Hue.unwrap (HSL.hue color)
      s = Sat.unwrap (HSL.saturation color)
      l = Light.unwrap (HSL.lightness color)
      step = toNumber s / toNumber (count + 1)
      makeColor i = HSL.hsl h (s - round (step * toNumber i)) l
  in map makeColor (range 1 count)

-- | Generate a monochromatic palette
-- |
-- | Combines tints and shades for a full value range.
monochromatic :: Int -> HSL.HSL -> Array HSL.HSL
monochromatic count color = tints (count / 2) color <> shades (count / 2) color

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // palette construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Empty palette
emptyPalette :: Palette
emptyPalette = []

-- | Add a color with role to palette
addColor :: Role -> HSL.HSL -> Palette -> Palette
addColor role color palette = { color, role } : palette

-- | Create palette from colors (all unassigned)
fromColors :: Array HSL.HSL -> Palette
fromColors = map (\color -> { color, role: Unassigned })
