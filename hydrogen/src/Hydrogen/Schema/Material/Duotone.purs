-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // material // duotone
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Duotone - two-color image effect compound.
-- |
-- | Maps image luminosity to a gradient between two colors.
-- | Dark areas map to the shadow color, light areas to the highlight color.
-- | Popular in modern web design, Spotify album art, etc.
-- |
-- | ## How It Works
-- |
-- | 1. Convert image to grayscale
-- | 2. Map black (0) to shadow color
-- | 3. Map white (255) to highlight color
-- | 4. Interpolate between for mid-tones
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | -- Purple/orange duotone
-- | effect = duotone (rgb 75 0 130) (rgb 255 165 0)
-- |
-- | -- Classic cyan/magenta
-- | cyanMagenta = duotoneCyanMagenta
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Color.RGB

module Hydrogen.Schema.Material.Duotone
  ( -- * Types
    Duotone(Duotone)
  
  -- * Constructors
  , duotone
  , duotoneWithContrast
  
  -- * Accessors
  , shadowColor
  , highlightColor
  , contrast
  
  -- * Presets
  , duotoneCyanMagenta
  , duotonePurpleOrange
  , duotoneBlueYellow
  , duotoneGreenPink
  , duotoneMonochrome
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.RGB (rgb) as RGB
import Hydrogen.Schema.Bounded (clampNumber) as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // duotone
-- ═════════════════════════════════════════════════════════════════════════════

-- | Duotone - two-color image mapping effect.
-- |
-- | Maps grayscale luminosity values to a two-color gradient.
newtype Duotone = Duotone
  { shadowColor :: RGB      -- ^ Color for dark areas (black maps here)
  , highlightColor :: RGB   -- ^ Color for light areas (white maps here)
  , contrast :: Number      -- ^ Contrast adjustment (0.0-2.0, 1.0 = normal)
  }

derive instance eqDuotone :: Eq Duotone

instance showDuotone :: Show Duotone where
  show (Duotone d) = 
    "(Duotone shadow:" <> show d.shadowColor 
      <> " highlight:" <> show d.highlightColor
      <> " contrast:" <> show d.contrast
      <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create duotone effect with default contrast
duotone :: RGB -> RGB -> Duotone
duotone shadow highlight = Duotone
  { shadowColor: shadow
  , highlightColor: highlight
  , contrast: 1.0
  }

-- | Create duotone effect with custom contrast
duotoneWithContrast :: RGB -> RGB -> Number -> Duotone
duotoneWithContrast shadow highlight c = Duotone
  { shadowColor: shadow
  , highlightColor: highlight
  , contrast: Bounded.clampNumber 0.0 2.0 c
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get shadow color (dark areas)
shadowColor :: Duotone -> RGB
shadowColor (Duotone d) = d.shadowColor

-- | Get highlight color (light areas)
highlightColor :: Duotone -> RGB
highlightColor (Duotone d) = d.highlightColor

-- | Get contrast value
contrast :: Duotone -> Number
contrast (Duotone d) = d.contrast

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cyan/Magenta duotone (classic print style)
duotoneCyanMagenta :: Duotone
duotoneCyanMagenta = Duotone
  { shadowColor: RGB.rgb 0 139 139      -- Dark cyan
  , highlightColor: RGB.rgb 255 0 255   -- Magenta
  , contrast: 1.0
  }

-- | Purple/Orange duotone (Spotify style)
duotonePurpleOrange :: Duotone
duotonePurpleOrange = Duotone
  { shadowColor: RGB.rgb 75 0 130       -- Indigo
  , highlightColor: RGB.rgb 255 165 0   -- Orange
  , contrast: 1.1
  }

-- | Blue/Yellow duotone (high contrast)
duotoneBlueYellow :: Duotone
duotoneBlueYellow = Duotone
  { shadowColor: RGB.rgb 0 0 139        -- Dark blue
  , highlightColor: RGB.rgb 255 255 0   -- Yellow
  , contrast: 1.2
  }

-- | Green/Pink duotone (vibrant)
duotoneGreenPink :: Duotone
duotoneGreenPink = Duotone
  { shadowColor: RGB.rgb 0 100 0        -- Dark green
  , highlightColor: RGB.rgb 255 182 193 -- Light pink
  , contrast: 1.0
  }

-- | Monochrome duotone (black to color)
-- |
-- | Creates tinted grayscale effect.
duotoneMonochrome :: RGB -> Duotone
duotoneMonochrome highlight = Duotone
  { shadowColor: RGB.rgb 0 0 0          -- Black
  , highlightColor: highlight
  , contrast: 1.0
  }
