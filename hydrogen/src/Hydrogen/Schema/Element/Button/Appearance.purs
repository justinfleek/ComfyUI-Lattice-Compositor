-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // element // button // appearance
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ButtonAppearance — visual atoms for button surface and elevation.
-- |
-- | ## Atoms Included
-- |
-- | - Fill (solid, gradient, noise)
-- | - Border (stroke width, color, style)
-- | - Shadow (layered box shadows)
-- | - Opacity

module Hydrogen.Schema.Element.Button.Appearance
  ( -- * Button Appearance Record
    ButtonAppearance
  , defaultAppearance
    -- * Accessors
  , appFill
  , appShadow
  , appBorderWidth
  , appBorderColor
  , appOpacity
  ) where

import Prelude
  ( class Eq
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Material.Fill (Fill, fillSolid) as Fill
import Hydrogen.Schema.Elevation.Shadow (LayeredShadow, noShadow) as Shadow
import Hydrogen.Schema.Color.RGB (RGB, rgb) as Color

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // button appearance
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Appearance atoms for button surface.
-- |
-- | Visual properties: fill, border, shadow, opacity.
type ButtonAppearance =
  { -- Surface
    fill :: Fill.Fill                   -- ^ Background fill
  , opacity :: Number                   -- ^ Overall opacity (0-1)
    -- Border
  , borderWidth :: Number               -- ^ Border width (0 = no border)
  , borderColor :: Maybe Color.RGB      -- ^ Border color (Nothing = transparent)
    -- Elevation
  , shadow :: Shadow.LayeredShadow      -- ^ Shadow layers
  }

-- | Default button appearance.
-- |
-- | Solid blue fill, no border, no shadow, full opacity.
defaultAppearance :: ButtonAppearance
defaultAppearance =
  { fill: Fill.fillSolid (Color.rgb 59 130 246)  -- Blue 500
  , opacity: 1.0
  , borderWidth: 0.0
  , borderColor: Nothing
  , shadow: Shadow.noShadow
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                    // accessors
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get fill.
appFill :: ButtonAppearance -> Fill.Fill
appFill a = a.fill

-- | Get shadow.
appShadow :: ButtonAppearance -> Shadow.LayeredShadow
appShadow a = a.shadow

-- | Get border width.
appBorderWidth :: ButtonAppearance -> Number
appBorderWidth a = a.borderWidth

-- | Get border color.
appBorderColor :: ButtonAppearance -> Maybe Color.RGB
appBorderColor a = a.borderColor

-- | Get opacity.
appOpacity :: ButtonAppearance -> Number
appOpacity a = a.opacity
