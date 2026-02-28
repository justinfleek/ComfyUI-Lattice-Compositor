-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // border-width
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BorderWidth - thickness of border strokes.
-- |
-- | Range: 0.0 to infinity (finite)
-- | - **0.0**: No border (invisible)
-- | - **1.0**: Hairline (standard thin border)
-- | - **2.0-4.0**: Medium borders
-- | - **8.0+**: Thick decorative borders
-- |
-- | Used for border-width in CSS, stroke-width in SVG, outline thickness.
-- | No maximum enforced - large borders are valid for decorative effects.

module Hydrogen.Schema.Material.BorderWidth
  ( BorderWidth
  , borderWidth
  , unwrap
  , toNumber
  , bounds
  , none
  , hairline
  , thin
  , medium
  , thick
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // border-width
-- ═════════════════════════════════════════════════════════════════════════════

-- | Border width in pixels (0.0 to infinity)
-- |
-- | Finite values only. Represents physical border thickness.
newtype BorderWidth = BorderWidth Number

derive instance eqBorderWidth :: Eq BorderWidth
derive instance ordBorderWidth :: Ord BorderWidth

instance showBorderWidth :: Show BorderWidth where
  show (BorderWidth w) = "BorderWidth " <> show w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a border width, clamping to minimum of 0.0
-- |
-- | Negative values become 0.0. Infinity and NaN are rejected (finite only).
borderWidth :: Number -> BorderWidth
borderWidth n = BorderWidth (Bounded.clampNumberMin 0.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No border (invisible)
none :: BorderWidth
none = BorderWidth 0.0

-- | Hairline border (1px)
hairline :: BorderWidth
hairline = BorderWidth 1.0

-- | Thin border (2px)
thin :: BorderWidth
thin = BorderWidth 2.0

-- | Medium border (4px)
medium :: BorderWidth
medium = BorderWidth 4.0

-- | Thick border (8px)
thick :: BorderWidth
thick = BorderWidth 8.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: BorderWidth -> Number
unwrap (BorderWidth w) = w

-- | Convert to Number (passthrough for this type)
toNumber :: BorderWidth -> Number
toNumber (BorderWidth w) = w

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 999999.0 "borderWidth" "Border stroke thickness in pixels"
