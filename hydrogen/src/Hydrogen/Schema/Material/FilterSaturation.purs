-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // material // filter-saturation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterSaturation - color saturation filter multiplier.
-- |
-- | Range: 0.0 to 2.0 (clamps)
-- | - **0.0**: Completely desaturated (grayscale)
-- | - **1.0**: Original saturation (no effect)
-- | - **2.0**: Hyper-saturated
-- |
-- | Note: This is distinct from HSL Saturation. This is a CSS filter multiplier.

module Hydrogen.Schema.Material.FilterSaturation
  ( FilterSaturation
  , filterSaturation
  , unwrap
  , toNumber
  , bounds
  , grayscale
  , normal
  , enhanced
  , hyper
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
--                                                          // filter-saturation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter saturation multiplier (0.0 to 2.0)
-- |
-- | Multiplier for color saturation in CSS filter effects.
-- | Values below 1.0 desaturate, above 1.0 intensify colors.
newtype FilterSaturation = FilterSaturation Number

derive instance eqFilterSaturation :: Eq FilterSaturation
derive instance ordFilterSaturation :: Ord FilterSaturation

instance showFilterSaturation :: Show FilterSaturation where
  show (FilterSaturation s) = show s <> "x"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter saturation, clamping to 0.0-2.0
filterSaturation :: Number -> FilterSaturation
filterSaturation n = FilterSaturation (Bounded.clampNumber 0.0 2.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Completely desaturated (grayscale)
grayscale :: FilterSaturation
grayscale = FilterSaturation 0.0

-- | Normal saturation (no effect)
normal :: FilterSaturation
normal = FilterSaturation 1.0

-- | Enhanced saturation (1.5x)
enhanced :: FilterSaturation
enhanced = FilterSaturation 1.5

-- | Hyper-saturated (2.0x)
hyper :: FilterSaturation
hyper = FilterSaturation 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterSaturation -> Number
unwrap (FilterSaturation s) = s

-- | Convert to Number (passthrough for this type)
toNumber :: FilterSaturation -> Number
toNumber (FilterSaturation s) = s

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 2.0 "filterSaturation" "Color saturation filter multiplier"
