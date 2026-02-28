-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // material // filter-brightness
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterBrightness - brightness filter multiplier.
-- |
-- | Range: 0.0 to 2.0 (clamps)
-- | - **0.0**: Completely black
-- | - **1.0**: Original brightness (no effect)
-- | - **2.0**: Double brightness
-- |
-- | Note: This is a linear multiplier, not perceptual lightness.

module Hydrogen.Schema.Material.FilterBrightness
  ( FilterBrightness
  , filterBrightness
  , unwrap
  , toNumber
  , bounds
  , black
  , normal
  , bright
  , veryBright
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
--                                                          // filter-brightness
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter brightness multiplier (0.0 to 2.0)
-- |
-- | Multiplier for brightness in CSS filter effects.
-- | Linear adjustment of pixel values.
newtype FilterBrightness = FilterBrightness Number

derive instance eqFilterBrightness :: Eq FilterBrightness
derive instance ordFilterBrightness :: Ord FilterBrightness

instance showFilterBrightness :: Show FilterBrightness where
  show (FilterBrightness b) = show b <> "x"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter brightness, clamping to 0.0-2.0
filterBrightness :: Number -> FilterBrightness
filterBrightness n = FilterBrightness (Bounded.clampNumber 0.0 2.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Completely black
black :: FilterBrightness
black = FilterBrightness 0.0

-- | Normal brightness (no effect)
normal :: FilterBrightness
normal = FilterBrightness 1.0

-- | Bright (1.5x)
bright :: FilterBrightness
bright = FilterBrightness 1.5

-- | Very bright (2.0x)
veryBright :: FilterBrightness
veryBright = FilterBrightness 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterBrightness -> Number
unwrap (FilterBrightness b) = b

-- | Convert to Number (passthrough for this type)
toNumber :: FilterBrightness -> Number
toNumber (FilterBrightness b) = b

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 2.0 "filterBrightness" "Brightness filter multiplier"
