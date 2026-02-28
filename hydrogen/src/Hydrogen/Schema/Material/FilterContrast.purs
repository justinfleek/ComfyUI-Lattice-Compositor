-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // material // filter-contrast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterContrast - contrast filter multiplier.
-- |
-- | Range: 0.0 to 2.0 (clamps)
-- | - **0.0**: No contrast (uniform gray)
-- | - **1.0**: Original contrast (no effect)
-- | - **2.0**: Double contrast
-- |
-- | Adjusts the difference between light and dark areas.

module Hydrogen.Schema.Material.FilterContrast
  ( FilterContrast
  , filterContrast
  , unwrap
  , toNumber
  , bounds
  , flat
  , normal
  , enhanced
  , high
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
--                                                            // filter-contrast
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter contrast multiplier (0.0 to 2.0)
-- |
-- | Multiplier for contrast in CSS filter effects.
-- | Adjusts difference between light and dark areas.
newtype FilterContrast = FilterContrast Number

derive instance eqFilterContrast :: Eq FilterContrast
derive instance ordFilterContrast :: Ord FilterContrast

instance showFilterContrast :: Show FilterContrast where
  show (FilterContrast c) = show c <> "x"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter contrast, clamping to 0.0-2.0
filterContrast :: Number -> FilterContrast
filterContrast n = FilterContrast (Bounded.clampNumber 0.0 2.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No contrast (flat gray)
flat :: FilterContrast
flat = FilterContrast 0.0

-- | Normal contrast (no effect)
normal :: FilterContrast
normal = FilterContrast 1.0

-- | Enhanced contrast (1.5x)
enhanced :: FilterContrast
enhanced = FilterContrast 1.5

-- | High contrast (2.0x)
high :: FilterContrast
high = FilterContrast 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterContrast -> Number
unwrap (FilterContrast c) = c

-- | Convert to Number (passthrough for this type)
toNumber :: FilterContrast -> Number
toNumber (FilterContrast c) = c

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 2.0 "filterContrast" "Contrast filter multiplier"
