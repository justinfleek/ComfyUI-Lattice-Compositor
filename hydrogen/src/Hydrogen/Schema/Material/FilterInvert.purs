-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // material // filter-invert
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterInvert - color inversion filter amount.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No effect (original colors)
-- | - **0.5**: Partial inversion
-- | - **1.0**: Full inversion (negative)
-- |
-- | Inverts all color channels, creating a negative image effect.

module Hydrogen.Schema.Material.FilterInvert
  ( FilterInvert
  , filterInvert
  , unwrap
  , toNumber
  , bounds
  , none
  , partial
  , moderate
  , full
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
--                                                              // filter-invert
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter invert amount (0.0 to 1.0)
-- |
-- | Inverts color channels to create negative image effect.
newtype FilterInvert = FilterInvert Number

derive instance eqFilterInvert :: Eq FilterInvert
derive instance ordFilterInvert :: Ord FilterInvert

instance showFilterInvert :: Show FilterInvert where
  show (FilterInvert i) = "FilterInvert " <> show i

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter invert, clamping to 0.0-1.0
filterInvert :: Number -> FilterInvert
filterInvert n = FilterInvert (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No inversion effect
none :: FilterInvert
none = FilterInvert 0.0

-- | Partial inversion (25%)
partial :: FilterInvert
partial = FilterInvert 0.25

-- | Moderate inversion (50%)
moderate :: FilterInvert
moderate = FilterInvert 0.5

-- | Full inversion (negative)
full :: FilterInvert
full = FilterInvert 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterInvert -> Number
unwrap (FilterInvert i) = i

-- | Convert to Number (passthrough for this type)
toNumber :: FilterInvert -> Number
toNumber (FilterInvert i) = i

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "filterInvert" "Color inversion filter amount"
