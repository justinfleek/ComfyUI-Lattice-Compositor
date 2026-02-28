-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // filter-sepia
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterSepia - sepia tone filter amount.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No effect (original colors)
-- | - **0.5**: Partial sepia tone
-- | - **1.0**: Full sepia tone (vintage brown)
-- |
-- | Creates warm, brownish tone reminiscent of old photographs.

module Hydrogen.Schema.Material.FilterSepia
  ( FilterSepia
  , filterSepia
  , unwrap
  , toNumber
  , bounds
  , none
  , subtle
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
--                                                               // filter-sepia
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter sepia amount (0.0 to 1.0)
-- |
-- | Applies a sepia tone effect, creating warm brownish tones.
newtype FilterSepia = FilterSepia Number

derive instance eqFilterSepia :: Eq FilterSepia
derive instance ordFilterSepia :: Ord FilterSepia

instance showFilterSepia :: Show FilterSepia where
  show (FilterSepia s) = "FilterSepia " <> show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter sepia, clamping to 0.0-1.0
filterSepia :: Number -> FilterSepia
filterSepia n = FilterSepia (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No sepia effect
none :: FilterSepia
none = FilterSepia 0.0

-- | Subtle sepia (25%)
subtle :: FilterSepia
subtle = FilterSepia 0.25

-- | Moderate sepia (50%)
moderate :: FilterSepia
moderate = FilterSepia 0.5

-- | Full sepia tone
full :: FilterSepia
full = FilterSepia 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterSepia -> Number
unwrap (FilterSepia s) = s

-- | Convert to Number (passthrough for this type)
toNumber :: FilterSepia -> Number
toNumber (FilterSepia s) = s

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "filterSepia" "Sepia tone filter amount"
