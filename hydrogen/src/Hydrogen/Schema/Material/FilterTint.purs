-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // material // filter-tint
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterTint - green-magenta tint adjustment.
-- |
-- | Range: -1.0 to +1.0 (clamps)
-- | - **-1.0**: More green
-- | - **0.0**: No adjustment
-- | - **+1.0**: More magenta
-- |
-- | Adjusts the green-magenta color balance, complementary to temperature.

module Hydrogen.Schema.Material.FilterTint
  ( FilterTint
  , filterTint
  , unwrap
  , toNumber
  , bounds
  , neutral
  , green
  , magenta
  , invert
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , negate
  , show
  , (<>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // filter-tint
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter tint adjustment (-1.0 to +1.0)
-- |
-- | Shifts color balance toward green or magenta.
newtype FilterTint = FilterTint Number

derive instance eqFilterTint :: Eq FilterTint
derive instance ordFilterTint :: Ord FilterTint

instance showFilterTint :: Show FilterTint where
  show (FilterTint t) = "FilterTint " <> show t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter tint, clamping to -1.0 to +1.0
filterTint :: Number -> FilterTint
filterTint n = FilterTint (Bounded.clampNumber (-1.0) 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Neutral tint
neutral :: FilterTint
neutral = FilterTint 0.0

-- | Green tint
green :: FilterTint
green = FilterTint (-0.5)

-- | Magenta tint
magenta :: FilterTint
magenta = FilterTint 0.5

-- | Invert the tint
-- |
-- | Converts green to magenta and vice versa.
invert :: FilterTint -> FilterTint
invert (FilterTint t) = FilterTint (negate t)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterTint -> Number
unwrap (FilterTint t) = t

-- | Convert to Number (passthrough for this type)
toNumber :: FilterTint -> Number
toNumber (FilterTint t) = t

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-1.0) 1.0 "filterTint" "Color tint (green-magenta) adjustment"
