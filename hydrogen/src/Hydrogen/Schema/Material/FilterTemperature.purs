-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // material // filter-temperature
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterTemperature - color temperature adjustment.
-- |
-- | Range: -1.0 to +1.0 (clamps)
-- | - **-1.0**: Cooler (more blue)
-- | - **0.0**: No adjustment
-- | - **+1.0**: Warmer (more orange)
-- |
-- | Adjusts the blue-orange color balance, simulating white balance shifts.

module Hydrogen.Schema.Material.FilterTemperature
  ( FilterTemperature
  , filterTemperature
  , unwrap
  , toNumber
  , bounds
  , neutral
  , cool
  , warm
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
--                                                         // filter-temperature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter temperature adjustment (-1.0 to +1.0)
-- |
-- | Shifts color balance toward blue (cool) or orange (warm).
newtype FilterTemperature = FilterTemperature Number

derive instance eqFilterTemperature :: Eq FilterTemperature
derive instance ordFilterTemperature :: Ord FilterTemperature

instance showFilterTemperature :: Show FilterTemperature where
  show (FilterTemperature t) = "FilterTemperature " <> show t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter temperature, clamping to -1.0 to +1.0
filterTemperature :: Number -> FilterTemperature
filterTemperature n = FilterTemperature (Bounded.clampNumber (-1.0) 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Neutral temperature
neutral :: FilterTemperature
neutral = FilterTemperature 0.0

-- | Cool (more blue)
cool :: FilterTemperature
cool = FilterTemperature (-0.5)

-- | Warm (more orange)
warm :: FilterTemperature
warm = FilterTemperature 0.5

-- | Invert the temperature
-- |
-- | Converts warm to cool and vice versa.
invert :: FilterTemperature -> FilterTemperature
invert (FilterTemperature t) = FilterTemperature (negate t)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterTemperature -> Number
unwrap (FilterTemperature t) = t

-- | Convert to Number (passthrough for this type)
toNumber :: FilterTemperature -> Number
toNumber (FilterTemperature t) = t

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-1.0) 1.0 "filterTemperature" "Color temperature (blue-orange) adjustment"
