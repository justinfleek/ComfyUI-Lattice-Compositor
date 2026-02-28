-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // material // filter-fade
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterFade - vintage fade effect amount.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No fade (full contrast)
-- | - **0.5**: Moderate fading
-- | - **1.0**: Heavy fade (washed out blacks)
-- |
-- | Lightens shadows to create a faded, vintage film look by lifting the black point.

module Hydrogen.Schema.Material.FilterFade
  ( FilterFade
  , filterFade
  , unwrap
  , toNumber
  , bounds
  , none
  , subtle
  , moderate
  , heavy
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
--                                                                // filter-fade
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter fade amount (0.0 to 1.0)
-- |
-- | Lifts black point to create vintage faded look.
newtype FilterFade = FilterFade Number

derive instance eqFilterFade :: Eq FilterFade
derive instance ordFilterFade :: Ord FilterFade

instance showFilterFade :: Show FilterFade where
  show (FilterFade f) = "FilterFade " <> show f

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter fade, clamping to 0.0-1.0
filterFade :: Number -> FilterFade
filterFade n = FilterFade (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No fade
none :: FilterFade
none = FilterFade 0.0

-- | Subtle fade
subtle :: FilterFade
subtle = FilterFade 0.25

-- | Moderate fade
moderate :: FilterFade
moderate = FilterFade 0.5

-- | Heavy fade
heavy :: FilterFade
heavy = FilterFade 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterFade -> Number
unwrap (FilterFade f) = f

-- | Convert to Number (passthrough for this type)
toNumber :: FilterFade -> Number
toNumber (FilterFade f) = f

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "filterFade" "Vintage fade (lifted black point) amount"
