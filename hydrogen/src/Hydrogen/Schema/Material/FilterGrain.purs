-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // material // filter-grain
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterGrain - film grain/noise amount.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No grain (clean)
-- | - **0.3**: Subtle film texture
-- | - **0.7**: Noticeable grain
-- | - **1.0**: Heavy grain
-- |
-- | Adds luminance noise to simulate film grain texture. Common in vintage filters.

module Hydrogen.Schema.Material.FilterGrain
  ( FilterGrain
  , filterGrain
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
--                                                               // filter-grain
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter grain amount (0.0 to 1.0)
-- |
-- | Adds film grain texture for vintage look.
newtype FilterGrain = FilterGrain Number

derive instance eqFilterGrain :: Eq FilterGrain
derive instance ordFilterGrain :: Ord FilterGrain

instance showFilterGrain :: Show FilterGrain where
  show (FilterGrain g) = "FilterGrain " <> show g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter grain, clamping to 0.0-1.0
filterGrain :: Number -> FilterGrain
filterGrain n = FilterGrain (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No grain
none :: FilterGrain
none = FilterGrain 0.0

-- | Subtle grain
subtle :: FilterGrain
subtle = FilterGrain 0.25

-- | Moderate grain
moderate :: FilterGrain
moderate = FilterGrain 0.5

-- | Heavy grain
heavy :: FilterGrain
heavy = FilterGrain 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterGrain -> Number
unwrap (FilterGrain g) = g

-- | Convert to Number (passthrough for this type)
toNumber :: FilterGrain -> Number
toNumber (FilterGrain g) = g

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "filterGrain" "Film grain/noise texture amount"
