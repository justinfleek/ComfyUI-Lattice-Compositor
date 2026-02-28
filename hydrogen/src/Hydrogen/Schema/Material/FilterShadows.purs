-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // material // filter-shadows
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterShadows - shadow brightness adjustment.
-- |
-- | Range: -1.0 to +1.0 (clamps)
-- | - **-1.0**: Crush shadows (deepen blacks)
-- | - **0.0**: No adjustment
-- | - **+1.0**: Lift shadows (reveal detail)
-- |
-- | Adjusts brightness of dark tones without affecting highlights.

module Hydrogen.Schema.Material.FilterShadows
  ( FilterShadows
  , filterShadows
  , unwrap
  , toNumber
  , bounds
  , normal
  , crushed
  , lifted
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
--                                                             // filter-shadows
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter shadows adjustment (-1.0 to +1.0)
-- |
-- | Controls brightness of dark tones independently of highlights.
newtype FilterShadows = FilterShadows Number

derive instance eqFilterShadows :: Eq FilterShadows
derive instance ordFilterShadows :: Ord FilterShadows

instance showFilterShadows :: Show FilterShadows where
  show (FilterShadows s) = "FilterShadows " <> show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter shadows, clamping to -1.0 to +1.0
filterShadows :: Number -> FilterShadows
filterShadows n = FilterShadows (Bounded.clampNumber (-1.0) 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No shadow adjustment
normal :: FilterShadows
normal = FilterShadows 0.0

-- | Crushed shadows (darker)
crushed :: FilterShadows
crushed = FilterShadows (-0.5)

-- | Lifted shadows (brighter)
lifted :: FilterShadows
lifted = FilterShadows 0.5

-- | Invert the shadow adjustment
-- |
-- | Converts lift to crush and vice versa.
invert :: FilterShadows -> FilterShadows
invert (FilterShadows s) = FilterShadows (negate s)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterShadows -> Number
unwrap (FilterShadows s) = s

-- | Convert to Number (passthrough for this type)
toNumber :: FilterShadows -> Number
toNumber (FilterShadows s) = s

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-1.0) 1.0 "filterShadows" "Shadow tone brightness adjustment"
