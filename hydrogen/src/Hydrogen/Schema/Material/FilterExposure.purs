-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // material // filter-exposure
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterExposure - exposure adjustment in stops.
-- |
-- | Range: -3.0 to +3.0 (clamps)
-- | - **-3.0**: Very underexposed (dark)
-- | - **0.0**: No adjustment
-- | - **+3.0**: Very overexposed (bright)
-- |
-- | Simulates camera exposure adjustment. Each stop doubles or halves brightness.

module Hydrogen.Schema.Material.FilterExposure
  ( FilterExposure
  , filterExposure
  , unwrap
  , toNumber
  , bounds
  , normal
  , underexposed
  , overexposed
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
--                                                            // filter-exposure
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter exposure in stops (-3.0 to +3.0)
-- |
-- | Simulates camera exposure compensation. Each stop is a doubling/halving.
newtype FilterExposure = FilterExposure Number

derive instance eqFilterExposure :: Eq FilterExposure
derive instance ordFilterExposure :: Ord FilterExposure

instance showFilterExposure :: Show FilterExposure where
  show (FilterExposure e) = show e <> " EV"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter exposure, clamping to -3.0 to +3.0
filterExposure :: Number -> FilterExposure
filterExposure n = FilterExposure (Bounded.clampNumber (-3.0) 3.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No exposure adjustment
normal :: FilterExposure
normal = FilterExposure 0.0

-- | One stop underexposed
underexposed :: FilterExposure
underexposed = FilterExposure (-1.0)

-- | One stop overexposed
overexposed :: FilterExposure
overexposed = FilterExposure 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterExposure -> Number
unwrap (FilterExposure e) = e

-- | Convert to Number (passthrough for this type)
toNumber :: FilterExposure -> Number
toNumber (FilterExposure e) = e

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-3.0) 3.0 "filterExposure" "Exposure compensation in stops"
