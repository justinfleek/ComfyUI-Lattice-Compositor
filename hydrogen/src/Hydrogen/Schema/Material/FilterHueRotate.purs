-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // material // filter-hue-rotate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterHueRotate - hue rotation filter in degrees.
-- |
-- | Range: -∞ to +∞ (finite, no bounds)
-- | - **0**: No rotation (original colors)
-- | - **90**: Rotate hue by 90 degrees
-- | - **180**: Rotate hue by 180 degrees (complementary colors)
-- | - **-90**: Rotate hue by -90 degrees (counter-clockwise)
-- |
-- | Rotates colors around the color wheel. Values can exceed 360 degrees.

module Hydrogen.Schema.Material.FilterHueRotate
  ( FilterHueRotate
  , filterHueRotate
  , unwrap
  , toNumber
  , bounds
  , none
  , quarter
  , half
  , threeQuarters
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Number (isFinite)
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // filter-hue-rotate
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter hue rotation in degrees (finite, unbounded)
-- |
-- | Rotates all hues by the specified angle around the color wheel.
newtype FilterHueRotate = FilterHueRotate Number

derive instance eqFilterHueRotate :: Eq FilterHueRotate
derive instance ordFilterHueRotate :: Ord FilterHueRotate

instance showFilterHueRotate :: Show FilterHueRotate where
  show (FilterHueRotate deg) = show deg <> "°"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter hue rotate, ensuring finite
filterHueRotate :: Number -> FilterHueRotate
filterHueRotate n = 
  if isFinite n
    then FilterHueRotate n
    else FilterHueRotate 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No rotation
none :: FilterHueRotate
none = FilterHueRotate 0.0

-- | Quarter turn (90 degrees)
quarter :: FilterHueRotate
quarter = FilterHueRotate 90.0

-- | Half turn (180 degrees)
half :: FilterHueRotate
half = FilterHueRotate 180.0

-- | Three-quarter turn (270 degrees)
threeQuarters :: FilterHueRotate
threeQuarters = FilterHueRotate 270.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterHueRotate -> Number
unwrap (FilterHueRotate deg) = deg

-- | Convert to Number (passthrough for this type)
toNumber :: FilterHueRotate -> Number
toNumber (FilterHueRotate deg) = deg

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 360.0 "filterHueRotate" "Hue rotation in degrees (can exceed 360)"
