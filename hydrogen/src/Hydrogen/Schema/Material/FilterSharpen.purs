-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // material // filter-sharpen
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterSharpen - sharpening amount.
-- |
-- | Range: 0.0 to 2.0 (clamps)
-- | - **0.0**: No sharpening (original)
-- | - **1.0**: Standard sharpening
-- | - **2.0**: Aggressive sharpening
-- |
-- | Enhances edge definition and perceived detail. Excessive values can create halos.

module Hydrogen.Schema.Material.FilterSharpen
  ( FilterSharpen
  , filterSharpen
  , unwrap
  , toNumber
  , bounds
  , none
  , subtle
  , standard
  , aggressive
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
--                                                             // filter-sharpen
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter sharpen amount (0.0 to 2.0)
-- |
-- | Enhances edges and fine detail. Higher values increase sharpening intensity.
newtype FilterSharpen = FilterSharpen Number

derive instance eqFilterSharpen :: Eq FilterSharpen
derive instance ordFilterSharpen :: Ord FilterSharpen

instance showFilterSharpen :: Show FilterSharpen where
  show (FilterSharpen s) = "FilterSharpen " <> show s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter sharpen, clamping to 0.0-2.0
filterSharpen :: Number -> FilterSharpen
filterSharpen n = FilterSharpen (Bounded.clampNumber 0.0 2.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No sharpening
none :: FilterSharpen
none = FilterSharpen 0.0

-- | Subtle sharpening
subtle :: FilterSharpen
subtle = FilterSharpen 0.5

-- | Standard sharpening
standard :: FilterSharpen
standard = FilterSharpen 1.0

-- | Aggressive sharpening
aggressive :: FilterSharpen
aggressive = FilterSharpen 2.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterSharpen -> Number
unwrap (FilterSharpen s) = s

-- | Convert to Number (passthrough for this type)
toNumber :: FilterSharpen -> Number
toNumber (FilterSharpen s) = s

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 2.0 "filterSharpen" "Sharpening intensity"
