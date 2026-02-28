-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // material // filter-highlights
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterHighlights - highlight brightness adjustment.
-- |
-- | Range: -1.0 to +1.0 (clamps)
-- | - **-1.0**: Lower highlights (recover blown areas)
-- | - **0.0**: No adjustment
-- | - **+1.0**: Boost highlights (increase brightness)
-- |
-- | Adjusts brightness of bright tones without affecting shadows.

module Hydrogen.Schema.Material.FilterHighlights
  ( FilterHighlights
  , filterHighlights
  , unwrap
  , toNumber
  , bounds
  , normal
  , recovered
  , boosted
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
--                                                          // filter-highlights
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter highlights adjustment (-1.0 to +1.0)
-- |
-- | Controls brightness of bright tones independently of shadows.
newtype FilterHighlights = FilterHighlights Number

derive instance eqFilterHighlights :: Eq FilterHighlights
derive instance ordFilterHighlights :: Ord FilterHighlights

instance showFilterHighlights :: Show FilterHighlights where
  show (FilterHighlights h) = "FilterHighlights " <> show h

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter highlights, clamping to -1.0 to +1.0
filterHighlights :: Number -> FilterHighlights
filterHighlights n = FilterHighlights (Bounded.clampNumber (-1.0) 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No highlight adjustment
normal :: FilterHighlights
normal = FilterHighlights 0.0

-- | Recovered highlights (darker, recover detail)
recovered :: FilterHighlights
recovered = FilterHighlights (-0.5)

-- | Boosted highlights (brighter)
boosted :: FilterHighlights
boosted = FilterHighlights 0.5

-- | Invert the highlights adjustment
-- |
-- | Converts boost to recovery and vice versa.
invert :: FilterHighlights -> FilterHighlights
invert (FilterHighlights h) = FilterHighlights (negate h)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterHighlights -> Number
unwrap (FilterHighlights h) = h

-- | Convert to Number (passthrough for this type)
toNumber :: FilterHighlights -> Number
toNumber (FilterHighlights h) = h

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-1.0) 1.0 "filterHighlights" "Highlight tone brightness adjustment"
