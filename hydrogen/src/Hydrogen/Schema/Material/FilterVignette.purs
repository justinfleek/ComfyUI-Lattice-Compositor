-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // material // filter-vignette
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterVignette - vignette darkening amount.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No vignette (uniform brightness)
-- | - **0.3**: Subtle edge darkening
-- | - **0.7**: Strong vignette
-- | - **1.0**: Heavy darkening at edges
-- |
-- | Darkens the corners and edges of an image, drawing focus to the center.
-- | Common in photography and Instagram-style filters.

module Hydrogen.Schema.Material.FilterVignette
  ( FilterVignette
  , filterVignette
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
--                                                            // filter-vignette
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter vignette amount (0.0 to 1.0)
-- |
-- | Controls darkening at image edges. 0 is no effect, 1 is maximum darkening.
newtype FilterVignette = FilterVignette Number

derive instance eqFilterVignette :: Eq FilterVignette
derive instance ordFilterVignette :: Ord FilterVignette

instance showFilterVignette :: Show FilterVignette where
  show (FilterVignette v) = "FilterVignette " <> show v

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter vignette, clamping to 0.0-1.0
filterVignette :: Number -> FilterVignette
filterVignette n = FilterVignette (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No vignette
none :: FilterVignette
none = FilterVignette 0.0

-- | Subtle edge darkening
subtle :: FilterVignette
subtle = FilterVignette 0.3

-- | Moderate vignette
moderate :: FilterVignette
moderate = FilterVignette 0.6

-- | Heavy vignette
heavy :: FilterVignette
heavy = FilterVignette 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterVignette -> Number
unwrap (FilterVignette v) = v

-- | Convert to Number (passthrough for this type)
toNumber :: FilterVignette -> Number
toNumber (FilterVignette v) = v

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "filterVignette" "Vignette edge darkening amount"
