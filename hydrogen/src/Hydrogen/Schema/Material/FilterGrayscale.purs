-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // material // filter-grayscale
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FilterGrayscale - grayscale filter amount.
-- |
-- | Range: 0.0 to 1.0 (clamps)
-- | - **0.0**: No effect (original colors)
-- | - **0.5**: Partial desaturation
-- | - **1.0**: Full grayscale (black and white)
-- |
-- | Converts colors to grayscale based on luminance.

module Hydrogen.Schema.Material.FilterGrayscale
  ( FilterGrayscale
  , filterGrayscale
  , unwrap
  , toNumber
  , bounds
  , none
  , partial
  , moderate
  , full
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
--                                                          // filter-gray-scale
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter grayscale amount (0.0 to 1.0)
-- |
-- | Converts image to grayscale based on perceived luminance.
newtype FilterGrayscale = FilterGrayscale Number

derive instance eqFilterGrayscale :: Eq FilterGrayscale
derive instance ordFilterGrayscale :: Ord FilterGrayscale

instance showFilterGrayscale :: Show FilterGrayscale where
  show (FilterGrayscale g) = "FilterGrayscale " <> show g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a filter grayscale, clamping to 0.0-1.0
filterGrayscale :: Number -> FilterGrayscale
filterGrayscale n = FilterGrayscale (Bounded.clampNumber 0.0 1.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No grayscale effect
none :: FilterGrayscale
none = FilterGrayscale 0.0

-- | Partial desaturation (25%)
partial :: FilterGrayscale
partial = FilterGrayscale 0.25

-- | Moderate desaturation (50%)
moderate :: FilterGrayscale
moderate = FilterGrayscale 0.5

-- | Full grayscale
full :: FilterGrayscale
full = FilterGrayscale 1.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: FilterGrayscale -> Number
unwrap (FilterGrayscale g) = g

-- | Convert to Number (passthrough for this type)
toNumber :: FilterGrayscale -> Number
toNumber (FilterGrayscale g) = g

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 1.0 "filterGrayscale" "Grayscale filter amount"
