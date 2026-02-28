-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // material // dash-length
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DashLength - length of dash segments in dashed borders/strokes.
-- |
-- | Range: 0.0 to infinity (finite)
-- | - **0.0**: No dash (solid line)
-- | - **4.0**: Short dashes
-- | - **8.0**: Medium dashes (common default)
-- | - **16.0+**: Long dashes
-- |
-- | Used in SVG stroke-dasharray and CSS border dash patterns.
-- | Composed with DashGap to create dash patterns.

module Hydrogen.Schema.Material.DashLength
  ( DashLength
  , dashLength
  , unwrap
  , toNumber
  , bounds
  , none
  , short
  , medium
  , long
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
--                                                                // dash-length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dash segment length in pixels (0.0 to infinity)
-- |
-- | Finite values only. Zero means solid line (no dashing).
newtype DashLength = DashLength Number

derive instance eqDashLength :: Eq DashLength
derive instance ordDashLength :: Ord DashLength

instance showDashLength :: Show DashLength where
  show (DashLength l) = "DashLength " <> show l

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a dash length, clamping to minimum of 0.0
-- |
-- | Negative values become 0.0. Infinity and NaN are rejected (finite only).
dashLength :: Number -> DashLength
dashLength n = DashLength (Bounded.clampNumberMin 0.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No dash (solid line)
none :: DashLength
none = DashLength 0.0

-- | Short dashes (4px)
short :: DashLength
short = DashLength 4.0

-- | Medium dashes (8px)
medium :: DashLength
medium = DashLength 8.0

-- | Long dashes (16px)
long :: DashLength
long = DashLength 16.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: DashLength -> Number
unwrap (DashLength l) = l

-- | Convert to Number (passthrough for this type)
toNumber :: DashLength -> Number
toNumber (DashLength l) = l

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 999999.0 "dashLength" "Dash segment length in dashed borders"
