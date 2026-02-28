-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // material // dashgap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DashGap - spacing between dash segments in dashed borders/strokes.
-- |
-- | Range: 0.0 to infinity (finite)
-- | - **0.0**: No gap (solid line)
-- | - **4.0**: Tight spacing
-- | - **8.0**: Medium spacing (common default)
-- | - **16.0+**: Wide spacing
-- |
-- | Used in SVG stroke-dasharray and CSS border dash patterns.
-- | Composed with DashLength to create dash patterns.

module Hydrogen.Schema.Material.DashGap
  ( DashGap
  , dashGap
  , unwrap
  , toNumber
  , bounds
  , none
  , tight
  , medium
  , wide
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
--                                                                    // dashgap
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dash gap length in pixels (0.0 to infinity)
-- |
-- | Finite values only. Zero means solid line (no gaps).
newtype DashGap = DashGap Number

derive instance eqDashGap :: Eq DashGap
derive instance ordDashGap :: Ord DashGap

instance showDashGap :: Show DashGap where
  show (DashGap g) = "DashGap " <> show g

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a dash gap, clamping to minimum of 0.0
-- |
-- | Negative values become 0.0. Infinity and NaN are rejected (finite only).
dashGap :: Number -> DashGap
dashGap n = DashGap (Bounded.clampNumberMin 0.0 n)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No gap (solid line)
none :: DashGap
none = DashGap 0.0

-- | Tight spacing (4px)
tight :: DashGap
tight = DashGap 4.0

-- | Medium spacing (8px)
medium :: DashGap
medium = DashGap 8.0

-- | Wide spacing (16px)
wide :: DashGap
wide = DashGap 16.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: DashGap -> Number
unwrap (DashGap g) = g

-- | Convert to Number (passthrough for this type)
toNumber :: DashGap -> Number
toNumber (DashGap g) = g

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds 0.0 999999.0 "dashGap" "Gap spacing between dashes in dashed borders"
