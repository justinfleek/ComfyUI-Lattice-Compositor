-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // schema // material // dash-offset
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | DashOffset - starting offset for dash patterns in borders/strokes.
-- |
-- | Range: -infinity to +infinity (finite)
-- | - **0.0**: Pattern starts at beginning
-- | - **Positive**: Shifts pattern forward along path
-- | - **Negative**: Shifts pattern backward along path
-- |
-- | Used in SVG stroke-dashoffset and CSS border dash offset.
-- | Allows animating "marching ants" effects by incrementing offset over time.

module Hydrogen.Schema.Material.DashOffset
  ( DashOffset
  , dashOffset
  , unwrap
  , toNumber
  , bounds
  , zero
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
--                                                                // dash-offset
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dash pattern offset in pixels (-infinity to +infinity)
-- |
-- | Finite values only. Can be negative to shift pattern backward.
newtype DashOffset = DashOffset Number

derive instance eqDashOffset :: Eq DashOffset
derive instance ordDashOffset :: Ord DashOffset

instance showDashOffset :: Show DashOffset where
  show (DashOffset o) = "DashOffset " <> show o

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a dash offset
-- |
-- | Accepts any finite value (positive or negative). Infinity and NaN are rejected.
dashOffset :: Number -> DashOffset
dashOffset n = DashOffset (Bounded.ensureFinite n 0.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | No offset (pattern starts at beginning)
zero :: DashOffset
zero = DashOffset 0.0

-- | Invert the offset direction
-- |
-- | Useful for reversing animation direction of marching ants effects.
invert :: DashOffset -> DashOffset
invert (DashOffset o) = DashOffset (negate o)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract the raw Number value
unwrap :: DashOffset -> Number
unwrap (DashOffset o) = o

-- | Convert to Number (passthrough for this type)
toNumber :: DashOffset -> Number
toNumber (DashOffset o) = o

-- | Bounds documentation for this type
bounds :: Bounded.NumberBounds
bounds = Bounded.numberBounds (-999999.0) 999999.0 "dashOffset" "Starting offset for dash pattern animation"
