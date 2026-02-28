-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // temporal // bezier-param
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | BezierParam — Control point coordinates for cubic bezier easing curves.
-- |
-- | ## CSS Cubic Bezier
-- |
-- | CSS timing functions use cubic bezier curves defined by two control points:
-- |   cubic-bezier(x1, y1, x2, y2)
-- |
-- | The curve goes from (0,0) to (1,1), with control points P1=(x1,y1) and P2=(x2,y2).
-- |
-- | ## Constraints
-- |
-- | - X coordinates (CubicX1, CubicX2) must be in [0, 1] for valid timing
-- | - Y coordinates (CubicY1, CubicY2) can be outside [0,1] for overshoot effects
-- |
-- | ## Examples
-- |
-- | - **ease**: (0.25, 0.1, 0.25, 1.0) — gentle acceleration and deceleration
-- | - **ease-in**: (0.42, 0, 1, 1) — slow start, fast end
-- | - **ease-out**: (0, 0, 0.58, 1) — fast start, slow end
-- | - **ease-in-out**: (0.42, 0, 0.58, 1) — slow start and end

module Hydrogen.Schema.Temporal.BezierParam
  ( -- * X Coordinates (bounded 0-1)
    CubicX1
  , cubicX1
  , unsafeCubicX1
  , unwrapCubicX1
  
  , CubicX2
  , cubicX2
  , unsafeCubicX2
  , unwrapCubicX2
  
  -- * Y Coordinates (unbounded for overshoot)
  , CubicY1
  , cubicY1
  , unsafeCubicY1
  , unwrapCubicY1
  
  , CubicY2
  , cubicY2
  , unsafeCubicY2
  , unwrapCubicY2
  
  -- * Bounds
  , cubicX1Bounds
  , cubicX2Bounds
  , cubicY1Bounds
  , cubicY2Bounds
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , negate
  , (<>)
  , (<)
  , (>)
  )

import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // cubic x1
-- ═════════════════════════════════════════════════════════════════════════════

-- | First control point X coordinate [0, 1]
-- |
-- | Bounded to ensure valid timing function (time cannot go backwards).
newtype CubicX1 = CubicX1 Number

derive instance eqCubicX1 :: Eq CubicX1
derive instance ordCubicX1 :: Ord CubicX1

instance showCubicX1 :: Show CubicX1 where
  show (CubicX1 x) = "(CubicX1 " <> show x <> ")"

-- | Create CubicX1, clamping to [0, 1]
cubicX1 :: Number -> CubicX1
cubicX1 x
  | x < 0.0 = CubicX1 0.0
  | x > 1.0 = CubicX1 1.0
  | otherwise = CubicX1 x

-- | Create CubicX1 without bounds checking
unsafeCubicX1 :: Number -> CubicX1
unsafeCubicX1 = CubicX1

-- | Extract raw Number from CubicX1
unwrapCubicX1 :: CubicX1 -> Number
unwrapCubicX1 (CubicX1 x) = x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // cubic x2
-- ═════════════════════════════════════════════════════════════════════════════

-- | Second control point X coordinate [0, 1]
-- |
-- | Bounded to ensure valid timing function.
newtype CubicX2 = CubicX2 Number

derive instance eqCubicX2 :: Eq CubicX2
derive instance ordCubicX2 :: Ord CubicX2

instance showCubicX2 :: Show CubicX2 where
  show (CubicX2 x) = "(CubicX2 " <> show x <> ")"

-- | Create CubicX2, clamping to [0, 1]
cubicX2 :: Number -> CubicX2
cubicX2 x
  | x < 0.0 = CubicX2 0.0
  | x > 1.0 = CubicX2 1.0
  | otherwise = CubicX2 x

-- | Create CubicX2 without bounds checking
unsafeCubicX2 :: Number -> CubicX2
unsafeCubicX2 = CubicX2

-- | Extract raw Number from CubicX2
unwrapCubicX2 :: CubicX2 -> Number
unwrapCubicX2 (CubicX2 x) = x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // cubic y1
-- ═════════════════════════════════════════════════════════════════════════════

-- | First control point Y coordinate (unbounded)
-- |
-- | Can be outside [0, 1] to create overshoot/anticipation effects:
-- | - y1 < 0: Animation anticipates before moving forward
-- | - y1 > 1: Animation overshoots early
newtype CubicY1 = CubicY1 Number

derive instance eqCubicY1 :: Eq CubicY1
derive instance ordCubicY1 :: Ord CubicY1

instance showCubicY1 :: Show CubicY1 where
  show (CubicY1 y) = "(CubicY1 " <> show y <> ")"

-- | Create CubicY1 (unbounded, any finite value)
cubicY1 :: Number -> CubicY1
cubicY1 = CubicY1

-- | Alias for cubicY1
unsafeCubicY1 :: Number -> CubicY1
unsafeCubicY1 = CubicY1

-- | Extract raw Number from CubicY1
unwrapCubicY1 :: CubicY1 -> Number
unwrapCubicY1 (CubicY1 y) = y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // cubic y2
-- ═════════════════════════════════════════════════════════════════════════════

-- | Second control point Y coordinate (unbounded)
-- |
-- | Can be outside [0, 1] to create overshoot/bounce effects:
-- | - y2 > 1: Animation overshoots target before settling
-- | - y2 < 0: Animation bounces back
newtype CubicY2 = CubicY2 Number

derive instance eqCubicY2 :: Eq CubicY2
derive instance ordCubicY2 :: Ord CubicY2

instance showCubicY2 :: Show CubicY2 where
  show (CubicY2 y) = "(CubicY2 " <> show y <> ")"

-- | Create CubicY2 (unbounded, any finite value)
cubicY2 :: Number -> CubicY2
cubicY2 = CubicY2

-- | Alias for cubicY2
unsafeCubicY2 :: Number -> CubicY2
unsafeCubicY2 = CubicY2

-- | Extract raw Number from CubicY2
unwrapCubicY2 :: CubicY2 -> Number
unwrapCubicY2 (CubicY2 y) = y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounds for CubicX1
cubicX1Bounds :: Bounded.NumberBounds
cubicX1Bounds = Bounded.numberBounds 0.0 1.0 "cubicX1"
  "First bezier control point X coordinate (0-1 for valid timing)"

-- | Bounds for CubicX2
cubicX2Bounds :: Bounded.NumberBounds
cubicX2Bounds = Bounded.numberBounds 0.0 1.0 "cubicX2"
  "Second bezier control point X coordinate (0-1 for valid timing)"

-- | Bounds for CubicY1 (practical limits, not strict)
cubicY1Bounds :: Bounded.NumberBounds
cubicY1Bounds = Bounded.numberBounds (-5.0) 5.0 "cubicY1"
  "First bezier control point Y coordinate (unbounded, typical -2 to 2)"

-- | Bounds for CubicY2 (practical limits, not strict)
cubicY2Bounds :: Bounded.NumberBounds
cubicY2Bounds = Bounded.numberBounds (-5.0) 5.0 "cubicY2"
  "Second bezier control point Y coordinate (unbounded, typical -2 to 2)"
