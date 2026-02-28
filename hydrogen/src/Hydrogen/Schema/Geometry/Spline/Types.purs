-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // geometry // spline // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Types: Catmull-Rom and B-Spline data structures.
-- |
-- | ## Design Philosophy
-- |
-- | While Bezier curves define shape through control points (some off-curve),
-- | splines provide different tradeoffs:
-- |
-- | - **Catmull-Rom**: Interpolating spline that passes through ALL control points.
-- |   Perfect for smooth paths through waypoints, camera motion, character animation.
-- |
-- | - **B-Spline**: Approximating spline with local control. Moving one point
-- |   only affects nearby curve segments. Ideal for modeling and design work.

module Hydrogen.Schema.Geometry.Spline.Types
  ( -- * Catmull-Rom Spline
    CatmullRomSpline(CatmullRomSpline)
  , catmullRomSpline
  , catmullRomClosed
  , catmullRomTension
  , getCatmullRomPoints
  , getCatmullRomClosed
  , getCatmullRomTensionValue
  
    -- * B-Spline
  , BSpline(BSpline)
  , bSpline
  , bSplineClosed
  , getBSplinePoints
  , getBSplineClosed
  ) where

import Prelude
  ( class Eq
  , class Show
  , show
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , (<>)
  , otherwise
  )

import Data.Array (length)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Point (Point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // catmull-rom spline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Catmull-Rom spline — interpolating spline through control points.
-- |
-- | The curve passes through every control point (except possibly first/last
-- | for open splines). Tension parameter controls curvature tightness.
-- |
-- | Minimum 4 points required for valid spline.
newtype CatmullRomSpline = CatmullRomSpline
  { points :: Array Point2D
  , closed :: Boolean
  , tension :: Number  -- 0.0 = Catmull-Rom, 0.5 = centripetal, 1.0 = chordal
  }

derive instance eqCatmullRomSpline :: Eq CatmullRomSpline

instance showCatmullRomSpline :: Show CatmullRomSpline where
  show (CatmullRomSpline s) = "(CatmullRomSpline points:" <> show (length s.points)
    <> " closed:" <> show s.closed
    <> " tension:" <> show s.tension <> ")"

-- | Create an open Catmull-Rom spline with standard tension (0.5).
-- |
-- | Returns Nothing if fewer than 4 points provided.
catmullRomSpline :: Array Point2D -> Maybe CatmullRomSpline
catmullRomSpline pts =
  if length pts < 4 then Nothing
  else Just (CatmullRomSpline { points: pts, closed: false, tension: 0.5 })

-- | Create a closed Catmull-Rom spline (loop).
-- |
-- | Returns Nothing if fewer than 4 points provided.
catmullRomClosed :: Array Point2D -> Maybe CatmullRomSpline
catmullRomClosed pts =
  if length pts < 4 then Nothing
  else Just (CatmullRomSpline { points: pts, closed: true, tension: 0.5 })

-- | Create a Catmull-Rom spline with custom tension.
-- |
-- | - tension = 0.0: Uniform (standard Catmull-Rom)
-- | - tension = 0.5: Centripetal (prevents cusps and self-intersection)
-- | - tension = 1.0: Chordal (follows chord lengths)
-- |
-- | Returns Nothing if fewer than 4 points provided.
catmullRomTension :: Number -> Array Point2D -> Maybe CatmullRomSpline
catmullRomTension t pts =
  if length pts < 4 then Nothing
  else Just (CatmullRomSpline { points: pts, closed: false, tension: clamp01 t })

-- | Get control points of Catmull-Rom spline.
getCatmullRomPoints :: CatmullRomSpline -> Array Point2D
getCatmullRomPoints (CatmullRomSpline s) = s.points

-- | Check if Catmull-Rom spline is closed.
getCatmullRomClosed :: CatmullRomSpline -> Boolean
getCatmullRomClosed (CatmullRomSpline s) = s.closed

-- | Get tension parameter of Catmull-Rom spline.
getCatmullRomTensionValue :: CatmullRomSpline -> Number
getCatmullRomTensionValue (CatmullRomSpline s) = s.tension

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // b-spline
-- ═════════════════════════════════════════════════════════════════════════════

-- | Cubic uniform B-Spline — approximating spline with local control.
-- |
-- | The curve does NOT pass through control points (except possibly endpoints).
-- | Moving a control point only affects the nearby curve segments, making
-- | B-splines excellent for interactive design.
-- |
-- | Minimum 4 points required for valid spline.
newtype BSpline = BSpline
  { points :: Array Point2D
  , closed :: Boolean
  }

derive instance eqBSpline :: Eq BSpline

instance showBSpline :: Show BSpline where
  show (BSpline s) = "(BSpline points:" <> show (length s.points)
    <> " closed:" <> show s.closed <> ")"

-- | Create an open cubic B-spline.
-- |
-- | Returns Nothing if fewer than 4 points provided.
bSpline :: Array Point2D -> Maybe BSpline
bSpline pts =
  if length pts < 4 then Nothing
  else Just (BSpline { points: pts, closed: false })

-- | Create a closed cubic B-spline (loop).
-- |
-- | Returns Nothing if fewer than 4 points provided.
bSplineClosed :: Array Point2D -> Maybe BSpline
bSplineClosed pts =
  if length pts < 4 then Nothing
  else Just (BSpline { points: pts, closed: true })

-- | Get control points of B-spline.
getBSplinePoints :: BSpline -> Array Point2D
getBSplinePoints (BSpline s) = s.points

-- | Check if B-spline is closed.
getBSplineClosed :: BSpline -> Boolean
getBSplineClosed (BSpline s) = s.closed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to [0, 1]
-- |
-- | All inputs are assumed finite (no NaN, no Infinity).
-- | The guards cover the complete bounded range.
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n  -- n is in [0, 1]
