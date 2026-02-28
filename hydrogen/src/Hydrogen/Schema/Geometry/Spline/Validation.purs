-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // spline // validation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Validation: Check spline validity.
-- |
-- | Valid splines have:
-- | - At least 4 control points
-- | - All finite coordinates (no NaN or Infinity)
-- | - Tension in [0, 1] (for Catmull-Rom)

module Hydrogen.Schema.Geometry.Spline.Validation
  ( -- * Validation
    isValidCatmullRom
  , isValidBSpline
  ) where

import Prelude
  ( (-)
  , (*)
  , (==)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (&&)
  , negate
  , show
  )

import Data.Array (length, foldl)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D))
import Hydrogen.Schema.Geometry.Spline.Types 
  ( CatmullRomSpline(CatmullRomSpline)
  , BSpline(BSpline)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if Catmull-Rom spline is valid.
-- |
-- | Valid means: at least 4 points, all points are finite numbers.
isValidCatmullRom :: CatmullRomSpline -> Boolean
isValidCatmullRom (CatmullRomSpline s) =
  length s.points >= 4 && allPointsFinite s.points && s.tension >= 0.0 && s.tension <= 1.0

-- | Check if B-spline is valid.
isValidBSpline :: BSpline -> Boolean
isValidBSpline (BSpline s) =
  length s.points >= 4 && allPointsFinite s.points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check all points have finite coordinates.
allPointsFinite :: Array Point2D -> Boolean
allPointsFinite pts = foldl (\acc p -> acc && isFinitePoint p) true pts

-- | Check if a point has finite coordinates.
isFinitePoint :: Point2D -> Boolean
isFinitePoint (Point2D p) =
  isFiniteNumber p.x && isFiniteNumber p.y

-- | Check if a number is finite (not NaN or Infinity).
isFiniteNumber :: Number -> Boolean
isFiniteNumber n = n == n && n < 1.0e308 && n > negate 1.0e308
