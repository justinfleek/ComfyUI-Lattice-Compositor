-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // geometry // spline // point-access
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Point Access: Get first and last control points.
-- |
-- | Useful for connecting splines, checking endpoints, etc.

module Hydrogen.Schema.Geometry.Spline.PointAccess
  ( -- * Catmull-Rom Point Access
    catmullRomFirstPoint
  , catmullRomLastPoint
  
    -- * B-Spline Point Access
  , bSplineFirstPoint
  , bSplineLastPoint
  ) where

import Prelude
  ( show
  )

import Data.Array (head, last)
import Data.Maybe (Maybe)

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Spline.Types 
  ( CatmullRomSpline(CatmullRomSpline)
  , BSpline(BSpline)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // point access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get first control point of Catmull-Rom spline.
catmullRomFirstPoint :: CatmullRomSpline -> Maybe Point2D
catmullRomFirstPoint (CatmullRomSpline s) = head s.points

-- | Get last control point of Catmull-Rom spline.
catmullRomLastPoint :: CatmullRomSpline -> Maybe Point2D
catmullRomLastPoint (CatmullRomSpline s) = last s.points

-- | Get first control point of B-spline.
bSplineFirstPoint :: BSpline -> Maybe Point2D
bSplineFirstPoint (BSpline s) = head s.points

-- | Get last control point of B-spline.
bSplineLastPoint :: BSpline -> Maybe Point2D
bSplineLastPoint (BSpline s) = last s.points
