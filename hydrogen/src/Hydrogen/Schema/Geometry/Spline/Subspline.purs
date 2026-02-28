-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // spline // sub-spline
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Subspline Extraction: Extract portions of splines.
-- |
-- | Useful for progressive reveal, splitting, and partial rendering.

module Hydrogen.Schema.Geometry.Spline.Subspline
  ( -- * Catmull-Rom Subsplines
    catmullRomSubspline
  , catmullRomHead
  , catmullRomTail
  
    -- * B-Spline Subsplines
  , bSplineSubspline
  , bSplineHead
  , bSplineTail
  ) where

import Prelude
  ( (+)
  , (-)
  , (/)
  , (<)
  , show
  )

import Data.Array (length, take, drop)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Spline.Types 
  ( CatmullRomSpline(CatmullRomSpline)
  , BSpline(BSpline)
  , getCatmullRomPoints
  , getCatmullRomTensionValue
  , getBSplinePoints
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // catmull-rom subsplines
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract a subspline from a Catmull-Rom spline.
-- |
-- | Takes first n points (minimum 4 required for valid spline).
catmullRomSubspline :: Int -> CatmullRomSpline -> Maybe CatmullRomSpline
catmullRomSubspline n (CatmullRomSpline s) =
  let pts = take n s.points
  in if length pts < 4 then Nothing
     else Just (CatmullRomSpline { points: pts, closed: false, tension: s.tension })

-- | Get head portion of Catmull-Rom spline (first half of points).
catmullRomHead :: CatmullRomSpline -> Maybe CatmullRomSpline
catmullRomHead spline =
  let n = length (getCatmullRomPoints spline)
      halfN = n / 2
  in if halfN < 4 then Nothing
     else catmullRomSubspline (halfN + 2) spline  -- +2 for overlap

-- | Get tail portion of Catmull-Rom spline (second half of points).
catmullRomTail :: CatmullRomSpline -> Maybe CatmullRomSpline
catmullRomTail (CatmullRomSpline s) =
  let n = length s.points
      halfN = n / 2
      pts = drop (halfN - 2) s.points  -- -2 for overlap
  in if length pts < 4 then Nothing
     else Just (CatmullRomSpline { points: pts, closed: false, tension: s.tension })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // b-spline subsplines
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract a subspline from a B-spline.
bSplineSubspline :: Int -> BSpline -> Maybe BSpline
bSplineSubspline n (BSpline s) =
  let pts = take n s.points
  in if length pts < 4 then Nothing
     else Just (BSpline { points: pts, closed: false })

-- | Get head portion of B-spline.
bSplineHead :: BSpline -> Maybe BSpline
bSplineHead spline =
  let n = length (getBSplinePoints spline)
      halfN = n / 2
  in if halfN < 4 then Nothing
     else bSplineSubspline (halfN + 2) spline

-- | Get tail portion of B-spline.
bSplineTail :: BSpline -> Maybe BSpline
bSplineTail (BSpline s) =
  let n = length s.points
      halfN = n / 2
      pts = drop (halfN - 2) s.points
  in if length pts < 4 then Nothing
     else Just (BSpline { points: pts, closed: false })
