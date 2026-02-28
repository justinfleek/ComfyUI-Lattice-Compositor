-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // spline // geometry
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Geometry: Length and bounding box calculations.
-- |
-- | Uses Bezier conversion for accurate measurements.

module Hydrogen.Schema.Geometry.Spline.Geometry
  ( -- * Arc Length
    catmullRomLength
  , bSplineLength
  
    -- * Bounding Box
  , catmullRomBoundingBox
  , bSplineBoundingBox
  ) where

import Prelude
  ( (+)
  , map
  , show
  )

import Data.Array (foldl)

import Hydrogen.Schema.Geometry.Bezier (cubicLength, cubicBoundingBox)
import Hydrogen.Schema.Geometry.Spline.Types (CatmullRomSpline, BSpline)
import Hydrogen.Schema.Geometry.Spline.Conversion (catmullRomToBeziers, bSplineToBeziers)
import Hydrogen.Schema.Geometry.Spline.Helpers (initialBounds, mergeBounds)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // arc length
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length of Catmull-Rom spline.
-- |
-- | Converts to Beziers and sums their lengths.
catmullRomLength :: CatmullRomSpline -> Number
catmullRomLength spline =
  let beziers = catmullRomToBeziers spline
  in foldl (\acc b -> acc + cubicLength b) 0.0 beziers

-- | Approximate arc length of B-spline.
bSplineLength :: BSpline -> Number
bSplineLength spline =
  let beziers = bSplineToBeziers spline
  in foldl (\acc b -> acc + cubicLength b) 0.0 beziers

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bounding box
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding box of Catmull-Rom spline.
catmullRomBoundingBox :: CatmullRomSpline -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
catmullRomBoundingBox spline =
  let beziers = catmullRomToBeziers spline
  in foldl mergeBounds initialBounds (map cubicBoundingBox beziers)

-- | Bounding box of B-spline.
bSplineBoundingBox :: BSpline -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
bSplineBoundingBox spline =
  let beziers = bSplineToBeziers spline
  in foldl mergeBounds initialBounds (map cubicBoundingBox beziers)
