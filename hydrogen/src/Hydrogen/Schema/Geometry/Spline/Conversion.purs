-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // spline // conversion
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Conversion: Convert splines to Bezier curves.
-- |
-- | Enables using existing Bezier infrastructure for rendering,
-- | hit-testing, and arc length calculations.

module Hydrogen.Schema.Geometry.Spline.Conversion
  ( -- * Catmull-Rom to Bezier
    catmullRomToBeziers
  
    -- * B-Spline to Bezier
  , bSplineToBeziers
  ) where

import Prelude
  ( show
  )

import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Bezier (CubicBezier)
import Hydrogen.Schema.Geometry.Spline.Types 
  ( CatmullRomSpline
  , BSpline
  , getCatmullRomTensionValue
  )
import Hydrogen.Schema.Geometry.Spline.Segments
  ( catmullRomSegmentCount
  , catmullRomSegment
  , bSplineSegmentCount
  , bSplineSegment
  )
import Hydrogen.Schema.Geometry.Spline.Helpers
  ( catmullRomToBezier
  , bSplineToBezier
  , buildArray
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // catmull-rom to beziers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Catmull-Rom spline to array of cubic Bezier curves.
-- |
-- | Each segment becomes one Bezier. This allows using existing Bezier
-- | infrastructure for rendering, hit-testing, etc.
catmullRomToBeziers :: CatmullRomSpline -> Array CubicBezier
catmullRomToBeziers spline =
  let
    segCount = catmullRomSegmentCount spline
    tension = getCatmullRomTensionValue spline
  in
    buildArray segCount (\i ->
      case catmullRomSegment i spline of
        Nothing -> Nothing
        Just { p0, p1, p2, p3 } -> Just (catmullRomToBezier p0 p1 p2 p3 tension)
    )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // b-spline to beziers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert B-spline to array of cubic Bezier curves.
bSplineToBeziers :: BSpline -> Array CubicBezier
bSplineToBeziers spline =
  let segCount = bSplineSegmentCount spline
  in buildArray segCount (\i ->
       case bSplineSegment i spline of
         Nothing -> Nothing
         Just { p0, p1, p2, p3 } -> Just (bSplineToBezier p0 p1 p2 p3)
     )
