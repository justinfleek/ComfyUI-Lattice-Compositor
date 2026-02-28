-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                     // hydrogen // schema // geometry // spline // evaluation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Evaluation: Point and tangent evaluation at parameter t.
-- |
-- | Evaluates splines at parameter t ∈ [0, 1] where:
-- | - t=0 corresponds to start of first segment
-- | - t=1 corresponds to end of last segment

module Hydrogen.Schema.Geometry.Spline.Evaluation
  ( -- * Catmull-Rom Evaluation
    catmullRomPointAt
  , catmullRomTangentAt
  
    -- * B-Spline Evaluation
  , bSplinePointAt
  , bSplineTangentAt
  ) where

import Prelude
  ( (-)
  , (*)
  , (>=)
  , show
  )

import Data.Int (floor) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2)
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
  ( catmullRomEvaluate
  , catmullRomTangentEvaluate
  , bSplineEvaluate
  , bSplineTangentEvaluate
  , clamp01
  , toNumber
  , origin
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // catmull-rom evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate Catmull-Rom spline at parameter t ∈ [0, 1].
-- |
-- | t=0 corresponds to start of first segment (after first point for open spline).
-- | t=1 corresponds to end of last segment.
catmullRomPointAt :: Number -> CatmullRomSpline -> Point2D
catmullRomPointAt t spline =
  let
    segCount = catmullRomSegmentCount spline
    t' = clamp01 t
    
    -- Map t to segment index and local parameter
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    
    -- Handle edge case at t=1
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case catmullRomSegment actualSegIndex spline of
      Nothing -> origin  -- Fallback (shouldn't happen with valid spline)
      Just { p0, p1, p2, p3 } -> 
        catmullRomEvaluate actualLocalT p0 p1 p2 p3 (getCatmullRomTensionValue spline)

-- | Tangent vector at parameter t for Catmull-Rom spline.
catmullRomTangentAt :: Number -> CatmullRomSpline -> Vector2D
catmullRomTangentAt t spline =
  let
    segCount = catmullRomSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case catmullRomSegment actualSegIndex spline of
      Nothing -> vec2 1.0 0.0
      Just { p0, p1, p2, p3 } ->
        catmullRomTangentEvaluate actualLocalT p0 p1 p2 p3 (getCatmullRomTensionValue spline)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // b-spline evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate B-spline at parameter t ∈ [0, 1].
bSplinePointAt :: Number -> BSpline -> Point2D
bSplinePointAt t spline =
  let
    segCount = bSplineSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case bSplineSegment actualSegIndex spline of
      Nothing -> origin
      Just { p0, p1, p2, p3 } -> bSplineEvaluate actualLocalT p0 p1 p2 p3

-- | Tangent vector at parameter t for B-spline.
bSplineTangentAt :: Number -> BSpline -> Vector2D
bSplineTangentAt t spline =
  let
    segCount = bSplineSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    segIndex = Int.floor tScaled
    localT = tScaled - toNumber segIndex
    actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
    actualLocalT = if segIndex >= segCount then 1.0 else localT
  in
    case bSplineSegment actualSegIndex spline of
      Nothing -> vec2 1.0 0.0
      Just { p0, p1, p2, p3 } -> bSplineTangentEvaluate actualLocalT p0 p1 p2 p3
