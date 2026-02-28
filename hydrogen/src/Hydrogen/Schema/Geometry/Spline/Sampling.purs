-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // schema // geometry // spline // sampling
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Sampling: Sample points and tangents along splines.
-- |
-- | Generates evenly-spaced samples for rendering, animation, etc.

module Hydrogen.Schema.Geometry.Spline.Sampling
  ( -- * Point Sampling
    sampleCatmullRom
  , sampleBSpline
  
    -- * Tangent Sampling
  , sampleCatmullRomTangents
  , sampleBSplineTangents
  ) where

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<=)
  , (>=)
  , show
  )

import Data.Array (index)
import Data.Int (floor) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Point (Point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2)
import Hydrogen.Schema.Geometry.Bezier (cubicTangentAt)
import Hydrogen.Schema.Geometry.Spline.Types (CatmullRomSpline, BSpline)
import Hydrogen.Schema.Geometry.Spline.Segments (catmullRomSegmentCount, bSplineSegmentCount)
import Hydrogen.Schema.Geometry.Spline.Evaluation (catmullRomPointAt, bSplinePointAt)
import Hydrogen.Schema.Geometry.Spline.Conversion (catmullRomToBeziers, bSplineToBeziers)
import Hydrogen.Schema.Geometry.Spline.Helpers (buildArray, toNumber)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // point sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample Catmull-Rom spline at n evenly-spaced parameter values.
-- |
-- | Returns array of n+1 points from t=0 to t=1.
sampleCatmullRom :: Int -> CatmullRomSpline -> Array Point2D
sampleCatmullRom n spline =
  if n <= 0 then []
  else buildArray (n + 1) (\i ->
    let t = toNumber i / toNumber n
    in Just (catmullRomPointAt t spline)
  )

-- | Sample B-spline at n evenly-spaced parameter values.
sampleBSpline :: Int -> BSpline -> Array Point2D
sampleBSpline n spline =
  if n <= 0 then []
  else buildArray (n + 1) (\i ->
    let t = toNumber i / toNumber n
    in Just (bSplinePointAt t spline)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // tangent sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample tangent vectors along Catmull-Rom spline.
-- |
-- | Returns array of n+1 tangent vectors from t=0 to t=1.
-- | Uses Bezier conversion for accurate tangent computation.
sampleCatmullRomTangents :: Int -> CatmullRomSpline -> Array Vector2D
sampleCatmullRomTangents n spline =
  if n <= 0 then []
  else 
    let 
      beziers = catmullRomToBeziers spline
      segCount = catmullRomSegmentCount spline
    in buildArray (n + 1) (\i ->
      let 
        t = toNumber i / toNumber n
        tScaled = t * toNumber segCount
        segIndex = Int.floor tScaled
        localT = tScaled - toNumber segIndex
        actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
        actualLocalT = if segIndex >= segCount then 1.0 else localT
      in case index beziers actualSegIndex of
        Nothing -> Just (vec2 1.0 0.0)
        Just bez -> Just (cubicTangentAt actualLocalT bez)
    )

-- | Sample tangent vectors along B-spline.
sampleBSplineTangents :: Int -> BSpline -> Array Vector2D
sampleBSplineTangents n spline =
  if n <= 0 then []
  else 
    let 
      beziers = bSplineToBeziers spline
      segCount = bSplineSegmentCount spline
    in buildArray (n + 1) (\i ->
      let 
        t = toNumber i / toNumber n
        tScaled = t * toNumber segCount
        segIndex = Int.floor tScaled
        localT = tScaled - toNumber segIndex
        actualSegIndex = if segIndex >= segCount then segCount - 1 else segIndex
        actualLocalT = if segIndex >= segCount then 1.0 else localT
      in case index beziers actualSegIndex of
        Nothing -> Just (vec2 1.0 0.0)
        Just bez -> Just (cubicTangentAt actualLocalT bez)
    )
