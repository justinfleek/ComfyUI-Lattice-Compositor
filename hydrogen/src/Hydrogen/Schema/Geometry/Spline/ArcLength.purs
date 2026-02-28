-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                      // hydrogen // schema // geometry // spline // arclength
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Arc Length Parameterization: Evaluate splines by arc length.
-- |
-- | Unlike parameter t which may produce uneven spacing, arc length
-- | parameterization gives uniform spacing along the curve.
-- | More expensive but essential for smooth animation and even sampling.

module Hydrogen.Schema.Geometry.Spline.ArcLength
  ( -- * Arc Length Evaluation
    catmullRomPointAtLength
  , bSplinePointAtLength
  ) where

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , show
  )

import Data.Array (index, foldl)
import Data.Int (floor) as Int
import Data.Maybe (Maybe(Just, Nothing))
import Data.Number (sqrt)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D))
import Hydrogen.Schema.Geometry.Bezier (CubicBezier, cubicLength, cubicPointAt)
import Hydrogen.Schema.Geometry.Spline.Types (CatmullRomSpline, BSpline)
import Hydrogen.Schema.Geometry.Spline.Segments (catmullRomSegmentCount, bSplineSegmentCount)
import Hydrogen.Schema.Geometry.Spline.Evaluation (catmullRomPointAt, bSplinePointAt)
import Hydrogen.Schema.Geometry.Spline.Conversion (catmullRomToBeziers, bSplineToBeziers)
import Hydrogen.Schema.Geometry.Spline.Geometry (catmullRomLength, bSplineLength)
import Hydrogen.Schema.Geometry.Spline.Helpers (clamp01, toNumber, buildIntArray)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // arc length parameterization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate Catmull-Rom spline at a given arc length.
-- |
-- | Unlike pointAt which uses parameter t, this uses actual curve length.
-- | More expensive but gives uniform spacing along the curve.
catmullRomPointAtLength :: Number -> CatmullRomSpline -> Point2D
catmullRomPointAtLength targetLength spline =
  let
    totalLen = catmullRomLength spline
    normalizedLen = clamp01 (targetLength / totalLen)
    
    -- Use bisection search to find t that gives desired arc length
    t = bisectForLength normalizedLen spline 0.0 1.0 20
  in
    catmullRomPointAt t spline

-- | Evaluate B-spline at a given arc length.
bSplinePointAtLength :: Number -> BSpline -> Point2D
bSplinePointAtLength targetLength spline =
  let
    totalLen = bSplineLength spline
    normalizedLen = clamp01 (targetLength / totalLen)
    t = bisectForLengthB normalizedLen spline 0.0 1.0 20
  in
    bSplinePointAt t spline

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // bisection search
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bisection search for arc length parameterization (Catmull-Rom).
bisectForLength :: Number -> CatmullRomSpline -> Number -> Number -> Int -> Number
bisectForLength targetRatio spline lo hi iterations =
  if iterations <= 0 then (lo + hi) / 2.0
  else
    let
      mid = (lo + hi) / 2.0
      -- Sample spline up to mid and estimate length ratio
      midLen = catmullRomLengthUpTo mid spline
      totalLen = catmullRomLength spline
      midRatio = midLen / totalLen
    in
      if midRatio < targetRatio
      then bisectForLength targetRatio spline mid hi (iterations - 1)
      else bisectForLength targetRatio spline lo mid (iterations - 1)

-- | Bisection search for arc length parameterization (B-spline).
bisectForLengthB :: Number -> BSpline -> Number -> Number -> Int -> Number
bisectForLengthB targetRatio spline lo hi iterations =
  if iterations <= 0 then (lo + hi) / 2.0
  else
    let
      mid = (lo + hi) / 2.0
      midLen = bSplineLengthUpTo mid spline
      totalLen = bSplineLength spline
      midRatio = midLen / totalLen
    in
      if midRatio < targetRatio
      then bisectForLengthB targetRatio spline mid hi (iterations - 1)
      else bisectForLengthB targetRatio spline lo mid (iterations - 1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // length up to t
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length up to parameter t.
catmullRomLengthUpTo :: Number -> CatmullRomSpline -> Number
catmullRomLengthUpTo t spline =
  let
    beziers = catmullRomToBeziers spline
    segCount = catmullRomSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    fullSegs = Int.floor tScaled
    localT = tScaled - toNumber fullSegs
    
    -- Sum full segments
    fullLen = sumBezierLengths fullSegs beziers 0 0.0
    
    -- Add partial segment using Bezier pointAt for distance approximation
    partialLen = case index beziers fullSegs of
      Nothing -> 0.0
      Just bez -> 
        -- Approximate partial length by sampling
        let samples = 10
        in foldl (\acc i ->
             let 
               t1 = toNumber i / toNumber samples * localT
               t2 = toNumber (i + 1) / toNumber samples * localT
               (Point2D p1) = cubicPointAt t1 bez
               (Point2D p2) = cubicPointAt t2 bez
               dx = p2.x - p1.x
               dy = p2.y - p1.y
             in acc + sqrt (dx * dx + dy * dy)
           ) 0.0 (buildIntArray samples)
  in
    fullLen + partialLen

-- | Approximate arc length up to parameter t for B-spline.
bSplineLengthUpTo :: Number -> BSpline -> Number
bSplineLengthUpTo t spline =
  let
    beziers = bSplineToBeziers spline
    segCount = bSplineSegmentCount spline
    t' = clamp01 t
    tScaled = t' * toNumber segCount
    fullSegs = Int.floor tScaled
    localT = tScaled - toNumber fullSegs
    
    fullLen = sumBezierLengths fullSegs beziers 0 0.0
    
    partialLen = case index beziers fullSegs of
      Nothing -> 0.0
      Just bez -> 
        let samples = 10
        in foldl (\acc i ->
             let 
               t1 = toNumber i / toNumber samples * localT
               t2 = toNumber (i + 1) / toNumber samples * localT
               (Point2D p1) = cubicPointAt t1 bez
               (Point2D p2) = cubicPointAt t2 bez
               dx = p2.x - p1.x
               dy = p2.y - p1.y
             in acc + sqrt (dx * dx + dy * dy)
           ) 0.0 (buildIntArray samples)
  in
    fullLen + partialLen

-- | Sum lengths of first n beziers.
sumBezierLengths :: Int -> Array CubicBezier -> Int -> Number -> Number
sumBezierLengths n beziers i acc =
  if i >= n then acc
  else case index beziers i of
    Nothing -> acc
    Just bez -> sumBezierLengths n beziers (i + 1) (acc + cubicLength bez)
