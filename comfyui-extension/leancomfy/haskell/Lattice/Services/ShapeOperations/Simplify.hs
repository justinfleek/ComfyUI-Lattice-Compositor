{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.ShapeOperations.Simplify
Description : Path Simplification
Copyright   : (c) Lattice, 2026
License     : MIT

Pure path simplification algorithms:
- Douglas-Peucker line simplification
- Perpendicular distance calculation
- Bezier curve fitting
- Path smoothing

Source: ui/src/services/shapeOperations.ts (simplification functions)
-}

module Lattice.Services.ShapeOperations.Simplify
  ( -- * Perpendicular Distance
    perpendicularDistance
    -- * Douglas-Peucker
  , douglasPeucker, rdpSimplify
    -- * Polygon Simplification
  , simplifyPolygon
    -- * Bezier Fitting
  , fitBezierToPolygon
    -- * Path Operations
  , simplifyPath, smoothPath
    -- * Visvalingam-Whyatt
  , triangleArea, visvalingamWhyatt
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

import Lattice.Services.ShapeOperations.Point2D
import Lattice.Services.ShapeOperations.Generators

--------------------------------------------------------------------------------
-- Perpendicular Distance
--------------------------------------------------------------------------------

-- | Calculate perpendicular distance from a point to a line segment.
perpendicularDistance :: Point2D -> Point2D -> Point2D -> Double
perpendicularDistance point lineStart lineEnd =
  let dx = px lineEnd - px lineStart
      dy = py lineEnd - py lineStart
      lineLengthSq = dx * dx + dy * dy

  in if lineLengthSq == 0
     then distance point lineStart
     else
       let t = ((px point - px lineStart) * dx + (py point - py lineStart) * dy) / lineLengthSq
           tClamped = max 0 (min 1 t)
           projection = Point2D
             (px lineStart + tClamped * dx)
             (py lineStart + tClamped * dy)
       in distance point projection

--------------------------------------------------------------------------------
-- Douglas-Peucker Algorithm
--------------------------------------------------------------------------------

-- | Douglas-Peucker line simplification algorithm.
douglasPeucker :: Vector Point2D -> Double -> Vector Point2D
douglasPeucker points tolerance
  | V.length points <= 2 = points
  | otherwise =
      let first = V.head points
          last = V.last points

          -- Find point with maximum distance
          findMax i maxDist maxIdx
            | i >= V.length points - 1 = (maxDist, maxIdx)
            | otherwise =
                let d = perpendicularDistance (points V.! i) first last
                in if d > maxDist
                   then findMax (i + 1) d i
                   else findMax (i + 1) maxDist maxIdx

          (maxDist, maxIndex) = findMax 1 0 0

      in if maxDist > tolerance
         then
           let leftPoints = V.take (maxIndex + 1) points
               rightPoints = V.drop maxIndex points
               leftSimplified = douglasPeucker leftPoints tolerance
               rightSimplified = douglasPeucker rightPoints tolerance
           in V.init leftSimplified V.++ rightSimplified
         else V.fromList [first, last]

-- | Ramer-Douglas-Peucker algorithm (alias)
rdpSimplify :: Vector Point2D -> Double -> Vector Point2D
rdpSimplify = douglasPeucker

--------------------------------------------------------------------------------
-- Polygon Simplification
--------------------------------------------------------------------------------

-- | Simplify a closed polygon using Douglas-Peucker.
simplifyPolygon :: Vector Point2D -> Double -> Vector Point2D
simplifyPolygon points tolerance
  | V.length points <= 3 = points
  | otherwise = douglasPeucker points tolerance

--------------------------------------------------------------------------------
-- Fit Bezier to Polygon
--------------------------------------------------------------------------------

-- | Fit smooth Bezier curves to a polygon.
fitBezierToPolygon :: Vector Point2D -> Bool -> BezierPath
fitBezierToPolygon points closed
  | V.length points < 2 = BezierPath V.empty closed
  | V.length points == 2 = BezierPath (V.map cornerVertex points) closed
  | otherwise =
      let n = V.length points
          handleScale = 0.25

          mkVertex i =
            let curr = points V.! i
                prev = points V.! ((i + n - 1) `mod` n)
                next = points V.! ((i + 1) `mod` n)

                toPrev = sub prev curr
                toNext = sub next curr

                distPrev = distance curr prev
                distNext = distance curr next

            in if not closed && i == 0
               then BezierVertex curr origin (scale (normalize toNext) (distNext * handleScale))
               else if not closed && i == n - 1
               then BezierVertex curr (scale (normalize toPrev) (distPrev * handleScale)) origin
               else
                 let tangent = normalize (sub toNext toPrev)
                 in BezierVertex curr
                      (scale tangent (-distPrev * handleScale))
                      (scale tangent (distNext * handleScale))

          vertices = V.generate n mkVertex

      in BezierPath vertices closed

--------------------------------------------------------------------------------
-- Path Simplification (High-Level)
--------------------------------------------------------------------------------

-- | Simplify a Bezier path.
simplifyPath :: BezierPath -> Double -> Bool -> BezierPath
simplifyPath path tolerance straightLines
  | V.length (bpVertices path) <= 2 = path
  | otherwise =
      let points = V.map bvPoint (bpVertices path)
          simplified = douglasPeucker points tolerance
      in if straightLines
         then BezierPath (V.map cornerVertex simplified) (bpClosed path)
         else fitBezierToPolygon simplified (bpClosed path)

--------------------------------------------------------------------------------
-- Path Smoothing
--------------------------------------------------------------------------------

-- | Smooth a path by adjusting handle lengths.
smoothPath :: BezierPath -> Double -> BezierPath
smoothPath path amount
  | V.length (bpVertices path) < 2 = path
  | otherwise =
      let factor = amount / 100
          n = V.length (bpVertices path)

          mkVertex i =
            let v = bpVertices path V.! i
                prev = bpVertices path V.! ((i + n - 1) `mod` n)
                next = bpVertices path V.! ((i + 1) `mod` n)

                toPrev = sub (bvPoint prev) (bvPoint v)
                toNext = sub (bvPoint next) (bvPoint v)

                avgDir = normalize (sub toNext toPrev)
                idealHandleLength = (distance (bvPoint v) (bvPoint prev) +
                                     distance (bvPoint v) (bvPoint next)) / 6

                idealIn = scale avgDir (-idealHandleLength)
                idealOut = scale avgDir idealHandleLength

            in BezierVertex (bvPoint v)
                 (lerp (bvInHandle v) idealIn factor)
                 (lerp (bvOutHandle v) idealOut factor)

          vertices = V.generate n mkVertex

      in BezierPath vertices (bpClosed path)

--------------------------------------------------------------------------------
-- Visvalingam-Whyatt Algorithm
--------------------------------------------------------------------------------

-- | Calculate area of triangle formed by three points.
triangleArea :: Point2D -> Point2D -> Point2D -> Double
triangleArea p1 p2 p3 =
  abs (px p1 * (py p2 - py p3) + px p2 * (py p3 - py p1) + px p3 * (py p1 - py p2)) / 2

-- | Visvalingam-Whyatt simplification algorithm.
visvalingamWhyatt :: Vector Point2D -> Double -> Vector Point2D
visvalingamWhyatt points minArea
  | V.length points <= 2 = points
  | otherwise =
      let -- Find point with minimum area
          findMinArea i minA minIdx
            | i >= V.length points - 1 = (minA, minIdx)
            | otherwise =
                let area = triangleArea (points V.! (i - 1)) (points V.! i) (points V.! (i + 1))
                in if area < minA
                   then findMinArea (i + 1) area i
                   else findMinArea (i + 1) minA minIdx

          (minAreaFound, minIdx) = findMinArea 1 (1e10) 1

      in if minAreaFound < minArea
         then let newPoints = V.take minIdx points V.++ V.drop (minIdx + 1) points
              in visvalingamWhyatt newPoints minArea
         else points
