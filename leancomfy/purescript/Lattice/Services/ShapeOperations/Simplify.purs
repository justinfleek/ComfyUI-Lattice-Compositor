-- | Lattice.Services.ShapeOperations.Simplify - Path Simplification
-- |
-- | Pure path simplification algorithms:
-- | - Douglas-Peucker line simplification
-- | - Perpendicular distance calculation
-- | - Bezier curve fitting
-- | - Path smoothing
-- |
-- | Source: ui/src/services/shapeOperations.ts (simplification functions)

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

import Prelude
import Data.Array (length, take, drop, head, last, (!!), range, mapWithIndex, filter, cons)
import Data.Maybe (Maybe(..), fromMaybe)
import Math (abs, max, min) as Math

import Lattice.Services.ShapeOperations.Point2D as P2D
import Lattice.Services.ShapeOperations.Generators (BezierVertex, BezierPath, cornerVertex)

--------------------------------------------------------------------------------
-- Perpendicular Distance
--------------------------------------------------------------------------------

-- | Calculate perpendicular distance from a point to a line segment.
perpendicularDistance :: P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> Number
perpendicularDistance point lineStart lineEnd =
  let dx = lineEnd.x - lineStart.x
      dy = lineEnd.y - lineStart.y
      lineLengthSq = dx * dx + dy * dy

  in if lineLengthSq == 0.0
     then P2D.distance point lineStart
     else
       let t = ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) / lineLengthSq
           tClamped = Math.max 0.0 (Math.min 1.0 t)
           projection = { x: lineStart.x + tClamped * dx
                        , y: lineStart.y + tClamped * dy
                        }
       in P2D.distance point projection

--------------------------------------------------------------------------------
-- Douglas-Peucker Algorithm
--------------------------------------------------------------------------------

-- | Douglas-Peucker line simplification algorithm.
douglasPeucker :: Array P2D.Point2D -> Number -> Array P2D.Point2D
douglasPeucker points tolerance
  | length points <= 2 = points
  | otherwise =
      case { first: head points, last: last points } of
        { first: Just first, last: Just lst } ->
          let -- Find point with maximum distance
              findMax i maxDist maxIdx
                | i >= length points - 1 = { maxDist, maxIdx }
                | otherwise =
                    case points !! i of
                      Nothing -> findMax (i + 1) maxDist maxIdx
                      Just pt ->
                        let d = perpendicularDistance pt first lst
                        in if d > maxDist
                           then findMax (i + 1) d i
                           else findMax (i + 1) maxDist maxIdx

              result = findMax 1 0.0 0

          in if result.maxDist > tolerance
             then
               let leftPoints = take (result.maxIdx + 1) points
                   rightPoints = drop result.maxIdx points
                   leftSimplified = douglasPeucker leftPoints tolerance
                   rightSimplified = douglasPeucker rightPoints tolerance
                   leftWithoutLast = take (length leftSimplified - 1) leftSimplified
               in leftWithoutLast <> rightSimplified
             else [first, lst]
        _ -> points

-- | Ramer-Douglas-Peucker algorithm (alias)
rdpSimplify :: Array P2D.Point2D -> Number -> Array P2D.Point2D
rdpSimplify = douglasPeucker

--------------------------------------------------------------------------------
-- Polygon Simplification
--------------------------------------------------------------------------------

-- | Simplify a closed polygon using Douglas-Peucker.
simplifyPolygon :: Array P2D.Point2D -> Number -> Array P2D.Point2D
simplifyPolygon points tolerance
  | length points <= 3 = points
  | otherwise = douglasPeucker points tolerance

--------------------------------------------------------------------------------
-- Fit Bezier to Polygon
--------------------------------------------------------------------------------

-- | Fit smooth Bezier curves to a polygon.
fitBezierToPolygon :: Array P2D.Point2D -> Boolean -> BezierPath
fitBezierToPolygon points closed
  | length points < 2 = { vertices: [], closed }
  | length points == 2 = { vertices: map cornerVertex points, closed }
  | otherwise =
      let n = length points
          handleScale = 0.25

          safeGet i = fromMaybe P2D.origin (points !! i)

          mkVertex i =
            let curr = safeGet i
                prev = safeGet ((i + n - 1) `mod` n)
                next = safeGet ((i + 1) `mod` n)

                toPrev = P2D.sub prev curr
                toNext = P2D.sub next curr

                distPrev = P2D.distance curr prev
                distNext = P2D.distance curr next

            in if not closed && i == 0
               then { point: curr
                    , inHandle: P2D.origin
                    , outHandle: P2D.scale (P2D.normalize toNext) (distNext * handleScale)
                    }
               else if not closed && i == n - 1
               then { point: curr
                    , inHandle: P2D.scale (P2D.normalize toPrev) (distPrev * handleScale)
                    , outHandle: P2D.origin
                    }
               else
                 let tangent = P2D.normalize (P2D.sub toNext toPrev)
                 in { point: curr
                    , inHandle: P2D.scale tangent (-distPrev * handleScale)
                    , outHandle: P2D.scale tangent (distNext * handleScale)
                    }

          vertices = mapWithIndex (\i _ -> mkVertex i) points

      in { vertices, closed }

--------------------------------------------------------------------------------
-- Path Simplification (High-Level)
--------------------------------------------------------------------------------

-- | Simplify a Bezier path.
simplifyPath :: BezierPath -> Number -> Boolean -> BezierPath
simplifyPath path tolerance straightLines
  | length path.vertices <= 2 = path
  | otherwise =
      let points = map (\v -> v.point) path.vertices
          simplified = douglasPeucker points tolerance
      in if straightLines
         then { vertices: map cornerVertex simplified, closed: path.closed }
         else fitBezierToPolygon simplified path.closed

--------------------------------------------------------------------------------
-- Path Smoothing
--------------------------------------------------------------------------------

-- | Smooth a path by adjusting handle lengths.
smoothPath :: BezierPath -> Number -> BezierPath
smoothPath path amount
  | length path.vertices < 2 = path
  | otherwise =
      let factor = amount / 100.0
          n = length path.vertices

          safeGet i = fromMaybe { point: P2D.origin, inHandle: P2D.origin, outHandle: P2D.origin }
                                (path.vertices !! i)

          mkVertex i =
            let v = safeGet i
                prev = safeGet ((i + n - 1) `mod` n)
                next = safeGet ((i + 1) `mod` n)

                toPrev = P2D.sub prev.point v.point
                toNext = P2D.sub next.point v.point

                avgDir = P2D.normalize (P2D.sub toNext toPrev)
                idealHandleLength = (P2D.distance v.point prev.point +
                                     P2D.distance v.point next.point) / 6.0

                idealIn = P2D.scale avgDir (-idealHandleLength)
                idealOut = P2D.scale avgDir idealHandleLength

            in { point: v.point
               , inHandle: P2D.lerp v.inHandle idealIn factor
               , outHandle: P2D.lerp v.outHandle idealOut factor
               }

          vertices = mapWithIndex (\i _ -> mkVertex i) path.vertices

      in { vertices, closed: path.closed }

--------------------------------------------------------------------------------
-- Visvalingam-Whyatt Algorithm
--------------------------------------------------------------------------------

-- | Calculate area of triangle formed by three points.
triangleArea :: P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> Number
triangleArea p1 p2 p3 =
  Math.abs (p1.x * (p2.y - p3.y) + p2.x * (p3.y - p1.y) + p3.x * (p1.y - p2.y)) / 2.0

-- | Visvalingam-Whyatt simplification algorithm.
visvalingamWhyatt :: Array P2D.Point2D -> Number -> Array P2D.Point2D
visvalingamWhyatt points minArea
  | length points <= 2 = points
  | otherwise =
      let safeGet i = fromMaybe P2D.origin (points !! i)

          -- Find point with minimum area
          findMinArea i minA minIdx
            | i >= length points - 1 = { minA, minIdx }
            | otherwise =
                let area = triangleArea (safeGet (i - 1)) (safeGet i) (safeGet (i + 1))
                in if area < minA
                   then findMinArea (i + 1) area i
                   else findMinArea (i + 1) minA minIdx

          result = findMinArea 1 1.0e10 1

      in if result.minA < minArea
         then let newPoints = take result.minIdx points <> drop (result.minIdx + 1) points
              in visvalingamWhyatt newPoints minArea
         else points
