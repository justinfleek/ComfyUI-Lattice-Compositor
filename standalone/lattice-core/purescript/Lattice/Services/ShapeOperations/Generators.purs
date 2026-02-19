-- | Lattice.Services.ShapeOperations.Generators - Shape Generation
-- |
-- | Pure shape generation algorithms:
-- | - Rectangle (with optional roundness)
-- | - Ellipse (circular Bezier approximation)
-- | - Regular polygon (n-gon)
-- | - Star (n-pointed with inner/outer radii)
-- |
-- | Source: ui/src/services/shapeOperations.ts (shape generators)

module Lattice.Services.ShapeOperations.Generators
  ( -- * Types
    WindingDirection(..)
  , BezierVertex
  , BezierPath
  , mkBezierVertex, mkBezierPath
    -- * Constants
  , kappa
    -- * Vertex Helpers
  , cornerVertex, smoothVertex, cloneVertex, clonePath
    -- * Generators
  , generateRectangle
  , generateEllipse
  , generatePolygon
  , generateStar
    -- * Path from Points
  , pathFromPoints, smoothPathFromPoints
  ) where

import Prelude
import Data.Array (length, range, mapWithIndex, (!!), concat)
import Data.Int (floor, toNumber)
import Data.Maybe (fromMaybe)
import Math (pi, cos, sin) as Math

import Lattice.Services.ShapeOperations.Point2D as P2D

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Direction for shape winding
data WindingDirection
  = Clockwise
  | CounterClockwise

derive instance eqWindingDirection :: Eq WindingDirection

-- | A Bezier vertex with point and control handles
type BezierVertex =
  { point :: P2D.Point2D
  , inHandle :: P2D.Point2D   -- ^ Relative to point
  , outHandle :: P2D.Point2D  -- ^ Relative to point
  }

-- | Constructor for BezierVertex
mkBezierVertex :: P2D.Point2D -> P2D.Point2D -> P2D.Point2D -> BezierVertex
mkBezierVertex point inHandle outHandle = { point, inHandle, outHandle }

-- | A Bezier path is a list of vertices with closed flag
type BezierPath =
  { vertices :: Array BezierVertex
  , closed :: Boolean
  }

-- | Constructor for BezierPath
mkBezierPath :: Array BezierVertex -> Boolean -> BezierPath
mkBezierPath vertices closed = { vertices, closed }

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Magic number for circular Bezier approximation.
kappa :: Number
kappa = 0.5522847498

-- | Convert degrees to radians
degToRad :: Number -> Number
degToRad deg = deg * Math.pi / 180.0

-- ────────────────────────────────────────────────────────────────────────────
-- Vertex Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a corner vertex (no handles)
cornerVertex :: P2D.Point2D -> BezierVertex
cornerVertex p = { point: p, inHandle: P2D.origin, outHandle: P2D.origin }

-- | Create a smooth vertex with symmetric handles
smoothVertex :: P2D.Point2D -> P2D.Point2D -> Number -> BezierVertex
smoothVertex p handleDir handleLen =
  let h = P2D.scale (P2D.normalize handleDir) handleLen
  in { point: p, inHandle: P2D.neg h, outHandle: h }

-- | Clone a vertex
cloneVertex :: BezierVertex -> BezierVertex
cloneVertex v = { point: P2D.clone v.point
                , inHandle: P2D.clone v.inHandle
                , outHandle: P2D.clone v.outHandle
                }

-- | Clone a path
clonePath :: BezierPath -> BezierPath
clonePath p = { vertices: map cloneVertex p.vertices, closed: p.closed }

-- ────────────────────────────────────────────────────────────────────────────
-- Rectangle
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate a rectangle path.
generateRectangle :: P2D.Point2D -> P2D.Point2D -> Number -> WindingDirection -> BezierPath
generateRectangle position size roundness direction =
  let hw = size.x / 2.0
      hh = size.y / 2.0
      r = min roundness (min hw hh)

      tl = { x: position.x - hw, y: position.y - hh }
      tr = { x: position.x + hw, y: position.y - hh }
      br = { x: position.x + hw, y: position.y + hh }
      bl = { x: position.x - hw, y: position.y + hh }

      corners = case direction of
        Clockwise        -> [tl, tr, br, bl]
        CounterClockwise -> [tl, bl, br, tr]

  in if r < 0.01
     then { vertices: map cornerVertex corners, closed: true }
     else
       let k = kappa * r

           mkRoundedCorner corner prevDir nextDir =
             let startPt = P2D.add corner (P2D.scale (P2D.normalize prevDir) r)
                 endPt = P2D.add corner (P2D.scale (P2D.normalize nextDir) r)
             in [ { point: startPt
                  , inHandle: P2D.scale (P2D.normalize prevDir) (-k)
                  , outHandle: P2D.origin
                  }
                , { point: endPt
                  , inHandle: P2D.origin
                  , outHandle: P2D.scale (P2D.normalize nextDir) (-k)
                  }
                ]

           vertices = case direction of
             Clockwise -> concat
               [ mkRoundedCorner tl { x: 0.0, y: 1.0 } { x: 1.0, y: 0.0 }
               , mkRoundedCorner tr { x: -1.0, y: 0.0 } { x: 0.0, y: 1.0 }
               , mkRoundedCorner br { x: 0.0, y: -1.0 } { x: -1.0, y: 0.0 }
               , mkRoundedCorner bl { x: 1.0, y: 0.0 } { x: 0.0, y: -1.0 }
               ]
             CounterClockwise -> concat
               [ mkRoundedCorner tl { x: 1.0, y: 0.0 } { x: 0.0, y: 1.0 }
               , mkRoundedCorner bl { x: 0.0, y: -1.0 } { x: 1.0, y: 0.0 }
               , mkRoundedCorner br { x: -1.0, y: 0.0 } { x: 0.0, y: -1.0 }
               , mkRoundedCorner tr { x: 0.0, y: 1.0 } { x: -1.0, y: 0.0 }
               ]

       in { vertices, closed: true }

-- ────────────────────────────────────────────────────────────────────────────
-- Ellipse
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate an ellipse path using 4-point Bezier approximation.
generateEllipse :: P2D.Point2D -> P2D.Point2D -> WindingDirection -> BezierPath
generateEllipse position size direction =
  let rx = size.x / 2.0
      ry = size.y / 2.0
      kx = rx * kappa
      ky = ry * kappa

      top = { point: { x: position.x, y: position.y - ry }
            , inHandle: { x: -kx, y: 0.0 }
            , outHandle: { x: kx, y: 0.0 }
            }

      right = { point: { x: position.x + rx, y: position.y }
              , inHandle: { x: 0.0, y: -ky }
              , outHandle: { x: 0.0, y: ky }
              }

      bottom = { point: { x: position.x, y: position.y + ry }
               , inHandle: { x: kx, y: 0.0 }
               , outHandle: { x: -kx, y: 0.0 }
               }

      left = { point: { x: position.x - rx, y: position.y }
             , inHandle: { x: 0.0, y: ky }
             , outHandle: { x: 0.0, y: -ky }
             }

      swapHandles v = { point: v.point, inHandle: v.outHandle, outHandle: v.inHandle }

      vertices = case direction of
        Clockwise -> [top, right, bottom, left]
        CounterClockwise -> map swapHandles [top, left, bottom, right]

  in { vertices, closed: true }

-- ────────────────────────────────────────────────────────────────────────────
-- Regular Polygon
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate a regular polygon (n-gon).
generatePolygon :: P2D.Point2D -> Int -> Number -> Number -> Number -> WindingDirection -> BezierPath
generatePolygon position points radius roundness rotation direction =
  let numPoints = max 3 points
      angleStep = Math.pi * 2.0 / toNumber numPoints
      startAngle = degToRad (rotation - 90.0)

      dirMult = case direction of
        Clockwise        -> 1.0
        CounterClockwise -> -1.0

      mkVertex i =
        let idx = case direction of
              Clockwise        -> i
              CounterClockwise -> numPoints - 1 - i

            angle = startAngle + angleStep * toNumber idx * dirMult

            pt = { x: position.x + Math.cos angle * radius
                 , y: position.y + Math.sin angle * radius
                 }

        in if roundness > 0.0
           then let handleLength = radius * (roundness / 100.0) * 0.5
                    tangentAngle = angle + Math.pi / 2.0 * dirMult
                    tangent = { x: Math.cos tangentAngle, y: Math.sin tangentAngle }
                in { point: pt
                   , inHandle: P2D.scale tangent handleLength
                   , outHandle: P2D.scale tangent (-handleLength)
                   }
           else cornerVertex pt

      vertices = map mkVertex (range 0 (numPoints - 1))

  in { vertices, closed: true }

-- ────────────────────────────────────────────────────────────────────────────
-- Star
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate a star shape.
generateStar :: P2D.Point2D -> Int -> Number -> Number -> Number -> Number
             -> Number -> WindingDirection -> BezierPath
generateStar position points outerRadius innerRadius outerRoundness innerRoundness
             rotation direction =
  let numPoints = max 3 points
      angleStep = Math.pi / toNumber numPoints
      startAngle = degToRad (rotation - 90.0)
      totalVertices = numPoints * 2

      dirMult = case direction of
        Clockwise        -> 1.0
        CounterClockwise -> -1.0

      mkVertex i =
        let idx = case direction of
              Clockwise        -> i
              CounterClockwise -> totalVertices - 1 - i

            angle = startAngle + angleStep * toNumber idx * dirMult
            isOuter = idx `mod` 2 == 0

            radius = if isOuter then outerRadius else innerRadius
            roundness = if isOuter then outerRoundness else innerRoundness

            pt = { x: position.x + Math.cos angle * radius
                 , y: position.y + Math.sin angle * radius
                 }

        in if roundness > 0.0
           then let handleLength = radius * (roundness / 100.0) * 0.3
                    tangentAngle = angle + Math.pi / 2.0 * dirMult
                    tangent = { x: Math.cos tangentAngle, y: Math.sin tangentAngle }
                in { point: pt
                   , inHandle: P2D.scale tangent handleLength
                   , outHandle: P2D.scale tangent (-handleLength)
                   }
           else cornerVertex pt

      vertices = map mkVertex (range 0 (totalVertices - 1))

  in { vertices, closed: true }

-- ────────────────────────────────────────────────────────────────────────────
-- Path from Points
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a path from an array of points (sharp corners)
pathFromPoints :: Array P2D.Point2D -> Boolean -> BezierPath
pathFromPoints points closed = { vertices: map cornerVertex points, closed }

-- | Create a smooth path from points using Catmull-Rom to Bezier conversion
smoothPathFromPoints :: Array P2D.Point2D -> Boolean -> Number -> BezierPath
smoothPathFromPoints points closed tension
  | length points < 2 = { vertices: [], closed }
  | otherwise =
      let n = length points

          safeGet i = fromMaybe P2D.origin (points !! i)

          mkVertex i =
            let curr = safeGet i
                prev = safeGet ((i + n - 1) `mod` n)
                next = safeGet ((i + 1) `mod` n)

                tangent = P2D.scale (P2D.sub next prev) (tension / 2.0)

                distPrev = P2D.distance curr prev
                distNext = P2D.distance curr next
                avgDist = (distPrev + distNext) / 2.0

                handleIn = P2D.scale (P2D.neg (P2D.normalize tangent)) (avgDist * 0.25)
                handleOut = P2D.scale (P2D.normalize tangent) (avgDist * 0.25)

            in { point: curr, inHandle: handleIn, outHandle: handleOut }

          vertices = mapWithIndex (\i _ -> mkVertex i) points

      in { vertices, closed }
