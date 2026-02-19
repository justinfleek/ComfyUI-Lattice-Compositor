{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.ShapeOperations.Generators
Description : Shape Generation
Copyright   : (c) Lattice, 2026
License     : MIT

Pure shape generation algorithms:
- Rectangle (with optional roundness)
- Ellipse (circular Bezier approximation)
- Regular polygon (n-gon)
- Star (n-pointed with inner/outer radii)

Source: ui/src/services/shapeOperations.ts (shape generators)
-}

module Lattice.Services.ShapeOperations.Generators
  ( -- * Types
    WindingDirection(..)
  , BezierVertex(..)
  , BezierPath(..)
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

import Data.Vector (Vector)
import qualified Data.Vector as V

import Lattice.Services.ShapeOperations.Point2D

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Direction for shape winding
data WindingDirection
  = Clockwise
  | CounterClockwise
  deriving (Show, Eq)

-- | A Bezier vertex with point and control handles
data BezierVertex = BezierVertex
  { bvPoint    :: Point2D
  , bvInHandle :: Point2D  -- ^ Relative to point
  , bvOutHandle :: Point2D -- ^ Relative to point
  } deriving (Show, Eq)

-- | A Bezier path is a list of vertices with closed flag
data BezierPath = BezierPath
  { bpVertices :: Vector BezierVertex
  , bpClosed   :: Bool
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Magic number for circular Bezier approximation.
-- Derived from: 4/3 * tan(π/8) ≈ 0.5522847498
kappa :: Double
kappa = 0.5522847498

-- | Convert degrees to radians
degToRad :: Double -> Double
degToRad deg = deg * pi / 180

--------------------------------------------------------------------------------
-- Vertex Helpers
--------------------------------------------------------------------------------

-- | Create a corner vertex (no handles)
cornerVertex :: Point2D -> BezierVertex
cornerVertex p = BezierVertex p origin origin

-- | Create a smooth vertex with symmetric handles
smoothVertex :: Point2D -> Point2D -> Double -> BezierVertex
smoothVertex p handleDir handleLen =
  let h = scale (normalize handleDir) handleLen
  in BezierVertex p (neg h) h

-- | Clone a vertex
cloneVertex :: BezierVertex -> BezierVertex
cloneVertex (BezierVertex p i o) = BezierVertex (clone p) (clone i) (clone o)

-- | Clone a path
clonePath :: BezierPath -> BezierPath
clonePath (BezierPath vs c) = BezierPath (V.map cloneVertex vs) c

--------------------------------------------------------------------------------
-- Rectangle
--------------------------------------------------------------------------------

-- | Generate a rectangle path.
generateRectangle :: Point2D -> Point2D -> Double -> WindingDirection -> BezierPath
generateRectangle position size roundness direction =
  let hw = px size / 2
      hh = py size / 2
      r = min roundness (min hw hh)

      -- Corner positions
      tl = Point2D (px position - hw) (py position - hh)
      tr = Point2D (px position + hw) (py position - hh)
      br = Point2D (px position + hw) (py position + hh)
      bl = Point2D (px position - hw) (py position + hh)

      corners = case direction of
        Clockwise        -> [tl, tr, br, bl]
        CounterClockwise -> [tl, bl, br, tr]

  in if r < 0.01
     then BezierPath (V.fromList $ map cornerVertex corners) True
     else
       let k = kappa * r

           mkRoundedCorner corner prevDir nextDir =
             let startPt = add corner (scale (normalize prevDir) r)
                 endPt = add corner (scale (normalize nextDir) r)
             in [ BezierVertex startPt (scale (normalize prevDir) (-k)) origin
                , BezierVertex endPt origin (scale (normalize nextDir) (-k))
                ]

           vertices = case direction of
             Clockwise ->
               mkRoundedCorner tl (Point2D 0 1) (Point2D 1 0) ++
               mkRoundedCorner tr (Point2D (-1) 0) (Point2D 0 1) ++
               mkRoundedCorner br (Point2D 0 (-1)) (Point2D (-1) 0) ++
               mkRoundedCorner bl (Point2D 1 0) (Point2D 0 (-1))
             CounterClockwise ->
               mkRoundedCorner tl (Point2D 1 0) (Point2D 0 1) ++
               mkRoundedCorner bl (Point2D 0 (-1)) (Point2D 1 0) ++
               mkRoundedCorner br (Point2D (-1) 0) (Point2D 0 (-1)) ++
               mkRoundedCorner tr (Point2D 0 1) (Point2D (-1) 0)

       in BezierPath (V.fromList vertices) True

--------------------------------------------------------------------------------
-- Ellipse
--------------------------------------------------------------------------------

-- | Generate an ellipse path using 4-point Bezier approximation.
generateEllipse :: Point2D -> Point2D -> WindingDirection -> BezierPath
generateEllipse position size direction =
  let rx = px size / 2
      ry = py size / 2
      kx = rx * kappa
      ky = ry * kappa

      top = BezierVertex
        (Point2D (px position) (py position - ry))
        (Point2D (-kx) 0)
        (Point2D kx 0)

      right = BezierVertex
        (Point2D (px position + rx) (py position))
        (Point2D 0 (-ky))
        (Point2D 0 ky)

      bottom = BezierVertex
        (Point2D (px position) (py position + ry))
        (Point2D kx 0)
        (Point2D (-kx) 0)

      left = BezierVertex
        (Point2D (px position - rx) (py position))
        (Point2D 0 ky)
        (Point2D 0 (-ky))

      swapHandles (BezierVertex p i o) = BezierVertex p o i

      vertices = case direction of
        Clockwise -> [top, right, bottom, left]
        CounterClockwise -> map swapHandles [top, left, bottom, right]

  in BezierPath (V.fromList vertices) True

--------------------------------------------------------------------------------
-- Regular Polygon
--------------------------------------------------------------------------------

-- | Generate a regular polygon (n-gon).
generatePolygon :: Point2D -> Int -> Double -> Double -> Double -> WindingDirection -> BezierPath
generatePolygon position points radius roundness rotation direction =
  let numPoints = max 3 points
      angleStep = pi * 2 / fromIntegral numPoints
      startAngle = degToRad (rotation - 90)

      dirMult = case direction of
        Clockwise        -> 1
        CounterClockwise -> -1

      mkVertex i =
        let idx = case direction of
              Clockwise        -> i
              CounterClockwise -> numPoints - 1 - i

            angle = startAngle + angleStep * fromIntegral idx * dirMult

            pt = Point2D
              (px position + cos angle * radius)
              (py position + sin angle * radius)

        in if roundness > 0
           then let handleLength = radius * (roundness / 100) * 0.5
                    tangentAngle = angle + pi / 2 * dirMult
                    tangent = Point2D (cos tangentAngle) (sin tangentAngle)
                in BezierVertex pt
                     (scale tangent handleLength)
                     (scale tangent (-handleLength))
           else cornerVertex pt

      vertices = map mkVertex [0 .. numPoints - 1]

  in BezierPath (V.fromList vertices) True

--------------------------------------------------------------------------------
-- Star
--------------------------------------------------------------------------------

-- | Generate a star shape.
generateStar :: Point2D -> Int -> Double -> Double -> Double -> Double
             -> Double -> WindingDirection -> BezierPath
generateStar position points outerRadius innerRadius outerRoundness innerRoundness
             rotation direction =
  let numPoints = max 3 points
      angleStep = pi / fromIntegral numPoints
      startAngle = degToRad (rotation - 90)
      totalVertices = numPoints * 2

      dirMult = case direction of
        Clockwise        -> 1
        CounterClockwise -> -1

      mkVertex i =
        let idx = case direction of
              Clockwise        -> i
              CounterClockwise -> totalVertices - 1 - i

            angle = startAngle + angleStep * fromIntegral idx * dirMult
            isOuter = idx `mod` 2 == 0

            radius = if isOuter then outerRadius else innerRadius
            roundness = if isOuter then outerRoundness else innerRoundness

            pt = Point2D
              (px position + cos angle * radius)
              (py position + sin angle * radius)

        in if roundness > 0
           then let handleLength = radius * (roundness / 100) * 0.3
                    tangentAngle = angle + pi / 2 * dirMult
                    tangent = Point2D (cos tangentAngle) (sin tangentAngle)
                in BezierVertex pt
                     (scale tangent handleLength)
                     (scale tangent (-handleLength))
           else cornerVertex pt

      vertices = map mkVertex [0 .. totalVertices - 1]

  in BezierPath (V.fromList vertices) True

--------------------------------------------------------------------------------
-- Path from Points
--------------------------------------------------------------------------------

-- | Create a path from an array of points (sharp corners)
pathFromPoints :: Vector Point2D -> Bool -> BezierPath
pathFromPoints points closed = BezierPath (V.map cornerVertex points) closed

-- | Create a smooth path from points using Catmull-Rom to Bezier conversion
smoothPathFromPoints :: Vector Point2D -> Bool -> Double -> BezierPath
smoothPathFromPoints points closed tension
  | V.length points < 2 = BezierPath V.empty closed
  | otherwise =
      let n = V.length points

          mkVertex i =
            let curr = points V.! i
                prev = points V.! ((i + n - 1) `mod` n)
                next = points V.! ((i + 1) `mod` n)

                tangent = scale (sub next prev) (tension / 2)

                distPrev = distance curr prev
                distNext = distance curr next
                avgDist = (distPrev + distNext) / 2

                handleIn = scale (neg (normalize tangent)) (avgDist * 0.25)
                handleOut = scale (normalize tangent) (avgDist * 0.25)

            in BezierVertex curr handleIn handleOut

          vertices = V.generate n mkVertex

      in BezierPath vertices closed
