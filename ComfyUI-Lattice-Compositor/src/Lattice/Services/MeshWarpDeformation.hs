-- |
-- Module      : Lattice.Services.MeshWarpDeformation
-- Description : Pure mesh warp deformation functions
-- 
-- Migrated from ui/src/services/meshWarpDeformation.ts
-- Pure geometric and triangulation functions for mesh deformation
-- Note: Service class (mesh caching) deferred
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.MeshWarpDeformation
  ( -- Types
    Triangle(..)
  -- Geometric utilities
  , pointDistance
  , pointLerp
  , pointClamp
  , rotatePoint
  , scalePoint
  -- Triangulation
  , delaunayTriangulate
  , isPointInCircumcircle
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Types.Primitives (Vec2(..))
import Lattice.Utils.NumericSafety (ensureFiniteD, safeSqrtD)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Triangle with vertex indices
data Triangle = Triangle
  { triangleA :: Int
  , triangleB :: Int
  , triangleC :: Int
  }
  deriving (Eq, Show)

-- ============================================================================
-- GEOMETRIC UTILITY FUNCTIONS
-- ============================================================================

-- | Calculate Euclidean distance between two 2D points
-- Pure function: same inputs → same outputs
pointDistance :: Vec2 -> Vec2 -> Double
pointDistance a b =
  let dx = vec2X b - vec2X a
      dy = vec2Y b - vec2Y a
      distSq = dx * dx + dy * dy
  in ensureFiniteD (safeSqrtD distSq) 0.0

-- | Linear interpolation between two values
-- Pure function: same inputs → same outputs
pointLerp :: Double -> Double -> Double -> Double
pointLerp a b t = ensureFiniteD (a + (b - a) * t) a

-- | Clamp a value between min and max
-- Pure function: same inputs → same outputs
pointClamp :: Double -> Double -> Double -> Double
pointClamp value minVal maxVal =
  let clamped = if value < minVal then minVal else if value > maxVal then maxVal else value
  in ensureFiniteD clamped minVal

-- | Rotate a point around an origin by angle (degrees)
-- Pure function: same inputs → same outputs
rotatePoint :: Vec2 -> Vec2 -> Double -> Vec2
rotatePoint point origin angleDegrees =
  let angleRadians = angleDegrees * pi / 180.0
      cosAngle = cos angleRadians
      sinAngle = sin angleRadians
      dx = vec2X point - vec2X origin
      dy = vec2Y point - vec2Y origin
      newX = vec2X origin + dx * cosAngle - dy * sinAngle
      newY = vec2Y origin + dx * sinAngle + dy * cosAngle
  in Vec2 (ensureFiniteD newX 0.0) (ensureFiniteD newY 0.0)

-- | Scale a point relative to an origin
-- Pure function: same inputs → same outputs
scalePoint :: Vec2 -> Vec2 -> Double -> Vec2
scalePoint point origin scale =
  let finiteScale = ensureFiniteD scale 1.0
      newX = vec2X origin + (vec2X point - vec2X origin) * finiteScale
      newY = vec2Y origin + (vec2Y point - vec2Y origin) * finiteScale
  in Vec2 (ensureFiniteD newX 0.0) (ensureFiniteD newY 0.0)

-- ============================================================================
-- DELAUNAY TRIANGULATION
-- ============================================================================

-- | Check if a point is inside the circumcircle of a triangle
-- Pure function: same inputs → same outputs
isPointInCircumcircle :: Vec2 -> Vec2 -> Vec2 -> Vec2 -> Bool
isPointInCircumcircle point a b c =
  let ax = vec2X a - vec2X point
      ay = vec2Y a - vec2Y point
      bx = vec2X b - vec2X point
      by = vec2Y b - vec2Y point
      cx = vec2X c - vec2X point
      cy = vec2Y c - vec2Y point
      -- Determinant calculation
      det = (ax * ax + ay * ay) * (bx * cy - cx * by)
          - (bx * bx + by * by) * (ax * cy - cx * ay)
          + (cx * cx + cy * cy) * (ax * by - bx * ay)
      -- Counter-clockwise orientation check
      orientation = (vec2X b - vec2X a) * (vec2Y c - vec2Y a)
                  - (vec2Y b - vec2Y a) * (vec2X c - vec2X a)
  in if orientation > 0 then det > 0 else det < 0

-- | Safe list accessor (returns default if out of bounds)
safeListGet :: [a] -> Int -> a -> a
safeListGet [] _ defaultVal = defaultVal
safeListGet arr idx defaultVal
  | idx < 0 = defaultVal
  | otherwise = go arr idx
  where
    go [] _ = defaultVal
    go (x:xs) 0 = x
    go (_:xs) n = go xs (n - 1)

-- | Simple Delaunay triangulation using Bowyer-Watson algorithm
-- Pure function: same inputs → same outputs
-- Returns list of triangles (vertex indices)
delaunayTriangulate :: [Vec2] -> [Triangle]
delaunayTriangulate points =
  if length points < 3
  then []
  else
    let -- Calculate bounding box
        xs = map vec2X points
        ys = map vec2Y points
        minX = minimum xs
        maxX = maximum xs
        minY = minimum ys
        maxY = maximum ys
        dx = maxX - minX
        dy = maxY - minY
        deltaMax = max dx dy * 2.0
        -- Create super triangle that encompasses all points
        superA = Vec2 (minX - deltaMax) (minY - deltaMax)
        superB = Vec2 (minX + deltaMax * 2.0) (minY - deltaMax)
        superC = Vec2 (minX + deltaMax / 2.0) (maxY + deltaMax * 2.0)
        -- All points including super triangle
        allPoints = points ++ [superA, superB, superC]
        pointCount = length points
        superIdxA = pointCount
        superIdxB = pointCount + 1
        superIdxC = pointCount + 2
        superIndices = [superIdxA, superIdxB, superIdxC]
        -- Initial triangle is the super triangle
        initialTriangles = [Triangle superIdxA superIdxB superIdxC]
        -- Process each point
        finalTriangles = foldl (insertPoint allPoints) initialTriangles (zip [0..] points)
        -- Remove triangles that include super triangle vertices
    in filter (\tri ->
        not (triangleA tri `elem` superIndices) &&
        not (triangleB tri `elem` superIndices) &&
        not (triangleC tri `elem` superIndices)
      ) finalTriangles
  where
    insertPoint :: [Vec2] -> [Triangle] -> (Int, Vec2) -> [Triangle]
    insertPoint allPointsWithSuper triangles (pointIdx, point) =
      let badTriangles = filter (\tri ->
            let a = safeListGet allPointsWithSuper (triangleA tri) (Vec2 0 0)
                b = safeListGet allPointsWithSuper (triangleB tri) (Vec2 0 0)
                c = safeListGet allPointsWithSuper (triangleC tri) (Vec2 0 0)
            in isPointInCircumcircle point a b c
            ) triangles
          boundaryEdges = findBoundaryEdges badTriangles
          remainingTriangles = filter (\tri -> not (tri `elem` badTriangles)) triangles
          newTriangles = map (\(edgeA, edgeB) -> Triangle edgeA edgeB pointIdx) boundaryEdges
      in remainingTriangles ++ newTriangles
    
    -- Helper to find boundary edges (edges not shared by two bad triangles)
    findBoundaryEdges :: [Triangle] -> [(Int, Int)]
    findBoundaryEdges badTriangles =
      let allEdges = concatMap
            (\tri ->
              [(triangleA tri, triangleB tri),
               (triangleB tri, triangleC tri),
               (triangleC tri, triangleA tri)])
            badTriangles
          isBoundaryEdge (edgeA, edgeB) =
            let edgeMatch (a, b) = (a == edgeA && b == edgeB) || (a == edgeB && b == edgeA)
                count = length (filter edgeMatch allEdges)
            in count == 1
      in filter isBoundaryEdge allEdges
