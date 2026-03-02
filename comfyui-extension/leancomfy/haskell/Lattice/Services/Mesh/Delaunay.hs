{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Mesh.Delaunay
Description : Delaunay Triangulation
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical implementation of Bowyer-Watson algorithm for
Delaunay triangulation. Used for mesh warp deformation.

Features:
- Super-triangle construction
- Circumcircle containment test
- Incremental point insertion
- Bad triangle removal

Source: ui/src/services/meshWarpDeformation.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Mesh.Delaunay
  ( -- * Types
    Point2D(..)
  , Triangle(..)
  , Edge(..)
    -- * Point Operations
  , distance
  , sub
    -- * Circumcircle Test
  , isPointInCircumcircle
    -- * Super Triangle
  , createSuperTriangle
    -- * Triangulation
  , delaunayTriangulate
    -- * Utilities
  , flattenTriangles
  , triangleCount
  ) where

import Data.List (foldl')
import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D point for mesh operations
data Point2D = Point2D
  { p2dX :: Double
  , p2dY :: Double
  } deriving (Show, Eq)

-- | Triangle defined by indices into point array
data Triangle = Triangle
  { triA :: Int
  , triB :: Int
  , triC :: Int
  } deriving (Show, Eq)

-- | Edge defined by two point indices
data Edge = Edge
  { edgeA :: Int
  , edgeB :: Int
  } deriving (Show, Eq)

-- | Check if two edges are equal (considering both directions)
edgeEquals :: Edge -> Edge -> Bool
edgeEquals e1 e2 =
  (edgeA e1 == edgeA e2 && edgeB e1 == edgeB e2) ||
  (edgeA e1 == edgeB e2 && edgeB e1 == edgeA e2)

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

-- | Distance between two points
distance :: Point2D -> Point2D -> Double
distance a b =
  let dx = p2dX b - p2dX a
      dy = p2dY b - p2dY a
  in sqrt (dx * dx + dy * dy)

-- | Point subtraction
sub :: Point2D -> Point2D -> Point2D
sub a b = Point2D (p2dX a - p2dX b) (p2dY a - p2dY b)

--------------------------------------------------------------------------------
-- Circumcircle Test
--------------------------------------------------------------------------------

-- | Check if a point is inside the circumcircle of a triangle.
--
-- Uses the determinant method. The sign of the determinant indicates
-- whether the point is inside (positive for CCW triangles) or outside.
--
-- Mathematical formula:
-- | ax-px  ay-py  (ax-px)²+(ay-py)² |
-- | bx-px  by-py  (bx-px)²+(by-py)² | > 0 for inside (CCW triangle)
-- | cx-px  cy-py  (cx-px)²+(cy-py)² |
isPointInCircumcircle :: Point2D -> Point2D -> Point2D -> Point2D -> Bool
isPointInCircumcircle point a b c =
  let ax = p2dX a - p2dX point
      ay = p2dY a - p2dY point
      bx = p2dX b - p2dX point
      by = p2dY b - p2dY point
      cx = p2dX c - p2dX point
      cy = p2dY c - p2dY point

      -- Determinant calculation
      det = (ax * ax + ay * ay) * (bx * cy - cx * by) -
            (bx * bx + by * by) * (ax * cy - cx * ay) +
            (cx * cx + cy * cy) * (ax * by - bx * ay)

      -- Check orientation of triangle
      orientation = (p2dX b - p2dX a) * (p2dY c - p2dY a) -
                    (p2dY b - p2dY a) * (p2dX c - p2dX a)
  in
      -- Inside if det and orientation have same sign
      if orientation > 0 then det > 0 else det < 0

--------------------------------------------------------------------------------
-- Super Triangle
--------------------------------------------------------------------------------

-- | Create a super triangle that encompasses all points.
--
-- The super triangle is large enough that all input points
-- lie strictly inside it. Used as initial state for Bowyer-Watson.
createSuperTriangle :: Vector Point2D -> (Point2D, Point2D, Point2D)
createSuperTriangle points
  | V.null points = (Point2D 0 0, Point2D 1 0, Point2D 0.5 1)
  | otherwise =
      let minX = V.foldl' (\acc p -> min acc (p2dX p)) (1/0) points
          maxX = V.foldl' (\acc p -> max acc (p2dX p)) (-1/0) points
          minY = V.foldl' (\acc p -> min acc (p2dY p)) (1/0) points
          maxY = V.foldl' (\acc p -> max acc (p2dY p)) (-1/0) points

          dx = maxX - minX
          dy = maxY - minY
          deltaMax = max dx dy * 2.0

          superA = Point2D (minX - deltaMax) (minY - deltaMax)
          superB = Point2D (minX + deltaMax * 2.0) (minY - deltaMax)
          superC = Point2D (minX + deltaMax / 2.0) (maxY + deltaMax * 2.0)
      in (superA, superB, superC)

--------------------------------------------------------------------------------
-- Triangle Edge Extraction
--------------------------------------------------------------------------------

-- | Get the three edges of a triangle
triangleEdges :: Triangle -> [Edge]
triangleEdges tri =
  [ Edge (triA tri) (triB tri)
  , Edge (triB tri) (triC tri)
  , Edge (triC tri) (triA tri)
  ]

-- | Check if an edge is shared between a triangle and any in a list
isEdgeShared :: Edge -> Triangle -> [Triangle] -> Bool
isEdgeShared edge tri others =
  any (\other ->
    if other == tri then False
    else any (edgeEquals edge) (triangleEdges other)
  ) others

--------------------------------------------------------------------------------
-- Bowyer-Watson Algorithm
--------------------------------------------------------------------------------

-- | Find all triangles whose circumcircle contains the given point
findBadTriangles :: Point2D -> [Triangle] -> Vector Point2D -> [Triangle]
findBadTriangles point triangles allPoints =
  filter isBad triangles
  where
    isBad tri =
      let pa = allPoints V.! triA tri
          pb = allPoints V.! triB tri
          pc = allPoints V.! triC tri
      in isPointInCircumcircle point pa pb pc

-- | Find the boundary polygon of bad triangles (non-shared edges)
findPolygonBoundary :: [Triangle] -> [Edge]
findPolygonBoundary badTriangles =
  let allEdges = concatMap triangleEdges badTriangles
  in filter (\edge -> countEdge edge allEdges == 1) allEdges
  where
    countEdge edge edges =
      foldl' (\acc e -> if edgeEquals edge e then acc + 1 else acc) 0 edges

-- | Delaunay triangulation auxiliary with explicit fuel for termination
delaunayTriangulateAux :: Vector Point2D -> Int -> [Triangle] -> Vector Point2D
                       -> Int -> [Triangle]
delaunayTriangulateAux points fuel triangles allPoints currentIdx
  | fuel == 0 || currentIdx >= V.length points = triangles
  | otherwise =
      let point = points V.! currentIdx

          -- Find triangles whose circumcircle contains this point
          badTriangles = findBadTriangles point triangles allPoints

          -- Find boundary polygon
          polygon = findPolygonBoundary badTriangles

          -- Remove bad triangles
          triangles' = filter (`notElem` badTriangles) triangles

          -- Create new triangles from polygon edges to new point
          newTriangles = map (\edge -> Triangle (edgeA edge) (edgeB edge) currentIdx) polygon

      in delaunayTriangulateAux points (fuel - 1) (triangles' ++ newTriangles)
           allPoints (currentIdx + 1)

-- | Delaunay triangulation of a point set.
--
-- Returns list of triangles (as index triples into input array).
-- Uses Bowyer-Watson algorithm.
delaunayTriangulate :: Vector Point2D -> [Triangle]
delaunayTriangulate points
  | V.length points < 3 = []
  | otherwise =
      let (superA, superB, superC) = createSuperTriangle points
          n = V.length points
          superIndices = [n, n + 1, n + 2]

          -- All points including super triangle
          allPoints = points V.++ V.fromList [superA, superB, superC]

          -- Initial triangle is the super triangle
          initialTriangles = [Triangle n (n + 1) (n + 2)]

          -- Run Bowyer-Watson with fuel = points.size
          triangles = delaunayTriangulateAux points n initialTriangles allPoints 0

          -- Remove triangles that include super triangle vertices
          isSuperVertex v = v `elem` superIndices
      in filter (\t -> not (isSuperVertex (triA t) ||
                            isSuperVertex (triB t) ||
                            isSuperVertex (triC t))) triangles

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- | Flatten triangles to index list (for GPU)
flattenTriangles :: [Triangle] -> [Int]
flattenTriangles = concatMap (\tri -> [triA tri, triB tri, triC tri])

-- | Get triangle count
triangleCount :: [Triangle] -> Int
triangleCount = length
