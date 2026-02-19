-- | Lattice.Services.Mesh.Delaunay - Delaunay Triangulation
-- |
-- | Pure mathematical implementation of Bowyer-Watson algorithm for
-- | Delaunay triangulation. Used for mesh warp deformation.
-- |
-- | Features:
-- | - Super-triangle construction
-- | - Circumcircle containment test
-- | - Incremental point insertion
-- | - Bad triangle removal
-- |
-- | Source: ui/src/services/meshWarpDeformation.ts

module Lattice.Services.Mesh.Delaunay
  ( Point2D
  , mkPoint2D
  , p2dX
  , p2dY
  , Triangle
  , mkTriangle
  , triA
  , triB
  , triC
  , Edge
  , mkEdge
  , edgeA
  , edgeB
  , distance
  , sub
  , isPointInCircumcircle
  , createSuperTriangle
  , delaunayTriangulate
  , flattenTriangles
  , triangleCount
  ) where

import Prelude

import Data.Array (filter, foldl, length, mapWithIndex, snoc, (!!))
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Math (sqrt)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point for mesh operations
newtype Point2D = Point2D { x :: Number, y :: Number }

derive instance eqPoint2D :: Eq Point2D

mkPoint2D :: Number -> Number -> Point2D
mkPoint2D x y = Point2D { x, y }

p2dX :: Point2D -> Number
p2dX (Point2D p) = p.x

p2dY :: Point2D -> Number
p2dY (Point2D p) = p.y

-- | Triangle defined by indices into point array
newtype Triangle = Triangle { a :: Int, b :: Int, c :: Int }

derive instance eqTriangle :: Eq Triangle

mkTriangle :: Int -> Int -> Int -> Triangle
mkTriangle a b c = Triangle { a, b, c }

triA :: Triangle -> Int
triA (Triangle t) = t.a

triB :: Triangle -> Int
triB (Triangle t) = t.b

triC :: Triangle -> Int
triC (Triangle t) = t.c

-- | Edge defined by two point indices
newtype Edge = Edge { a :: Int, b :: Int }

derive instance eqEdge :: Eq Edge

mkEdge :: Int -> Int -> Edge
mkEdge a b = Edge { a, b }

edgeA :: Edge -> Int
edgeA (Edge e) = e.a

edgeB :: Edge -> Int
edgeB (Edge e) = e.b

-- | Check if two edges are equal (considering both directions)
edgeEquals :: Edge -> Edge -> Boolean
edgeEquals e1 e2 =
  (edgeA e1 == edgeA e2 && edgeB e1 == edgeB e2) ||
  (edgeA e1 == edgeB e2 && edgeB e1 == edgeA e2)

-- ────────────────────────────────────────────────────────────────────────────
-- Point Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Distance between two points
distance :: Point2D -> Point2D -> Number
distance a b =
  let dx = p2dX b - p2dX a
      dy = p2dY b - p2dY a
  in sqrt (dx * dx + dy * dy)

-- | Point subtraction
sub :: Point2D -> Point2D -> Point2D
sub a b = mkPoint2D (p2dX a - p2dX b) (p2dY a - p2dY b)

-- ────────────────────────────────────────────────────────────────────────────
-- Circumcircle Test
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if a point is inside the circumcircle of a triangle.
-- |
-- | Uses the determinant method. The sign of the determinant indicates
-- | whether the point is inside (positive for CCW triangles) or outside.
isPointInCircumcircle :: Point2D -> Point2D -> Point2D -> Point2D -> Boolean
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
      if orientation > 0.0 then det > 0.0 else det < 0.0

-- ────────────────────────────────────────────────────────────────────────────
-- Super Triangle
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a super triangle that encompasses all points.
-- |
-- | The super triangle is large enough that all input points
-- | lie strictly inside it. Used as initial state for Bowyer-Watson.
createSuperTriangle :: Array Point2D -> { a :: Point2D, b :: Point2D, c :: Point2D }
createSuperTriangle points
  | length points == 0 =
      { a: mkPoint2D 0.0 0.0
      , b: mkPoint2D 1.0 0.0
      , c: mkPoint2D 0.5 1.0
      }
  | otherwise =
      let inf = 1.0e308  -- Use large number instead of Infinity
          negInf = -1.0e308

          minX = foldl (\acc p -> min acc (p2dX p)) inf points
          maxX = foldl (\acc p -> max acc (p2dX p)) negInf points
          minY = foldl (\acc p -> min acc (p2dY p)) inf points
          maxY = foldl (\acc p -> max acc (p2dY p)) negInf points

          dx = maxX - minX
          dy = maxY - minY
          deltaMax = max dx dy * 2.0

          superA = mkPoint2D (minX - deltaMax) (minY - deltaMax)
          superB = mkPoint2D (minX + deltaMax * 2.0) (minY - deltaMax)
          superC = mkPoint2D (minX + deltaMax / 2.0) (maxY + deltaMax * 2.0)
      in { a: superA, b: superB, c: superC }

-- ────────────────────────────────────────────────────────────────────────────
-- Triangle Edge Extraction
-- ────────────────────────────────────────────────────────────────────────────

-- | Get the three edges of a triangle
triangleEdges :: Triangle -> Array Edge
triangleEdges tri =
  [ mkEdge (triA tri) (triB tri)
  , mkEdge (triB tri) (triC tri)
  , mkEdge (triC tri) (triA tri)
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Bowyer-Watson Algorithm
-- ────────────────────────────────────────────────────────────────────────────

-- | Find all triangles whose circumcircle contains the given point
findBadTriangles :: Point2D -> Array Triangle -> Array Point2D -> Array Triangle
findBadTriangles point triangles allPoints =
  filter isBad triangles
  where
    isBad tri =
      let pa = fromMaybe (mkPoint2D 0.0 0.0) (allPoints !! triA tri)
          pb = fromMaybe (mkPoint2D 0.0 0.0) (allPoints !! triB tri)
          pc = fromMaybe (mkPoint2D 0.0 0.0) (allPoints !! triC tri)
      in isPointInCircumcircle point pa pb pc

-- | Find the boundary polygon of bad triangles (non-shared edges)
findPolygonBoundary :: Array Triangle -> Array Edge
findPolygonBoundary badTriangles =
  let allEdges = foldl (\acc tri -> acc <> triangleEdges tri) [] badTriangles
      countEdge edge = foldl (\acc e -> if edgeEquals edge e then acc + 1 else acc) 0 allEdges
  in filter (\edge -> countEdge edge == 1) allEdges

-- | Delaunay triangulation auxiliary with explicit fuel for termination
delaunayTriangulateAux :: Array Point2D -> Int -> Array Triangle -> Array Point2D
                       -> Int -> Array Triangle
delaunayTriangulateAux points fuel triangles allPoints currentIdx
  | fuel == 0 || currentIdx >= length points = triangles
  | otherwise =
      let point = fromMaybe (mkPoint2D 0.0 0.0) (points !! currentIdx)

          -- Find triangles whose circumcircle contains this point
          badTriangles = findBadTriangles point triangles allPoints

          -- Find boundary polygon
          polygon = findPolygonBoundary badTriangles

          -- Remove bad triangles
          triangles' = filter (\t -> not (Array.elem t badTriangles)) triangles

          -- Create new triangles from polygon edges to new point
          newTriangles = map (\edge -> mkTriangle (edgeA edge) (edgeB edge) currentIdx) polygon

      in delaunayTriangulateAux points (fuel - 1) (triangles' <> newTriangles)
           allPoints (currentIdx + 1)

-- | Delaunay triangulation of a point set.
-- |
-- | Returns array of triangles (as index triples into input array).
-- | Uses Bowyer-Watson algorithm.
delaunayTriangulate :: Array Point2D -> Array Triangle
delaunayTriangulate points
  | length points < 3 = []
  | otherwise =
      let super = createSuperTriangle points
          n = length points
          superIndices = [n, n + 1, n + 2]

          -- All points including super triangle
          allPoints = points <> [super.a, super.b, super.c]

          -- Initial triangle is the super triangle
          initialTriangles = [mkTriangle n (n + 1) (n + 2)]

          -- Run Bowyer-Watson with fuel = length points
          triangles = delaunayTriangulateAux points n initialTriangles allPoints 0

          -- Remove triangles that include super triangle vertices
          isSuperVertex v = Array.elem v superIndices
      in filter (\t -> not (isSuperVertex (triA t) ||
                            isSuperVertex (triB t) ||
                            isSuperVertex (triC t))) triangles

-- ────────────────────────────────────────────────────────────────────────────
-- Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Flatten triangles to index array (for GPU)
flattenTriangles :: Array Triangle -> Array Int
flattenTriangles = foldl (\acc tri -> acc <> [triA tri, triB tri, triC tri]) []

-- | Get triangle count
triangleCount :: Array Triangle -> Int
triangleCount = length
