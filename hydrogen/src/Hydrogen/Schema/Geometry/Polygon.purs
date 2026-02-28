-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // polygon
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Polygon — closed 2D shape defined by vertices.
-- |
-- | ## Design Philosophy
-- |
-- | A polygon is a closed shape defined by 3+ vertices in order.
-- | Vertices are stored counter-clockwise for consistent winding.
-- |
-- | This module provides:
-- | - Construction with validation (minimum 3 vertices)
-- | - Area calculation (signed, based on winding)
-- | - Point containment testing
-- | - Centroid calculation
-- | - Convexity testing
-- | - Regular polygon constructors
-- |
-- | ## Dependencies
-- |
-- | - Hydrogen.Schema.Geometry.Point (Point2D)
-- | - Hydrogen.Schema.Geometry.Angle (Degrees)
-- | - Data.Array
-- |
-- | ## Dependents
-- |
-- | - SVG polygon rendering
-- | - Hit testing for complex shapes
-- | - Clipping and masking

module Hydrogen.Schema.Geometry.Polygon
  ( -- * Polygon Type
    Polygon(Polygon)
  , mkPolygon
  , mkPolygonUnsafe
  , vertices
  , vertexCount
  
  -- * Measurements
  , signedArea
  , area
  , perimeter
  , centroid
  
  -- * Properties
  , isConvex
  , isClockwise
  , windingOrder
  , WindingOrder(..)
  
  -- * Point Operations
  , contains
  
  -- * Constructors
  , triangle
  , rectangle
  , regularPolygon
  
  -- * Transformations
  , translatePolygon
  , reverseWinding
  , rotatePolygon
  , scalePolygon
  , reflectX
  , reflectY
  
  -- * Comparison
  , compareByVertexCount
  , compareByArea
  , sameVertexCount
  
  -- * Edge Operations
  , edges
  , lastVertex
  , interiorAngleSum
  
  -- * Display
  , showPolygon
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering
  , (>)
  , (>=)
  , (<=)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (&&)
  , (||)
  , (==)
  , (/=)
  , compare
  , show
  , negate
  , not
  , map
  , otherwise
  )

import Data.Array (length, (!!), zipWith, foldl, reverse, snoc, head, last)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Number (pi, cos, sin, abs)
import Data.Int (toNumber)

import Hydrogen.Schema.Geometry.Point 
  ( Point2D(Point2D)
  , point2D
  , getX
  , getY
  , distance2D
  , translate2D
  )

import Hydrogen.Schema.Geometry.Angle
  ( Degrees(Degrees)
  , toRadians
  , unwrapRadians
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // polygon type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Winding order of polygon vertices.
data WindingOrder
  = CounterClockwise  -- ^ Standard mathematical convention
  | Clockwise         -- ^ Screen coordinates convention

derive instance eqWindingOrder :: Eq WindingOrder
derive instance ordWindingOrder :: Ord WindingOrder

instance showWindingOrder :: Show WindingOrder where
  show CounterClockwise = "CounterClockwise"
  show Clockwise = "Clockwise"

-- | Polygon molecule.
-- |
-- | A closed shape defined by 3 or more vertices.
-- | Vertices are stored in order (winding determined by signed area).
newtype Polygon = Polygon (Array Point2D)

derive instance eqPolygon :: Eq Polygon
derive instance ordPolygon :: Ord Polygon

instance showPolygonInstance :: Show Polygon where
  show (Polygon pts) = "(Polygon " <> show pts <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a polygon with validation.
-- |
-- | Returns Nothing if fewer than 3 vertices provided.
mkPolygon :: Array Point2D -> Maybe Polygon
mkPolygon pts =
  if length pts >= 3
  then Just (Polygon pts)
  else Nothing

-- | Create a polygon without validation.
-- |
-- | WARNING: Only use when at least 3 vertices are guaranteed.
mkPolygonUnsafe :: Array Point2D -> Polygon
mkPolygonUnsafe pts = Polygon pts

-- | Get the vertices of the polygon.
vertices :: Polygon -> Array Point2D
vertices (Polygon pts) = pts

-- | Get the number of vertices.
vertexCount :: Polygon -> Int
vertexCount (Polygon pts) = length pts

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // measurements
-- ═════════════════════════════════════════════════════════════════════════════

-- | Signed area using the shoelace formula.
-- |
-- | Positive for counter-clockwise, negative for clockwise winding.
-- | A = 1/2 × Σ(x_i × y_{i+1} - x_{i+1} × y_i)
signedArea :: Polygon -> Number
signedArea (Polygon pts) =
  let n = length pts
      sumTerms = foldl (\acc i -> acc + crossTerm i) 0.0 (range 0 (n - 1))
  in sumTerms / 2.0
  where
    crossTerm :: Int -> Number
    crossTerm i =
      let n = length pts
          p1 = fromMaybe (point2D 0.0 0.0) (pts !! i)
          p2 = fromMaybe (point2D 0.0 0.0) (pts !! ((i + 1) `mod` n))
      in getX p1 * getY p2 - getX p2 * getY p1
    
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod :: Int -> Int -> Int
    mod a b = a - (a / b) * b

-- | Absolute area of the polygon.
area :: Polygon -> Number
area p = abs (signedArea p)

-- | Perimeter of the polygon.
-- |
-- | Sum of all edge lengths.
perimeter :: Polygon -> Number
perimeter (Polygon pts) =
  let n = length pts
  in foldl (\acc i -> acc + edgeLength i) 0.0 (range 0 (n - 1))
  where
    edgeLength :: Int -> Number
    edgeLength i =
      let n = length pts
          p1 = fromMaybe (point2D 0.0 0.0) (pts !! i)
          p2 = fromMaybe (point2D 0.0 0.0) (pts !! ((i + 1) `mod` n))
      in distance2D p1 p2
    
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod :: Int -> Int -> Int
    mod a b = a - (a / b) * b

-- | Centroid (geometric center) of the polygon.
-- |
-- | Weighted average of vertices based on triangle areas.
centroid :: Polygon -> Point2D
centroid poly@(Polygon pts) =
  let a = signedArea poly
      n = length pts
      sumX = foldl (\acc i -> acc + centroidTermX i) 0.0 (range 0 (n - 1))
      sumY = foldl (\acc i -> acc + centroidTermY i) 0.0 (range 0 (n - 1))
      factor = 1.0 / (6.0 * a)
  in point2D (factor * sumX) (factor * sumY)
  where
    centroidTermX :: Int -> Number
    centroidTermX i =
      let n = length pts
          p1 = fromMaybe (point2D 0.0 0.0) (pts !! i)
          p2 = fromMaybe (point2D 0.0 0.0) (pts !! ((i + 1) `mod` n))
          cross = getX p1 * getY p2 - getX p2 * getY p1
      in (getX p1 + getX p2) * cross
    
    centroidTermY :: Int -> Number
    centroidTermY i =
      let n = length pts
          p1 = fromMaybe (point2D 0.0 0.0) (pts !! i)
          p2 = fromMaybe (point2D 0.0 0.0) (pts !! ((i + 1) `mod` n))
          cross = getX p1 * getY p2 - getX p2 * getY p1
      in (getY p1 + getY p2) * cross
    
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod :: Int -> Int -> Int
    mod a b = a - (a / b) * b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if polygon is convex.
-- |
-- | A polygon is convex if all cross products of consecutive edges
-- | have the same sign.
isConvex :: Polygon -> Boolean
isConvex (Polygon pts) =
  let n = length pts
      signs = map (crossSign pts n) (range 0 (n - 1))
      firstSign = fromMaybe 0.0 (head signs)
  in foldl (\acc s -> acc && sameSign firstSign s) true signs
  where
    crossSign :: Array Point2D -> Int -> Int -> Number
    crossSign arr n i =
      let p1 = fromMaybe (point2D 0.0 0.0) (arr !! i)
          p2 = fromMaybe (point2D 0.0 0.0) (arr !! ((i + 1) `mod` n))
          p3 = fromMaybe (point2D 0.0 0.0) (arr !! ((i + 2) `mod` n))
          dx1 = getX p2 - getX p1
          dy1 = getY p2 - getY p1
          dx2 = getX p3 - getX p2
          dy2 = getY p3 - getY p2
      in dx1 * dy2 - dy1 * dx2
    
    sameSign :: Number -> Number -> Boolean
    sameSign a b = (a >= 0.0 && b >= 0.0) || (a <= 0.0 && b <= 0.0)
    
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod :: Int -> Int -> Int
    mod a b = a - (a / b) * b

-- | Check if polygon has clockwise winding.
isClockwise :: Polygon -> Boolean
isClockwise p = signedArea p < 0.0

-- | Get the winding order of the polygon.
windingOrder :: Polygon -> WindingOrder
windingOrder p =
  if signedArea p >= 0.0
  then CounterClockwise
  else Clockwise

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // point operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a point is inside the polygon.
-- |
-- | Uses ray casting algorithm: count edge crossings.
-- | Odd number of crossings = inside.
contains :: Point2D -> Polygon -> Boolean
contains (Point2D p) (Polygon pts) =
  let n = length pts
  in foldl (\acc i -> if crossesRay i then not acc else acc) false (range 0 (n - 1))
  where
    crossesRay :: Int -> Boolean
    crossesRay i =
      let n = length pts
          Point2D v1 = fromMaybe (point2D 0.0 0.0) (pts !! i)
          Point2D v2 = fromMaybe (point2D 0.0 0.0) (pts !! ((i + 1) `mod` n))
          -- Check if ray from point crosses this edge
          cond1 = (v1.y > p.y) /= (v2.y > p.y)
          slope = (v2.x - v1.x) * (p.y - v1.y) / (v2.y - v1.y) + v1.x
          cond2 = p.x < slope
      in cond1 && cond2
    
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod :: Int -> Int -> Int
    mod a b = a - (a / b) * b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // shape constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a triangle from three points.
triangle :: Point2D -> Point2D -> Point2D -> Polygon
triangle p1 p2 p3 = Polygon [p1, p2, p3]

-- | Create a rectangle from center, width, and height.
-- |
-- | Vertices in counter-clockwise order starting from bottom-left.
rectangle :: Point2D -> Number -> Number -> Polygon
rectangle (Point2D center) width height =
  let hw = width / 2.0
      hh = height / 2.0
      bl = point2D (center.x - hw) (center.y - hh)
      br = point2D (center.x + hw) (center.y - hh)
      tr = point2D (center.x + hw) (center.y + hh)
      tl = point2D (center.x - hw) (center.y + hh)
  in Polygon [bl, br, tr, tl]

-- | Create a regular n-sided polygon.
-- |
-- | Centered at given point with given radius (center to vertex).
-- | First vertex at angle 0 (positive X direction).
regularPolygon :: Int -> Point2D -> Number -> Polygon
regularPolygon sides (Point2D center) radius =
  let n = if sides < 3 then 3 else sides
      angleStep = 2.0 * pi / toNumber n
      makeVertex i =
        let angle = toNumber i * angleStep
            x = center.x + radius * cos angle
            y = center.y + radius * sin angle
        in point2D x y
  in Polygon (map makeVertex (range 0 (n - 1)))
  where
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate all vertices by offset.
translatePolygon :: Number -> Number -> Polygon -> Polygon
translatePolygon dx dy (Polygon pts) =
  Polygon (map (translate2D dx dy) pts)

-- | Reverse the winding order of vertices.
-- |
-- | Clockwise becomes counter-clockwise and vice versa.
reverseWinding :: Polygon -> Polygon
reverseWinding (Polygon pts) = Polygon (reverse pts)

-- | Rotate all vertices around a center point.
-- |
-- | Uses trigonometric rotation formula.
rotatePolygon :: Degrees -> Point2D -> Polygon -> Polygon
rotatePolygon angle (Point2D center) (Polygon pts) =
  let rad = unwrapRadians (toRadians angle)
      cosA = cos rad
      sinA = sin rad
      rotatePoint (Point2D p) =
        let dx = p.x - center.x
            dy = p.y - center.y
            x' = dx * cosA - dy * sinA + center.x
            y' = dx * sinA + dy * cosA + center.y
        in point2D x' y'
  in Polygon (map rotatePoint pts)

-- | Scale all vertices relative to a center point.
scalePolygon :: Number -> Point2D -> Polygon -> Polygon
scalePolygon factor (Point2D center) (Polygon pts) =
  let scalePoint (Point2D p) =
        let dx = p.x - center.x
            dy = p.y - center.y
            x' = center.x + dx * factor
            y' = center.y + dy * factor
        in point2D x' y'
  in Polygon (map scalePoint pts)

-- | Reflect polygon across the X axis (negate Y coordinates).
reflectX :: Polygon -> Polygon
reflectX (Polygon pts) =
  let reflectPoint (Point2D p) = point2D p.x (negate p.y)
  in Polygon (map reflectPoint pts)

-- | Reflect polygon across the Y axis (negate X coordinates).
reflectY :: Polygon -> Polygon
reflectY (Polygon pts) =
  let reflectPoint (Point2D p) = point2D (negate p.x) p.y
  in Polygon (map reflectPoint pts)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compare polygons by vertex count.
compareByVertexCount :: Polygon -> Polygon -> Ordering
compareByVertexCount p1 p2 = compare (vertexCount p1) (vertexCount p2)

-- | Compare polygons by area.
compareByArea :: Polygon -> Polygon -> Ordering
compareByArea p1 p2 = compare (area p1) (area p2)

-- | Check if two polygons have the same number of vertices.
sameVertexCount :: Polygon -> Polygon -> Boolean
sameVertexCount p1 p2 = vertexCount p1 == vertexCount p2

-- | Get pairs of consecutive edges as vertex pairs.
-- |
-- | Uses zipWith to pair each vertex with the next.
edges :: Polygon -> Array { start :: Point2D, end :: Point2D }
edges (Polygon pts) =
  let n = length pts
      shifted = map (\i -> fromMaybe (point2D 0.0 0.0) (pts !! ((i + 1) `mod` n))) (range 0 (n - 1))
  in zipWith (\s e -> { start: s, end: e }) pts shifted
  where
    range :: Int -> Int -> Array Int
    range start end = rangeHelper start end []
    
    rangeHelper :: Int -> Int -> Array Int -> Array Int
    rangeHelper cur end acc
      | cur > end = acc
      | otherwise = rangeHelper (cur + 1) end (snoc acc cur)
    
    mod :: Int -> Int -> Int
    mod a b = a - (a / b) * b

-- | Get the last vertex of the polygon.
lastVertex :: Polygon -> Maybe Point2D
lastVertex (Polygon pts) = last pts

-- | Calculate the interior angle sum for a polygon.
-- |
-- | For an n-sided polygon: (n-2) × 180°
interiorAngleSum :: Polygon -> Degrees
interiorAngleSum p =
  let n = vertexCount p
  in Degrees (toNumber (n - 2) * 180.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // display
-- ═════════════════════════════════════════════════════════════════════════════

-- | Format polygon for display.
-- |
-- | Shows vertex count and winding order.
showPolygon :: Polygon -> String
showPolygon p =
  let n = vertexCount p
      w = windingOrder p
  in "Polygon { vertices: " <> show n <> ", winding: " <> show w <> " }"
