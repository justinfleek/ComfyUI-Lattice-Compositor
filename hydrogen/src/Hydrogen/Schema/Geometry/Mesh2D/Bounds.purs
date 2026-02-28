-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // geometry // mesh2d // bounds
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Mesh2D axis-aligned bounding box types and operations.
-- |
-- | ## Types
-- |
-- | - `Bounds2D`: Axis-aligned bounding box (min/max corners)
-- |
-- | ## Operations
-- |
-- | - Construction: `bounds2D`, `boundsEmpty`, `boundsFromPoints`
-- | - Queries: `boundsCenter`, `boundsSize`, `boundsContains`, `boundsIntersects`
-- | - Expansion: `expandBoundsWithPoint`

module Hydrogen.Schema.Geometry.Mesh2D.Bounds
  ( -- * Types
    Bounds2D(Bounds2D)
  
  -- * Construction
  , bounds2D
  , boundsEmpty
  , boundsFromPoints
  
  -- * Queries
  , boundsCenter
  , boundsSize
  , boundsContains
  , boundsIntersects
  
  -- * Operations
  , expandBoundsWithPoint
  
  -- * Accessors
  , getMinX
  , getMinY
  , getMaxX
  , getMaxY
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (/)
  , (<>)
  , (>=)
  , (<=)
  , (&&)
  )

import Data.Array (length, index)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // bounds2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis-aligned bounding box in 2D.
-- |
-- | Represents a rectangular region defined by minimum and maximum corners.
-- | Used for spatial queries, culling, and containment tests.
newtype Bounds2D = Bounds2D
  { minX :: Number
  , minY :: Number
  , maxX :: Number
  , maxY :: Number
  }

derive instance eqBounds2D :: Eq Bounds2D

instance showBounds2D :: Show Bounds2D where
  show (Bounds2D b) = "(Bounds2D minX:" <> show b.minX <> " minY:" <> show b.minY
    <> " maxX:" <> show b.maxX <> " maxY:" <> show b.maxY <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create bounds from min/max coordinates.
-- |
-- | Automatically swaps values if min > max.
bounds2D :: Number -> Number -> Number -> Number -> Bounds2D
bounds2D minX' minY' maxX' maxY' = Bounds2D
  { minX: if minX' <= maxX' then minX' else maxX'
  , minY: if minY' <= maxY' then minY' else maxY'
  , maxX: if maxX' >= minX' then maxX' else minX'
  , maxY: if maxY' >= minY' then maxY' else minY'
  }

-- | Empty bounds (inverted, will expand on first point).
-- |
-- | Uses very large numbers as sentinel values.
-- | Any point added will properly initialize the bounds.
boundsEmpty :: Bounds2D
boundsEmpty = Bounds2D
  { minX: infinity
  , minY: infinity
  , maxX: negInfinity
  , maxY: negInfinity
  }
  where
    infinity = 1.0e308
    negInfinity = -1.0e308

-- | Compute bounds from array of points.
-- |
-- | Returns empty bounds if array is empty.
boundsFromPoints :: Array Point2D -> Bounds2D
boundsFromPoints points = foldlArray expandBoundsWithPoint boundsEmpty points

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get center point of bounds.
boundsCenter :: Bounds2D -> Point2D
boundsCenter (Bounds2D b) = point2D
  ((b.minX + b.maxX) / 2.0)
  ((b.minY + b.maxY) / 2.0)

-- | Get size as width and height.
boundsSize :: Bounds2D -> { width :: Number, height :: Number }
boundsSize (Bounds2D b) =
  { width: b.maxX - b.minX
  , height: b.maxY - b.minY
  }

-- | Check if bounds contains a point.
boundsContains :: Point2D -> Bounds2D -> Boolean
boundsContains (Point2D p) (Bounds2D b) =
  p.x >= b.minX && p.x <= b.maxX &&
  p.y >= b.minY && p.y <= b.maxY

-- | Check if two bounds intersect.
boundsIntersects :: Bounds2D -> Bounds2D -> Boolean
boundsIntersects (Bounds2D a) (Bounds2D b) =
  a.minX <= b.maxX && a.maxX >= b.minX &&
  a.minY <= b.maxY && a.maxY >= b.minY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Expand bounds to include a point.
expandBoundsWithPoint :: Bounds2D -> Point2D -> Bounds2D
expandBoundsWithPoint (Bounds2D b) (Point2D p) = Bounds2D
  { minX: minNumber b.minX p.x
  , minY: minNumber b.minY p.y
  , maxX: maxNumber b.maxX p.x
  , maxY: maxNumber b.maxY p.y
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get minimum X coordinate.
getMinX :: Bounds2D -> Number
getMinX (Bounds2D b) = b.minX

-- | Get minimum Y coordinate.
getMinY :: Bounds2D -> Number
getMinY (Bounds2D b) = b.minY

-- | Get maximum X coordinate.
getMaxX :: Bounds2D -> Number
getMaxX (Bounds2D b) = b.maxX

-- | Get maximum Y coordinate.
getMaxY :: Bounds2D -> Number
getMaxY (Bounds2D b) = b.maxY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fold left over array.
foldlArray :: forall a b. (b -> a -> b) -> b -> Array a -> b
foldlArray f initial arr = foldlArrayImpl f initial arr 0 (length arr)

foldlArrayImpl :: forall a b. (b -> a -> b) -> b -> Array a -> Int -> Int -> b
foldlArrayImpl f acc arr idx len =
  if idx >= len
    then acc
    else case index arr idx of
      Nothing -> acc
      Just x -> foldlArrayImpl f (f acc x) arr (idx + 1) len

-- | Minimum of two numbers.
minNumber :: Number -> Number -> Number
minNumber a b = if a <= b then a else b

-- | Maximum of two numbers.
maxNumber :: Number -> Number -> Number
maxNumber a b = if a >= b then a else b
