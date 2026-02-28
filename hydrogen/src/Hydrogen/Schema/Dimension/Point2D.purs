-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // dimension // point2d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Point2D — X and Y coordinate for 2D positions.
-- |
-- | **WHY POINT2D?**
-- | Point2D represents a position in 2D space:
-- | - X coordinate (horizontal position)
-- | - Y coordinate (vertical position)
-- |
-- | Unlike Vec2 which represents direction/displacement, Point2D represents
-- | a specific location. Unlike Size2D, coordinates can be negative.
-- |
-- | **Use cases:**
-- | - Element position (left: 100px, top: 50px)
-- | - Click/touch coordinates
-- | - Anchor points
-- | - Transform origins
-- |
-- | **Coordinate systems:**
-- | - Screen/CSS: Origin at top-left, Y increases downward
-- | - Cartesian: Origin at center, Y increases upward
-- | - Normalized: Coordinates in 0.0-1.0 range

module Hydrogen.Schema.Dimension.Point2D
  ( -- * Types
    Point2D(Point2D)
  
  -- * Constructors
  , point2D
  , point2DFromRecord
  , origin
  
  -- * Accessors
  , x
  , y
  , toRecord
  
  -- * Operations
  , add
  , subtract
  , scale
  , negate
  , distance
  , distanceSquared
  , midpoint
  , lerp
  
  -- * Transformations
  , translate
  , translateX
  , translateY
  , reflectX
  , reflectY
  , reflectOrigin
  
  -- * Predicates
  , isOrigin
  , isEqual
  , isInBounds
  
  -- * Conversion
  , toVec2
  , fromVec2
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , otherwise
  , (&&)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (<=)
  , (>=)
  , (==)
  , (<>)
  )

import Data.Number (sqrt) as Num
import Hydrogen.Schema.Dimension.Vector.Vec2 (Vec2(Vec2))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // point2d
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D point with x and y coordinates.
-- |
-- | Represents a position in 2D space. Coordinates can be negative.
data Point2D = Point2D Number Number

derive instance eqPoint2D :: Eq Point2D
derive instance ordPoint2D :: Ord Point2D

instance showPoint2D :: Show Point2D where
  show (Point2D px py) = "Point2D(" <> show px <> ", " <> show py <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a Point2D from x and y coordinates.
-- |
-- | ```purescript
-- | point2D 100.0 50.0  -- position at (100, 50)
-- | ```
point2D :: Number -> Number -> Point2D
point2D = Point2D

-- | Create from a record.
point2DFromRecord :: { x :: Number, y :: Number } -> Point2D
point2DFromRecord { x: px, y: py } = Point2D px py

-- | The origin point (0, 0).
origin :: Point2D
origin = Point2D 0.0 0.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get x coordinate.
x :: Point2D -> Number
x (Point2D px _) = px

-- | Get y coordinate.
y :: Point2D -> Number
y (Point2D _ py) = py

-- | Convert to record.
toRecord :: Point2D -> { x :: Number, y :: Number }
toRecord (Point2D px py) = { x: px, y: py }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two points (component-wise).
-- |
-- | Semantically: translate p1 by the displacement represented by p2.
add :: Point2D -> Point2D -> Point2D
add (Point2D x1 y1) (Point2D x2 y2) = Point2D (x1 + x2) (y1 + y2)

-- | Subtract points (component-wise).
-- |
-- | `subtract p1 p2` = displacement from p2 to p1.
subtract :: Point2D -> Point2D -> Point2D
subtract (Point2D x1 y1) (Point2D x2 y2) = Point2D (x1 - x2) (y1 - y2)

-- | Scale point by a factor (from origin).
scale :: Number -> Point2D -> Point2D
scale factor (Point2D px py) = Point2D (px * factor) (py * factor)

-- | Negate coordinates (reflect through origin).
negate :: Point2D -> Point2D
negate (Point2D px py) = Point2D (0.0 - px) (0.0 - py)

-- | Calculate Euclidean distance between two points.
distance :: Point2D -> Point2D -> Number
distance p1 p2 = Num.sqrt (distanceSquared p1 p2)

-- | Calculate squared distance (avoids sqrt for comparisons).
distanceSquared :: Point2D -> Point2D -> Number
distanceSquared (Point2D x1 y1) (Point2D x2 y2) =
  let dx = x2 - x1
      dy = y2 - y1
  in dx * dx + dy * dy

-- | Calculate midpoint between two points.
midpoint :: Point2D -> Point2D -> Point2D
midpoint (Point2D x1 y1) (Point2D x2 y2) =
  Point2D ((x1 + x2) / 2.0) ((y1 + y2) / 2.0)

-- | Linear interpolation between two points.
-- |
-- | `lerp p1 p2 0.0` = p1
-- | `lerp p1 p2 1.0` = p2
-- | `lerp p1 p2 0.5` = midpoint
lerp :: Point2D -> Point2D -> Number -> Point2D
lerp (Point2D x1 y1) (Point2D x2 y2) t =
  let t' = clamp01 t
      px = x1 + (x2 - x1) * t'
      py = y1 + (y2 - y1) * t'
  in Point2D px py

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // transformations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate point by dx and dy.
translate :: Number -> Number -> Point2D -> Point2D
translate dx dy (Point2D px py) = Point2D (px + dx) (py + dy)

-- | Translate only in x direction.
translateX :: Number -> Point2D -> Point2D
translateX dx (Point2D px py) = Point2D (px + dx) py

-- | Translate only in y direction.
translateY :: Number -> Point2D -> Point2D
translateY dy (Point2D px py) = Point2D px (py + dy)

-- | Reflect across Y axis (negate x).
reflectX :: Point2D -> Point2D
reflectX (Point2D px py) = Point2D (0.0 - px) py

-- | Reflect across X axis (negate y).
reflectY :: Point2D -> Point2D
reflectY (Point2D px py) = Point2D px (0.0 - py)

-- | Reflect through origin (negate both).
reflectOrigin :: Point2D -> Point2D
reflectOrigin = negate

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if point is at origin.
isOrigin :: Point2D -> Boolean
isOrigin (Point2D px py) = px == 0.0 && py == 0.0

-- | Check if two points are equal.
isEqual :: Point2D -> Point2D -> Boolean
isEqual (Point2D x1 y1) (Point2D x2 y2) = x1 == x2 && y1 == y2

-- | Check if point is within rectangular bounds.
-- |
-- | `isInBounds minPt maxPt pt` returns true if pt is within the rectangle
-- | defined by minPt (bottom-left) and maxPt (top-right).
isInBounds :: Point2D -> Point2D -> Point2D -> Boolean
isInBounds (Point2D minX minY) (Point2D maxX maxY) (Point2D px py) =
  px >= minX && px <= maxX && py >= minY && py <= maxY

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Point2D to Vec2.
-- |
-- | Semantically: treat point as a position vector from origin.
toVec2 :: Point2D -> Vec2 Number
toVec2 (Point2D px py) = Vec2 px py

-- | Convert Vec2 to Point2D.
-- |
-- | Semantically: treat vector as a position from origin.
fromVec2 :: Vec2 Number -> Point2D
fromVec2 (Vec2 vx vy) = Point2D vx vy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // internal
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp to 0.0-1.0
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n <= 1.0 = n
  | otherwise = 1.0
