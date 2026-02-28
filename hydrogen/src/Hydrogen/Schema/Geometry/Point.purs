-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // point
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Point — 2D and 3D coordinate molecules for spatial positioning.
-- |
-- | ## Design Philosophy
-- |
-- | Points represent positions in space. They are NOT vectors — a point is
-- | a location, while a vector is a displacement. The distinction matters:
-- |
-- | - Points can be translated by vectors
-- | - Vectors can be added/subtracted
-- | - Points CANNOT be meaningfully added (what does "New York + Paris" mean?)
-- |
-- | This module provides both 2D and 3D points with proper operations.
-- |
-- | ## Coordinate Systems
-- |
-- | - **2D**: X (right), Y (down in screen coordinates, up in math coordinates)
-- | - **3D**: X (right), Y (up), Z (toward viewer) — right-handed system
-- |
-- | Screen coordinates (Y-down) vs mathematical coordinates (Y-up) are handled
-- | at the rendering layer, not here. Points are abstract positions.
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Semiring, Ring)
-- | - Data.Number (sqrt for distance)
-- |
-- | ## Dependents
-- |
-- | - Schema.Geometry.Shape (vertices, centers)
-- | - Schema.Geometry.Vector (vector operations)
-- | - Schema.Geometry.Transform (translation targets)
-- | - Component.Canvas (drawing coordinates)
-- | - Component.Signature (path points)

module Hydrogen.Schema.Geometry.Point
  ( -- * 2D Points
    Point2D(Point2D)
  , point2D
  , origin2D
  , getX
  , getY
  , setX
  , setY
  , withX
  , withY
  
  -- * 3D Points
  , Point3D(Point3D)
  , point3D
  , origin3D
  , getX3
  , getY3
  , getZ3
  , setX3
  , setY3
  , setZ3
  , withX3
  , withY3
  , withZ3
  
  -- * Conversions
  , to3D
  , to2D
  , project
  
  -- * 2D Operations
  , translate2D
  , midpoint2D
  , distance2D
  , distanceSquared2D
  , lerp2D
  , reflect2D
  , reflectX2D
  , reflectY2D
  
  -- * 3D Operations
  , translate3D
  , midpoint3D
  , distance3D
  , distanceSquared3D
  , lerp3D
  , reflect3D
  , reflectX3D
  , reflectY3D
  , reflectZ3D
  
  -- * Common Points
  , unitX2D
  , unitY2D
  , unitX3D
  , unitY3D
  , unitZ3D
  
  -- * Comparison
  , isOrigin2D
  , isOrigin3D
  , areCollinear2D
  , areCollinear3D
  
  -- * CSS Conversion
  , toLegacyCss2D
  , toTranslate2D
  , toTranslate3D
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (&&)
  , (<)
  , (>)
  )

import Data.Number (sqrt, abs)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // 2d points
-- ═════════════════════════════════════════════════════════════════════════════

-- | A point in 2D space.
-- |
-- | Coordinates are unbounded Numbers — points can be anywhere in the plane.
newtype Point2D = Point2D { x :: Number, y :: Number }

derive instance eqPoint2D :: Eq Point2D
derive instance ordPoint2D :: Ord Point2D

instance showPoint2D :: Show Point2D where
  show (Point2D p) = "(Point2D " <> show p.x <> " " <> show p.y <> ")"

-- | Create a 2D point
point2D :: Number -> Number -> Point2D
point2D x y = Point2D { x, y }

-- | The origin (0, 0)
origin2D :: Point2D
origin2D = Point2D { x: 0.0, y: 0.0 }

-- | Get X coordinate
getX :: Point2D -> Number
getX (Point2D p) = p.x

-- | Get Y coordinate
getY :: Point2D -> Number
getY (Point2D p) = p.y

-- | Set X coordinate
setX :: Number -> Point2D -> Point2D
setX x (Point2D p) = Point2D { x, y: p.y }

-- | Set Y coordinate
setY :: Number -> Point2D -> Point2D
setY y (Point2D p) = Point2D { x: p.x, y }

-- | Modify X coordinate with function
withX :: (Number -> Number) -> Point2D -> Point2D
withX f (Point2D p) = Point2D { x: f p.x, y: p.y }

-- | Modify Y coordinate with function
withY :: (Number -> Number) -> Point2D -> Point2D
withY f (Point2D p) = Point2D { x: p.x, y: f p.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // 3d points
-- ═════════════════════════════════════════════════════════════════════════════

-- | A point in 3D space.
-- |
-- | Uses right-handed coordinate system:
-- | - X: positive to the right
-- | - Y: positive upward
-- | - Z: positive toward the viewer
newtype Point3D = Point3D { x :: Number, y :: Number, z :: Number }

derive instance eqPoint3D :: Eq Point3D
derive instance ordPoint3D :: Ord Point3D

instance showPoint3D :: Show Point3D where
  show (Point3D p) = "(Point3D " <> show p.x <> " " <> show p.y <> " " <> show p.z <> ")"

-- | Create a 3D point
point3D :: Number -> Number -> Number -> Point3D
point3D x y z = Point3D { x, y, z }

-- | The 3D origin (0, 0, 0)
origin3D :: Point3D
origin3D = Point3D { x: 0.0, y: 0.0, z: 0.0 }

-- | Get X coordinate
getX3 :: Point3D -> Number
getX3 (Point3D p) = p.x

-- | Get Y coordinate
getY3 :: Point3D -> Number
getY3 (Point3D p) = p.y

-- | Get Z coordinate
getZ3 :: Point3D -> Number
getZ3 (Point3D p) = p.z

-- | Set X coordinate
setX3 :: Number -> Point3D -> Point3D
setX3 x (Point3D p) = Point3D { x, y: p.y, z: p.z }

-- | Set Y coordinate
setY3 :: Number -> Point3D -> Point3D
setY3 y (Point3D p) = Point3D { x: p.x, y, z: p.z }

-- | Set Z coordinate
setZ3 :: Number -> Point3D -> Point3D
setZ3 z (Point3D p) = Point3D { x: p.x, y: p.y, z }

-- | Modify X coordinate with function
withX3 :: (Number -> Number) -> Point3D -> Point3D
withX3 f (Point3D p) = Point3D { x: f p.x, y: p.y, z: p.z }

-- | Modify Y coordinate with function
withY3 :: (Number -> Number) -> Point3D -> Point3D
withY3 f (Point3D p) = Point3D { x: p.x, y: f p.y, z: p.z }

-- | Modify Z coordinate with function
withZ3 :: (Number -> Number) -> Point3D -> Point3D
withZ3 f (Point3D p) = Point3D { x: p.x, y: p.y, z: f p.z }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // conversions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert 2D point to 3D (z = 0)
to3D :: Point2D -> Point3D
to3D (Point2D p) = Point3D { x: p.x, y: p.y, z: 0.0 }

-- | Convert 3D point to 2D (drop z)
to2D :: Point3D -> Point2D
to2D (Point3D p) = Point2D { x: p.x, y: p.y }

-- | Project 3D point to 2D using simple perspective.
-- |
-- | Uses focal length for perspective division.
-- | Points with z <= 0 are clamped to avoid division issues.
project :: Number -> Point3D -> Point2D
project focalLength (Point3D p) =
  let
    -- Clamp z to positive to avoid division by zero or negative
    z' = if p.z > 0.0 then p.z else 0.001
    scale = focalLength / (focalLength + z')
  in
    Point2D { x: p.x * scale, y: p.y * scale }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 2d operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate a 2D point by dx and dy
translate2D :: Number -> Number -> Point2D -> Point2D
translate2D dx dy (Point2D p) = Point2D { x: p.x + dx, y: p.y + dy }

-- | Midpoint between two 2D points
midpoint2D :: Point2D -> Point2D -> Point2D
midpoint2D (Point2D a) (Point2D b) =
  Point2D { x: (a.x + b.x) / 2.0, y: (a.y + b.y) / 2.0 }

-- | Euclidean distance between two 2D points
distance2D :: Point2D -> Point2D -> Number
distance2D a b = sqrt (distanceSquared2D a b)

-- | Squared distance (avoids sqrt for comparisons)
distanceSquared2D :: Point2D -> Point2D -> Number
distanceSquared2D (Point2D a) (Point2D b) =
  let
    dx = b.x - a.x
    dy = b.y - a.y
  in
    dx * dx + dy * dy

-- | Linear interpolation between two 2D points.
-- |
-- | `t` in [0, 1]: t=0 returns `from`, t=1 returns `to`
lerp2D :: Number -> Point2D -> Point2D -> Point2D
lerp2D t (Point2D from) (Point2D to) =
  Point2D
    { x: from.x + (to.x - from.x) * t
    , y: from.y + (to.y - from.y) * t
    }

-- | Reflect point through another point (center of reflection)
reflect2D :: Point2D -> Point2D -> Point2D
reflect2D (Point2D center) (Point2D p) =
  Point2D
    { x: 2.0 * center.x - p.x
    , y: 2.0 * center.y - p.y
    }

-- | Reflect point through X axis (negate Y)
reflectX2D :: Point2D -> Point2D
reflectX2D (Point2D p) = Point2D { x: p.x, y: negate p.y }

-- | Reflect point through Y axis (negate X)
reflectY2D :: Point2D -> Point2D
reflectY2D (Point2D p) = Point2D { x: negate p.x, y: p.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // 3d operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate a 3D point by dx, dy, dz
translate3D :: Number -> Number -> Number -> Point3D -> Point3D
translate3D dx dy dz (Point3D p) =
  Point3D { x: p.x + dx, y: p.y + dy, z: p.z + dz }

-- | Midpoint between two 3D points
midpoint3D :: Point3D -> Point3D -> Point3D
midpoint3D (Point3D a) (Point3D b) =
  Point3D
    { x: (a.x + b.x) / 2.0
    , y: (a.y + b.y) / 2.0
    , z: (a.z + b.z) / 2.0
    }

-- | Euclidean distance between two 3D points
distance3D :: Point3D -> Point3D -> Number
distance3D a b = sqrt (distanceSquared3D a b)

-- | Squared distance (avoids sqrt for comparisons)
distanceSquared3D :: Point3D -> Point3D -> Number
distanceSquared3D (Point3D a) (Point3D b) =
  let
    dx = b.x - a.x
    dy = b.y - a.y
    dz = b.z - a.z
  in
    dx * dx + dy * dy + dz * dz

-- | Linear interpolation between two 3D points.
lerp3D :: Number -> Point3D -> Point3D -> Point3D
lerp3D t (Point3D from) (Point3D to) =
  Point3D
    { x: from.x + (to.x - from.x) * t
    , y: from.y + (to.y - from.y) * t
    , z: from.z + (to.z - from.z) * t
    }

-- | Reflect point through another point (center of reflection)
reflect3D :: Point3D -> Point3D -> Point3D
reflect3D (Point3D center) (Point3D p) =
  Point3D
    { x: 2.0 * center.x - p.x
    , y: 2.0 * center.y - p.y
    , z: 2.0 * center.z - p.z
    }

-- | Reflect point through XZ plane (negate Y)
reflectX3D :: Point3D -> Point3D
reflectX3D (Point3D p) = Point3D { x: p.x, y: negate p.y, z: p.z }

-- | Reflect point through YZ plane (negate X)
reflectY3D :: Point3D -> Point3D
reflectY3D (Point3D p) = Point3D { x: negate p.x, y: p.y, z: p.z }

-- | Reflect point through XY plane (negate Z)
reflectZ3D :: Point3D -> Point3D
reflectZ3D (Point3D p) = Point3D { x: p.x, y: p.y, z: negate p.z }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // common points
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unit point on X axis (1, 0)
unitX2D :: Point2D
unitX2D = Point2D { x: 1.0, y: 0.0 }

-- | Unit point on Y axis (0, 1)
unitY2D :: Point2D
unitY2D = Point2D { x: 0.0, y: 1.0 }

-- | Unit point on X axis (1, 0, 0)
unitX3D :: Point3D
unitX3D = Point3D { x: 1.0, y: 0.0, z: 0.0 }

-- | Unit point on Y axis (0, 1, 0)
unitY3D :: Point3D
unitY3D = Point3D { x: 0.0, y: 1.0, z: 0.0 }

-- | Unit point on Z axis (0, 0, 1)
unitZ3D :: Point3D
unitZ3D = Point3D { x: 0.0, y: 0.0, z: 1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // comparison
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this the origin?
isOrigin2D :: Point2D -> Boolean
isOrigin2D (Point2D p) = p.x == 0.0 && p.y == 0.0

-- | Is this the 3D origin?
isOrigin3D :: Point3D -> Boolean
isOrigin3D (Point3D p) = p.x == 0.0 && p.y == 0.0 && p.z == 0.0

-- | Are three points collinear (on the same line)?
-- |
-- | Uses cross product — if zero (within epsilon), points are collinear.
areCollinear2D :: Point2D -> Point2D -> Point2D -> Boolean
areCollinear2D (Point2D a) (Point2D b) (Point2D c) =
  let
    -- Cross product of vectors AB and AC
    cross = (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)
  in
    abs cross < epsilon

-- | Are three 3D points collinear?
-- |
-- | Uses magnitude of cross product of direction vectors.
areCollinear3D :: Point3D -> Point3D -> Point3D -> Boolean
areCollinear3D (Point3D a) (Point3D b) (Point3D c) =
  let
    -- Vector AB
    abx = b.x - a.x
    aby = b.y - a.y
    abz = b.z - a.z
    -- Vector AC
    acx = c.x - a.x
    acy = c.y - a.y
    acz = c.z - a.z
    -- Cross product AB × AC
    cx = aby * acz - abz * acy
    cy = abz * acx - abx * acz
    cz = abx * acy - aby * acx
    -- Magnitude squared of cross product
    magSq = cx * cx + cy * cy + cz * cz
  in
    magSq < epsilon * epsilon

-- | Small value for floating point comparisons
epsilon :: Number
epsilon = 0.0000001

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // css conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert 2D point to CSS coordinate string
toLegacyCss2D :: Point2D -> String
toLegacyCss2D (Point2D p) = show p.x <> "px " <> show p.y <> "px"

-- | Convert 2D point to CSS translate() transform
toTranslate2D :: Point2D -> String
toTranslate2D (Point2D p) =
  "translate(" <> show p.x <> "px, " <> show p.y <> "px)"

-- | Convert 3D point to CSS translate3d() transform
toTranslate3D :: Point3D -> String
toTranslate3D (Point3D p) =
  "translate3d(" <> show p.x <> "px, " <> show p.y <> "px, " <> show p.z <> "px)"
