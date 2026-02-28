-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // geometry // vector
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vector — 2D and 3D displacement/direction atoms.
-- |
-- | ## Design Philosophy
-- |
-- | Vectors represent displacement, direction, or velocity — NOT position.
-- | The distinction from Point is fundamental:
-- |
-- | - **Point**: "Where am I?" — a location in space
-- | - **Vector**: "Which way and how far?" — a displacement
-- |
-- | Operations that make sense:
-- | - Vector + Vector = Vector (displacements combine)
-- | - Point + Vector = Point (translate a position)
-- | - Point - Point = Vector (displacement between positions)
-- | - Vector × Scalar = Vector (scale a displacement)
-- |
-- | Operations that DON'T make sense:
-- | - Point + Point = ??? (adding locations is meaningless)
-- |
-- | ## Use Cases
-- |
-- | - Motion/velocity: "moving at 5 units/second in direction (0.7, 0.7)"
-- | - Forces: "gravity pulls with force (0, -9.8, 0)"
-- | - Normals: "this surface faces direction (0, 1, 0)"
-- | - Gradients: "color changes fastest in direction (1, 0)"
-- | - Camera: "looking toward (-1, 0, -1)"
-- |
-- | ## Dependencies
-- |
-- | - Prelude (Eq, Ord, Show, Semiring, Ring)
-- | - Data.Number (sqrt, trig)
-- | - Schema.Geometry.Point (point-vector operations)
-- | - Schema.Geometry.Angle (direction angles)

module Hydrogen.Schema.Geometry.Vector
  ( -- * 2D Vectors
    Vector2D(Vector2D)
  , vec2
  , zeroVec2
  , getVX
  , getVY
  
  -- * 3D Vectors
  , Vector3D(Vector3D)
  , vec3
  , zeroVec3
  , getVX3
  , getVY3
  , getVZ3
  
  -- * 2D Operations
  , addVec2
  , subVec2
  , scaleVec2
  , negateVec2
  , magnitude2
  , magnitudeSquared2
  , normalize2
  , dot2
  , cross2
  , perpendicular2
  , perpendicularCW2
  , angle2
  , angleBetween2
  , rotate2
  , lerp2
  , project2
  , reflect2
  
  -- * 3D Operations
  , addVec3
  , subVec3
  , scaleVec3
  , negateVec3
  , magnitude3
  , magnitudeSquared3
  , normalize3
  , dot3
  , cross3
  , angleBetween3
  , lerp3
  , project3
  , reflect3
  , rotateX3
  , rotateY3
  , rotateZ3
  
  -- * Point-Vector Operations
  , translatePoint2
  , translatePoint3
  , pointDiff2
  , pointDiff3
  , directionTo2
  , directionTo3
  
  -- * Common Vectors
  , right2
  , left2
  , up2
  , down2
  , right3
  , left3
  , up3
  , down3
  , forward3
  , backward3
  
  -- * Queries
  , isZero2
  , isZero3
  , isUnit2
  , isUnit3
  , areParallel2
  , areParallel3
  , arePerpendicular2
  , arePerpendicular3
  
  -- * Conversion
  , toVec3
  , toVec2
  , fromAngle
  , toAngle
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , class Semiring
  , class Ring
  , show
  , negate
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  , (>)
  )

import Data.Number (sqrt, abs, sin, cos, acos, atan2, pi)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), Point3D(Point3D))
import Hydrogen.Schema.Geometry.Angle (Degrees, Radians, degrees, radians, unwrapDegrees, unwrapRadians)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // 2d vectors
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 2D vector (displacement/direction).
-- |
-- | Components are unbounded — vectors can have any magnitude.
newtype Vector2D = Vector2D { x :: Number, y :: Number }

derive instance eqVector2D :: Eq Vector2D
derive instance ordVector2D :: Ord Vector2D

instance showVector2D :: Show Vector2D where
  show (Vector2D v) = "(Vector2D " <> show v.x <> " " <> show v.y <> ")"

instance semiringVector2D :: Semiring Vector2D where
  add = addVec2
  mul (Vector2D a) (Vector2D b) = Vector2D { x: a.x * b.x, y: a.y * b.y }
  zero = zeroVec2
  one = Vector2D { x: 1.0, y: 1.0 }

instance ringVector2D :: Ring Vector2D where
  sub = subVec2

-- | Create a 2D vector
vec2 :: Number -> Number -> Vector2D
vec2 x y = Vector2D { x, y }

-- | Zero vector (no displacement)
zeroVec2 :: Vector2D
zeroVec2 = Vector2D { x: 0.0, y: 0.0 }

-- | Get X component
getVX :: Vector2D -> Number
getVX (Vector2D v) = v.x

-- | Get Y component
getVY :: Vector2D -> Number
getVY (Vector2D v) = v.y

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // 3d vectors
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 3D vector (displacement/direction).
-- |
-- | Right-handed coordinate system:
-- | - X: positive to the right
-- | - Y: positive upward  
-- | - Z: positive toward viewer
newtype Vector3D = Vector3D { x :: Number, y :: Number, z :: Number }

derive instance eqVector3D :: Eq Vector3D
derive instance ordVector3D :: Ord Vector3D

instance showVector3D :: Show Vector3D where
  show (Vector3D v) = "(Vector3D " <> show v.x <> " " <> show v.y <> " " <> show v.z <> ")"

instance semiringVector3D :: Semiring Vector3D where
  add = addVec3
  mul (Vector3D a) (Vector3D b) = Vector3D { x: a.x * b.x, y: a.y * b.y, z: a.z * b.z }
  zero = zeroVec3
  one = Vector3D { x: 1.0, y: 1.0, z: 1.0 }

instance ringVector3D :: Ring Vector3D where
  sub = subVec3

-- | Create a 3D vector
vec3 :: Number -> Number -> Number -> Vector3D
vec3 x y z = Vector3D { x, y, z }

-- | Zero vector
zeroVec3 :: Vector3D
zeroVec3 = Vector3D { x: 0.0, y: 0.0, z: 0.0 }

-- | Get X component
getVX3 :: Vector3D -> Number
getVX3 (Vector3D v) = v.x

-- | Get Y component
getVY3 :: Vector3D -> Number
getVY3 (Vector3D v) = v.y

-- | Get Z component
getVZ3 :: Vector3D -> Number
getVZ3 (Vector3D v) = v.z

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // 2d operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two vectors
addVec2 :: Vector2D -> Vector2D -> Vector2D
addVec2 (Vector2D a) (Vector2D b) = Vector2D { x: a.x + b.x, y: a.y + b.y }

-- | Subtract vectors (a - b)
subVec2 :: Vector2D -> Vector2D -> Vector2D
subVec2 (Vector2D a) (Vector2D b) = Vector2D { x: a.x - b.x, y: a.y - b.y }

-- | Scale vector by scalar
scaleVec2 :: Number -> Vector2D -> Vector2D
scaleVec2 s (Vector2D v) = Vector2D { x: v.x * s, y: v.y * s }

-- | Negate vector (reverse direction)
negateVec2 :: Vector2D -> Vector2D
negateVec2 (Vector2D v) = Vector2D { x: negate v.x, y: negate v.y }

-- | Magnitude (length) of vector
magnitude2 :: Vector2D -> Number
magnitude2 v = sqrt (magnitudeSquared2 v)

-- | Squared magnitude (avoids sqrt)
magnitudeSquared2 :: Vector2D -> Number
magnitudeSquared2 (Vector2D v) = v.x * v.x + v.y * v.y

-- | Normalize to unit length.
-- | Returns zero vector if input is zero.
normalize2 :: Vector2D -> Vector2D
normalize2 v =
  let mag = magnitude2 v
  in if mag < epsilon
       then zeroVec2
       else scaleVec2 (1.0 / mag) v

-- | Dot product
dot2 :: Vector2D -> Vector2D -> Number
dot2 (Vector2D a) (Vector2D b) = a.x * b.x + a.y * b.y

-- | 2D cross product (returns scalar — z component of 3D cross)
-- |
-- | Useful for determining winding order and signed area.
cross2 :: Vector2D -> Vector2D -> Number
cross2 (Vector2D a) (Vector2D b) = a.x * b.y - a.y * b.x

-- | Perpendicular vector (90° counter-clockwise)
perpendicular2 :: Vector2D -> Vector2D
perpendicular2 (Vector2D v) = Vector2D { x: negate v.y, y: v.x }

-- | Perpendicular vector (90° clockwise)
perpendicularCW2 :: Vector2D -> Vector2D
perpendicularCW2 (Vector2D v) = Vector2D { x: v.y, y: negate v.x }

-- | Angle of vector from positive X axis
angle2 :: Vector2D -> Degrees
angle2 (Vector2D v) = degrees (atan2 v.y v.x * 180.0 / pi)

-- | Angle between two vectors
angleBetween2 :: Vector2D -> Vector2D -> Degrees
angleBetween2 a b =
  let
    d = dot2 a b
    m1 = magnitude2 a
    m2 = magnitude2 b
    denom = m1 * m2
  in
    if denom < epsilon
      then degrees 0.0
      else degrees (acos (clampNeg1to1 (d / denom)) * 180.0 / pi)

-- | Rotate vector by angle
rotate2 :: Degrees -> Vector2D -> Vector2D
rotate2 deg (Vector2D v) =
  let
    r = unwrapRadians (toRadians deg)
    c = cos r
    s = sin r
  in
    Vector2D { x: v.x * c - v.y * s, y: v.x * s + v.y * c }

-- | Linear interpolation
lerp2 :: Number -> Vector2D -> Vector2D -> Vector2D
lerp2 t (Vector2D a) (Vector2D b) =
  Vector2D
    { x: a.x + (b.x - a.x) * t
    , y: a.y + (b.y - a.y) * t
    }

-- | Project vector a onto vector b
project2 :: Vector2D -> Vector2D -> Vector2D
project2 a b =
  let d = dot2 a b
      bMagSq = magnitudeSquared2 b
  in if bMagSq < epsilon
       then zeroVec2
       else scaleVec2 (d / bMagSq) b

-- | Reflect vector off surface with given normal
reflect2 :: Vector2D -> Vector2D -> Vector2D
reflect2 incident normal =
  let d = dot2 incident normal
  in subVec2 incident (scaleVec2 (2.0 * d) normal)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // 3d operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two 3D vectors
addVec3 :: Vector3D -> Vector3D -> Vector3D
addVec3 (Vector3D a) (Vector3D b) =
  Vector3D { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

-- | Subtract 3D vectors
subVec3 :: Vector3D -> Vector3D -> Vector3D
subVec3 (Vector3D a) (Vector3D b) =
  Vector3D { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z }

-- | Scale 3D vector
scaleVec3 :: Number -> Vector3D -> Vector3D
scaleVec3 s (Vector3D v) = Vector3D { x: v.x * s, y: v.y * s, z: v.z * s }

-- | Negate 3D vector
negateVec3 :: Vector3D -> Vector3D
negateVec3 (Vector3D v) = Vector3D { x: negate v.x, y: negate v.y, z: negate v.z }

-- | Magnitude of 3D vector
magnitude3 :: Vector3D -> Number
magnitude3 v = sqrt (magnitudeSquared3 v)

-- | Squared magnitude
magnitudeSquared3 :: Vector3D -> Number
magnitudeSquared3 (Vector3D v) = v.x * v.x + v.y * v.y + v.z * v.z

-- | Normalize 3D vector
normalize3 :: Vector3D -> Vector3D
normalize3 v =
  let mag = magnitude3 v
  in if mag < epsilon
       then zeroVec3
       else scaleVec3 (1.0 / mag) v

-- | 3D dot product
dot3 :: Vector3D -> Vector3D -> Number
dot3 (Vector3D a) (Vector3D b) = a.x * b.x + a.y * b.y + a.z * b.z

-- | 3D cross product
-- |
-- | Produces vector perpendicular to both inputs.
-- | Right-hand rule: a × b points in direction of curled fingers
-- | when rotating from a toward b.
cross3 :: Vector3D -> Vector3D -> Vector3D
cross3 (Vector3D a) (Vector3D b) =
  Vector3D
    { x: a.y * b.z - a.z * b.y
    , y: a.z * b.x - a.x * b.z
    , z: a.x * b.y - a.y * b.x
    }

-- | Angle between 3D vectors
angleBetween3 :: Vector3D -> Vector3D -> Degrees
angleBetween3 a b =
  let
    d = dot3 a b
    m1 = magnitude3 a
    m2 = magnitude3 b
    denom = m1 * m2
  in
    if denom < epsilon
      then degrees 0.0
      else degrees (acos (clampNeg1to1 (d / denom)) * 180.0 / pi)

-- | Linear interpolation 3D
lerp3 :: Number -> Vector3D -> Vector3D -> Vector3D
lerp3 t (Vector3D a) (Vector3D b) =
  Vector3D
    { x: a.x + (b.x - a.x) * t
    , y: a.y + (b.y - a.y) * t
    , z: a.z + (b.z - a.z) * t
    }

-- | Project 3D vector a onto b
project3 :: Vector3D -> Vector3D -> Vector3D
project3 a b =
  let d = dot3 a b
      bMagSq = magnitudeSquared3 b
  in if bMagSq < epsilon
       then zeroVec3
       else scaleVec3 (d / bMagSq) b

-- | Reflect 3D vector off surface
reflect3 :: Vector3D -> Vector3D -> Vector3D
reflect3 incident normal =
  let d = dot3 incident normal
  in subVec3 incident (scaleVec3 (2.0 * d) normal)

-- | Rotate around X axis
rotateX3 :: Degrees -> Vector3D -> Vector3D
rotateX3 deg (Vector3D v) =
  let
    r = unwrapRadians (toRadians deg)
    c = cos r
    s = sin r
  in
    Vector3D { x: v.x, y: v.y * c - v.z * s, z: v.y * s + v.z * c }

-- | Rotate around Y axis
rotateY3 :: Degrees -> Vector3D -> Vector3D
rotateY3 deg (Vector3D v) =
  let
    r = unwrapRadians (toRadians deg)
    c = cos r
    s = sin r
  in
    Vector3D { x: v.x * c + v.z * s, y: v.y, z: negate v.x * s + v.z * c }

-- | Rotate around Z axis
rotateZ3 :: Degrees -> Vector3D -> Vector3D
rotateZ3 deg (Vector3D v) =
  let
    r = unwrapRadians (toRadians deg)
    c = cos r
    s = sin r
  in
    Vector3D { x: v.x * c - v.y * s, y: v.x * s + v.y * c, z: v.z }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // point-vector operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate point by vector
translatePoint2 :: Vector2D -> Point2D -> Point2D
translatePoint2 (Vector2D v) (Point2D p) =
  Point2D { x: p.x + v.x, y: p.y + v.y }

-- | Translate 3D point by vector
translatePoint3 :: Vector3D -> Point3D -> Point3D
translatePoint3 (Vector3D v) (Point3D p) =
  Point3D { x: p.x + v.x, y: p.y + v.y, z: p.z + v.z }

-- | Vector from point a to point b
pointDiff2 :: Point2D -> Point2D -> Vector2D
pointDiff2 (Point2D a) (Point2D b) =
  Vector2D { x: b.x - a.x, y: b.y - a.y }

-- | Vector from 3D point a to point b
pointDiff3 :: Point3D -> Point3D -> Vector3D
pointDiff3 (Point3D a) (Point3D b) =
  Vector3D { x: b.x - a.x, y: b.y - a.y, z: b.z - a.z }

-- | Unit vector pointing from a toward b
directionTo2 :: Point2D -> Point2D -> Vector2D
directionTo2 a b = normalize2 (pointDiff2 a b)

-- | Unit vector pointing from 3D point a toward b
directionTo3 :: Point3D -> Point3D -> Vector3D
directionTo3 a b = normalize3 (pointDiff3 a b)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // common vectors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unit vector pointing right (+X)
right2 :: Vector2D
right2 = Vector2D { x: 1.0, y: 0.0 }

-- | Unit vector pointing left (-X)
left2 :: Vector2D
left2 = Vector2D { x: -1.0, y: 0.0 }

-- | Unit vector pointing up (+Y)
up2 :: Vector2D
up2 = Vector2D { x: 0.0, y: 1.0 }

-- | Unit vector pointing down (-Y)
down2 :: Vector2D
down2 = Vector2D { x: 0.0, y: -1.0 }

-- | 3D unit right (+X)
right3 :: Vector3D
right3 = Vector3D { x: 1.0, y: 0.0, z: 0.0 }

-- | 3D unit left (-X)
left3 :: Vector3D
left3 = Vector3D { x: -1.0, y: 0.0, z: 0.0 }

-- | 3D unit up (+Y)
up3 :: Vector3D
up3 = Vector3D { x: 0.0, y: 1.0, z: 0.0 }

-- | 3D unit down (-Y)
down3 :: Vector3D
down3 = Vector3D { x: 0.0, y: -1.0, z: 0.0 }

-- | 3D unit forward (+Z, toward viewer)
forward3 :: Vector3D
forward3 = Vector3D { x: 0.0, y: 0.0, z: 1.0 }

-- | 3D unit backward (-Z, away from viewer)
backward3 :: Vector3D
backward3 = Vector3D { x: 0.0, y: 0.0, z: -1.0 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is zero vector?
isZero2 :: Vector2D -> Boolean
isZero2 v = magnitudeSquared2 v < epsilon

-- | Is 3D zero vector?
isZero3 :: Vector3D -> Boolean
isZero3 v = magnitudeSquared3 v < epsilon

-- | Is unit length?
isUnit2 :: Vector2D -> Boolean
isUnit2 v = abs (magnitude2 v - 1.0) < epsilon

-- | Is 3D unit length?
isUnit3 :: Vector3D -> Boolean
isUnit3 v = abs (magnitude3 v - 1.0) < epsilon

-- | Are vectors parallel (same or opposite direction)?
areParallel2 :: Vector2D -> Vector2D -> Boolean
areParallel2 a b = abs (cross2 a b) < epsilon

-- | Are 3D vectors parallel?
areParallel3 :: Vector3D -> Vector3D -> Boolean
areParallel3 a b =
  let c = cross3 a b
  in magnitudeSquared3 c < epsilon

-- | Are vectors perpendicular?
arePerpendicular2 :: Vector2D -> Vector2D -> Boolean
arePerpendicular2 a b = abs (dot2 a b) < epsilon

-- | Are 3D vectors perpendicular?
arePerpendicular3 :: Vector3D -> Vector3D -> Boolean
arePerpendicular3 a b = abs (dot3 a b) < epsilon

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert 2D vector to 3D (z = 0)
toVec3 :: Vector2D -> Vector3D
toVec3 (Vector2D v) = Vector3D { x: v.x, y: v.y, z: 0.0 }

-- | Convert 3D vector to 2D (drop z)
toVec2 :: Vector3D -> Vector2D
toVec2 (Vector3D v) = Vector2D { x: v.x, y: v.y }

-- | Create unit vector from angle (measured from +X axis)
fromAngle :: Degrees -> Vector2D
fromAngle deg =
  let r = unwrapRadians (toRadians deg)
  in Vector2D { x: cos r, y: sin r }

-- | Get angle of vector (from +X axis)
toAngle :: Vector2D -> Degrees
toAngle = angle2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert degrees to radians (internal helper)
toRadians :: Degrees -> Radians
toRadians d = radians (unwrapDegrees d * pi / 180.0)

-- | Small value for comparisons
epsilon :: Number
epsilon = 0.0000001

-- | Clamp to [-1, 1] for acos safety
clampNeg1to1 :: Number -> Number
clampNeg1to1 n
  | n < -1.0 = -1.0
  | n > 1.0 = 1.0
  | true = n
