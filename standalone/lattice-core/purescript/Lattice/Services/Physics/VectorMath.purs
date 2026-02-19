-- | Lattice.Services.Physics.VectorMath - 2D Vector Math Operations
-- |
-- | Pure mathematical functions for 2D vector operations used in physics
-- | simulation. All operations are deterministic and side-effect free.
-- |
-- | Operations:
-- | - Basic: add, sub, scale, negate
-- | - Products: dot, cross (2D pseudo-cross)
-- | - Metrics: length, lengthSq, distance, distanceSq
-- | - Normalization and rotation
-- | - Interpolation: lerp
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts

module Lattice.Services.Physics.VectorMath
  ( Vec2
  , zero
  , create
  , clone
  , add
  , sub
  , scale
  , negate
  , dot
  , cross
  , lengthSq
  , vecLength
  , distanceSq
  , distance
  , normalize
  , perpendicular
  , rotate
  , lerp
  , project
  , reflect
  , angle
  , angleBetween
  ) where

import Prelude

import Math (atan2, acos, cos, sin, sqrt)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D Vector for physics calculations
type Vec2 =
  { x :: Number
  , y :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a zero vector
zero :: Vec2
zero = { x: 0.0, y: 0.0 }

-- | Create a vector from components
create :: Number -> Number -> Vec2
create x y = { x, y }

-- | Clone a vector (identity, for API compatibility)
clone :: Vec2 -> Vec2
clone v = { x: v.x, y: v.y }

-- ────────────────────────────────────────────────────────────────────────────
-- Basic Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Vector addition
add :: Vec2 -> Vec2 -> Vec2
add a b = { x: a.x + b.x, y: a.y + b.y }

-- | Vector subtraction
sub :: Vec2 -> Vec2 -> Vec2
sub a b = { x: a.x - b.x, y: a.y - b.y }

-- | Scalar multiplication
scale :: Vec2 -> Number -> Vec2
scale v s = { x: v.x * s, y: v.y * s }

-- | Vector negation
negate :: Vec2 -> Vec2
negate v = { x: 0.0 - v.x, y: 0.0 - v.y }

-- ────────────────────────────────────────────────────────────────────────────
-- Products
-- ────────────────────────────────────────────────────────────────────────────

-- | Dot product of two vectors
dot :: Vec2 -> Vec2 -> Number
dot a b = a.x * b.x + a.y * b.y

-- | 2D cross product (pseudo-cross, returns scalar).
-- |
-- | This is the Z component of the 3D cross product with z=0.
-- | Geometrically: |a| * |b| * sin(angle from a to b)
cross :: Vec2 -> Vec2 -> Number
cross a b = a.x * b.y - a.y * b.x

-- ────────────────────────────────────────────────────────────────────────────
-- Metrics
-- ────────────────────────────────────────────────────────────────────────────

-- | Squared length of a vector (avoids sqrt)
lengthSq :: Vec2 -> Number
lengthSq v = v.x * v.x + v.y * v.y

-- | Length (magnitude) of a vector
vecLength :: Vec2 -> Number
vecLength v = sqrt (lengthSq v)

-- | Squared distance between two points (avoids sqrt)
distanceSq :: Vec2 -> Vec2 -> Number
distanceSq a b = lengthSq (sub b a)

-- | Distance between two points
distance :: Vec2 -> Vec2 -> Number
distance a b = vecLength (sub b a)

-- ────────────────────────────────────────────────────────────────────────────
-- Normalization
-- ────────────────────────────────────────────────────────────────────────────

-- | Normalize a vector to unit length.
-- |
-- | Returns zero vector if input has zero length.
normalize :: Vec2 -> Vec2
normalize v =
  let len = vecLength v
  in if len < 0.0001
     then zero
     else { x: v.x / len, y: v.y / len }

-- ────────────────────────────────────────────────────────────────────────────
-- Perpendicular and Rotation
-- ────────────────────────────────────────────────────────────────────────────

-- | Get perpendicular vector (90 degrees counter-clockwise).
-- |
-- | For (x, y), returns (-y, x).
perpendicular :: Vec2 -> Vec2
perpendicular v = { x: 0.0 - v.y, y: v.x }

-- | Rotate vector by angle (in radians).
-- |
-- | Uses rotation matrix:
-- | ```
-- | [cos θ  -sin θ] [x]
-- | [sin θ   cos θ] [y]
-- | ```
rotate :: Vec2 -> Number -> Vec2
rotate v ang =
  let c = cos ang
      s = sin ang
  in { x: v.x * c - v.y * s, y: v.x * s + v.y * c }

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation between two vectors.
-- |
-- | Returns: a + (b - a) * t
lerp :: Vec2 -> Vec2 -> Number -> Vec2
lerp a b t =
  { x: a.x + (b.x - a.x) * t
  , y: a.y + (b.y - a.y) * t }

-- ────────────────────────────────────────────────────────────────────────────
-- Projection
-- ────────────────────────────────────────────────────────────────────────────

-- | Project vector a onto vector b.
-- |
-- | Returns component of a in the direction of b.
project :: Vec2 -> Vec2 -> Vec2
project a b =
  let bLenSq = lengthSq b
  in if bLenSq < 0.0001
     then zero
     else let scalar = dot a b / bLenSq
          in scale b scalar

-- | Reflect vector v off a surface with normal n.
reflect :: Vec2 -> Vec2 -> Vec2
reflect v n =
  let dotVN = dot v n
  in sub v (scale n (2.0 * dotVN))

-- ────────────────────────────────────────────────────────────────────────────
-- Angle Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Get angle of vector from positive x-axis (in radians).
angle :: Vec2 -> Number
angle v = atan2 v.y v.x

-- | Get angle between two vectors (in radians).
-- |
-- | Returns 0 if either vector has zero length.
angleBetween :: Vec2 -> Vec2 -> Number
angleBetween a b =
  let lenA = vecLength a
      lenB = vecLength b
  in if lenA < 0.0001 || lenB < 0.0001
     then 0.0
     else let cosAng = dot a b / (lenA * lenB)
              clamped = max (0.0 - 1.0) (min 1.0 cosAng)
          in acos clamped
