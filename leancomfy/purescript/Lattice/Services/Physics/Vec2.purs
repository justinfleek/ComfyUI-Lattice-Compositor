-- | Lattice.Services.Physics.Vec2 - 2D Vector Mathematics
-- |
-- | Pure mathematical functions for 2D vector operations:
-- | - Vector creation and cloning
-- | - Addition, subtraction, scaling
-- | - Length, normalization
-- | - Dot product, cross product
-- | - Rotation, perpendicular
-- | - Linear interpolation
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts (vec2 object)

module Lattice.Services.Physics.Vec2
  ( Vec2(..)
  , vec2
  , vec2Zero
  , add
  , sub
  , scale
  , negate'
  , length'
  , lengthSq
  , normalize
  , safeNormalize
  , dot
  , cross
  , perpendicular
  , rotate
  , lerp
  , distance
  , distanceSq
  ) where

import Prelude

import Math (cos, sin, sqrt, max)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D vector with x and y components
type Vec2 =
  { x :: Number
  , y :: Number
  }

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Create a new vector
vec2 :: Number -> Number -> Vec2
vec2 x y = { x, y }

-- | Zero vector
vec2Zero :: Vec2
vec2Zero = { x: 0.0, y: 0.0 }

--------------------------------------------------------------------------------
-- Arithmetic
--------------------------------------------------------------------------------

-- | Add two vectors
add :: Vec2 -> Vec2 -> Vec2
add a b = { x: a.x + b.x, y: a.y + b.y }

-- | Subtract two vectors
sub :: Vec2 -> Vec2 -> Vec2
sub a b = { x: a.x - b.x, y: a.y - b.y }

-- | Scale a vector by a scalar
scale :: Number -> Vec2 -> Vec2
scale s v = { x: v.x * s, y: v.y * s }

-- | Negate a vector
negate' :: Vec2 -> Vec2
negate' v = { x: -v.x, y: -v.y }

--------------------------------------------------------------------------------
-- Length and Normalization
--------------------------------------------------------------------------------

-- | Calculate vector length (magnitude)
length' :: Vec2 -> Number
length' v = sqrt (v.x * v.x + v.y * v.y)

-- | Calculate squared length (avoids sqrt for comparisons)
lengthSq :: Vec2 -> Number
lengthSq v = v.x * v.x + v.y * v.y

-- | Normalize vector to unit length.
-- Returns zero vector if input has zero length.
normalize :: Vec2 -> Vec2
normalize v =
  let len = length' v
  in if len < 0.000001
     then vec2Zero
     else { x: v.x / len, y: v.y / len }

-- | Safe normalize with custom default for zero vectors
safeNormalize :: Vec2 -> Vec2 -> Vec2
safeNormalize defaultVec v =
  let len = length' v
  in if len < 0.000001
     then defaultVec
     else { x: v.x / len, y: v.y / len }

--------------------------------------------------------------------------------
-- Products
--------------------------------------------------------------------------------

-- | Dot product of two vectors
dot :: Vec2 -> Vec2 -> Number
dot a b = a.x * b.x + a.y * b.y

-- | 2D cross product (returns scalar - z component of 3D cross)
cross :: Vec2 -> Vec2 -> Number
cross a b = a.x * b.y - a.y * b.x

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

-- | Get perpendicular vector (90 degree rotation)
perpendicular :: Vec2 -> Vec2
perpendicular v = { x: -v.y, y: v.x }

-- | Rotate vector by angle (in radians)
rotate :: Number -> Vec2 -> Vec2
rotate angle v =
  let cosA = cos angle
      sinA = sin angle
  in { x: v.x * cosA - v.y * sinA
     , y: v.x * sinA + v.y * cosA
     }

-- | Linear interpolation between two vectors
lerp :: Vec2 -> Vec2 -> Number -> Vec2
lerp a b t =
  { x: a.x + (b.x - a.x) * t
  , y: a.y + (b.y - a.y) * t
  }

--------------------------------------------------------------------------------
-- Distance
--------------------------------------------------------------------------------

-- | Distance between two points
distance :: Vec2 -> Vec2 -> Number
distance a b = length' (sub b a)

-- | Squared distance between two points
distanceSq :: Vec2 -> Vec2 -> Number
distanceSq a b = lengthSq (sub b a)
