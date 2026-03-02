{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Physics.Vec2
Description : 2D Vector Mathematics for Physics Simulation
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for 2D vector operations:
- Vector creation and cloning
- Addition, subtraction, scaling
- Length, normalization
- Dot product, cross product
- Rotation, perpendicular
- Linear interpolation

All functions are total and deterministic.

Source: ui/src/services/physics/PhysicsEngine.ts (vec2 object)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.Vec2
  ( -- * Types
    Vec2(..)
    -- * Construction
  , vec2
  , vec2Zero
  , clone
    -- * Arithmetic
  , add
  , sub
  , scale
  , negate'
    -- * Length and Normalization
  , length'
  , lengthSq
  , normalize
  , safeNormalize
    -- * Products
  , dot
  , cross
    -- * Transformations
  , perpendicular
  , rotate
  , lerp
    -- * Distance
  , distance
  , distanceSq
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D vector with x and y components
data Vec2 = Vec2
  { vX :: Double
  , vY :: Double
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Construction
--------------------------------------------------------------------------------

-- | Create a new vector
vec2 :: Double -> Double -> Vec2
vec2 = Vec2

-- | Zero vector
vec2Zero :: Vec2
vec2Zero = Vec2 0 0

-- | Clone a vector (identity in pure functional code)
clone :: Vec2 -> Vec2
clone (Vec2 x y) = Vec2 x y

--------------------------------------------------------------------------------
-- Arithmetic
--------------------------------------------------------------------------------

-- | Add two vectors
add :: Vec2 -> Vec2 -> Vec2
add (Vec2 ax ay) (Vec2 bx by) = Vec2 (ax + bx) (ay + by)

-- | Subtract two vectors
sub :: Vec2 -> Vec2 -> Vec2
sub (Vec2 ax ay) (Vec2 bx by) = Vec2 (ax - bx) (ay - by)

-- | Scale a vector by a scalar
scale :: Double -> Vec2 -> Vec2
scale s (Vec2 x y) = Vec2 (x * s) (y * s)

-- | Negate a vector
negate' :: Vec2 -> Vec2
negate' (Vec2 x y) = Vec2 (-x) (-y)

--------------------------------------------------------------------------------
-- Length and Normalization
--------------------------------------------------------------------------------

-- | Calculate vector length (magnitude)
length' :: Vec2 -> Double
length' (Vec2 x y) = sqrt (x * x + y * y)

-- | Calculate squared length (avoids sqrt for comparisons)
lengthSq :: Vec2 -> Double
lengthSq (Vec2 x y) = x * x + y * y

-- | Normalize vector to unit length.
-- Returns zero vector if input has zero length.
normalize :: Vec2 -> Vec2
normalize v =
  let len = length' v
  in if len < 0.000001
     then vec2Zero
     else Vec2 (vX v / len) (vY v / len)

-- | Safe normalize with custom default for zero vectors
safeNormalize :: Vec2 -> Vec2 -> Vec2
safeNormalize defaultVec v =
  let len = length' v
  in if len < 0.000001
     then defaultVec
     else Vec2 (vX v / len) (vY v / len)

--------------------------------------------------------------------------------
-- Products
--------------------------------------------------------------------------------

-- | Dot product of two vectors
dot :: Vec2 -> Vec2 -> Double
dot (Vec2 ax ay) (Vec2 bx by) = ax * bx + ay * by

-- | 2D cross product (returns scalar - z component of 3D cross)
cross :: Vec2 -> Vec2 -> Double
cross (Vec2 ax ay) (Vec2 bx by) = ax * by - ay * bx

--------------------------------------------------------------------------------
-- Transformations
--------------------------------------------------------------------------------

-- | Get perpendicular vector (90 degree rotation)
perpendicular :: Vec2 -> Vec2
perpendicular (Vec2 x y) = Vec2 (-y) x

-- | Rotate vector by angle (in radians)
rotate :: Double -> Vec2 -> Vec2
rotate angle (Vec2 x y) =
  let cosA = cos angle
      sinA = sin angle
  in Vec2 (x * cosA - y * sinA) (x * sinA + y * cosA)

-- | Linear interpolation between two vectors
lerp :: Vec2 -> Vec2 -> Double -> Vec2
lerp (Vec2 ax ay) (Vec2 bx by) t =
  Vec2 (ax + (bx - ax) * t) (ay + (by - ay) * t)

--------------------------------------------------------------------------------
-- Distance
--------------------------------------------------------------------------------

-- | Distance between two points
distance :: Vec2 -> Vec2 -> Double
distance a b = length' (sub b a)

-- | Squared distance between two points
distanceSq :: Vec2 -> Vec2 -> Double
distanceSq a b = lengthSq (sub b a)
