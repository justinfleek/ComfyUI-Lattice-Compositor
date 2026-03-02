{-|
Module      : Lattice.Services.Physics.VectorMath
Description : 2D Vector Math Operations
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for 2D vector operations used in physics
simulation. All operations are deterministic and side-effect free.

Operations:
- Basic: add, sub, scale, negate
- Products: dot, cross (2D pseudo-cross)
- Metrics: length, lengthSq, distance, distanceSq
- Normalization and rotation
- Interpolation: lerp

Source: ui/src/services/physics/PhysicsEngine.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.VectorMath
  ( -- * Types
    Vec2(..)
    -- * Constructors
  , zero
  , create
  , clone
    -- * Basic Operations
  , add
  , sub
  , scale
  , negate'
    -- * Products
  , dot
  , cross
    -- * Metrics
  , lengthSq
  , vecLength
  , distanceSq
  , distance
    -- * Normalization
  , normalize
    -- * Perpendicular and Rotation
  , perpendicular
  , rotate
    -- * Interpolation
  , lerp
    -- * Projection
  , project
  , reflect
    -- * Angle Operations
  , angle
  , angleBetween
  ) where

import Prelude hiding (negate)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D Vector for physics calculations
data Vec2 = Vec2
  { vx :: Double  -- ^ X component
  , vy :: Double  -- ^ Y component
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a zero vector
zero :: Vec2
zero = Vec2 0 0

-- | Create a vector from components
create :: Double -> Double -> Vec2
create = Vec2

-- | Clone a vector (identity, for API compatibility)
clone :: Vec2 -> Vec2
clone (Vec2 x y) = Vec2 x y

-- ────────────────────────────────────────────────────────────────────────────
-- Basic Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Vector addition
add :: Vec2 -> Vec2 -> Vec2
add (Vec2 x1 y1) (Vec2 x2 y2) = Vec2 (x1 + x2) (y1 + y2)

-- | Vector subtraction
sub :: Vec2 -> Vec2 -> Vec2
sub (Vec2 x1 y1) (Vec2 x2 y2) = Vec2 (x1 - x2) (y1 - y2)

-- | Scalar multiplication
scale :: Vec2 -> Double -> Vec2
scale (Vec2 x y) s = Vec2 (x * s) (y * s)

-- | Vector negation (named negate' to avoid conflict with Prelude)
negate' :: Vec2 -> Vec2
negate' (Vec2 x y) = Vec2 (-x) (-y)

-- ────────────────────────────────────────────────────────────────────────────
-- Products
-- ────────────────────────────────────────────────────────────────────────────

-- | Dot product of two vectors
dot :: Vec2 -> Vec2 -> Double
dot (Vec2 x1 y1) (Vec2 x2 y2) = x1 * x2 + y1 * y2

-- | 2D cross product (pseudo-cross, returns scalar).
--
-- This is the Z component of the 3D cross product with z=0.
-- Geometrically: |a| * |b| * sin(angle from a to b)
cross :: Vec2 -> Vec2 -> Double
cross (Vec2 x1 y1) (Vec2 x2 y2) = x1 * y2 - y1 * x2

-- ────────────────────────────────────────────────────────────────────────────
-- Metrics
-- ────────────────────────────────────────────────────────────────────────────

-- | Squared length of a vector (avoids sqrt)
lengthSq :: Vec2 -> Double
lengthSq (Vec2 x y) = x * x + y * y

-- | Length (magnitude) of a vector
vecLength :: Vec2 -> Double
vecLength = sqrt . lengthSq

-- | Squared distance between two points (avoids sqrt)
distanceSq :: Vec2 -> Vec2 -> Double
distanceSq a b = lengthSq (sub b a)

-- | Distance between two points
distance :: Vec2 -> Vec2 -> Double
distance a b = vecLength (sub b a)

-- ────────────────────────────────────────────────────────────────────────────
-- Normalization
-- ────────────────────────────────────────────────────────────────────────────

-- | Normalize a vector to unit length.
--
-- Returns zero vector if input has zero length.
normalize :: Vec2 -> Vec2
normalize v =
  let len = vecLength v
  in if len < 0.0001
     then zero
     else Vec2 (vx v / len) (vy v / len)

-- ────────────────────────────────────────────────────────────────────────────
-- Perpendicular and Rotation
-- ────────────────────────────────────────────────────────────────────────────

-- | Get perpendicular vector (90 degrees counter-clockwise).
--
-- For (x, y), returns (-y, x).
perpendicular :: Vec2 -> Vec2
perpendicular (Vec2 x y) = Vec2 (-y) x

-- | Rotate vector by angle (in radians).
--
-- Uses rotation matrix:
-- @
-- [cos θ  -sin θ] [x]
-- [sin θ   cos θ] [y]
-- @
rotate :: Vec2 -> Double -> Vec2
rotate (Vec2 x y) ang =
  let c = cos ang
      s = sin ang
  in Vec2 (x * c - y * s) (x * s + y * c)

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation between two vectors.
--
-- @param a Start vector (t=0)
-- @param b End vector (t=1)
-- @param t Interpolation parameter (0 to 1)
-- @return Interpolated vector: a + (b - a) * t
lerp :: Vec2 -> Vec2 -> Double -> Vec2
lerp (Vec2 x1 y1) (Vec2 x2 y2) t =
  Vec2 (x1 + (x2 - x1) * t) (y1 + (y2 - y1) * t)

-- ────────────────────────────────────────────────────────────────────────────
-- Projection
-- ────────────────────────────────────────────────────────────────────────────

-- | Project vector a onto vector b.
--
-- Returns component of a in the direction of b.
project :: Vec2 -> Vec2 -> Vec2
project a b =
  let bLenSq = lengthSq b
  in if bLenSq < 0.0001
     then zero
     else let scalar = dot a b / bLenSq
          in scale b scalar

-- | Reflect vector v off a surface with normal n.
--
-- @param v Incoming vector
-- @param n Surface normal (should be normalized)
-- @return Reflected vector
reflect :: Vec2 -> Vec2 -> Vec2
reflect v n =
  let dotVN = dot v n
  in sub v (scale n (2 * dotVN))

-- ────────────────────────────────────────────────────────────────────────────
-- Angle Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Get angle of vector from positive x-axis (in radians).
--
-- Returns 0 for zero vector.
angle :: Vec2 -> Double
angle (Vec2 x y) = atan2 y x

-- | Get angle between two vectors (in radians).
--
-- Returns 0 if either vector has zero length.
angleBetween :: Vec2 -> Vec2 -> Double
angleBetween a b =
  let lenA = vecLength a
      lenB = vecLength b
  in if lenA < 0.0001 || lenB < 0.0001
     then 0
     else let cosAng = dot a b / (lenA * lenB)
              clamped = max (-1) (min 1 cosAng)
          in acos clamped
