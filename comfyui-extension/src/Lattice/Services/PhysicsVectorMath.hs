-- |
-- Module      : Lattice.Services.PhysicsVectorMath
-- Description : Pure 2D vector math functions for physics simulation
-- 
-- Migrated from ui/src/services/physics/PhysicsEngine.ts (vec2 object)
-- Pure vector operations for deterministic physics calculations
-- Uses Vec2 from Primitives.hs (compatible with PhysicsVec2)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.PhysicsVectorMath
  ( -- Vector creation
    vec2Create
  , vec2Clone
  -- Vector arithmetic
  , vec2Add
  , vec2Sub
  , vec2Scale
  -- Vector properties
  , vec2Length
  , vec2LengthSq
  , vec2Normalize
  -- Vector products
  , vec2Dot
  , vec2Cross
  -- Vector transformations
  , vec2Perpendicular
  , vec2Rotate
  -- Vector interpolation
  , vec2Lerp
  -- Vector distance
  , vec2Distance
  , vec2DistanceSq
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Types.Primitives (Vec2(..))
import Lattice.Utils.NumericSafety (ensureFiniteD, safeSqrtD)

-- ============================================================================
-- VECTOR CREATION
-- ============================================================================

-- | Create a 2D vector from x and y components
-- Pure function: same inputs → same outputs
vec2Create :: Double -> Double -> Vec2
vec2Create x y = Vec2 (ensureFiniteD x 0.0) (ensureFiniteD y 0.0)

-- | Clone a vector (creates new Vec2 with same values)
-- Pure function: same inputs → same outputs
vec2Clone :: Vec2 -> Vec2
vec2Clone v = Vec2 (vec2X v) (vec2Y v)

-- ============================================================================
-- VECTOR ARITHMETIC
-- ============================================================================

-- | Add two vectors
-- Pure function: same inputs → same outputs
vec2Add :: Vec2 -> Vec2 -> Vec2
vec2Add a b =
  Vec2 (ensureFiniteD (vec2X a + vec2X b) 0.0) (ensureFiniteD (vec2Y a + vec2Y b) 0.0)

-- | Subtract second vector from first vector
-- Pure function: same inputs → same outputs
vec2Sub :: Vec2 -> Vec2 -> Vec2
vec2Sub a b =
  Vec2 (ensureFiniteD (vec2X a - vec2X b) 0.0) (ensureFiniteD (vec2Y a - vec2Y b) 0.0)

-- | Scale a vector by a scalar
-- Pure function: same inputs → same outputs
vec2Scale :: Vec2 -> Double -> Vec2
vec2Scale v s =
  let finiteS = ensureFiniteD s 0.0
  in Vec2 (ensureFiniteD (vec2X v * finiteS) 0.0) (ensureFiniteD (vec2Y v * finiteS) 0.0)

-- ============================================================================
-- VECTOR PROPERTIES
-- ============================================================================

-- | Calculate vector length (magnitude)
-- Pure function: same inputs → same outputs
vec2Length :: Vec2 -> Double
vec2Length v =
  let lengthSq = vec2X v * vec2X v + vec2Y v * vec2Y v
  in ensureFiniteD (safeSqrtD lengthSq) 0.0

-- | Calculate squared vector length (for performance, avoids sqrt)
-- Pure function: same inputs → same outputs
vec2LengthSq :: Vec2 -> Double
vec2LengthSq v = ensureFiniteD (vec2X v * vec2X v + vec2Y v * vec2Y v) 0.0

-- | Normalize vector to unit length
-- Returns zero vector if input is zero vector
-- Pure function: same inputs → same outputs
vec2Normalize :: Vec2 -> Vec2
vec2Normalize v =
  let len = vec2Length v
  in if len == 0.0
     then Vec2 0.0 0.0
     else vec2Scale v (1.0 / len)

-- ============================================================================
-- VECTOR PRODUCTS
-- ============================================================================

-- | Dot product of two vectors
-- Pure function: same inputs → same outputs
vec2Dot :: Vec2 -> Vec2 -> Double
vec2Dot a b = ensureFiniteD (vec2X a * vec2X b + vec2Y a * vec2Y b) 0.0

-- | Cross product of two vectors (2D scalar result)
-- Pure function: same inputs → same outputs
vec2Cross :: Vec2 -> Vec2 -> Double
vec2Cross a b = ensureFiniteD (vec2X a * vec2Y b - vec2Y a * vec2X b) 0.0

-- ============================================================================
-- VECTOR TRANSFORMATIONS
-- ============================================================================

-- | Get perpendicular vector (rotated 90 degrees counterclockwise)
-- Pure function: same inputs → same outputs
vec2Perpendicular :: Vec2 -> Vec2
vec2Perpendicular v = Vec2 (-vec2Y v) (vec2X v)

-- | Rotate vector by angle (in radians)
-- Pure function: same inputs → same outputs
vec2Rotate :: Vec2 -> Double -> Vec2
vec2Rotate v angle =
  let finiteAngle = ensureFiniteD angle 0.0
      cosAngle = cos finiteAngle
      sinAngle = sin finiteAngle
      x = vec2X v
      y = vec2Y v
      newX = x * cosAngle - y * sinAngle
      newY = x * sinAngle + y * cosAngle
  in Vec2 (ensureFiniteD newX 0.0) (ensureFiniteD newY 0.0)

-- ============================================================================
-- VECTOR INTERPOLATION
-- ============================================================================

-- | Linear interpolation between two vectors
-- Pure function: same inputs → same outputs
vec2Lerp :: Vec2 -> Vec2 -> Double -> Vec2
vec2Lerp a b t =
  let finiteT = ensureFiniteD t 0.0
      x1 = vec2X a
      y1 = vec2Y a
      x2 = vec2X b
      y2 = vec2Y b
      newX = x1 + (x2 - x1) * finiteT
      newY = y1 + (y2 - y1) * finiteT
  in Vec2 (ensureFiniteD newX 0.0) (ensureFiniteD newY 0.0)

-- ============================================================================
-- VECTOR DISTANCE
-- ============================================================================

-- | Distance between two vectors
-- Pure function: same inputs → same outputs
vec2Distance :: Vec2 -> Vec2 -> Double
vec2Distance a b = vec2Length (vec2Sub b a)

-- | Squared distance between two vectors (for performance)
-- Pure function: same inputs → same outputs
vec2DistanceSq :: Vec2 -> Vec2 -> Double
vec2DistanceSq a b = vec2LengthSq (vec2Sub b a)
