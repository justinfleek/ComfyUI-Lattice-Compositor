{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.ShapeOperations.Point2D
Description : 2D Point/Vector Operations
Copyright   : (c) Lattice, 2026
License     : MIT

Pure 2D vector math for shape operations:
- Point arithmetic (add, subtract, scale)
- Vector operations (dot, cross, normalize, perpendicular)
- Rotation operations
- Distance calculations

Source: ui/src/services/shapeOperations.ts (utility functions)
-}

module Lattice.Services.ShapeOperations.Point2D
  ( -- * Types
    Point2D(..)
  , origin
    -- * Basic Arithmetic
  , add, sub, scale, neg, mul, pointDiv
    -- * Vector Operations
  , lengthSquared, len, distance, distanceSquared
  , normalize, dot, cross, perpendicular, perpendicularCW
    -- * Rotation
  , rotate, rotateAround
    -- * Interpolation
  , lerp, lerpClamped
    -- * Projection and Reflection
  , project, reflect
    -- * Angle Operations
  , angle, angleBetween, fromAngle
    -- * Clone/Copy
  , clone
    -- * Comparison
  , approxEqual, isZero
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point or vector
data Point2D = Point2D
  { px :: Double
  , py :: Double
  } deriving (Show, Eq)

-- | Default point at origin
origin :: Point2D
origin = Point2D 0 0

-- ────────────────────────────────────────────────────────────────────────────
-- Basic Arithmetic
-- ────────────────────────────────────────────────────────────────────────────

-- | Add two points/vectors
add :: Point2D -> Point2D -> Point2D
add (Point2D ax ay) (Point2D bx by) = Point2D (ax + bx) (ay + by)

-- | Subtract points (a - b)
sub :: Point2D -> Point2D -> Point2D
sub (Point2D ax ay) (Point2D bx by) = Point2D (ax - bx) (ay - by)

-- | Scale a point by a scalar
scale :: Point2D -> Double -> Point2D
scale (Point2D x y) s = Point2D (x * s) (y * s)

-- | Negate a vector
neg :: Point2D -> Point2D
neg (Point2D x y) = Point2D (-x) (-y)

-- | Component-wise multiplication
mul :: Point2D -> Point2D -> Point2D
mul (Point2D ax ay) (Point2D bx by) = Point2D (ax * bx) (ay * by)

-- | Component-wise division (safe)
pointDiv :: Point2D -> Point2D -> Point2D
pointDiv (Point2D ax ay) (Point2D bx by) =
  let bx' = if bx == 0 then 1 else bx
      by' = if by == 0 then 1 else by
  in Point2D (ax / bx') (ay / by')

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Squared length of a vector (avoids sqrt)
lengthSquared :: Point2D -> Double
lengthSquared (Point2D x y) = x * x + y * y

-- | Length/magnitude of a vector
len :: Point2D -> Double
len = sqrt . lengthSquared

-- | Distance between two points
distance :: Point2D -> Point2D -> Double
distance a b = len (sub b a)

-- | Squared distance between two points (avoids sqrt)
distanceSquared :: Point2D -> Point2D -> Double
distanceSquared a b = lengthSquared (sub b a)

-- | Normalize a vector to unit length.
-- Returns zero vector if input length is too small.
normalize :: Point2D -> Point2D
normalize p =
  let l = len p
  in if l < 0.0001 then origin
     else scale p (1 / l)

-- | Dot product of two vectors
dot :: Point2D -> Point2D -> Double
dot (Point2D ax ay) (Point2D bx by) = ax * bx + ay * by

-- | Cross product (2D returns scalar z-component)
cross :: Point2D -> Point2D -> Double
cross (Point2D ax ay) (Point2D bx by) = ax * by - ay * bx

-- | Perpendicular vector (rotate 90° counter-clockwise)
perpendicular :: Point2D -> Point2D
perpendicular (Point2D x y) = Point2D (-y) x

-- | Perpendicular vector (rotate 90° clockwise)
perpendicularCW :: Point2D -> Point2D
perpendicularCW (Point2D x y) = Point2D y (-x)

-- ────────────────────────────────────────────────────────────────────────────
-- Rotation
-- ────────────────────────────────────────────────────────────────────────────

-- | Rotate point around origin by angle (radians)
rotate :: Point2D -> Double -> Point2D
rotate (Point2D x y) theta =
  let c = cos theta
      s = sin theta
  in Point2D (x * c - y * s) (x * s + y * c)

-- | Rotate point around a center by angle (radians)
rotateAround :: Point2D -> Point2D -> Double -> Point2D
rotateAround p center theta =
  let translated = sub p center
      rotated = rotate translated theta
  in add rotated center

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation between two points
lerp :: Point2D -> Point2D -> Double -> Point2D
lerp (Point2D ax ay) (Point2D bx by) t =
  Point2D (ax + (bx - ax) * t) (ay + (by - ay) * t)

-- | Clamp t to [0, 1] then lerp
lerpClamped :: Point2D -> Point2D -> Double -> Point2D
lerpClamped a b t =
  let tc = max 0 (min 1 t)
  in lerp a b tc

-- ────────────────────────────────────────────────────────────────────────────
-- Projection and Reflection
-- ────────────────────────────────────────────────────────────────────────────

-- | Project point a onto vector b
project :: Point2D -> Point2D -> Point2D
project a b =
  let bLenSq = lengthSquared b
  in if bLenSq < 0.0001 then origin
     else scale b (dot a b / bLenSq)

-- | Reflect vector a across normal n
reflect :: Point2D -> Point2D -> Point2D
reflect a n =
  let nNorm = normalize n
  in sub a (scale nNorm (2 * dot a nNorm))

-- ────────────────────────────────────────────────────────────────────────────
-- Angle Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Angle of vector from positive x-axis (radians)
angle :: Point2D -> Double
angle (Point2D x y) = atan2 y x

-- | Angle between two vectors (radians)
angleBetween :: Point2D -> Point2D -> Double
angleBetween a b =
  let d = dot (normalize a) (normalize b)
      clamped = max (-1) (min 1 d)
  in acos clamped

-- | Create unit vector from angle (radians)
fromAngle :: Double -> Point2D
fromAngle theta = Point2D (cos theta) (sin theta)

-- ────────────────────────────────────────────────────────────────────────────
-- Clone/Copy
-- ────────────────────────────────────────────────────────────────────────────

-- | Clone a point
clone :: Point2D -> Point2D
clone (Point2D x y) = Point2D x y

-- ────────────────────────────────────────────────────────────────────────────
-- Comparison
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if two points are approximately equal
approxEqual :: Point2D -> Point2D -> Double -> Bool
approxEqual (Point2D ax ay) (Point2D bx by) epsilon =
  abs (ax - bx) < epsilon && abs (ay - by) < epsilon

-- | Check if point is approximately at origin
isZero :: Point2D -> Double -> Bool
isZero p epsilon = lengthSquared p < epsilon * epsilon
