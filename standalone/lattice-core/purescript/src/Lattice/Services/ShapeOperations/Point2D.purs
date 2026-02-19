-- | Lattice.Services.ShapeOperations.Point2D - 2D Point/Vector Operations
-- |
-- | Pure 2D vector math for shape operations:
-- | - Point arithmetic (add, subtract, scale)
-- | - Vector operations (dot, cross, normalize, perpendicular)
-- | - Rotation operations
-- | - Distance calculations
-- |
-- | Source: ui/src/services/shapeOperations.ts (utility functions)

module Lattice.Services.ShapeOperations.Point2D
  ( -- * Types
    Point2D
  , mkPoint2D, getX, getY
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

import Prelude
import Math (sqrt, cos, sin, atan2, acos, abs) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D point or vector
type Point2D =
  { x :: Number
  , y :: Number
  }

-- | Constructor for Point2D
mkPoint2D :: Number -> Number -> Point2D
mkPoint2D x y = { x, y }

-- | Get x coordinate
getX :: Point2D -> Number
getX p = p.x

-- | Get y coordinate
getY :: Point2D -> Number
getY p = p.y

-- | Default point at origin
origin :: Point2D
origin = { x: 0.0, y: 0.0 }

-- ────────────────────────────────────────────────────────────────────────────
-- Basic Arithmetic
-- ────────────────────────────────────────────────────────────────────────────

-- | Add two points/vectors
add :: Point2D -> Point2D -> Point2D
add a b = { x: a.x + b.x, y: a.y + b.y }

-- | Subtract points (a - b)
sub :: Point2D -> Point2D -> Point2D
sub a b = { x: a.x - b.x, y: a.y - b.y }

-- | Scale a point by a scalar
scale :: Point2D -> Number -> Point2D
scale p s = { x: p.x * s, y: p.y * s }

-- | Negate a vector
neg :: Point2D -> Point2D
neg p = { x: -p.x, y: -p.y }

-- | Component-wise multiplication
mul :: Point2D -> Point2D -> Point2D
mul a b = { x: a.x * b.x, y: a.y * b.y }

-- | Component-wise division (safe)
pointDiv :: Point2D -> Point2D -> Point2D
pointDiv a b =
  let bx = if b.x == 0.0 then 1.0 else b.x
      by = if b.y == 0.0 then 1.0 else b.y
  in { x: a.x / bx, y: a.y / by }

-- ────────────────────────────────────────────────────────────────────────────
-- Vector Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Squared length of a vector (avoids sqrt)
lengthSquared :: Point2D -> Number
lengthSquared p = p.x * p.x + p.y * p.y

-- | Length/magnitude of a vector
len :: Point2D -> Number
len p = Math.sqrt (lengthSquared p)

-- | Distance between two points
distance :: Point2D -> Point2D -> Number
distance a b = len (sub b a)

-- | Squared distance between two points (avoids sqrt)
distanceSquared :: Point2D -> Point2D -> Number
distanceSquared a b = lengthSquared (sub b a)

-- | Normalize a vector to unit length.
-- | Returns zero vector if input length is too small.
normalize :: Point2D -> Point2D
normalize p =
  let l = len p
  in if l < 0.0001 then origin
     else scale p (1.0 / l)

-- | Dot product of two vectors
dot :: Point2D -> Point2D -> Number
dot a b = a.x * b.x + a.y * b.y

-- | Cross product (2D returns scalar z-component)
cross :: Point2D -> Point2D -> Number
cross a b = a.x * b.y - a.y * b.x

-- | Perpendicular vector (rotate 90° counter-clockwise)
perpendicular :: Point2D -> Point2D
perpendicular p = { x: -p.y, y: p.x }

-- | Perpendicular vector (rotate 90° clockwise)
perpendicularCW :: Point2D -> Point2D
perpendicularCW p = { x: p.y, y: -p.x }

-- ────────────────────────────────────────────────────────────────────────────
-- Rotation
-- ────────────────────────────────────────────────────────────────────────────

-- | Rotate point around origin by angle (radians)
rotate :: Point2D -> Number -> Point2D
rotate p theta =
  let c = Math.cos theta
      s = Math.sin theta
  in { x: p.x * c - p.y * s, y: p.x * s + p.y * c }

-- | Rotate point around a center by angle (radians)
rotateAround :: Point2D -> Point2D -> Number -> Point2D
rotateAround p center theta =
  let translated = sub p center
      rotated = rotate translated theta
  in add rotated center

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation between two points
lerp :: Point2D -> Point2D -> Number -> Point2D
lerp a b t =
  { x: a.x + (b.x - a.x) * t
  , y: a.y + (b.y - a.y) * t
  }

-- | Clamp t to [0, 1] then lerp
lerpClamped :: Point2D -> Point2D -> Number -> Point2D
lerpClamped a b t =
  let tc = max 0.0 (min 1.0 t)
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
  in sub a (scale nNorm (2.0 * dot a nNorm))

-- ────────────────────────────────────────────────────────────────────────────
-- Angle Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Angle of vector from positive x-axis (radians)
angle :: Point2D -> Number
angle p = Math.atan2 p.y p.x

-- | Angle between two vectors (radians)
angleBetween :: Point2D -> Point2D -> Number
angleBetween a b =
  let d = dot (normalize a) (normalize b)
      clamped = max (-1.0) (min 1.0 d)
  in Math.acos clamped

-- | Create unit vector from angle (radians)
fromAngle :: Number -> Point2D
fromAngle theta = { x: Math.cos theta, y: Math.sin theta }

-- ────────────────────────────────────────────────────────────────────────────
-- Clone/Copy
-- ────────────────────────────────────────────────────────────────────────────

-- | Clone a point
clone :: Point2D -> Point2D
clone p = { x: p.x, y: p.y }

-- ────────────────────────────────────────────────────────────────────────────
-- Comparison
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if two points are approximately equal
approxEqual :: Point2D -> Point2D -> Number -> Boolean
approxEqual a b epsilon =
  Math.abs (a.x - b.x) < epsilon && Math.abs (a.y - b.y) < epsilon

-- | Check if point is approximately at origin
isZero :: Point2D -> Number -> Boolean
isZero p epsilon = lengthSquared p < epsilon * epsilon
