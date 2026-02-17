{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Services.Math3D.Vec3
Description : 3D Vector operations
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions for 3D vector manipulation.

Source: ui/src/services/math3d.ts
-}

module Lattice.Services.Math3D.Vec3
  ( -- * Types
    Vec3(..)
    -- * Constructors
  , vec3
  , zero
  , unitX, unitY, unitZ
    -- * Basic Operations
  , add, sub, scale, neg
  , dot, cross, mul, divVec
    -- * Length and Distance
  , lengthSq, lengthVec3
  , distanceSq, distance
    -- * Normalization
  , normalize
  , isNormalized
    -- * Interpolation
  , lerp, slerp
    -- * Component Operations
  , minComponent, maxComponent
  , minVec, maxVec, absVec
  , clampVec
    -- * Projection and Reflection
  , project, reflect, angle
    -- * Conversion
  , toArray, fromArray
  ) where

import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Vec3 Type
--------------------------------------------------------------------------------

-- | 3D Vector
data Vec3 = Vec3
  { x :: Double
  , y :: Double
  , z :: Double
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Create a Vec3
vec3 :: Double -> Double -> Double -> Vec3
vec3 = Vec3

-- | Zero vector
zero :: Vec3
zero = Vec3 0.0 0.0 0.0

-- | Unit vectors
unitX :: Vec3
unitX = Vec3 1.0 0.0 0.0

unitY :: Vec3
unitY = Vec3 0.0 1.0 0.0

unitZ :: Vec3
unitZ = Vec3 0.0 0.0 1.0

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

-- | Vector addition
add :: Vec3 -> Vec3 -> Vec3
add (Vec3 ax ay az) (Vec3 bx by bz) = Vec3 (ax + bx) (ay + by) (az + bz)

-- | Vector subtraction
sub :: Vec3 -> Vec3 -> Vec3
sub (Vec3 ax ay az) (Vec3 bx by bz) = Vec3 (ax - bx) (ay - by) (az - bz)

-- | Scalar multiplication
scale :: Vec3 -> Double -> Vec3
scale (Vec3 vx vy vz) s = Vec3 (vx * s) (vy * s) (vz * s)

-- | Negation
neg :: Vec3 -> Vec3
neg (Vec3 vx vy vz) = Vec3 (-vx) (-vy) (-vz)

--------------------------------------------------------------------------------
-- Vector Products
--------------------------------------------------------------------------------

-- | Dot product
dot :: Vec3 -> Vec3 -> Double
dot (Vec3 ax ay az) (Vec3 bx by bz) = ax * bx + ay * by + az * bz

-- | Cross product
cross :: Vec3 -> Vec3 -> Vec3
cross (Vec3 ax ay az) (Vec3 bx by bz) = Vec3
  (ay * bz - az * by)
  (az * bx - ax * bz)
  (ax * by - ay * bx)

-- | Component-wise multiplication (Hadamard product)
mul :: Vec3 -> Vec3 -> Vec3
mul (Vec3 ax ay az) (Vec3 bx by bz) = Vec3 (ax * bx) (ay * by) (az * bz)

-- | Component-wise division
divVec :: Vec3 -> Vec3 -> Vec3
divVec (Vec3 ax ay az) (Vec3 bx by bz) = Vec3 (ax / bx) (ay / by) (az / bz)

--------------------------------------------------------------------------------
-- Length and Distance
--------------------------------------------------------------------------------

-- | Squared length (avoids sqrt)
lengthSq :: Vec3 -> Double
lengthSq (Vec3 vx vy vz) = vx * vx + vy * vy + vz * vz

-- | Vector length
lengthVec3 :: Vec3 -> Double
lengthVec3 v = sqrt (lengthSq v)

-- | Squared distance between two points
distanceSq :: Vec3 -> Vec3 -> Double
distanceSq a b = lengthSq (sub a b)

-- | Distance between two points
distance :: Vec3 -> Vec3 -> Double
distance a b = lengthVec3 (sub a b)

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

-- | Normalize vector (returns zero for zero vector)
normalize :: Vec3 -> Vec3
normalize v =
  let len = lengthVec3 v
  in if len == 0.0
     then zero
     else Vec3 (x v / len) (y v / len) (z v / len)

-- | Check if vector is normalized (unit length)
isNormalized :: Vec3 -> Double -> Bool
isNormalized v tolerance =
  let lenSq = lengthSq v
  in abs (lenSq - 1.0) < tolerance

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Linear interpolation
lerp :: Vec3 -> Vec3 -> Double -> Vec3
lerp a b t = Vec3
  (x a + (x b - x a) * t)
  (y a + (y b - y a) * t)
  (z a + (z b - z a) * t)

-- | Spherical linear interpolation (for normalized vectors)
slerp :: Vec3 -> Vec3 -> Double -> Vec3
slerp a b t =
  let d = dot a b
      d' = max (-1.0) (min 1.0 d)
      theta = acos d'
  in if abs theta < 0.0001
     then normalize (lerp a b t)
     else
       let sinTheta = sin theta
           s0 = sin ((1.0 - t) * theta) / sinTheta
           s1 = sin (t * theta) / sinTheta
       in Vec3
            (x a * s0 + x b * s1)
            (y a * s0 + y b * s1)
            (z a * s0 + z b * s1)

--------------------------------------------------------------------------------
-- Component Operations
--------------------------------------------------------------------------------

-- | Get minimum component value
minComponent :: Vec3 -> Double
minComponent (Vec3 vx vy vz) = min vx (min vy vz)

-- | Get maximum component value
maxComponent :: Vec3 -> Double
maxComponent (Vec3 vx vy vz) = max vx (max vy vz)

-- | Component-wise min of two vectors
minVec :: Vec3 -> Vec3 -> Vec3
minVec (Vec3 ax ay az) (Vec3 bx by bz) =
  Vec3 (min ax bx) (min ay by) (min az bz)

-- | Component-wise max of two vectors
maxVec :: Vec3 -> Vec3 -> Vec3
maxVec (Vec3 ax ay az) (Vec3 bx by bz) =
  Vec3 (max ax bx) (max ay by) (max az bz)

-- | Component-wise absolute value
absVec :: Vec3 -> Vec3
absVec (Vec3 vx vy vz) = Vec3 (abs vx) (abs vy) (abs vz)

-- | Clamp each component to range
clampVec :: Vec3 -> Vec3 -> Vec3 -> Vec3
clampVec (Vec3 vx vy vz) (Vec3 lox loy loz) (Vec3 hix hiy hiz) = Vec3
  (max lox (min hix vx))
  (max loy (min hiy vy))
  (max loz (min hiz vz))

--------------------------------------------------------------------------------
-- Projection and Reflection
--------------------------------------------------------------------------------

-- | Project vector a onto vector b
project :: Vec3 -> Vec3 -> Vec3
project a b =
  let bLenSq = lengthSq b
  in if bLenSq == 0.0
     then zero
     else scale b (dot a b / bLenSq)

-- | Reflect vector v around normal n (n should be normalized)
reflect :: Vec3 -> Vec3 -> Vec3
reflect v n = sub v (scale n (2.0 * dot v n))

-- | Compute the angle between two vectors (in radians)
angle :: Vec3 -> Vec3 -> Double
angle a b =
  let lenA = lengthVec3 a
      lenB = lengthVec3 b
  in if lenA == 0.0 || lenB == 0.0
     then 0.0
     else
       let d = dot a b / (lenA * lenB)
       in acos (max (-1.0) (min 1.0 d))

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

-- | Convert to array [x, y, z]
toArray :: Vec3 -> [Double]
toArray (Vec3 vx vy vz) = [vx, vy, vz]

-- | Create from array (returns zero if array too short)
fromArray :: [Double] -> Vec3
fromArray [vx, vy, vz] = Vec3 vx vy vz
fromArray (vx:vy:vz:_) = Vec3 vx vy vz
fromArray _ = zero
