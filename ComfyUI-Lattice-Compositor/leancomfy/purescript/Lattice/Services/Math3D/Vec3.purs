-- | Lattice.Services.Math3D.Vec3 - 3D Vector operations
-- |
-- | Pure math functions for 3D vector manipulation.
-- |
-- | Source: ui/src/services/math3d.ts

module Lattice.Services.Math3D.Vec3
  ( -- * Types
    Vec3(..)
    -- * Accessors
  , getX, getY, getZ
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

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Array as Array
import Math (sqrt, sin, cos, acos, abs) as Math

--------------------------------------------------------------------------------
-- Vec3 Type
--------------------------------------------------------------------------------

-- | 3D Vector
newtype Vec3 = Vec3 { x :: Number, y :: Number, z :: Number }

derive instance Generic Vec3 _
derive newtype instance Eq Vec3
instance Show Vec3 where show = genericShow

-- | Extract x component
getX :: Vec3 -> Number
getX (Vec3 v) = v.x

-- | Extract y component
getY :: Vec3 -> Number
getY (Vec3 v) = v.y

-- | Extract z component
getZ :: Vec3 -> Number
getZ (Vec3 v) = v.z

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Create a Vec3
vec3 :: Number -> Number -> Number -> Vec3
vec3 x y z = Vec3 { x, y, z }

-- | Zero vector
zero :: Vec3
zero = Vec3 { x: 0.0, y: 0.0, z: 0.0 }

-- | Unit vectors
unitX :: Vec3
unitX = Vec3 { x: 1.0, y: 0.0, z: 0.0 }

unitY :: Vec3
unitY = Vec3 { x: 0.0, y: 1.0, z: 0.0 }

unitZ :: Vec3
unitZ = Vec3 { x: 0.0, y: 0.0, z: 1.0 }

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

-- | Vector addition
add :: Vec3 -> Vec3 -> Vec3
add (Vec3 a) (Vec3 b) = Vec3 { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z }

-- | Vector subtraction
sub :: Vec3 -> Vec3 -> Vec3
sub (Vec3 a) (Vec3 b) = Vec3 { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z }

-- | Scalar multiplication
scale :: Vec3 -> Number -> Vec3
scale (Vec3 v) s = Vec3 { x: v.x * s, y: v.y * s, z: v.z * s }

-- | Negation
neg :: Vec3 -> Vec3
neg (Vec3 v) = Vec3 { x: -v.x, y: -v.y, z: -v.z }

--------------------------------------------------------------------------------
-- Vector Products
--------------------------------------------------------------------------------

-- | Dot product
dot :: Vec3 -> Vec3 -> Number
dot (Vec3 a) (Vec3 b) = a.x * b.x + a.y * b.y + a.z * b.z

-- | Cross product
cross :: Vec3 -> Vec3 -> Vec3
cross (Vec3 a) (Vec3 b) = Vec3
  { x: a.y * b.z - a.z * b.y
  , y: a.z * b.x - a.x * b.z
  , z: a.x * b.y - a.y * b.x
  }

-- | Component-wise multiplication (Hadamard product)
mul :: Vec3 -> Vec3 -> Vec3
mul (Vec3 a) (Vec3 b) = Vec3 { x: a.x * b.x, y: a.y * b.y, z: a.z * b.z }

-- | Component-wise division
divVec :: Vec3 -> Vec3 -> Vec3
divVec (Vec3 a) (Vec3 b) = Vec3 { x: a.x / b.x, y: a.y / b.y, z: a.z / b.z }

--------------------------------------------------------------------------------
-- Length and Distance
--------------------------------------------------------------------------------

-- | Squared length (avoids sqrt)
lengthSq :: Vec3 -> Number
lengthSq (Vec3 v) = v.x * v.x + v.y * v.y + v.z * v.z

-- | Vector length
lengthVec3 :: Vec3 -> Number
lengthVec3 v = Math.sqrt (lengthSq v)

-- | Squared distance between two points
distanceSq :: Vec3 -> Vec3 -> Number
distanceSq a b = lengthSq (sub a b)

-- | Distance between two points
distance :: Vec3 -> Vec3 -> Number
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
     else Vec3 { x: getX v / len, y: getY v / len, z: getZ v / len }

-- | Check if vector is normalized (unit length)
isNormalized :: Vec3 -> Number -> Boolean
isNormalized v tolerance =
  let lenSq' = lengthSq v
  in Math.abs (lenSq' - 1.0) < tolerance

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Linear interpolation
lerp :: Vec3 -> Vec3 -> Number -> Vec3
lerp (Vec3 a) (Vec3 b) t = Vec3
  { x: a.x + (b.x - a.x) * t
  , y: a.y + (b.y - a.y) * t
  , z: a.z + (b.z - a.z) * t
  }

-- | Spherical linear interpolation (for normalized vectors)
slerp :: Vec3 -> Vec3 -> Number -> Vec3
slerp a b t =
  let d = dot a b
      d' = max (-1.0) (min 1.0 d)
      theta = Math.acos d'
  in if Math.abs theta < 0.0001
     then normalize (lerp a b t)
     else
       let sinTheta = Math.sin theta
           s0 = Math.sin ((1.0 - t) * theta) / sinTheta
           s1 = Math.sin (t * theta) / sinTheta
       in Vec3
            { x: getX a * s0 + getX b * s1
            , y: getY a * s0 + getY b * s1
            , z: getZ a * s0 + getZ b * s1
            }

--------------------------------------------------------------------------------
-- Component Operations
--------------------------------------------------------------------------------

-- | Get minimum component value
minComponent :: Vec3 -> Number
minComponent (Vec3 v) = min v.x (min v.y v.z)

-- | Get maximum component value
maxComponent :: Vec3 -> Number
maxComponent (Vec3 v) = max v.x (max v.y v.z)

-- | Component-wise min of two vectors
minVec :: Vec3 -> Vec3 -> Vec3
minVec (Vec3 a) (Vec3 b) = Vec3
  { x: min a.x b.x
  , y: min a.y b.y
  , z: min a.z b.z
  }

-- | Component-wise max of two vectors
maxVec :: Vec3 -> Vec3 -> Vec3
maxVec (Vec3 a) (Vec3 b) = Vec3
  { x: max a.x b.x
  , y: max a.y b.y
  , z: max a.z b.z
  }

-- | Component-wise absolute value
absVec :: Vec3 -> Vec3
absVec (Vec3 v) = Vec3
  { x: Math.abs v.x
  , y: Math.abs v.y
  , z: Math.abs v.z
  }

-- | Clamp each component to range
clampVec :: Vec3 -> Vec3 -> Vec3 -> Vec3
clampVec (Vec3 v) (Vec3 lo) (Vec3 hi) = Vec3
  { x: max lo.x (min hi.x v.x)
  , y: max lo.y (min hi.y v.y)
  , z: max lo.z (min hi.z v.z)
  }

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
angle :: Vec3 -> Vec3 -> Number
angle a b =
  let lenA = lengthVec3 a
      lenB = lengthVec3 b
  in if lenA == 0.0 || lenB == 0.0
     then 0.0
     else
       let d = dot a b / (lenA * lenB)
       in Math.acos (max (-1.0) (min 1.0 d))

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

-- | Convert to array [x, y, z]
toArray :: Vec3 -> Array Number
toArray (Vec3 v) = [v.x, v.y, v.z]

-- | Create from array (returns zero if array too short)
fromArray :: Array Number -> Vec3
fromArray arr = case Array.index arr 0, Array.index arr 1, Array.index arr 2 of
  Just vx, Just vy, Just vz -> Vec3 { x: vx, y: vy, z: vz }
  _, _, _ -> zero
