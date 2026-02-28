-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // geometry // vector4
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Vector4 — 4D vector for homogeneous coordinates.
-- |
-- | Used primarily for:
-- | - Homogeneous coordinates (x, y, z, w)
-- | - Color data (r, g, b, a)
-- | - Matrix multiplication inputs
-- | - Quaternion storage (x, y, z, w)

module Hydrogen.Schema.Geometry.Vector4
  ( Vector4D(Vector4D)
  , vec4
  , zeroVec4
  , getVX4
  , getVY4
  , getVZ4
  , getVW4
  , addVec4
  , subVec4
  , scaleVec4
  , negateVec4
  , dot4
  , normalize4
  , magnitude4
  , magnitudeSquared4
  , lerp4
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
  , (<)
  )

import Data.Number (sqrt)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // vector4d
-- ═════════════════════════════════════════════════════════════════════════════

-- | A 4D vector.
newtype Vector4D = Vector4D { x :: Number, y :: Number, z :: Number, w :: Number }

derive instance eqVector4D :: Eq Vector4D
derive instance ordVector4D :: Ord Vector4D

instance showVector4D :: Show Vector4D where
  show (Vector4D v) = "(Vector4D " <> show v.x <> " " <> show v.y <> " " <> show v.z <> " " <> show v.w <> ")"

instance semiringVector4D :: Semiring Vector4D where
  add = addVec4
  mul (Vector4D a) (Vector4D b) = Vector4D { x: a.x * b.x, y: a.y * b.y, z: a.z * b.z, w: a.w * b.w }
  zero = zeroVec4
  one = Vector4D { x: 1.0, y: 1.0, z: 1.0, w: 1.0 }

instance ringVector4D :: Ring Vector4D where
  sub = subVec4

-- | Create a 4D vector
vec4 :: Number -> Number -> Number -> Number -> Vector4D
vec4 x y z w = Vector4D { x, y, z, w }

-- | Zero vector
zeroVec4 :: Vector4D
zeroVec4 = Vector4D { x: 0.0, y: 0.0, z: 0.0, w: 0.0 }

-- | Get X component
getVX4 :: Vector4D -> Number
getVX4 (Vector4D v) = v.x

-- | Get Y component
getVY4 :: Vector4D -> Number
getVY4 (Vector4D v) = v.y

-- | Get Z component
getVZ4 :: Vector4D -> Number
getVZ4 (Vector4D v) = v.z

-- | Get W component
getVW4 :: Vector4D -> Number
getVW4 (Vector4D v) = v.w

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add two 4D vectors
addVec4 :: Vector4D -> Vector4D -> Vector4D
addVec4 (Vector4D a) (Vector4D b) =
  Vector4D { x: a.x + b.x, y: a.y + b.y, z: a.z + b.z, w: a.w + b.w }

-- | Subtract 4D vectors
subVec4 :: Vector4D -> Vector4D -> Vector4D
subVec4 (Vector4D a) (Vector4D b) =
  Vector4D { x: a.x - b.x, y: a.y - b.y, z: a.z - b.z, w: a.w - b.w }

-- | Scale 4D vector
scaleVec4 :: Number -> Vector4D -> Vector4D
scaleVec4 s (Vector4D v) =
  Vector4D { x: v.x * s, y: v.y * s, z: v.z * s, w: v.w * s }

-- | Negate 4D vector
negateVec4 :: Vector4D -> Vector4D
negateVec4 (Vector4D v) =
  Vector4D { x: negate v.x, y: negate v.y, z: negate v.z, w: negate v.w }

-- | Dot product
dot4 :: Vector4D -> Vector4D -> Number
dot4 (Vector4D a) (Vector4D b) =
  a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w

-- | Squared magnitude
magnitudeSquared4 :: Vector4D -> Number
magnitudeSquared4 v = dot4 v v

-- | Magnitude
magnitude4 :: Vector4D -> Number
magnitude4 v = sqrt (magnitudeSquared4 v)

-- | Normalize
normalize4 :: Vector4D -> Vector4D
normalize4 v =
  let mag = magnitude4 v
  in if mag < 0.000001
       then zeroVec4
       else scaleVec4 (1.0 / mag) v

-- | Linear interpolation
lerp4 :: Number -> Vector4D -> Vector4D -> Vector4D
lerp4 t (Vector4D a) (Vector4D b) =
  Vector4D
    { x: a.x + (b.x - a.x) * t
    , y: a.y + (b.y - a.y) * t
    , z: a.z + (b.z - a.z) * t
    , w: a.w + (b.w - a.w) * t
    }
