-- | Lattice.Services.Math3D.Quat - Quaternion operations
-- |
-- | Pure math functions for quaternion manipulation.
-- | Used for smooth rotation interpolation.
-- |
-- | Source: ui/src/services/math3d.ts

module Lattice.Services.Math3D.Quat
  ( -- * Types
    Quat(..)
    -- * Constructors
  , identity, quatFromComponents
    -- * Basic Operations
  , lengthQuat, lengthSq, normalize
  , conjugate, invert, multiply, dotQuat
    -- * Euler Angle Conversion
  , fromEuler, toEuler
    -- * Axis-Angle Conversion
  , fromAxisAngle, toAxisAngle
    -- * Interpolation
  , slerp, lerpQuat, nlerp
    -- * Rotation Application
  , rotateVec3
    -- * Conversion
  , toArray, fromArray
  ) where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Data.Number (sqrt, sin, cos, asin, acos, atan2, abs) as Math
import Lattice.Services.Math3D.Vec3 (Vec3(..))
import Lattice.Services.Math3D.Vec3 as V

-- ────────────────────────────────────────────────────────────────────────────
-- Quat Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Quaternion (x, y, z, w) where w is the scalar component
newtype Quat = Quat { x :: Number, y :: Number, z :: Number, w :: Number }

derive instance Generic Quat _
derive newtype instance Eq Quat
instance Show Quat where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Constructors
-- ────────────────────────────────────────────────────────────────────────────

-- | Identity quaternion (no rotation)
identity :: Quat
identity = Quat { x: 0.0, y: 0.0, z: 0.0, w: 1.0 }

-- | Create quaternion from components
quatFromComponents :: Number -> Number -> Number -> Number -> Quat
quatFromComponents x y z w = Quat { x, y, z, w }

-- ────────────────────────────────────────────────────────────────────────────
-- Basic Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Quaternion length (magnitude)
lengthQuat :: Quat -> Number
lengthQuat q = Math.sqrt (lengthSq q)

-- | Squared length
lengthSq :: Quat -> Number
lengthSq (Quat q) = q.x*q.x + q.y*q.y + q.z*q.z + q.w*q.w

-- | Normalize quaternion
normalize :: Quat -> Quat
normalize q =
  let len = lengthQuat q
  in if len == 0.0
     then identity
     else case q of
       Quat r -> Quat { x: r.x / len, y: r.y / len, z: r.z / len, w: r.w / len }

-- | Conjugate (inverse for unit quaternions)
conjugate :: Quat -> Quat
conjugate (Quat q) = Quat { x: -q.x, y: -q.y, z: -q.z, w: q.w }

-- | Invert quaternion
invert :: Quat -> Quat
invert q =
  let lenSq' = lengthSq q
  in if lenSq' == 0.0
     then identity
     else case q of
       Quat r -> Quat { x: -r.x / lenSq', y: -r.y / lenSq', z: -r.z / lenSq', w: r.w / lenSq' }

-- | Quaternion multiplication
multiply :: Quat -> Quat -> Quat
multiply (Quat a) (Quat b) = Quat
  { x: a.w * b.x + a.x * b.w + a.y * b.z - a.z * b.y
  , y: a.w * b.y - a.x * b.z + a.y * b.w + a.z * b.x
  , z: a.w * b.z + a.x * b.y - a.y * b.x + a.z * b.w
  , w: a.w * b.w - a.x * b.x - a.y * b.y - a.z * b.z
  }

-- | Dot product
dotQuat :: Quat -> Quat -> Number
dotQuat (Quat a) (Quat b) = a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w

-- ────────────────────────────────────────────────────────────────────────────
-- Euler Angle Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Create quaternion from Euler angles (XYZ order) in radians
fromEuler :: Number -> Number -> Number -> Quat
fromEuler x y z = Quat
  { x: s1 * c2 * c3 + c1 * s2 * s3
  , y: c1 * s2 * c3 - s1 * c2 * s3
  , z: c1 * c2 * s3 + s1 * s2 * c3
  , w: c1 * c2 * c3 - s1 * s2 * s3
  }
  where
    c1 = Math.cos (x / 2.0)
    c2 = Math.cos (y / 2.0)
    c3 = Math.cos (z / 2.0)
    s1 = Math.sin (x / 2.0)
    s2 = Math.sin (y / 2.0)
    s3 = Math.sin (z / 2.0)

-- | Convert quaternion to Euler angles (XYZ order) in radians
toEuler :: Quat -> Vec3
toEuler q =
  let len = lengthQuat q
  in if len == 0.0 then V.zero
     else
       let Quat qr = q
           qxn = qr.x / len
           qyn = qr.y / len
           qzn = qr.z / len
           qwn = qr.w / len

           sqx = qxn * qxn
           sqy = qyn * qyn
           sqz = qzn * qzn
           sqw = qwn * qwn

           m11 = sqw + sqx - sqy - sqz
           m12 = 2.0 * (qxn * qyn - qwn * qzn)
           m13 = 2.0 * (qxn * qzn + qwn * qyn)
           m22 = sqw - sqx + sqy - sqz
           m23 = 2.0 * (qyn * qzn - qwn * qxn)
           m32 = 2.0 * (qyn * qzn + qwn * qxn)
           m33 = sqw - sqx - sqy + sqz

           sinY = max (-1.0) (min 1.0 m13)
       in if Math.abs sinY > 0.9999999
          then Vec3 { x: Math.atan2 (-m32) m22, y: Math.asin sinY, z: 0.0 }
          else Vec3 { x: Math.atan2 (-m23) m33, y: Math.asin sinY, z: Math.atan2 (-m12) m11 }

-- ────────────────────────────────────────────────────────────────────────────
-- Axis-Angle Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Create quaternion from axis-angle representation
fromAxisAngle :: Vec3 -> Number -> Quat
fromAxisAngle axis angle = Quat
  { x: V.getX normalizedAxis * s
  , y: V.getY normalizedAxis * s
  , z: V.getZ normalizedAxis * s
  , w: Math.cos halfAngle
  }
  where
    normalizedAxis = V.normalize axis
    halfAngle = angle / 2.0
    s = Math.sin halfAngle

-- | Convert quaternion to axis-angle representation
toAxisAngle :: Quat -> Tuple Vec3 Number
toAxisAngle q =
  let Quat qn = normalize q
      qnx = qn.x
      qny = qn.y
      qnz = qn.z
      angle = 2.0 * Math.acos (max (-1.0) (min 1.0 qn.w))
      sinHalfAngle = Math.sin (angle / 2.0)
  in if Math.abs sinHalfAngle < 0.0001
     then Tuple V.unitX 0.0
     else Tuple (Vec3 { x: qnx / sinHalfAngle, y: qny / sinHalfAngle, z: qnz / sinHalfAngle }) angle

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Spherical linear interpolation (SLERP)
slerp :: Quat -> Quat -> Number -> Quat
slerp a b t =
  let Quat ar = a
      Quat br = b
      ax = ar.x
      ay = ar.y
      az = ar.z
      aw = ar.w

      d = dotQuat a b
      (Tuple b' d') = if d < 0.0
                      then Tuple (Quat { x: -br.x, y: -br.y, z: -br.z, w: -br.w }) (-d)
                      else Tuple b d
  in if d' > 0.9995
     then normalize (lerpQuat a b' t)
     else
       let Quat br' = b'
           bx' = br'.x
           by' = br'.y
           bz' = br'.z
           bw' = br'.w

           theta0 = Math.acos d'
           theta = theta0 * t
           sinTheta = Math.sin theta
           sinTheta0 = Math.sin theta0

           s0 = Math.cos theta - d' * sinTheta / sinTheta0
           s1 = sinTheta / sinTheta0
       in Quat
            { x: s0 * ax + s1 * bx'
            , y: s0 * ay + s1 * by'
            , z: s0 * az + s1 * bz'
            , w: s0 * aw + s1 * bw'
            }

-- | Linear interpolation (not normalized)
lerpQuat :: Quat -> Quat -> Number -> Quat
lerpQuat (Quat a) (Quat b) t = Quat
  { x: a.x + t * (b.x - a.x)
  , y: a.y + t * (b.y - a.y)
  , z: a.z + t * (b.z - a.z)
  , w: a.w + t * (b.w - a.w)
  }

-- | Normalized linear interpolation
nlerp :: Quat -> Quat -> Number -> Quat
nlerp a b t = normalize (lerpQuat a b t)

-- ────────────────────────────────────────────────────────────────────────────
-- Rotation Application
-- ────────────────────────────────────────────────────────────────────────────

-- | Rotate a vector by quaternion
rotateVec3 :: Quat -> Vec3 -> Vec3
rotateVec3 q (Vec3 v) =
  let qv = Quat { x: v.x, y: v.y, z: v.z, w: 0.0 }
      qConj = conjugate q
      Quat result = multiply (multiply q qv) qConj
  in Vec3 { x: result.x, y: result.y, z: result.z }

-- ────────────────────────────────────────────────────────────────────────────
-- Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert to array [x, y, z, w]
toArray :: Quat -> Array Number
toArray (Quat q) = [q.x, q.y, q.z, q.w]

-- | Create from array (returns identity if array too short)
fromArray :: Array Number -> Quat
fromArray arr = case Array.index arr 0, Array.index arr 1, Array.index arr 2, Array.index arr 3 of
  Just x, Just y, Just z, Just w -> Quat { x, y, z, w }
  _, _, _, _ -> identity
