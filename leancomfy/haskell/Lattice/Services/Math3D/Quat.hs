{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Services.Math3D.Quat
Description : Quaternion operations
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions for quaternion manipulation.
Used for smooth rotation interpolation.

Source: ui/src/services/math3d.ts
-}

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

import GHC.Generics (Generic)
import Lattice.Services.Math3D.Vec3 (Vec3(..))
import qualified Lattice.Services.Math3D.Vec3 as V

--------------------------------------------------------------------------------
-- Quat Type
--------------------------------------------------------------------------------

-- | Quaternion (x, y, z, w) where w is the scalar component
data Quat = Quat
  { qx :: Double
  , qy :: Double
  , qz :: Double
  , qw :: Double
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Constructors
--------------------------------------------------------------------------------

-- | Identity quaternion (no rotation)
identity :: Quat
identity = Quat 0.0 0.0 0.0 1.0

-- | Create quaternion from components
quatFromComponents :: Double -> Double -> Double -> Double -> Quat
quatFromComponents = Quat

--------------------------------------------------------------------------------
-- Basic Operations
--------------------------------------------------------------------------------

-- | Quaternion length (magnitude)
lengthQuat :: Quat -> Double
lengthQuat q = sqrt (lengthSq q)

-- | Squared length
lengthSq :: Quat -> Double
lengthSq (Quat x y z w) = x*x + y*y + z*z + w*w

-- | Normalize quaternion
normalize :: Quat -> Quat
normalize q =
  let len = lengthQuat q
  in if len == 0.0
     then identity
     else Quat (qx q / len) (qy q / len) (qz q / len) (qw q / len)

-- | Conjugate (inverse for unit quaternions)
conjugate :: Quat -> Quat
conjugate (Quat x y z w) = Quat (-x) (-y) (-z) w

-- | Invert quaternion
invert :: Quat -> Quat
invert q =
  let lenSq' = lengthSq q
  in if lenSq' == 0.0
     then identity
     else Quat (-qx q / lenSq') (-qy q / lenSq') (-qz q / lenSq') (qw q / lenSq')

-- | Quaternion multiplication
multiply :: Quat -> Quat -> Quat
multiply a b = Quat
  (qw a * qx b + qx a * qw b + qy a * qz b - qz a * qy b)
  (qw a * qy b - qx a * qz b + qy a * qw b + qz a * qx b)
  (qw a * qz b + qx a * qy b - qy a * qx b + qz a * qw b)
  (qw a * qw b - qx a * qx b - qy a * qy b - qz a * qz b)

-- | Dot product
dotQuat :: Quat -> Quat -> Double
dotQuat a b = qx a * qx b + qy a * qy b + qz a * qz b + qw a * qw b

--------------------------------------------------------------------------------
-- Euler Angle Conversion
--------------------------------------------------------------------------------

-- | Create quaternion from Euler angles (XYZ order) in radians
fromEuler :: Double -> Double -> Double -> Quat
fromEuler x y z = Quat
  (s1 * c2 * c3 + c1 * s2 * s3)
  (c1 * s2 * c3 - s1 * c2 * s3)
  (c1 * c2 * s3 + s1 * s2 * c3)
  (c1 * c2 * c3 - s1 * s2 * s3)
  where
    c1 = cos (x / 2.0)
    c2 = cos (y / 2.0)
    c3 = cos (z / 2.0)
    s1 = sin (x / 2.0)
    s2 = sin (y / 2.0)
    s3 = sin (z / 2.0)

-- | Convert quaternion to Euler angles (XYZ order) in radians
toEuler :: Quat -> Vec3
toEuler q
  | len == 0.0 = V.zero
  | abs sinY > 0.9999999 = Vec3 x' y' z'  -- Gimbal lock
  | otherwise = Vec3 x'' y'' z''
  where
    len = lengthQuat q
    qxn = qx q / len
    qyn = qy q / len
    qzn = qz q / len
    qwn = qw q / len

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

    -- Gimbal lock case
    y' = asin sinY
    z' = 0.0
    x' = atan2 (-m32) m22

    -- Normal case
    y'' = asin sinY
    x'' = atan2 (-m23) m33
    z'' = atan2 (-m12) m11

--------------------------------------------------------------------------------
-- Axis-Angle Conversion
--------------------------------------------------------------------------------

-- | Create quaternion from axis-angle representation
fromAxisAngle :: Vec3 -> Double -> Quat
fromAxisAngle axis angle = Quat
  (V.x normalizedAxis * s)
  (V.y normalizedAxis * s)
  (V.z normalizedAxis * s)
  (cos halfAngle)
  where
    normalizedAxis = V.normalize axis
    halfAngle = angle / 2.0
    s = sin halfAngle

-- | Convert quaternion to axis-angle representation
toAxisAngle :: Quat -> (Vec3, Double)
toAxisAngle q
  | abs sinHalfAngle < 0.0001 = (V.unitX, 0.0)
  | otherwise = (Vec3 (qx qn / sinHalfAngle) (qy qn / sinHalfAngle) (qz qn / sinHalfAngle), angle)
  where
    qn = normalize q
    angle = 2.0 * acos (max (-1.0) (min 1.0 (qw qn)))
    sinHalfAngle = sin (angle / 2.0)

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Spherical linear interpolation (SLERP)
slerp :: Quat -> Quat -> Double -> Quat
slerp a b t
  | d' > 0.9995 = normalize (lerpQuat a b' t)
  | otherwise = Quat
      (s0 * qx a + s1 * qx b')
      (s0 * qy a + s1 * qy b')
      (s0 * qz a + s1 * qz b')
      (s0 * qw a + s1 * qw b')
  where
    d = dotQuat a b
    (b', d') = if d < 0.0
               then (Quat (-qx b) (-qy b) (-qz b) (-qw b), -d)
               else (b, d)

    theta0 = acos d'
    theta = theta0 * t
    sinTheta = sin theta
    sinTheta0 = sin theta0

    s0 = cos theta - d' * sinTheta / sinTheta0
    s1 = sinTheta / sinTheta0

-- | Linear interpolation (not normalized)
lerpQuat :: Quat -> Quat -> Double -> Quat
lerpQuat a b t = Quat
  (qx a + t * (qx b - qx a))
  (qy a + t * (qy b - qy a))
  (qz a + t * (qz b - qz a))
  (qw a + t * (qw b - qw a))

-- | Normalized linear interpolation
nlerp :: Quat -> Quat -> Double -> Quat
nlerp a b t = normalize (lerpQuat a b t)

--------------------------------------------------------------------------------
-- Rotation Application
--------------------------------------------------------------------------------

-- | Rotate a vector by quaternion
rotateVec3 :: Quat -> Vec3 -> Vec3
rotateVec3 q v =
  let qv = Quat (V.x v) (V.y v) (V.z v) 0.0
      qConj = conjugate q
      result = multiply (multiply q qv) qConj
  in Vec3 (qx result) (qy result) (qz result)

--------------------------------------------------------------------------------
-- Conversion
--------------------------------------------------------------------------------

-- | Convert to array [x, y, z, w]
toArray :: Quat -> [Double]
toArray (Quat x y z w) = [x, y, z, w]

-- | Create from array (returns identity if array too short)
fromArray :: [Double] -> Quat
fromArray [x, y, z, w] = Quat x y z w
fromArray (x:y:z:w:_) = Quat x y z w
fromArray _ = identity
