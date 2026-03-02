{-|
Module      : Lattice.Services.Camera.Matrix
Description : Camera matrix computations
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for camera matrix calculations:
- View matrix (camera transform inverse)
- Projection matrix (perspective)
- World-to-camera (w2c) matrix
- Rotation matrix composition

Source: ui/src/services/export/cameraExportFormats.ts (lines 167-286, 782-861)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Camera.Matrix
  ( -- * Types
    Vec3(..)
  , Mat4
  , Mat3x4
  , InterpolatedCamera(..)
    -- * Constants
  , defaultNearClip
  , defaultFarClip
  , defaultFilmSize
  , standardFocalLength
    -- * Angle Conversion
  , degreesToRadians
  , radiansToDegrees
    -- * Focal Length to FOV
  , focalLengthToFOV
  , fovToFocalLength
    -- * View Matrix
  , computeViewMatrix
    -- * Projection Matrix
  , computeProjectionMatrix
    -- * World-to-Camera Matrix
  , computeW2CMatrix
  , flattenMat3x4
    -- * Identity Matrix
  , identityMat4
  ) where

import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D vector.
data Vec3 = Vec3
  { v3x :: Double
  , v3y :: Double
  , v3z :: Double
  } deriving (Show, Eq)

-- | 4x4 matrix stored as vector of rows.
type Mat4 = Vector (Vector Double)

-- | 3x4 matrix for w2c transforms.
type Mat3x4 = Vector (Vector Double)

-- | Interpolated camera state.
data InterpolatedCamera = InterpolatedCamera
  { icamPosition      :: Vec3
  , icamRotation      :: Vec3
  , icamFocalLength   :: Double
  , icamZoom          :: Double
  , icamFocusDistance :: Double
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Default near clip plane.
defaultNearClip :: Double
defaultNearClip = 0.1

-- | Default far clip plane.
defaultFarClip :: Double
defaultFarClip = 1000.0

-- | Default film size (36mm full frame).
defaultFilmSize :: Double
defaultFilmSize = 36.0

-- | Standard focal length (50mm).
standardFocalLength :: Double
standardFocalLength = 50.0

-- ────────────────────────────────────────────────────────────────────────────
-- Angle Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert degrees to radians.
degreesToRadians :: Double -> Double
degreesToRadians degrees = degrees * pi / 180.0

-- | Convert radians to degrees.
radiansToDegrees :: Double -> Double
radiansToDegrees radians = radians * 180.0 / pi

-- ────────────────────────────────────────────────────────────────────────────
-- Focal Length to FOV
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert focal length (mm) to field of view (radians).
focalLengthToFOV :: Double -> Double -> Double
focalLengthToFOV focalLength filmSize =
  let safeFocal = if focalLength > 0 then focalLength else standardFocalLength
  in 2.0 * atan (filmSize / (2.0 * safeFocal))

-- | Convert field of view (radians) to focal length (mm).
fovToFocalLength :: Double -> Double -> Double
fovToFocalLength fovRadians filmSize =
  filmSize / (2.0 * tan (fovRadians / 2.0))

-- ────────────────────────────────────────────────────────────────────────────
-- View Matrix Computation
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute 4x4 view matrix from camera state.
computeViewMatrix :: InterpolatedCamera -> Mat4
computeViewMatrix cam =
  let rot = icamRotation cam
      pos = icamPosition cam
      -- Guard against invalid values
      rotX = if isFinite (v3x rot) then v3x rot else 0
      rotY = if isFinite (v3y rot) then v3y rot else 0
      rotZ = if isFinite (v3z rot) then v3z rot else 0
      posX = if isFinite (v3x pos) then v3x pos else 0
      posY = if isFinite (v3y pos) then v3y pos else 0
      posZ = if isFinite (v3z pos) then v3z pos else 0
      -- Convert to radians
      rx = degreesToRadians rotX
      ry = degreesToRadians rotY
      rz = degreesToRadians rotZ
      -- Trig values
      (sinX, cosX) = (sin rx, cos rx)
      (sinY, cosY) = (sin ry, cos ry)
      (sinZ, cosZ) = (sin rz, cos rz)
      -- Combined rotation (Y * X * Z order)
      r00 = cosY * cosZ + sinY * sinX * sinZ
      r01 = -cosY * sinZ + sinY * sinX * cosZ
      r02 = sinY * cosX
      r10 = cosX * sinZ
      r11 = cosX * cosZ
      r12 = -sinX
      r20 = -sinY * cosZ + cosY * sinX * sinZ
      r21 = sinY * sinZ + cosY * sinX * cosZ
      r22 = cosY * cosX
      -- Translation = -R^T * position
      tx = -(r00 * posX + r10 * posY + r20 * posZ)
      ty = -(r01 * posX + r11 * posY + r21 * posZ)
      tz = -(r02 * posX + r12 * posY + r22 * posZ)
  in V.fromList
      [ V.fromList [r00, r01, r02, tx]
      , V.fromList [r10, r11, r12, ty]
      , V.fromList [r20, r21, r22, tz]
      , V.fromList [0, 0, 0, 1]
      ]
  where
    isFinite x = not (isNaN x) && not (isInfinite x)

-- ────────────────────────────────────────────────────────────────────────────
-- Projection Matrix Computation
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute perspective projection matrix.
computeProjectionMatrix :: InterpolatedCamera -> Double -> Double -> Double -> Mat4
computeProjectionMatrix cam aspectRatio nearClip farClip =
  let validAspect = if aspectRatio > 0 && not (isNaN aspectRatio) then aspectRatio else 1.0
      validNear = if nearClip > 0 && not (isNaN nearClip) then nearClip else defaultNearClip
      validFar = if farClip > validNear && not (isNaN farClip) then farClip else defaultFarClip
      validFocal = if icamFocalLength cam > 0 && not (isNaN (icamFocalLength cam))
                   then icamFocalLength cam else standardFocalLength
      fovRad = focalLengthToFOV validFocal defaultFilmSize
      tanHalfFov = tan (fovRad / 2.0)
      f = if tanHalfFov > 0.001 then 1.0 / tanHalfFov else 1000.0
      nf = 1.0 / (validNear - validFar)
  in V.fromList
      [ V.fromList [f / validAspect, 0, 0, 0]
      , V.fromList [0, f, 0, 0]
      , V.fromList [0, 0, (validFar + validNear) * nf, 2 * validFar * validNear * nf]
      , V.fromList [0, 0, -1, 0]
      ]

-- ────────────────────────────────────────────────────────────────────────────
-- World-to-Camera Matrix
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute 3x4 world-to-camera (w2c) matrix.
computeW2CMatrix :: InterpolatedCamera -> Mat3x4
computeW2CMatrix cam =
  let rot = icamRotation cam
      pos = icamPosition cam
      -- Guard against invalid values
      rotX = if isFinite (v3x rot) then v3x rot else 0
      rotY = if isFinite (v3y rot) then v3y rot else 0
      rotZ = if isFinite (v3z rot) then v3z rot else 0
      posX = if isFinite (v3x pos) then v3x pos else 0
      posY = if isFinite (v3y pos) then v3y pos else 0
      posZ = if isFinite (v3z pos) then v3z pos else 0
      -- Convert to radians
      rx = degreesToRadians rotX
      ry = degreesToRadians rotY
      rz = degreesToRadians rotZ
      -- Trig values
      (sinX, cosX) = (sin rx, cos rx)
      (sinY, cosY) = (sin ry, cos ry)
      (sinZ, cosZ) = (sin rz, cos rz)
      -- Combined rotation (Y * X * Z order) for c2w
      r00 = cosY * cosZ + sinY * sinX * sinZ
      r01 = -cosY * sinZ + sinY * sinX * cosZ
      r02 = sinY * cosX
      r10 = cosX * sinZ
      r11 = cosX * cosZ
      r12 = -sinX
      r20 = -sinY * cosZ + cosY * sinX * sinZ
      r21 = sinY * sinZ + cosY * sinX * cosZ
      r22 = cosY * cosX
      -- w2c rotation (transpose of c2w)
      w2c_r00 = r00; w2c_r01 = r10; w2c_r02 = r20
      w2c_r10 = r01; w2c_r11 = r11; w2c_r12 = r21
      w2c_r20 = r02; w2c_r21 = r12; w2c_r22 = r22
      -- w2c translation = -R^T * t
      tx = -(w2c_r00 * posX + w2c_r01 * posY + w2c_r02 * posZ)
      ty = -(w2c_r10 * posX + w2c_r11 * posY + w2c_r12 * posZ)
      tz = -(w2c_r20 * posX + w2c_r21 * posY + w2c_r22 * posZ)
  in V.fromList
      [ V.fromList [w2c_r00, w2c_r01, w2c_r02, tx]
      , V.fromList [w2c_r10, w2c_r11, w2c_r12, ty]
      , V.fromList [w2c_r20, w2c_r21, w2c_r22, tz]
      ]
  where
    isFinite x = not (isNaN x) && not (isInfinite x)

-- | Flatten 3x4 matrix to 12-element list (row-major).
flattenMat3x4 :: Mat3x4 -> [Double]
flattenMat3x4 m = concatMap V.toList (V.toList m)

-- ────────────────────────────────────────────────────────────────────────────
-- Identity Matrix
-- ────────────────────────────────────────────────────────────────────────────

-- | 4x4 identity matrix.
identityMat4 :: Mat4
identityMat4 = V.fromList
  [ V.fromList [1, 0, 0, 0]
  , V.fromList [0, 1, 0, 0]
  , V.fromList [0, 0, 1, 0]
  , V.fromList [0, 0, 0, 1]
  ]
