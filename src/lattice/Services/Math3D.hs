-- |
-- Module      : Lattice.Services.Math3D
-- Description : Pure 3D math utilities for camera system
-- 
-- Migrated from ui/src/services/math3d.ts
-- Pure vector operations and camera utilities
-- Note: Matrix operations deferred (require Mat4 type definition)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.Math3D
  ( -- Vector operations
    vec3Create
  , addVec3
  , subVec3
  , scaleVec3
  , lengthVec3
  , normalizeVec3
  , crossVec3
  , dotVec3
  , lerpVec3
  , distanceVec3
  -- Camera utilities
  , focalLengthToFOV
  , fovToFocalLength
  , zoomToFocalLength
  , focalLengthToZoom
  , degToRad
  ) where

import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Types.Primitives (Vec3(..))
import Lattice.Utils.NumericSafety
  ( ensureFinite
  , safeSqrt
  , safeDivide
  )

-- ============================================================================
-- VECTOR OPERATIONS
-- ============================================================================

-- | Create a Vec3 from x, y, z components
vec3Create :: Double -> Double -> Double -> Vec3
vec3Create x y z = Vec3 (ensureFinite x 0.0) (ensureFinite y 0.0) (ensureFinite z 0.0)

-- | Add two Vec3 vectors
addVec3 :: Vec3 -> Vec3 -> Vec3
addVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  Vec3 (ensureFinite (x1 + x2) 0.0) (ensureFinite (y1 + y2) 0.0) (ensureFinite (z1 + z2) 0.0)

-- | Subtract second Vec3 from first Vec3
subVec3 :: Vec3 -> Vec3 -> Vec3
subVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  Vec3 (ensureFinite (x1 - x2) 0.0) (ensureFinite (y1 - y2) 0.0) (ensureFinite (z1 - z2) 0.0)

-- | Scale a Vec3 by a scalar
scaleVec3 :: Vec3 -> Double -> Vec3
scaleVec3 (Vec3 x y z) s =
  Vec3 (ensureFinite (x * s) 0.0) (ensureFinite (y * s) 0.0) (ensureFinite (z * s) 0.0)

-- | Calculate length/magnitude of a Vec3
lengthVec3 :: Vec3 -> Double
lengthVec3 (Vec3 x y z) =
  safeSqrt (x * x + y * y + z * z)

-- | Normalize a Vec3 to unit length
-- Returns Nothing if vector is zero length
normalizeVec3 :: Vec3 -> Maybe Vec3
normalizeVec3 v =
  let len = lengthVec3 v
  in if len == 0.0
     then Nothing
     else Just (scaleVec3 v (1.0 / len))

-- | Cross product of two Vec3 vectors
crossVec3 :: Vec3 -> Vec3 -> Vec3
crossVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  Vec3
    (ensureFinite (y1 * z2 - z1 * y2) 0.0)
    (ensureFinite (z1 * x2 - x1 * z2) 0.0)
    (ensureFinite (x1 * y2 - y1 * x2) 0.0)

-- | Dot product of two Vec3 vectors
dotVec3 :: Vec3 -> Vec3 -> Double
dotVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  ensureFinite (x1 * x2 + y1 * y2 + z1 * z2) 0.0

-- | Linear interpolation between two Vec3 vectors
lerpVec3 :: Vec3 -> Vec3 -> Double -> Vec3
lerpVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) t =
  let finiteT = ensureFinite t 0.0
      x = x1 + (x2 - x1) * finiteT
      y = y1 + (y2 - y1) * finiteT
      z = z1 + (z2 - z1) * finiteT
  in Vec3 (ensureFinite x 0.0) (ensureFinite y 0.0) (ensureFinite z 0.0)

-- | Distance between two Vec3 vectors
distanceVec3 :: Vec3 -> Vec3 -> Double
distanceVec3 a b = lengthVec3 (subVec3 a b)

-- ============================================================================
-- CAMERA UTILITIES
-- ============================================================================

-- | Convert focal length to field of view (in radians)
focalLengthToFOV :: Double -> Double -> Double
focalLengthToFOV focalLength sensorSize =
  let finiteFocal = ensureFinite focalLength 50.0
      finiteSensor = ensureFinite sensorSize 36.0
      fovRad = 2.0 * atan (finiteSensor / (2.0 * finiteFocal))
  in ensureFinite fovRad 0.0

-- | Convert field of view (in radians) to focal length
fovToFocalLength :: Double -> Double -> Double
fovToFocalLength fov sensorSize =
  let finiteFOV = ensureFinite fov 0.785398  -- ~45 degrees default
      finiteSensor = ensureFinite sensorSize 36.0
      focalLength = finiteSensor / (2.0 * tan (finiteFOV / 2.0))
  in ensureFinite focalLength 50.0

-- | Convert zoom to focal length
zoomToFocalLength :: Double -> Double -> Double -> Double
zoomToFocalLength zoom compWidth filmSize =
  let finiteZoom = ensureFinite zoom 1.0
      finiteCompWidth = ensureFinite compWidth 1920.0
      finiteFilmSize = ensureFinite filmSize 36.0
      focalLength = safeDivide (finiteZoom * finiteFilmSize) finiteCompWidth finiteFilmSize
  in ensureFinite focalLength 50.0

-- | Convert focal length to zoom
focalLengthToZoom :: Double -> Double -> Double -> Double
focalLengthToZoom focalLength compWidth filmSize =
  let finiteFocal = ensureFinite focalLength 50.0
      finiteCompWidth = ensureFinite compWidth 1920.0
      finiteFilmSize = ensureFinite filmSize 36.0
      zoom = safeDivide (finiteFocal * finiteCompWidth) finiteFilmSize finiteCompWidth
  in ensureFinite zoom 1.0

-- | Convert degrees to radians
degToRad :: Double -> Double
degToRad degrees =
  let finiteDeg = ensureFinite degrees 0.0
      radians = finiteDeg * pi / 180.0
  in ensureFinite radians 0.0
