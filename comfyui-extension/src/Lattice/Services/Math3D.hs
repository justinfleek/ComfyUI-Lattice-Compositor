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
  ( ensureFiniteD
  , safeSqrtD
  , safeDivide
  )

-- ============================================================================
-- VECTOR OPERATIONS
-- ============================================================================

-- | Create a Vec3 from x, y, z components
vec3Create :: Double -> Double -> Double -> Vec3
vec3Create x y z = Vec3 (ensureFiniteD x 0.0) (ensureFiniteD y 0.0) (ensureFiniteD z 0.0)

-- | Add two Vec3 vectors
addVec3 :: Vec3 -> Vec3 -> Vec3
addVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  Vec3 (ensureFiniteD (x1 + x2) 0.0) (ensureFiniteD (y1 + y2) 0.0) (ensureFiniteD (z1 + z2) 0.0)

-- | Subtract second Vec3 from first Vec3
subVec3 :: Vec3 -> Vec3 -> Vec3
subVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  Vec3 (ensureFiniteD (x1 - x2) 0.0) (ensureFiniteD (y1 - y2) 0.0) (ensureFiniteD (z1 - z2) 0.0)

-- | Scale a Vec3 by a scalar
scaleVec3 :: Vec3 -> Double -> Vec3
scaleVec3 (Vec3 x y z) s =
  Vec3 (ensureFiniteD (x * s) 0.0) (ensureFiniteD (y * s) 0.0) (ensureFiniteD (z * s) 0.0)

-- | Calculate length/magnitude of a Vec3
lengthVec3 :: Vec3 -> Double
lengthVec3 (Vec3 x y z) =
  safeSqrtD (x * x + y * y + z * z)

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
    (ensureFiniteD (y1 * z2 - z1 * y2) 0.0)
    (ensureFiniteD (z1 * x2 - x1 * z2) 0.0)
    (ensureFiniteD (x1 * y2 - y1 * x2) 0.0)

-- | Dot product of two Vec3 vectors
dotVec3 :: Vec3 -> Vec3 -> Double
dotVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) =
  ensureFiniteD (x1 * x2 + y1 * y2 + z1 * z2) 0.0

-- | Linear interpolation between two Vec3 vectors
lerpVec3 :: Vec3 -> Vec3 -> Double -> Vec3
lerpVec3 (Vec3 x1 y1 z1) (Vec3 x2 y2 z2) t =
  let finiteT = ensureFiniteD t 0.0
      x = x1 + (x2 - x1) * finiteT
      y = y1 + (y2 - y1) * finiteT
      z = z1 + (z2 - z1) * finiteT
  in Vec3 (ensureFiniteD x 0.0) (ensureFiniteD y 0.0) (ensureFiniteD z 0.0)

-- | Distance between two Vec3 vectors
distanceVec3 :: Vec3 -> Vec3 -> Double
distanceVec3 a b = lengthVec3 (subVec3 a b)

-- ============================================================================
-- CAMERA UTILITIES
-- ============================================================================

-- | Convert focal length to field of view (in radians)
focalLengthToFOV :: Double -> Double -> Double
focalLengthToFOV focalLength sensorSize =
  let finiteFocal = ensureFiniteD focalLength 50.0
      finiteSensor = ensureFiniteD sensorSize 36.0
      fovRad = 2.0 * atan (finiteSensor / (2.0 * finiteFocal))
  in ensureFiniteD fovRad 0.0

-- | Convert field of view (in radians) to focal length
fovToFocalLength :: Double -> Double -> Double
fovToFocalLength fov sensorSize =
  let finiteFOV = ensureFiniteD fov 0.785398  -- ~45 degrees default
      finiteSensor = ensureFiniteD sensorSize 36.0
      focalLength = finiteSensor / (2.0 * tan (finiteFOV / 2.0))
  in ensureFiniteD focalLength 50.0

-- | Convert zoom to focal length
zoomToFocalLength :: Double -> Double -> Double -> Double
zoomToFocalLength zoom compWidth filmSize =
  let finiteZoom = ensureFiniteD zoom 1.0
      finiteCompWidth = ensureFiniteD compWidth 1920.0
      finiteFilmSize = ensureFiniteD filmSize 36.0
      focalLength = safeDivide (finiteZoom * finiteFilmSize) finiteCompWidth finiteFilmSize
  in ensureFiniteD focalLength 50.0

-- | Convert focal length to zoom
focalLengthToZoom :: Double -> Double -> Double -> Double
focalLengthToZoom focalLength compWidth filmSize =
  let finiteFocal = ensureFiniteD focalLength 50.0
      finiteCompWidth = ensureFiniteD compWidth 1920.0
      finiteFilmSize = ensureFiniteD filmSize 36.0
      zoom = safeDivide (finiteFocal * finiteCompWidth) finiteFilmSize finiteCompWidth
  in ensureFiniteD zoom 1.0

-- | Convert degrees to radians
degToRad :: Double -> Double
degToRad degrees =
  let finiteDeg = ensureFiniteD degrees 0.0
      radians = finiteDeg * pi / 180.0
  in ensureFiniteD radians 0.0
