{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Services.CoordinateConversion
Description : Coordinate conversion math
Copyright   : (c) Lattice, 2026
License     : MIT

Functions for converting between coordinate spaces and calculating
orientations. Pure math without side effects.

Source: ui/src/services/expressions/coordinateConversion.ts
-}

module Lattice.Services.CoordinateConversion
  ( -- * Types
    Point3D(..)
  , EulerRotation(..)
  , LayerTransform(..)
    -- * Constants
  , degToRad, radToDeg
    -- * Orientation
  , lookAt, orientToTangent
    -- * Rotation Helpers
  , rotateX, rotateY, rotateZ
    -- * Coordinate Conversion
  , toCompSingle, fromCompSingle
  , toComp, fromComp
  , toWorld, fromWorld
    -- * Utilities
  , safeDivide
  , maxParentDepth
  ) where

import GHC.Generics (Generic)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Convert degrees to radians
degToRad :: Double -> Double
degToRad deg = deg * pi / 180

-- | Convert radians to degrees
radToDeg :: Double -> Double
radToDeg rad = rad * 180 / pi

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 3D point
data Point3D = Point3D
  { point3DX :: Double
  , point3DY :: Double
  , point3DZ :: Double
  } deriving stock (Eq, Show, Generic)

-- | Euler rotation angles in degrees
data EulerRotation = EulerRotation
  { eulerPitch :: Double  -- ^ X rotation
  , eulerYaw :: Double    -- ^ Y rotation
  , eulerRoll :: Double   -- ^ Z rotation
  } deriving stock (Eq, Show, Generic)

-- | Layer transform properties
data LayerTransform = LayerTransform
  { ltPosition :: Point3D
  , ltScale :: Point3D     -- ^ As percentages (100 = 1.0)
  , ltRotation :: Point3D  -- ^ Euler angles in degrees
  , ltAnchor :: Point3D
  } deriving stock (Eq, Show, Generic)

-- | Identity transform
identityTransform :: LayerTransform
identityTransform = LayerTransform
  { ltPosition = Point3D 0 0 0
  , ltScale = Point3D 100 100 100
  , ltRotation = Point3D 0 0 0
  , ltAnchor = Point3D 0 0 0
  }

--------------------------------------------------------------------------------
-- Orientation Functions
--------------------------------------------------------------------------------

-- | Calculate rotation to face from one point to another.
--   Returns rotation angles (pitch, yaw, roll) in degrees.
--   Uses Y-up, Z-forward convention.
lookAt :: Point3D -> Point3D -> EulerRotation
lookAt from_ to =
  let dx = point3DX to - point3DX from_
      dy = point3DY to - point3DY from_
      dz = point3DZ to - point3DZ from_
      -- Calculate yaw (Y rotation) from XZ plane
      yaw = radToDeg (atan2 dx dz)
      -- Calculate pitch (X rotation) from horizontal distance
      dist = sqrt (dx * dx + dz * dz)
      pitch = radToDeg (-(atan2 dy dist))
  in EulerRotation pitch yaw 0

-- | Calculate rotation from velocity/tangent vector
orientToTangent :: Point3D -> EulerRotation
orientToTangent tangent =
  let dx = if isNaN (point3DX tangent) || isInfinite (point3DX tangent)
           then 0 else point3DX tangent
      dy = if isNaN (point3DY tangent) || isInfinite (point3DY tangent)
           then 0 else point3DY tangent
      dz = if isNaN (point3DZ tangent) || isInfinite (point3DZ tangent)
           then 1 else point3DZ tangent  -- Default forward
      yaw = radToDeg (atan2 dx dz)
      dist = sqrt (dx * dx + dz * dz)
      pitch = radToDeg (-(atan2 dy dist))
  in EulerRotation pitch yaw 0

--------------------------------------------------------------------------------
-- Rotation Helpers
--------------------------------------------------------------------------------

-- | Apply rotation around Z axis
rotateZ :: Double -> Double -> Double -> Double -> Point3D
rotateZ x y z angle =
  let rad = degToRad angle
      cosA = cos rad
      sinA = sin rad
  in Point3D (x * cosA - y * sinA) (x * sinA + y * cosA) z

-- | Apply rotation around Y axis
rotateY :: Point3D -> Double -> Point3D
rotateY p angle =
  let rad = degToRad angle
      cosA = cos rad
      sinA = sin rad
  in Point3D
       (point3DX p * cosA + point3DZ p * sinA)
       (point3DY p)
       (-point3DX p * sinA + point3DZ p * cosA)

-- | Apply rotation around X axis
rotateX :: Point3D -> Double -> Point3D
rotateX p angle =
  let rad = degToRad angle
      cosA = cos rad
      sinA = sin rad
  in Point3D
       (point3DX p)
       (point3DY p * cosA - point3DZ p * sinA)
       (point3DY p * sinA + point3DZ p * cosA)

--------------------------------------------------------------------------------
-- Coordinate Conversion (Single Layer)
--------------------------------------------------------------------------------

-- | Safe divide with fallback
safeDivide :: Double -> Double -> Double -> Double
safeDivide num denom fallback
  | denom == 0 || isNaN denom || isInfinite denom = fallback
  | otherwise =
      let result = num / denom
      in if isNaN result || isInfinite result then fallback else result

-- | Convert point from layer space to composition space (single layer).
--   Applies: anchor offset → scale → rotation (ZYX order) → position
toCompSingle :: Point3D -> LayerTransform -> Point3D
toCompSingle point transform =
  -- Apply anchor offset
  let x = point3DX point - point3DX (ltAnchor transform)
      y = point3DY point - point3DY (ltAnchor transform)
      z = point3DZ point - point3DZ (ltAnchor transform)
      -- Apply scale (percentage to multiplier)
      x' = x * point3DX (ltScale transform) / 100
      y' = y * point3DY (ltScale transform) / 100
      z' = z * point3DZ (ltScale transform) / 100
      -- Apply rotation (Z, then Y, then X - matching AE order)
      rotZ = rotateZ x' y' z' (point3DZ (ltRotation transform))
      rotY = rotateY rotZ (point3DY (ltRotation transform))
      rotX = rotateX rotY (point3DX (ltRotation transform))
  -- Apply position offset
  in Point3D
       (point3DX rotX + point3DX (ltPosition transform))
       (point3DY rotX + point3DY (ltPosition transform))
       (point3DZ rotX + point3DZ (ltPosition transform))

-- | Convert point from composition space to layer space (single layer).
--   Applies: position → inverse rotation (XYZ order) → inverse scale → anchor
fromCompSingle :: Point3D -> LayerTransform -> Point3D
fromCompSingle point transform =
  -- Subtract position
  let x = point3DX point - point3DX (ltPosition transform)
      y = point3DY point - point3DY (ltPosition transform)
      z = point3DZ point - point3DZ (ltPosition transform)
      -- Inverse rotation (X, then Y, then Z - reverse order, negative angles)
      rotX = rotateX (Point3D x y z) (-(point3DX (ltRotation transform)))
      rotY = rotateY rotX (-(point3DY (ltRotation transform)))
      rotZ = rotateZ (point3DX rotY) (point3DY rotY) (point3DZ rotY)
                     (-(point3DZ (ltRotation transform)))
      -- Inverse scale (divide, with safety)
      sx = point3DX (ltScale transform) / 100
      sy = point3DY (ltScale transform) / 100
      sz = point3DZ (ltScale transform) / 100
      x' = safeDivide (point3DX rotZ) sx (point3DX rotZ)
      y' = safeDivide (point3DY rotZ) sy (point3DY rotZ)
      z' = safeDivide (point3DZ rotZ) sz (point3DZ rotZ)
  -- Add anchor
  in Point3D
       (x' + point3DX (ltAnchor transform))
       (y' + point3DY (ltAnchor transform))
       (z' + point3DZ (ltAnchor transform))

--------------------------------------------------------------------------------
-- Coordinate Conversion with Parent Chain
--------------------------------------------------------------------------------

-- | Maximum parent depth to prevent infinite loops
maxParentDepth :: Int
maxParentDepth = 50

-- | Convert to composition space with parent chain
toComp :: Point3D -> [LayerTransform] -> Point3D
toComp point transforms = go point transforms maxParentDepth
  where
    go p [] _ = p
    go p _ 0 = p  -- Max depth reached
    go p (t:rest) n =
      let transformed = toCompSingle p t
      in go transformed rest (n - 1)

-- | Convert from composition space with parent chain
fromComp :: Point3D -> [LayerTransform] -> Point3D
fromComp point transforms = go point (reverse transforms) maxParentDepth
  where
    go p [] _ = p
    go p _ 0 = p  -- Max depth reached
    go p (t:rest) n =
      let parentTransformed = go p rest n
      in fromCompSingle parentTransformed t

--------------------------------------------------------------------------------
-- Aliases for 3D Context
--------------------------------------------------------------------------------

-- | Convert to world space (alias for toComp)
toWorld :: Point3D -> [LayerTransform] -> Point3D
toWorld = toComp

-- | Convert from world space (alias for fromComp)
fromWorld :: Point3D -> [LayerTransform] -> Point3D
fromWorld = fromComp
