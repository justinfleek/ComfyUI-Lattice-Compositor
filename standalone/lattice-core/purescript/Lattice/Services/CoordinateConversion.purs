-- | Lattice.Services.CoordinateConversion - Coordinate conversion math
-- |
-- | Functions for converting between coordinate spaces and calculating
-- | orientations. Pure math without side effects.
-- |
-- | Source: ui/src/services/expressions/coordinateConversion.ts

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
  , identityTransform
  ) where

import Prelude
import Data.Array (foldl, reverse)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Global (isNaN, isFinite) as Global
import Math (atan2, cos, pi, sin, sqrt) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert degrees to radians
degToRad :: Number -> Number
degToRad deg = deg * Math.pi / 180.0

-- | Convert radians to degrees
radToDeg :: Number -> Number
radToDeg rad = rad * 180.0 / Math.pi

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D point
newtype Point3D = Point3D { x :: Number, y :: Number, z :: Number }

derive instance Generic Point3D _
derive newtype instance Eq Point3D
instance Show Point3D where show = genericShow

-- | Euler rotation angles in degrees
newtype EulerRotation = EulerRotation
  { pitch :: Number  -- X rotation
  , yaw :: Number    -- Y rotation
  , roll :: Number   -- Z rotation
  }

derive instance Generic EulerRotation _
derive newtype instance Eq EulerRotation
instance Show EulerRotation where show = genericShow

-- | Layer transform properties
newtype LayerTransform = LayerTransform
  { position :: Point3D
  , scale :: Point3D     -- As percentages (100 = 1.0)
  , rotation :: Point3D  -- Euler angles in degrees
  , anchor :: Point3D
  }

derive instance Generic LayerTransform _
derive newtype instance Eq LayerTransform
instance Show LayerTransform where show = genericShow

-- | Identity transform
identityTransform :: LayerTransform
identityTransform = LayerTransform
  { position: Point3D { x: 0.0, y: 0.0, z: 0.0 }
  , scale: Point3D { x: 100.0, y: 100.0, z: 100.0 }
  , rotation: Point3D { x: 0.0, y: 0.0, z: 0.0 }
  , anchor: Point3D { x: 0.0, y: 0.0, z: 0.0 }
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Orientation Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate rotation to face from one point to another.
--   Returns rotation angles (pitch, yaw, roll) in degrees.
--   Uses Y-up, Z-forward convention.
lookAt :: Point3D -> Point3D -> EulerRotation
lookAt (Point3D from_) (Point3D to) =
  let dx = to.x - from_.x
      dy = to.y - from_.y
      dz = to.z - from_.z
      -- Calculate yaw (Y rotation) from XZ plane
      yaw = radToDeg (Math.atan2 dx dz)
      -- Calculate pitch (X rotation) from horizontal distance
      dist = Math.sqrt (dx * dx + dz * dz)
      pitch = radToDeg (-(Math.atan2 dy dist))
  in EulerRotation { pitch, yaw, roll: 0.0 }

-- | Calculate rotation from velocity/tangent vector
orientToTangent :: Point3D -> EulerRotation
orientToTangent (Point3D tangent) =
  let dx = if Global.isNaN tangent.x || not (Global.isFinite tangent.x)
           then 0.0 else tangent.x
      dy = if Global.isNaN tangent.y || not (Global.isFinite tangent.y)
           then 0.0 else tangent.y
      dz = if Global.isNaN tangent.z || not (Global.isFinite tangent.z)
           then 1.0 else tangent.z  -- Default forward
      yaw = radToDeg (Math.atan2 dx dz)
      dist = Math.sqrt (dx * dx + dz * dz)
      pitch = radToDeg (-(Math.atan2 dy dist))
  in EulerRotation { pitch, yaw, roll: 0.0 }

-- ────────────────────────────────────────────────────────────────────────────
-- Rotation Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply rotation around Z axis
rotateZ :: Number -> Number -> Number -> Number -> Point3D
rotateZ x y z angle =
  let rad = degToRad angle
      cosA = Math.cos rad
      sinA = Math.sin rad
  in Point3D { x: x * cosA - y * sinA, y: x * sinA + y * cosA, z }

-- | Apply rotation around Y axis
rotateY :: Point3D -> Number -> Point3D
rotateY (Point3D p) angle =
  let rad = degToRad angle
      cosA = Math.cos rad
      sinA = Math.sin rad
  in Point3D
       { x: p.x * cosA + p.z * sinA
       , y: p.y
       , z: -p.x * sinA + p.z * cosA
       }

-- | Apply rotation around X axis
rotateX :: Point3D -> Number -> Point3D
rotateX (Point3D p) angle =
  let rad = degToRad angle
      cosA = Math.cos rad
      sinA = Math.sin rad
  in Point3D
       { x: p.x
       , y: p.y * cosA - p.z * sinA
       , z: p.y * sinA + p.z * cosA
       }

-- ────────────────────────────────────────────────────────────────────────────
-- Coordinate Conversion (Single Layer)
-- ────────────────────────────────────────────────────────────────────────────

-- | Safe divide with fallback
safeDivide :: Number -> Number -> Number -> Number
safeDivide num denom fallback =
  if denom == 0.0 || Global.isNaN denom || not (Global.isFinite denom) then fallback
  else
    let result = num / denom
    in if Global.isNaN result || not (Global.isFinite result) then fallback else result

-- | Convert point from layer space to composition space (single layer).
--   Applies: anchor offset → scale → rotation (ZYX order) → position
toCompSingle :: Point3D -> LayerTransform -> Point3D
toCompSingle (Point3D point) (LayerTransform transform) =
  let Point3D anchor = transform.anchor
      Point3D scale = transform.scale
      Point3D rotation = transform.rotation
      Point3D position = transform.position
      -- Apply anchor offset
      x = point.x - anchor.x
      y = point.y - anchor.y
      z = point.z - anchor.z
      -- Apply scale (percentage to multiplier)
      x' = x * scale.x / 100.0
      y' = y * scale.y / 100.0
      z' = z * scale.z / 100.0
      -- Apply rotation (Z, then Y, then X - matching AE order)
      rotZ = rotateZ x' y' z' rotation.z
      rotY = rotateY rotZ rotation.y
      Point3D rotX = rotateX rotY rotation.x
  -- Apply position offset
  in Point3D
       { x: rotX.x + position.x
       , y: rotX.y + position.y
       , z: rotX.z + position.z
       }

-- | Convert point from composition space to layer space (single layer).
--   Applies: position → inverse rotation (XYZ order) → inverse scale → anchor
fromCompSingle :: Point3D -> LayerTransform -> Point3D
fromCompSingle (Point3D point) (LayerTransform transform) =
  let Point3D position = transform.position
      Point3D rotation = transform.rotation
      Point3D scale = transform.scale
      Point3D anchor = transform.anchor
      -- Subtract position
      x = point.x - position.x
      y = point.y - position.y
      z = point.z - position.z
      -- Inverse rotation (X, then Y, then Z - reverse order, negative angles)
      rotX = rotateX (Point3D { x, y, z }) (-rotation.x)
      rotY = rotateY rotX (-rotation.y)
      Point3D rotZ = rotateZ
        (let Point3D p = rotY in p.x)
        (let Point3D p = rotY in p.y)
        (let Point3D p = rotY in p.z)
        (-rotation.z)
      -- Inverse scale (divide, with safety)
      sx = scale.x / 100.0
      sy = scale.y / 100.0
      sz = scale.z / 100.0
      x' = safeDivide rotZ.x sx rotZ.x
      y' = safeDivide rotZ.y sy rotZ.y
      z' = safeDivide rotZ.z sz rotZ.z
  -- Add anchor
  in Point3D
       { x: x' + anchor.x
       , y: y' + anchor.y
       , z: z' + anchor.z
       }

-- ────────────────────────────────────────────────────────────────────────────
-- Coordinate Conversion with Parent Chain
-- ────────────────────────────────────────────────────────────────────────────

-- | Maximum parent depth to prevent infinite loops
maxParentDepth :: Int
maxParentDepth = 50

-- | Convert to composition space with parent chain
toComp :: Point3D -> Array LayerTransform -> Point3D
toComp point transforms =
  foldl (\p t -> toCompSingle p t) point transforms

-- | Convert from composition space with parent chain
fromComp :: Point3D -> Array LayerTransform -> Point3D
fromComp point transforms =
  foldl (\p t -> fromCompSingle p t) point (reverse transforms)

-- ────────────────────────────────────────────────────────────────────────────
-- Aliases for 3D Context
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert to world space (alias for toComp)
toWorld :: Point3D -> Array LayerTransform -> Point3D
toWorld = toComp

-- | Convert from world space (alias for fromComp)
fromWorld :: Point3D -> Array LayerTransform -> Point3D
fromWorld = fromComp
