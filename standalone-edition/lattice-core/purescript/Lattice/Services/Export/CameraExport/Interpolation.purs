-- | Lattice.Services.Export.CameraExport.Interpolation - Camera interpolation
-- |
-- | Interpolates camera properties between keyframes including position,
-- | rotation, focal length, zoom, and focus distance.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Interpolation
  ( -- * Interpolation
    interpolateCameraAtFrame
    -- * Math Utilities
  , lerp
  , lerpAngle
  , normalizeAngle
  ) where

import Prelude
import Data.Array (foldl)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Int (toNumber)

import Lattice.Services.Export.CameraExport.Types
  ( InterpolatedCamera
  , Vec3
  , defaultInterpolatedCamera
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Input Types (simplified from full Camera3D)
-- ────────────────────────────────────────────────────────────────────────────

-- | Camera keyframe
type CameraKeyframe =
  { frame :: Int
  , position :: Maybe Vec3
  , orientation :: Maybe Vec3
  , focalLength :: Maybe Number
  , zoom :: Maybe Number
  , focusDistance :: Maybe Number
  }

-- | Camera3D base properties
type Camera3D =
  { position :: Vec3
  , orientation :: Vec3
  , focalLength :: Number
  , zoom :: Number
  , focusDistance :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Interpolate camera properties at a specific frame
interpolateCameraAtFrame
  :: Camera3D
  -> Array CameraKeyframe
  -> Int
  -> InterpolatedCamera
interpolateCameraAtFrame camera keyframes frame =
  case findSurroundingKeyframes keyframes frame of
    { prev: Nothing, next: Nothing } ->
      cameraToInterpolated camera
    { prev: Just p, next: Nothing } ->
      keyframeToInterpolated camera p
    { prev: Nothing, next: Just n } ->
      keyframeToInterpolated camera n
    { prev: Just p, next: Just n } ->
      if p.frame == n.frame then
        keyframeToInterpolated camera p
      else
        interpolateBetween camera p n frame

-- | Find surrounding keyframes for a frame
findSurroundingKeyframes
  :: Array CameraKeyframe
  -> Int
  -> { prev :: Maybe CameraKeyframe, next :: Maybe CameraKeyframe }
findSurroundingKeyframes keyframes frame =
  foldl
    (\acc kf ->
      { prev: if kf.frame <= frame then Just kf else acc.prev
      , next:
          case acc.next of
            Nothing -> if kf.frame >= frame then Just kf else Nothing
            Just existing -> if kf.frame >= frame && kf.frame < existing.frame then Just kf else acc.next
      }
    )
    { prev: Nothing, next: Nothing }
    keyframes

-- | Convert camera to interpolated state
cameraToInterpolated :: Camera3D -> InterpolatedCamera
cameraToInterpolated cam =
  { position: cam.position
  , rotation: cam.orientation
  , focalLength: cam.focalLength
  , zoom: cam.zoom
  , focusDistance: cam.focusDistance
  }

-- | Convert keyframe to interpolated state (with camera defaults)
keyframeToInterpolated :: Camera3D -> CameraKeyframe -> InterpolatedCamera
keyframeToInterpolated cam kf =
  { position: fromMaybe cam.position kf.position
  , rotation: fromMaybe cam.orientation kf.orientation
  , focalLength: fromMaybe cam.focalLength kf.focalLength
  , zoom: fromMaybe cam.zoom kf.zoom
  , focusDistance: fromMaybe cam.focusDistance kf.focusDistance
  }

-- | Interpolate between two keyframes
interpolateBetween
  :: Camera3D
  -> CameraKeyframe
  -> CameraKeyframe
  -> Int
  -> InterpolatedCamera
interpolateBetween cam prev next frame =
  let
    prevFrame = prev.frame
    nextFrame = next.frame
    t = toNumber (frame - prevFrame) / toNumber (nextFrame - prevFrame)

    prevPos = fromMaybe cam.position prev.position
    nextPos = fromMaybe cam.position next.position
    prevOri = fromMaybe cam.orientation prev.orientation
    nextOri = fromMaybe cam.orientation next.orientation
    prevFocal = fromMaybe cam.focalLength prev.focalLength
    nextFocal = fromMaybe cam.focalLength next.focalLength
    prevZoom = fromMaybe cam.zoom prev.zoom
    nextZoom = fromMaybe cam.zoom next.zoom
    prevFocus = fromMaybe cam.focusDistance prev.focusDistance
    nextFocus = fromMaybe cam.focusDistance next.focusDistance
  in
    { position: lerpVec3 prevPos nextPos t
    , rotation: lerpAngleVec3 prevOri nextOri t
    , focalLength: lerp prevFocal nextFocal t
    , zoom: lerp prevZoom nextZoom t
    , focusDistance: lerp prevFocus nextFocus t
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Math Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Linear interpolation for Vec3
lerpVec3 :: Vec3 -> Vec3 -> Number -> Vec3
lerpVec3 a b t =
  { x: lerp a.x b.x t
  , y: lerp a.y b.y t
  , z: lerp a.z b.z t
  }

-- | Angle interpolation (shortest path around circle)
lerpAngle :: Number -> Number -> Number -> Number
lerpAngle a b t =
  let
    diff0 = b - a
    diff1 = if diff0 > 180.0 then diff0 - 360.0 else diff0
    diff = if diff1 < -180.0 then diff1 + 360.0 else diff1
    result = a + diff * t
  in
    normalizeAngle result

-- | Angle interpolation for Vec3 (rotation)
lerpAngleVec3 :: Vec3 -> Vec3 -> Number -> Vec3
lerpAngleVec3 a b t =
  { x: lerpAngle a.x b.x t
  , y: lerpAngle a.y b.y t
  , z: lerpAngle a.z b.z t
  }

-- | Normalize angle to [0, 360] range
normalizeAngle :: Number -> Number
normalizeAngle angle =
  let
    normalized = angle `mod'` 360.0
  in
    if normalized < 0.0 then normalized + 360.0 else normalized

-- | Floating point modulo
mod' :: Number -> Number -> Number
mod' x y = x - (toNumber (floor (x / y))) * y

-- | Floor function
foreign import floor :: Number -> Int
