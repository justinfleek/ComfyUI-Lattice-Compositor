-- | Lattice.Services.Export.CameraExport.Formats.Common - Shared types and helpers
-- |
-- | @module Lattice.Services.Export.CameraExport.Formats.Common
-- | @description Shared types and interpolation helpers for camera export formats.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Formats.Common
  ( -- * Types
    Camera3D
  , CameraKeyframe
    -- * Interpolation
  , interpolateCameraAtFrame
    -- * Helpers
  , min
  , round
  , floor
  ) where

import Prelude
import Data.Array (foldl)
import Data.Int (toNumber) as Data.Int
import Data.Maybe (Maybe(..), fromMaybe)

import Lattice.Services.Export.CameraExport.Types
  ( InterpolatedCamera
  , Vec3
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

type Camera3D =
  { position :: Vec3
  , orientation :: Vec3
  , focalLength :: Number
  , filmSize :: Number
  , zoom :: Number
  , focusDistance :: Number
  , cameraType :: String
  }

type CameraKeyframe =
  { frame :: Int
  , position :: Maybe Vec3
  , orientation :: Maybe Vec3
  , focalLength :: Maybe Number
  , zoom :: Maybe Number
  , focusDistance :: Maybe Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Simplified interpolation (inline for this module)
interpolateCameraAtFrame :: Camera3D -> Array CameraKeyframe -> Int -> InterpolatedCamera
interpolateCameraAtFrame camera keyframes frame =
  case findSurrounding keyframes frame of
    { prev: Nothing, next: Nothing } ->
      { position: camera.position
      , rotation: camera.orientation
      , focalLength: camera.focalLength
      , zoom: camera.zoom
      , focusDistance: camera.focusDistance
      }
    { prev: Just p, next: Nothing } ->
      keyframeToInterpolated camera p
    { prev: Nothing, next: Just n } ->
      keyframeToInterpolated camera n
    { prev: Just p, next: Just n } ->
      interpolateBetween camera p n frame

findSurrounding :: Array CameraKeyframe -> Int -> { prev :: Maybe CameraKeyframe, next :: Maybe CameraKeyframe }
findSurrounding keyframes frame =
  foldl
    (\acc kf ->
      { prev: if kf.frame <= frame then Just kf else acc.prev
      , next: case acc.next of
          Nothing -> if kf.frame >= frame then Just kf else Nothing
          Just existing -> if kf.frame >= frame && kf.frame < existing.frame then Just kf else acc.next
      }
    )
    { prev: Nothing, next: Nothing }
    keyframes

keyframeToInterpolated :: Camera3D -> CameraKeyframe -> InterpolatedCamera
keyframeToInterpolated cam kf =
  { position: fromMaybe cam.position kf.position
  , rotation: fromMaybe cam.orientation kf.orientation
  , focalLength: fromMaybe cam.focalLength kf.focalLength
  , zoom: fromMaybe cam.zoom kf.zoom
  , focusDistance: fromMaybe cam.focusDistance kf.focusDistance
  }

interpolateBetween :: Camera3D -> CameraKeyframe -> CameraKeyframe -> Int -> InterpolatedCamera
interpolateBetween cam prev next frame =
  let
    t = if prev.frame == next.frame then 0.0
        else toNumber (frame - prev.frame) / toNumber (next.frame - prev.frame)
    prevPos = fromMaybe cam.position prev.position
    nextPos = fromMaybe cam.position next.position
    prevOri = fromMaybe cam.orientation prev.orientation
    nextOri = fromMaybe cam.orientation next.orientation
  in
    { position: lerpVec3 prevPos nextPos t
    , rotation: lerpVec3 prevOri nextOri t
    , focalLength: lerp (fromMaybe cam.focalLength prev.focalLength) (fromMaybe cam.focalLength next.focalLength) t
    , zoom: lerp (fromMaybe cam.zoom prev.zoom) (fromMaybe cam.zoom next.zoom) t
    , focusDistance: lerp (fromMaybe cam.focusDistance prev.focusDistance) (fromMaybe cam.focusDistance next.focusDistance) t
    }
  where
    toNumber :: Int -> Number
    toNumber n = Data.Int.toNumber n

lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

lerpVec3 :: Vec3 -> Vec3 -> Number -> Vec3
lerpVec3 a b t = { x: lerp a.x b.x t, y: lerp a.y b.y t, z: lerp a.z b.z t }

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

min :: Int -> Int -> Int
min a b = if a < b then a else b

round :: Number -> Int
round n = floor (n + 0.5)

foreign import floor :: Number -> Int
