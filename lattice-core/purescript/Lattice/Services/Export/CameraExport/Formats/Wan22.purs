-- | Lattice.Services.Export.CameraExport.Formats.Wan22 - Wan 2.2 Fun Camera format
-- |
-- | @module Lattice.Services.Export.CameraExport.Formats.Wan22
-- | @description Map camera motion to Wan 2.2 Fun Camera presets.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Formats.Wan22
  ( mapToWan22FunCamera
  ) where

import Prelude
import Data.Maybe (Maybe(..))

import Lattice.Services.Export.CameraExport.Types
  ( CameraMotionAnalysis
  , Wan22CameraMotion(..)
  , Wan22FunCameraData
  , OrbitDirection(..)
  , ZoomDirection(..)
  , PanDirection(..)
  )
import Lattice.Services.Export.CameraExport.Formats.Common (CameraKeyframe)
import Lattice.Services.Export.CameraExport.MotionAnalysis (analyzeCameraMotion)

-- ────────────────────────────────────────────────────────────────────────────
-- Wan 2.2 Fun Camera Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Map to Wan 2.2 Fun Camera preset
mapToWan22FunCamera :: Array CameraKeyframe -> Wan22FunCameraData
mapToWan22FunCamera keyframes =
  let
    motion = analyzeCameraMotionKF keyframes
    preset =
      -- Priority: Orbit > Zoom+Pan > Zoom > Pan
      if motion.hasOrbit then
        case motion.orbitDirection of
          Just dir -> if dir == OrbitLeft then Wan22OrbitalLeft else Wan22OrbitalRight
          Nothing -> Wan22Static
      else if motion.hasZoom && motion.hasPan then
        mapZoomPanToWan22 motion
      else if motion.hasZoom then
        case motion.zoomDirection of
          Just dir -> if dir == ZoomIn then Wan22ZoomIn else Wan22ZoomOut
          Nothing -> Wan22Static
      else if motion.hasPan then
        mapPanToWan22 motion
      else Wan22Static
  in
    { cameraMotion: preset }

mapPanToWan22 :: CameraMotionAnalysis -> Wan22CameraMotion
mapPanToWan22 motion = case motion.panDirection of
  Just PanUp -> Wan22PanUp
  Just PanDown -> Wan22PanDown
  Just PanLeft -> Wan22PanLeft
  Just PanRight -> Wan22PanRight
  Nothing -> Wan22Static

mapZoomPanToWan22 :: CameraMotionAnalysis -> Wan22CameraMotion
mapZoomPanToWan22 motion =
  let
    isZoomIn = motion.zoomDirection == Just ZoomIn
  in
    case motion.panDirection of
      Just PanUp -> if isZoomIn then Wan22PanUpZoomIn else Wan22PanUpZoomOut
      Just PanDown -> if isZoomIn then Wan22PanDownZoomIn else Wan22PanDownZoomOut
      Just PanLeft -> if isZoomIn then Wan22PanLeftZoomIn else Wan22PanLeftZoomOut
      Just PanRight -> if isZoomIn then Wan22PanRightZoomIn else Wan22PanRightZoomOut
      Nothing -> if isZoomIn then Wan22ZoomIn else Wan22ZoomOut

analyzeCameraMotionKF :: Array CameraKeyframe -> CameraMotionAnalysis
analyzeCameraMotionKF keyframes = analyzeCameraMotion (map toMotionKeyframe keyframes)
  where
    toMotionKeyframe kf = { frame: kf.frame, position: kf.position, orientation: kf.orientation }
