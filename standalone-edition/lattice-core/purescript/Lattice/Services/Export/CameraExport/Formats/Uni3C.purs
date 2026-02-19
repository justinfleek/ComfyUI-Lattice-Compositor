-- | Lattice.Services.Export.CameraExport.Formats.Uni3C - Uni3C format
-- |
-- | @module Lattice.Services.Export.CameraExport.Formats.Uni3C
-- | @description Export camera to Uni3C trajectory format.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Formats.Uni3C
  ( detectUni3CTrajectoryType
  , exportToUni3C
  ) where

import Prelude
import Data.Array (range, mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))

import Lattice.Services.Export.CameraExport.Types
  ( Uni3CTrajType(..)
  , Uni3CCameraData
  )
import Lattice.Services.Export.CameraExport.Formats.Common
  ( Camera3D
  , CameraKeyframe
  , interpolateCameraAtFrame
  )
import Lattice.Services.Export.CameraExport.MotionAnalysis (analyzeCameraMotion)

-- ────────────────────────────────────────────────────────────────────────────
-- Uni3C Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Detect Uni3C trajectory type
detectUni3CTrajectoryType :: Array CameraKeyframe -> Uni3CTrajType
detectUni3CTrajectoryType keyframes =
  let
    motion = analyzeCameraMotionKF keyframes
  in
    if motion.hasOrbit && motion.orbitMagnitude > 45.0 then Uni3COrbit
    else if motion.hasPan && motion.hasZoom then Uni3CCustom
    else if not motion.hasPan && not motion.hasZoom && not motion.hasOrbit then Uni3CFree1
    else Uni3CCustom

-- | Export to Uni3C format
exportToUni3C
  :: Camera3D
  -> Array CameraKeyframe
  -> Int
  -> Int  -- ^ Comp width
  -> Int  -- ^ Comp height
  -> Uni3CCameraData
exportToUni3C camera keyframes frameCount compWidth compHeight =
  let
    detectedType = detectUni3CTrajectoryType keyframes
  in
    if detectedType /= Uni3CCustom then
      { trajType: detectedType, customTrajectory: Nothing }
    else
      let
        baseCamera = interpolateCameraAtFrame camera keyframes 0
        trajectory = mapWithIndex
          (\frame _ ->
            let
              cam = interpolateCameraAtFrame camera keyframes frame
            in
              { zoom: cam.zoom / baseCamera.zoom
              , xOffset: (cam.position.x - baseCamera.position.x) / toNumber compWidth
              , yOffset: (cam.position.y - baseCamera.position.y) / toNumber compHeight
              , zOffset: (cam.position.z - baseCamera.position.z) / 1000.0
              , pitch: cam.rotation.x
              , yaw: cam.rotation.y
              , roll: cam.rotation.z
              }
          )
          (range 0 (frameCount - 1))
      in
        { trajType: Uni3CCustom, customTrajectory: Just trajectory }

analyzeCameraMotionKF keyframes = analyzeCameraMotion (map toMotionKeyframe keyframes)
  where
    toMotionKeyframe kf = { frame: kf.frame, position: kf.position, orientation: kf.orientation }
