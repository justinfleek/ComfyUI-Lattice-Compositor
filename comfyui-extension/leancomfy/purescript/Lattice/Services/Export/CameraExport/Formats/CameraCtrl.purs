-- | Lattice.Services.Export.CameraExport.Formats.CameraCtrl - AnimateDiff CameraCtrl
-- |
-- | @module Lattice.Services.Export.CameraExport.Formats.CameraCtrl
-- | @description Export camera to AnimateDiff CameraCtrl format.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Formats.CameraCtrl
  ( detectCameraCtrlMotionType
  , exportToCameraCtrl
  , exportAsCameraCtrlPoses
  , exportAsCameraCtrlPosesText
  ) where

import Prelude
import Data.Array (range, length, (!!), mapWithIndex)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (abs)
import Data.String (joinWith)

import Lattice.Services.Export.CameraExport.Types
  ( CameraCtrlMotionType(..)
  , CameraCtrlPoses
  , CameraCtrlPoseEntry
  , ZoomDirection(..)
  , PanDirection(..)
  )
import Lattice.Services.Export.CameraExport.Formats.Common
  ( Camera3D
  , CameraKeyframe
  , interpolateCameraAtFrame
  , min
  , round
  )
import Lattice.Services.Export.CameraExport.Matrix (computeW2CMatrixFlat)
import Lattice.Services.Export.CameraExport.MotionAnalysis (analyzeCameraMotion)

--------------------------------------------------------------------------------
-- CameraCtrl Format
--------------------------------------------------------------------------------

-- | Detect AnimateDiff CameraCtrl motion type
detectCameraCtrlMotionType :: Array CameraKeyframe -> CameraCtrlMotionType
detectCameraCtrlMotionType keyframes =
  let
    motion = analyzeCameraMotionKF keyframes
  in
    if not motion.hasPan && not motion.hasZoom && not motion.hasRotation then
      CameraCtrlStatic
    else if motion.hasZoom then
      case motion.zoomDirection of
        Just ZoomIn -> CameraCtrlMoveForward
        Just ZoomOut -> CameraCtrlMoveBackward
        Nothing -> CameraCtrlStatic
    else if motion.hasPan then
      case motion.panDirection of
        Just PanLeft -> CameraCtrlMoveLeft
        Just PanRight -> CameraCtrlMoveRight
        Just PanUp -> CameraCtrlMoveUp
        Just PanDown -> CameraCtrlMoveDown
        Nothing -> CameraCtrlStatic
    else if motion.hasRotation then
      detectRotationMotion keyframes
    else CameraCtrlStatic

detectRotationMotion :: Array CameraKeyframe -> CameraCtrlMotionType
detectRotationMotion keyframes =
  case { first: keyframes !! 0, last: keyframes !! (length keyframes - 1) } of
    { first: Just f, last: Just l } ->
      let
        defaultVec = { x: 0.0, y: 0.0, z: 0.0 }
        firstOri = fromMaybe defaultVec f.orientation
        lastOri = fromMaybe defaultVec l.orientation
        deltaRx = lastOri.x - firstOri.x
        deltaRy = lastOri.y - firstOri.y
        deltaRz = lastOri.z - firstOri.z
      in
        if abs deltaRy > abs deltaRx && abs deltaRy > abs deltaRz then
          if deltaRy > 0.0 then CameraCtrlRotateRight else CameraCtrlRotateLeft
        else if abs deltaRx > abs deltaRz then
          if deltaRx > 0.0 then CameraCtrlRotateDown else CameraCtrlRotateUp
        else
          if deltaRz > 0.0 then CameraCtrlRollRight else CameraCtrlRollLeft
    _ -> CameraCtrlStatic

-- | Export to CameraCtrl format
exportToCameraCtrl :: Array CameraKeyframe -> Int -> CameraCtrlPoses
exportToCameraCtrl keyframes frameCount =
  let
    motionType = detectCameraCtrlMotionType keyframes
    motion = analyzeCameraMotionKF keyframes
    speed =
      if motion.hasZoom then min 100 (round (motion.zoomMagnitude / 5.0))
      else if motion.hasPan then min 100 (round (motion.panMagnitude / 3.0))
      else if motion.hasRotation then min 100 (round (motion.rotationMagnitude * 2.0))
      else 0
  in
    { motionType, speed, frameLength: frameCount }

-- | Export as CameraCtrl poses (array format)
exportAsCameraCtrlPoses
  :: Camera3D
  -> Array CameraKeyframe
  -> Int
  -> Int  -- ^ Width
  -> Int  -- ^ Height
  -> Array CameraCtrlPoseEntry
exportAsCameraCtrlPoses camera keyframes frameCount width height =
  let
    sensorWidth = camera.filmSize
    widthN = toNumber width
    heightN = toNumber height
  in
    mapWithIndex
      (\frame _ ->
        let
          cam = interpolateCameraAtFrame camera keyframes frame
          focalLengthMM = cam.focalLength * cam.zoom
          fx = focalLengthMM * widthN / sensorWidth
          fy = fx
          cx = 0.5
          cy = 0.5
          aspect = widthN / heightN
          w2cFlat = computeW2CMatrixFlat cam
        in
          [toNumber frame, fx, fy, cx, cy, aspect, 0.0, 0.0] <> w2cFlat
      )
      (range 0 (frameCount - 1))

-- | Export as text format (space-separated)
exportAsCameraCtrlPosesText
  :: Camera3D
  -> Array CameraKeyframe
  -> Int
  -> Int
  -> Int
  -> String
exportAsCameraCtrlPosesText camera keyframes frameCount width height =
  let
    poses = exportAsCameraCtrlPoses camera keyframes frameCount width height
  in
    joinWith "\n" (map (\pose -> joinWith " " (map show pose)) poses)

analyzeCameraMotionKF keyframes = analyzeCameraMotion (map toMotionKeyframe keyframes)
  where
    toMotionKeyframe kf = { frame: kf.frame, position: kf.position, orientation: kf.orientation }
