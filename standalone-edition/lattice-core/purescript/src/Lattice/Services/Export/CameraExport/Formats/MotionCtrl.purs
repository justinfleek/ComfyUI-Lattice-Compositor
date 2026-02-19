-- | Lattice.Services.Export.CameraExport.Formats.MotionCtrl - MotionCtrl format
-- |
-- | @module Lattice.Services.Export.CameraExport.Formats.MotionCtrl
-- | @description Export camera animation to MotionCtrl format (4x4 RT matrices).
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Formats.MotionCtrl
  ( exportToMotionCtrl
  , detectMotionCtrlSVDPreset
  , exportToMotionCtrlSVD
  , serializePoses
  ) where

import Prelude
import Data.Array (range, length, (!!), mapWithIndex)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (abs)
import Data.String (joinWith)

import Lattice.Services.Export.CameraExport.Types
  ( MotionCtrlPose
  , MotionCtrlCameraData
  , MotionCtrlSVDPreset(..)
  , MotionCtrlSVDCameraData
  )
import Lattice.Services.Export.CameraExport.Formats.Common
  ( Camera3D
  , CameraKeyframe
  , interpolateCameraAtFrame
  )
import Lattice.Services.Export.CameraExport.Matrix (computeViewMatrix)

-- ────────────────────────────────────────────────────────────────────────────
-- MotionCtrl Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Export camera animation to MotionCtrl format (4x4 RT matrices)
exportToMotionCtrl
  :: Camera3D
  -> Array CameraKeyframe
  -> Int  -- ^ Frame count
  -> MotionCtrlCameraData
exportToMotionCtrl camera keyframes frameCount =
  let
    poses = mapWithIndex
      (\frame _ ->
        let
          interpolated = interpolateCameraAtFrame camera keyframes frame
          viewMatrix = computeViewMatrix interpolated
        in
          { rt: viewMatrix }
      )
      (range 0 (frameCount - 1))
  in
    { cameraPoses: poses }

-- | Detect best MotionCtrl-SVD preset from keyframes
detectMotionCtrlSVDPreset :: Array CameraKeyframe -> MotionCtrlSVDPreset
detectMotionCtrlSVDPreset keyframes =
  if length keyframes < 2 then SVDStatic
  else
    case { first: keyframes !! 0, last: keyframes !! (length keyframes - 1) } of
      { first: Just f, last: Just l } ->
        detectPresetFromPair f l
      _ -> SVDStatic

detectPresetFromPair :: CameraKeyframe -> CameraKeyframe -> MotionCtrlSVDPreset
detectPresetFromPair first last =
  let
    defaultVec = { x: 0.0, y: 0.0, z: 0.0 }
    firstPos = fromMaybe defaultVec first.position
    lastPos = fromMaybe defaultVec last.position
    firstOri = fromMaybe defaultVec first.orientation
    lastOri = fromMaybe defaultVec last.orientation

    deltaX = lastPos.x - firstPos.x
    deltaY = lastPos.y - firstPos.y
    deltaZ = lastPos.z - firstPos.z
    deltaRy = lastOri.y - firstOri.y

    threshold = 50.0
  in
    -- Zoom detection
    if abs deltaZ > threshold then
      let
        distStart = abs firstPos.z
        distEnd = abs lastPos.z
      in
        if distEnd < distStart then SVDZoomIn else SVDZoomOut
    -- Rotation detection
    else if abs deltaRy > 15.0 then
      if deltaRy > 0.0 then SVDRotateCW else SVDRotateCCW
    -- Pan detection
    else if abs deltaX > threshold then
      if deltaX > 0.0 then SVDPanRight else SVDPanLeft
    else if abs deltaY > threshold then
      if deltaY > 0.0 then SVDPanDown else SVDPanUp
    else SVDStatic

-- | Export to MotionCtrl-SVD format
exportToMotionCtrlSVD
  :: Camera3D
  -> Array CameraKeyframe
  -> Int
  -> MotionCtrlSVDCameraData
exportToMotionCtrlSVD camera keyframes frameCount =
  let
    preset = detectMotionCtrlSVDPreset keyframes
  in
    if preset /= SVDStatic && length keyframes <= 2 then
      { motionCamera: preset, cameraPoses: Nothing }
    else
      let
        motionctrlData = exportToMotionCtrl camera keyframes frameCount
      in
        { motionCamera: preset
        , cameraPoses: Just (serializePoses motionctrlData.cameraPoses)
        }

-- | Serialize poses to JSON string
serializePoses :: Array MotionCtrlPose -> String
serializePoses poses = "[" <> joinWith "," (map (\p -> serializeMatrix p.rt) poses) <> "]"

serializeMatrix :: Array (Array Number) -> String
serializeMatrix rows = "[" <> joinWith "," (map (\row -> "[" <> joinWith "," (map show row) <> "]") rows) <> "]"
