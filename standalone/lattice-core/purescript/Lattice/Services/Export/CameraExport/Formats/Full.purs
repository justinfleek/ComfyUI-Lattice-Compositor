-- | Lattice.Services.Export.CameraExport.Formats.Full - Full matrix export
-- |
-- | @module Lattice.Services.Export.CameraExport.Formats.Full
-- | @description Export camera with full matrices and metadata.
-- |
-- | Source: ui/src/services/export/cameraExportFormats.ts

module Lattice.Services.Export.CameraExport.Formats.Full
  ( exportCameraMatrices
  , exportCameraForTarget
  ) where

import Prelude
import Data.Array (range, length, mapWithIndex)
import Data.Int (toNumber)

import Lattice.Services.Export.CameraExport.Types
  ( ExportTarget(..)
  , FullCameraExport
  )
import Lattice.Services.Export.CameraExport.Formats.Common
  ( Camera3D
  , CameraKeyframe
  , interpolateCameraAtFrame
  )
import Lattice.Services.Export.CameraExport.Formats.MotionCtrl
  ( exportToMotionCtrl
  , exportToMotionCtrlSVD
  , serializePoses
  )
import Lattice.Services.Export.CameraExport.Formats.Wan22 (mapToWan22FunCamera)
import Lattice.Services.Export.CameraExport.Formats.Uni3C (exportToUni3C)
import Lattice.Services.Export.CameraExport.Formats.CameraCtrl (exportToCameraCtrl)
import Lattice.Services.Export.CameraExport.Matrix
  ( computeViewMatrix
  , computeProjectionMatrix
  , focalLengthToFOV
  )

--------------------------------------------------------------------------------
-- Full Export
--------------------------------------------------------------------------------

-- | Export camera with full matrices
exportCameraMatrices
  :: Camera3D
  -> Array CameraKeyframe
  -> { frameCount :: Int, width :: Int, height :: Int, fps :: Number }
  -> FullCameraExport
exportCameraMatrices camera keyframes options =
  let
    { frameCount, width, height, fps } = options
    aspectRatio = toNumber width / toNumber height

    frames = mapWithIndex
      (\frame _ ->
        let
          cam = interpolateCameraAtFrame camera keyframes frame
          viewMatrix = computeViewMatrix cam
          projMatrix = computeProjectionMatrix cam aspectRatio 0.1 1000.0
        in
          { frame
          , timestamp: toNumber frame / fps
          , viewMatrix
          , projectionMatrix: projMatrix
          , position: [cam.position.x, cam.position.y, cam.position.z]
          , rotation: [cam.rotation.x, cam.rotation.y, cam.rotation.z]
          , fov: focalLengthToFOV cam.focalLength camera.filmSize
          , focalLength: cam.focalLength
          , focusDistance: cam.focusDistance
          }
      )
      (range 0 (frameCount - 1))

    metadata =
      { width
      , height
      , fps
      , totalFrames: frameCount
      , cameraType: camera.cameraType
      , filmSize: camera.filmSize
      }
  in
    { frames, metadata }

-- | Export camera for target format
exportCameraForTarget
  :: ExportTarget
  -> Camera3D
  -> Array CameraKeyframe
  -> Int
  -> Int
  -> Int
  -> Number
  -> { format :: String, data :: String }
exportCameraForTarget target camera keyframes frameCount compWidth compHeight fps =
  case target of
    TargetMotionCtrl ->
      let result = exportToMotionCtrl camera keyframes frameCount
      in { format: "motionctrl", data: serializePoses result.cameraPoses }
    TargetMotionCtrlSVD ->
      let result = exportToMotionCtrlSVD camera keyframes frameCount
      in { format: "motionctrl-svd", data: show result.motionCamera }
    TargetWan22FunCamera ->
      let result = mapToWan22FunCamera keyframes
      in { format: "wan22-fun-camera", data: show result.cameraMotion }
    TargetUni3CCamera ->
      let result = exportToUni3C camera keyframes frameCount compWidth compHeight
      in { format: "uni3c-camera", data: show result.trajType }
    TargetUni3CMotion ->
      let result = exportToUni3C camera keyframes frameCount compWidth compHeight
      in { format: "uni3c-motion", data: show result.trajType }
    TargetAnimateDiffCameraCtrl ->
      let result = exportToCameraCtrl keyframes frameCount
      in { format: "cameractrl", data: show result.motionType <> " speed=" <> show result.speed }
    TargetFullMatrices ->
      let result = exportCameraMatrices camera keyframes { frameCount, width: compWidth, height: compHeight, fps }
      in { format: "full-matrices", data: "frames=" <> show (length result.frames) }
