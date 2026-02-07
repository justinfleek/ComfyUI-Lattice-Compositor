{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.ComfyUI.Targets
Description : Export targets and format enums for ComfyUI
Copyright   : (c) Lattice, 2026
License     : MIT

Export targets and format enums for ComfyUI integration.

Source: ui/src/schemas/comfyui-schema.ts
-}

module Lattice.Schemas.ComfyUI.Targets
  ( -- * Export Target
    ExportTarget(..)
  , exportTargetFromText
  , exportTargetToText
    -- * Depth Map Format
  , DepthMapFormat(..)
  , depthMapFormatFromText
  , depthMapFormatToText
    -- * Control Type
  , ControlType(..)
  , controlTypeFromText
  , controlTypeToText
    -- * Video Format
  , VideoFormat(..)
  , videoFormatFromText
  , videoFormatToText
    -- * Video Codec
  , VideoCodec(..)
  , videoCodecFromText
  , videoCodecToText
    -- * Frame Sequence Format
  , FrameSequenceFormat(..)
  , frameSequenceFormatFromText
  , frameSequenceFormatToText
    -- * Depth Colormap
  , DepthColormap(..)
  , depthColormapFromText
  , depthColormapToText
    -- * Export Stage
  , ExportStage(..)
  , exportStageFromText
  , exportStageToText
    -- * Generation Status
  , GenerationStatus(..)
  , generationStatusFromText
  , generationStatusToText
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Export Target
--------------------------------------------------------------------------------

-- | Export target options
data ExportTarget
  = TargetWan22I2V
  | TargetWan22T2V
  | TargetWan22FunCamera
  | TargetWan22FirstLast
  | TargetUni3CCamera
  | TargetUni3CMotion
  | TargetMotionCtrl
  | TargetMotionCtrlSVD
  | TargetCogVideoX
  | TargetControlnetDepth
  | TargetControlnetCanny
  | TargetControlnetLineart
  | TargetControlnetPose
  | TargetAnimateDiffCameraCtrl
  | TargetCustomWorkflow
  | TargetLightX
  | TargetWanMove
  | TargetATI
  | TargetTTM
  | TargetTTMWan
  | TargetTTMCogVideoX
  | TargetTTMSVD
  | TargetScail
  | TargetCameraComfyUI
  deriving stock (Eq, Show, Generic, Enum, Bounded)

exportTargetFromText :: Text -> Maybe ExportTarget
exportTargetFromText "wan22-i2v" = Just TargetWan22I2V
exportTargetFromText "wan22-t2v" = Just TargetWan22T2V
exportTargetFromText "wan22-fun-camera" = Just TargetWan22FunCamera
exportTargetFromText "wan22-first-last" = Just TargetWan22FirstLast
exportTargetFromText "uni3c-camera" = Just TargetUni3CCamera
exportTargetFromText "uni3c-motion" = Just TargetUni3CMotion
exportTargetFromText "motionctrl" = Just TargetMotionCtrl
exportTargetFromText "motionctrl-svd" = Just TargetMotionCtrlSVD
exportTargetFromText "cogvideox" = Just TargetCogVideoX
exportTargetFromText "controlnet-depth" = Just TargetControlnetDepth
exportTargetFromText "controlnet-canny" = Just TargetControlnetCanny
exportTargetFromText "controlnet-lineart" = Just TargetControlnetLineart
exportTargetFromText "controlnet-pose" = Just TargetControlnetPose
exportTargetFromText "animatediff-cameractrl" = Just TargetAnimateDiffCameraCtrl
exportTargetFromText "custom-workflow" = Just TargetCustomWorkflow
exportTargetFromText "light-x" = Just TargetLightX
exportTargetFromText "wan-move" = Just TargetWanMove
exportTargetFromText "ati" = Just TargetATI
exportTargetFromText "ttm" = Just TargetTTM
exportTargetFromText "ttm-wan" = Just TargetTTMWan
exportTargetFromText "ttm-cogvideox" = Just TargetTTMCogVideoX
exportTargetFromText "ttm-svd" = Just TargetTTMSVD
exportTargetFromText "scail" = Just TargetScail
exportTargetFromText "camera-comfyui" = Just TargetCameraComfyUI
exportTargetFromText _ = Nothing

exportTargetToText :: ExportTarget -> Text
exportTargetToText TargetWan22I2V = "wan22-i2v"
exportTargetToText TargetWan22T2V = "wan22-t2v"
exportTargetToText TargetWan22FunCamera = "wan22-fun-camera"
exportTargetToText TargetWan22FirstLast = "wan22-first-last"
exportTargetToText TargetUni3CCamera = "uni3c-camera"
exportTargetToText TargetUni3CMotion = "uni3c-motion"
exportTargetToText TargetMotionCtrl = "motionctrl"
exportTargetToText TargetMotionCtrlSVD = "motionctrl-svd"
exportTargetToText TargetCogVideoX = "cogvideox"
exportTargetToText TargetControlnetDepth = "controlnet-depth"
exportTargetToText TargetControlnetCanny = "controlnet-canny"
exportTargetToText TargetControlnetLineart = "controlnet-lineart"
exportTargetToText TargetControlnetPose = "controlnet-pose"
exportTargetToText TargetAnimateDiffCameraCtrl = "animatediff-cameractrl"
exportTargetToText TargetCustomWorkflow = "custom-workflow"
exportTargetToText TargetLightX = "light-x"
exportTargetToText TargetWanMove = "wan-move"
exportTargetToText TargetATI = "ati"
exportTargetToText TargetTTM = "ttm"
exportTargetToText TargetTTMWan = "ttm-wan"
exportTargetToText TargetTTMCogVideoX = "ttm-cogvideox"
exportTargetToText TargetTTMSVD = "ttm-svd"
exportTargetToText TargetScail = "scail"
exportTargetToText TargetCameraComfyUI = "camera-comfyui"

--------------------------------------------------------------------------------
-- Depth Map Format
--------------------------------------------------------------------------------

-- | Depth map format options
data DepthMapFormat
  = DepthRaw
  | DepthMidas
  | DepthZoe
  | DepthPro
  | DepthAnything
  | DepthMarigold
  | DepthNormalized
  deriving stock (Eq, Show, Generic, Enum, Bounded)

depthMapFormatFromText :: Text -> Maybe DepthMapFormat
depthMapFormatFromText "raw" = Just DepthRaw
depthMapFormatFromText "midas" = Just DepthMidas
depthMapFormatFromText "zoe" = Just DepthZoe
depthMapFormatFromText "depth-pro" = Just DepthPro
depthMapFormatFromText "depth-anything" = Just DepthAnything
depthMapFormatFromText "marigold" = Just DepthMarigold
depthMapFormatFromText "normalized" = Just DepthNormalized
depthMapFormatFromText _ = Nothing

depthMapFormatToText :: DepthMapFormat -> Text
depthMapFormatToText DepthRaw = "raw"
depthMapFormatToText DepthMidas = "midas"
depthMapFormatToText DepthZoe = "zoe"
depthMapFormatToText DepthPro = "depth-pro"
depthMapFormatToText DepthAnything = "depth-anything"
depthMapFormatToText DepthMarigold = "marigold"
depthMapFormatToText DepthNormalized = "normalized"

--------------------------------------------------------------------------------
-- Control Type
--------------------------------------------------------------------------------

-- | Control type options
data ControlType
  = ControlDepth
  | ControlCanny
  | ControlLineart
  | ControlSoftedge
  | ControlNormal
  | ControlScribble
  | ControlSeg
  | ControlPose
  deriving stock (Eq, Show, Generic, Enum, Bounded)

controlTypeFromText :: Text -> Maybe ControlType
controlTypeFromText "depth" = Just ControlDepth
controlTypeFromText "canny" = Just ControlCanny
controlTypeFromText "lineart" = Just ControlLineart
controlTypeFromText "softedge" = Just ControlSoftedge
controlTypeFromText "normal" = Just ControlNormal
controlTypeFromText "scribble" = Just ControlScribble
controlTypeFromText "seg" = Just ControlSeg
controlTypeFromText "pose" = Just ControlPose
controlTypeFromText _ = Nothing

controlTypeToText :: ControlType -> Text
controlTypeToText ControlDepth = "depth"
controlTypeToText ControlCanny = "canny"
controlTypeToText ControlLineart = "lineart"
controlTypeToText ControlSoftedge = "softedge"
controlTypeToText ControlNormal = "normal"
controlTypeToText ControlScribble = "scribble"
controlTypeToText ControlSeg = "seg"
controlTypeToText ControlPose = "pose"

--------------------------------------------------------------------------------
-- Video Format
--------------------------------------------------------------------------------

-- | Video format options
data VideoFormat
  = VideoMP4
  | VideoWebM
  | VideoGIF
  | VideoWebP
  | VideoImageSequence
  deriving stock (Eq, Show, Generic, Enum, Bounded)

videoFormatFromText :: Text -> Maybe VideoFormat
videoFormatFromText "mp4" = Just VideoMP4
videoFormatFromText "webm" = Just VideoWebM
videoFormatFromText "gif" = Just VideoGIF
videoFormatFromText "webp" = Just VideoWebP
videoFormatFromText "image_sequence" = Just VideoImageSequence
videoFormatFromText _ = Nothing

videoFormatToText :: VideoFormat -> Text
videoFormatToText VideoMP4 = "mp4"
videoFormatToText VideoWebM = "webm"
videoFormatToText VideoGIF = "gif"
videoFormatToText VideoWebP = "webp"
videoFormatToText VideoImageSequence = "image_sequence"

--------------------------------------------------------------------------------
-- Video Codec
--------------------------------------------------------------------------------

-- | Video codec options
data VideoCodec = CodecH264 | CodecH265 | CodecVP9 | CodecAV1
  deriving stock (Eq, Show, Generic, Enum, Bounded)

videoCodecFromText :: Text -> Maybe VideoCodec
videoCodecFromText "h264" = Just CodecH264
videoCodecFromText "h265" = Just CodecH265
videoCodecFromText "vp9" = Just CodecVP9
videoCodecFromText "av1" = Just CodecAV1
videoCodecFromText _ = Nothing

videoCodecToText :: VideoCodec -> Text
videoCodecToText CodecH264 = "h264"
videoCodecToText CodecH265 = "h265"
videoCodecToText CodecVP9 = "vp9"
videoCodecToText CodecAV1 = "av1"

--------------------------------------------------------------------------------
-- Frame Sequence Format
--------------------------------------------------------------------------------

-- | Frame sequence format options
data FrameSequenceFormat
  = SeqPNG
  | SeqJPEG
  | SeqWebP
  | SeqTIFF
  | SeqEXR
  | SeqDPX
  deriving stock (Eq, Show, Generic, Enum, Bounded)

frameSequenceFormatFromText :: Text -> Maybe FrameSequenceFormat
frameSequenceFormatFromText "png" = Just SeqPNG
frameSequenceFormatFromText "jpeg" = Just SeqJPEG
frameSequenceFormatFromText "webp" = Just SeqWebP
frameSequenceFormatFromText "tiff" = Just SeqTIFF
frameSequenceFormatFromText "exr" = Just SeqEXR
frameSequenceFormatFromText "dpx" = Just SeqDPX
frameSequenceFormatFromText _ = Nothing

frameSequenceFormatToText :: FrameSequenceFormat -> Text
frameSequenceFormatToText SeqPNG = "png"
frameSequenceFormatToText SeqJPEG = "jpeg"
frameSequenceFormatToText SeqWebP = "webp"
frameSequenceFormatToText SeqTIFF = "tiff"
frameSequenceFormatToText SeqEXR = "exr"
frameSequenceFormatToText SeqDPX = "dpx"

--------------------------------------------------------------------------------
-- Depth Colormap
--------------------------------------------------------------------------------

-- | Depth colormap options
data DepthColormap
  = ColormapGrayscale
  | ColormapViridis
  | ColormapMagma
  | ColormapPlasma
  | ColormapInferno
  | ColormapTurbo
  deriving stock (Eq, Show, Generic, Enum, Bounded)

depthColormapFromText :: Text -> Maybe DepthColormap
depthColormapFromText "grayscale" = Just ColormapGrayscale
depthColormapFromText "viridis" = Just ColormapViridis
depthColormapFromText "magma" = Just ColormapMagma
depthColormapFromText "plasma" = Just ColormapPlasma
depthColormapFromText "inferno" = Just ColormapInferno
depthColormapFromText "turbo" = Just ColormapTurbo
depthColormapFromText _ = Nothing

depthColormapToText :: DepthColormap -> Text
depthColormapToText ColormapGrayscale = "grayscale"
depthColormapToText ColormapViridis = "viridis"
depthColormapToText ColormapMagma = "magma"
depthColormapToText ColormapPlasma = "plasma"
depthColormapToText ColormapInferno = "inferno"
depthColormapToText ColormapTurbo = "turbo"

--------------------------------------------------------------------------------
-- Export Stage
--------------------------------------------------------------------------------

-- | Export progress stage
data ExportStage
  = StagePreparing
  | StageRenderingFrames
  | StageRenderingDepth
  | StageRenderingControl
  | StageExportingCamera
  | StageGeneratingWorkflow
  | StageUploading
  | StageQueuing
  | StageGenerating
  | StageDownloading
  | StageComplete
  | StageError
  deriving stock (Eq, Show, Generic, Enum, Bounded)

exportStageFromText :: Text -> Maybe ExportStage
exportStageFromText "preparing" = Just StagePreparing
exportStageFromText "rendering_frames" = Just StageRenderingFrames
exportStageFromText "rendering_depth" = Just StageRenderingDepth
exportStageFromText "rendering_control" = Just StageRenderingControl
exportStageFromText "exporting_camera" = Just StageExportingCamera
exportStageFromText "generating_workflow" = Just StageGeneratingWorkflow
exportStageFromText "uploading" = Just StageUploading
exportStageFromText "queuing" = Just StageQueuing
exportStageFromText "generating" = Just StageGenerating
exportStageFromText "downloading" = Just StageDownloading
exportStageFromText "complete" = Just StageComplete
exportStageFromText "error" = Just StageError
exportStageFromText _ = Nothing

exportStageToText :: ExportStage -> Text
exportStageToText StagePreparing = "preparing"
exportStageToText StageRenderingFrames = "rendering_frames"
exportStageToText StageRenderingDepth = "rendering_depth"
exportStageToText StageRenderingControl = "rendering_control"
exportStageToText StageExportingCamera = "exporting_camera"
exportStageToText StageGeneratingWorkflow = "generating_workflow"
exportStageToText StageUploading = "uploading"
exportStageToText StageQueuing = "queuing"
exportStageToText StageGenerating = "generating"
exportStageToText StageDownloading = "downloading"
exportStageToText StageComplete = "complete"
exportStageToText StageError = "error"

--------------------------------------------------------------------------------
-- Generation Status
--------------------------------------------------------------------------------

-- | Generation status options
data GenerationStatus
  = GenQueued
  | GenExecuting
  | GenCompleted
  | GenError
  deriving stock (Eq, Show, Generic, Enum, Bounded)

generationStatusFromText :: Text -> Maybe GenerationStatus
generationStatusFromText "queued" = Just GenQueued
generationStatusFromText "executing" = Just GenExecuting
generationStatusFromText "completed" = Just GenCompleted
generationStatusFromText "error" = Just GenError
generationStatusFromText _ = Nothing

generationStatusToText :: GenerationStatus -> Text
generationStatusToText GenQueued = "queued"
generationStatusToText GenExecuting = "executing"
generationStatusToText GenCompleted = "completed"
generationStatusToText GenError = "error"
