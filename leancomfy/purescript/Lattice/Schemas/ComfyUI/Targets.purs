-- | Lattice.Schemas.ComfyUI.Targets - Export targets and format enums
-- |
-- | Export targets and format enums for ComfyUI integration.
-- |
-- | Source: ui/src/schemas/comfyui-schema.ts

module Lattice.Schemas.ComfyUI.Targets
  ( -- Export Target
    ExportTarget(..)
  , exportTargetFromString
  , exportTargetToString
    -- Depth Map Format
  , DepthMapFormat(..)
  , depthMapFormatFromString
  , depthMapFormatToString
    -- Control Type
  , ControlType(..)
  , controlTypeFromString
  , controlTypeToString
    -- Video Format
  , VideoFormat(..)
  , videoFormatFromString
  , videoFormatToString
    -- Video Codec
  , VideoCodec(..)
  , videoCodecFromString
  , videoCodecToString
    -- Frame Sequence Format
  , FrameSequenceFormat(..)
  , frameSequenceFormatFromString
  , frameSequenceFormatToString
    -- Depth Colormap
  , DepthColormap(..)
  , depthColormapFromString
  , depthColormapToString
    -- Export Stage
  , ExportStage(..)
  , exportStageFromString
  , exportStageToString
    -- Generation Status
  , GenerationStatus(..)
  , generationStatusFromString
  , generationStatusToString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

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

derive instance Eq ExportTarget
derive instance Generic ExportTarget _

instance Show ExportTarget where
  show = genericShow

exportTargetFromString :: String -> Maybe ExportTarget
exportTargetFromString = case _ of
  "wan22-i2v" -> Just TargetWan22I2V
  "wan22-t2v" -> Just TargetWan22T2V
  "wan22-fun-camera" -> Just TargetWan22FunCamera
  "wan22-first-last" -> Just TargetWan22FirstLast
  "uni3c-camera" -> Just TargetUni3CCamera
  "uni3c-motion" -> Just TargetUni3CMotion
  "motionctrl" -> Just TargetMotionCtrl
  "motionctrl-svd" -> Just TargetMotionCtrlSVD
  "cogvideox" -> Just TargetCogVideoX
  "controlnet-depth" -> Just TargetControlnetDepth
  "controlnet-canny" -> Just TargetControlnetCanny
  "controlnet-lineart" -> Just TargetControlnetLineart
  "controlnet-pose" -> Just TargetControlnetPose
  "animatediff-cameractrl" -> Just TargetAnimateDiffCameraCtrl
  "custom-workflow" -> Just TargetCustomWorkflow
  "light-x" -> Just TargetLightX
  "wan-move" -> Just TargetWanMove
  "ati" -> Just TargetATI
  "ttm" -> Just TargetTTM
  "ttm-wan" -> Just TargetTTMWan
  "ttm-cogvideox" -> Just TargetTTMCogVideoX
  "ttm-svd" -> Just TargetTTMSVD
  "scail" -> Just TargetScail
  "camera-comfyui" -> Just TargetCameraComfyUI
  _ -> Nothing

exportTargetToString :: ExportTarget -> String
exportTargetToString = case _ of
  TargetWan22I2V -> "wan22-i2v"
  TargetWan22T2V -> "wan22-t2v"
  TargetWan22FunCamera -> "wan22-fun-camera"
  TargetWan22FirstLast -> "wan22-first-last"
  TargetUni3CCamera -> "uni3c-camera"
  TargetUni3CMotion -> "uni3c-motion"
  TargetMotionCtrl -> "motionctrl"
  TargetMotionCtrlSVD -> "motionctrl-svd"
  TargetCogVideoX -> "cogvideox"
  TargetControlnetDepth -> "controlnet-depth"
  TargetControlnetCanny -> "controlnet-canny"
  TargetControlnetLineart -> "controlnet-lineart"
  TargetControlnetPose -> "controlnet-pose"
  TargetAnimateDiffCameraCtrl -> "animatediff-cameractrl"
  TargetCustomWorkflow -> "custom-workflow"
  TargetLightX -> "light-x"
  TargetWanMove -> "wan-move"
  TargetATI -> "ati"
  TargetTTM -> "ttm"
  TargetTTMWan -> "ttm-wan"
  TargetTTMCogVideoX -> "ttm-cogvideox"
  TargetTTMSVD -> "ttm-svd"
  TargetScail -> "scail"
  TargetCameraComfyUI -> "camera-comfyui"

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

derive instance Eq DepthMapFormat
derive instance Generic DepthMapFormat _

instance Show DepthMapFormat where
  show = genericShow

depthMapFormatFromString :: String -> Maybe DepthMapFormat
depthMapFormatFromString = case _ of
  "raw" -> Just DepthRaw
  "midas" -> Just DepthMidas
  "zoe" -> Just DepthZoe
  "depth-pro" -> Just DepthPro
  "depth-anything" -> Just DepthAnything
  "marigold" -> Just DepthMarigold
  "normalized" -> Just DepthNormalized
  _ -> Nothing

depthMapFormatToString :: DepthMapFormat -> String
depthMapFormatToString = case _ of
  DepthRaw -> "raw"
  DepthMidas -> "midas"
  DepthZoe -> "zoe"
  DepthPro -> "depth-pro"
  DepthAnything -> "depth-anything"
  DepthMarigold -> "marigold"
  DepthNormalized -> "normalized"

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

derive instance Eq ControlType
derive instance Generic ControlType _

instance Show ControlType where
  show = genericShow

controlTypeFromString :: String -> Maybe ControlType
controlTypeFromString = case _ of
  "depth" -> Just ControlDepth
  "canny" -> Just ControlCanny
  "lineart" -> Just ControlLineart
  "softedge" -> Just ControlSoftedge
  "normal" -> Just ControlNormal
  "scribble" -> Just ControlScribble
  "seg" -> Just ControlSeg
  "pose" -> Just ControlPose
  _ -> Nothing

controlTypeToString :: ControlType -> String
controlTypeToString = case _ of
  ControlDepth -> "depth"
  ControlCanny -> "canny"
  ControlLineart -> "lineart"
  ControlSoftedge -> "softedge"
  ControlNormal -> "normal"
  ControlScribble -> "scribble"
  ControlSeg -> "seg"
  ControlPose -> "pose"

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

derive instance Eq VideoFormat
derive instance Generic VideoFormat _

instance Show VideoFormat where
  show = genericShow

videoFormatFromString :: String -> Maybe VideoFormat
videoFormatFromString = case _ of
  "mp4" -> Just VideoMP4
  "webm" -> Just VideoWebM
  "gif" -> Just VideoGIF
  "webp" -> Just VideoWebP
  "image_sequence" -> Just VideoImageSequence
  _ -> Nothing

videoFormatToString :: VideoFormat -> String
videoFormatToString = case _ of
  VideoMP4 -> "mp4"
  VideoWebM -> "webm"
  VideoGIF -> "gif"
  VideoWebP -> "webp"
  VideoImageSequence -> "image_sequence"

--------------------------------------------------------------------------------
-- Video Codec
--------------------------------------------------------------------------------

-- | Video codec options
data VideoCodec = CodecH264 | CodecH265 | CodecVP9 | CodecAV1

derive instance Eq VideoCodec
derive instance Generic VideoCodec _

instance Show VideoCodec where
  show = genericShow

videoCodecFromString :: String -> Maybe VideoCodec
videoCodecFromString = case _ of
  "h264" -> Just CodecH264
  "h265" -> Just CodecH265
  "vp9" -> Just CodecVP9
  "av1" -> Just CodecAV1
  _ -> Nothing

videoCodecToString :: VideoCodec -> String
videoCodecToString = case _ of
  CodecH264 -> "h264"
  CodecH265 -> "h265"
  CodecVP9 -> "vp9"
  CodecAV1 -> "av1"

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

derive instance Eq FrameSequenceFormat
derive instance Generic FrameSequenceFormat _

instance Show FrameSequenceFormat where
  show = genericShow

frameSequenceFormatFromString :: String -> Maybe FrameSequenceFormat
frameSequenceFormatFromString = case _ of
  "png" -> Just SeqPNG
  "jpeg" -> Just SeqJPEG
  "webp" -> Just SeqWebP
  "tiff" -> Just SeqTIFF
  "exr" -> Just SeqEXR
  "dpx" -> Just SeqDPX
  _ -> Nothing

frameSequenceFormatToString :: FrameSequenceFormat -> String
frameSequenceFormatToString = case _ of
  SeqPNG -> "png"
  SeqJPEG -> "jpeg"
  SeqWebP -> "webp"
  SeqTIFF -> "tiff"
  SeqEXR -> "exr"
  SeqDPX -> "dpx"

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

derive instance Eq DepthColormap
derive instance Generic DepthColormap _

instance Show DepthColormap where
  show = genericShow

depthColormapFromString :: String -> Maybe DepthColormap
depthColormapFromString = case _ of
  "grayscale" -> Just ColormapGrayscale
  "viridis" -> Just ColormapViridis
  "magma" -> Just ColormapMagma
  "plasma" -> Just ColormapPlasma
  "inferno" -> Just ColormapInferno
  "turbo" -> Just ColormapTurbo
  _ -> Nothing

depthColormapToString :: DepthColormap -> String
depthColormapToString = case _ of
  ColormapGrayscale -> "grayscale"
  ColormapViridis -> "viridis"
  ColormapMagma -> "magma"
  ColormapPlasma -> "plasma"
  ColormapInferno -> "inferno"
  ColormapTurbo -> "turbo"

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

derive instance Eq ExportStage
derive instance Generic ExportStage _

instance Show ExportStage where
  show = genericShow

exportStageFromString :: String -> Maybe ExportStage
exportStageFromString = case _ of
  "preparing" -> Just StagePreparing
  "rendering_frames" -> Just StageRenderingFrames
  "rendering_depth" -> Just StageRenderingDepth
  "rendering_control" -> Just StageRenderingControl
  "exporting_camera" -> Just StageExportingCamera
  "generating_workflow" -> Just StageGeneratingWorkflow
  "uploading" -> Just StageUploading
  "queuing" -> Just StageQueuing
  "generating" -> Just StageGenerating
  "downloading" -> Just StageDownloading
  "complete" -> Just StageComplete
  "error" -> Just StageError
  _ -> Nothing

exportStageToString :: ExportStage -> String
exportStageToString = case _ of
  StagePreparing -> "preparing"
  StageRenderingFrames -> "rendering_frames"
  StageRenderingDepth -> "rendering_depth"
  StageRenderingControl -> "rendering_control"
  StageExportingCamera -> "exporting_camera"
  StageGeneratingWorkflow -> "generating_workflow"
  StageUploading -> "uploading"
  StageQueuing -> "queuing"
  StageGenerating -> "generating"
  StageDownloading -> "downloading"
  StageComplete -> "complete"
  StageError -> "error"

--------------------------------------------------------------------------------
-- Generation Status
--------------------------------------------------------------------------------

-- | Generation status options
data GenerationStatus
  = GenQueued
  | GenExecuting
  | GenCompleted
  | GenError

derive instance Eq GenerationStatus
derive instance Generic GenerationStatus _

instance Show GenerationStatus where
  show = genericShow

generationStatusFromString :: String -> Maybe GenerationStatus
generationStatusFromString = case _ of
  "queued" -> Just GenQueued
  "executing" -> Just GenExecuting
  "completed" -> Just GenCompleted
  "error" -> Just GenError
  _ -> Nothing

generationStatusToString :: GenerationStatus -> String
generationStatusToString = case _ of
  GenQueued -> "queued"
  GenExecuting -> "executing"
  GenCompleted -> "completed"
  GenError -> "error"
