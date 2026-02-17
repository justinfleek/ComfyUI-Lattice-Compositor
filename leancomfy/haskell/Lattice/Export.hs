{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Export
Description : Export types and ComfyUI integration
Copyright   : (c) Lattice, 2026
License     : MIT

Export types for video generation models and ComfyUI workflow integration.

Source: ui/src/types/export.ts (404 lines)
-}

module Lattice.Export
  ( -- * Enumerations
    ExportTarget(..)
  , VideoFormat(..)
  , VideoCodec(..)
  , PixelFormat(..)
  , DepthFormat(..)
  , NormalFormat(..)
  , PoseFormat(..)
  , FlowFormat(..)
  , ExportStatus(..)
  , ComfyUIInputType(..)
    -- * Encoder Options
  , VideoEncoderOptions(..)
  , DepthExportOptions(..)
  , NormalExportOptions(..)
  , PoseExportOptions(..)
    -- * Camera Motion Types
  , MotionCtrlPose(..)
  , MotionCtrlExportData(..)
  , Wan22CameraKeyframe(..)
  , Wan22CameraMotion(..)
  , Uni3CIntrinsics(..)
  , Uni3CCameraPose(..)
  , Uni3CCameraData(..)
    -- * ComfyUI Types
  , ComfyUIInputValue(..)
  , ComfyUIInput(..)
  , ComfyUINode(..)
  , ComfyUIWorkflow(..)
    -- * Export Types
  , ExportConfig(..)
  , ExportResult(..)
    -- * Default Values
  , defaultVideoOptions
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives
  ( NonEmptyString
  , FrameNumber
  , FiniteFloat
  , PositiveFloat
  , NonNegativeFloat
  , RGBA
  )

-- | Export target types (video generation models)
data ExportTarget
  = Wan22           -- ^ Wan 2.2 video generation
  | Uni3C           -- ^ Uni3C camera control
  | MotionCtrl      -- ^ MotionCtrl pose-based
  | CogVideoX       -- ^ CogVideoX
  | ControlNet      -- ^ ControlNet preprocessors
  | DepthAnything   -- ^ Depth Anything export
  | NormalMap       -- ^ Normal map export
  | PoseSequence    -- ^ OpenPose sequence
  | OpticalFlow     -- ^ Optical flow maps
  | Segmentation    -- ^ Segmentation masks
  | Custom          -- ^ Custom workflow
  deriving stock (Eq, Show, Generic)

-- | Output video format
data VideoFormat
  = FormatMp4   -- ^ H.264/H.265
  | FormatWebm  -- ^ VP9
  | FormatGif   -- ^ Animated GIF
  | FormatPng   -- ^ PNG sequence
  | FormatExr   -- ^ EXR sequence (HDR)
  deriving stock (Eq, Show, Generic)

-- | Video codec
data VideoCodec
  = CodecH264
  | CodecH265
  | CodecVP9
  | CodecProRes
  deriving stock (Eq, Show, Generic)

-- | Pixel format
data PixelFormat
  = PixelYuv420p
  | PixelYuv444p
  | PixelRgb24
  | PixelRgba
  deriving stock (Eq, Show, Generic)

-- | Depth map format
data DepthFormat
  = DepthGrayscale16   -- ^ 16-bit grayscale PNG
  | DepthGrayscale8    -- ^ 8-bit grayscale PNG
  | DepthExr32         -- ^ 32-bit EXR
  | DepthDisparity     -- ^ Inverse depth (disparity)
  deriving stock (Eq, Show, Generic)

-- | Normal map format
data NormalFormat
  = NormalOpenGL     -- ^ Y+ up
  | NormalDirectX    -- ^ Y- up
  | NormalWorldSpace
  | NormalViewSpace
  deriving stock (Eq, Show, Generic)

-- | Pose estimation format
data PoseFormat
  = PoseOpenpose18    -- ^ COCO 18 keypoints
  | PoseOpenpose25    -- ^ Body25
  | PoseMediapipe     -- ^ MediaPipe pose
  | PoseDWPose        -- ^ DWPose (133 keypoints)
  deriving stock (Eq, Show, Generic)

-- | Optical flow format
data FlowFormat
  = FlowFlo     -- ^ Middlebury .flo
  | FlowPng     -- ^ PNG with color coding
  | FlowExr     -- ^ EXR with raw values
  deriving stock (Eq, Show, Generic)

-- | Export result status
data ExportStatus
  = ExportSuccess
  | ExportFailed
  | ExportCancelled
  deriving stock (Eq, Show, Generic)

-- | ComfyUI node input type
data ComfyUIInputType
  = CUIInt
  | CUIFloat
  | CUIString
  | CUIBoolean
  | CUIImage
  | CUILatent
  | CUIModel
  | CUIClip
  | CUIVAE
  | CUIConditioning
  | CUIMask
  | CUIControlNet
  deriving stock (Eq, Show, Generic)

-- | Video encoder configuration
data VideoEncoderOptions = VideoEncoderOptions
  { veoFormat      :: !VideoFormat
  , veoCodec       :: !VideoCodec
  , veoQuality     :: !Int              -- ^ 0-51 for H.264 (lower = better)
  , veoBitrate     :: !(Maybe Int)      -- ^ kbps
  , veoPixelFormat :: !PixelFormat
  , veoFps         :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

-- | Depth export configuration
data DepthExportOptions = DepthExportOptions
  { deoFormat           :: !DepthFormat
  , deoMinDepth         :: !FiniteFloat
  , deoMaxDepth         :: !FiniteFloat
  , deoInvertDepth      :: !Bool
  , deoNormalizeToRange :: !Bool
  } deriving stock (Eq, Show, Generic)

-- | Normal map export configuration
data NormalExportOptions = NormalExportOptions
  { neoFormat :: !NormalFormat
  , neoFlipY  :: !Bool
  , neoFlipX  :: !Bool
  } deriving stock (Eq, Show, Generic)

-- | Pose export configuration
data PoseExportOptions = PoseExportOptions
  { peoFormat          :: !PoseFormat
  , peoDrawSkeleton    :: !Bool
  , peoDrawKeypoints   :: !Bool
  , peoKeypointRadius  :: !Int    -- ^ > 0
  , peoLineThickness   :: !Int    -- ^ > 0
  , peoBackgroundColor :: !RGBA
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Camera Motion Types
--------------------------------------------------------------------------------

-- | Single pose for MotionCtrl (18 keypoints)
data MotionCtrlPose = MotionCtrlPose
  { mcpKeypoints :: !(Vector (Double, Double, Double))  -- ^ (x, y, confidence) * 18
  } deriving stock (Eq, Show, Generic)

-- | MotionCtrl export data
data MotionCtrlExportData = MotionCtrlExportData
  { mcesPoses  :: !(Vector MotionCtrlPose)
  , mcesWidth  :: !Int    -- ^ > 0
  , mcesHeight :: !Int    -- ^ > 0
  , mcesFps    :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

-- | Wan 2.2 camera motion keyframe
data Wan22CameraKeyframe = Wan22CameraKeyframe
  { w22kfFrame :: !FrameNumber
  , w22kfPan   :: !FiniteFloat  -- ^ -1 to 1
  , w22kfTilt  :: !FiniteFloat  -- ^ -1 to 1
  , w22kfRoll  :: !FiniteFloat  -- ^ -180 to 180
  , w22kfZoom  :: !FiniteFloat  -- ^ 0.5 to 2.0
  } deriving stock (Eq, Show, Generic)

-- | Wan 2.2 camera motion data
data Wan22CameraMotion = Wan22CameraMotion
  { w22cmKeyframes  :: !(Vector Wan22CameraKeyframe)
  , w22cmFrameCount :: !FrameNumber
  } deriving stock (Eq, Show, Generic)

-- | Uni3C camera intrinsics
data Uni3CIntrinsics = Uni3CIntrinsics
  { uni3cFx :: !PositiveFloat
  , uni3cFy :: !PositiveFloat
  , uni3cCx :: !FiniteFloat
  , uni3cCy :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

-- | Uni3C camera pose (4x4 matrix, row-major)
data Uni3CCameraPose = Uni3CCameraPose
  { uni3cpFrame  :: !FrameNumber
  , uni3cpMatrix :: !(Vector Double)  -- ^ 16 elements
  } deriving stock (Eq, Show, Generic)

-- | Uni3C export data
data Uni3CCameraData = Uni3CCameraData
  { uni3cIntrinsics :: !Uni3CIntrinsics
  , uni3cPoses      :: !(Vector Uni3CCameraPose)
  , uni3cWidth      :: !Int    -- ^ > 0
  , uni3cHeight     :: !Int    -- ^ > 0
  , uni3cFps        :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- ComfyUI Types
--------------------------------------------------------------------------------

-- | ComfyUI node input value
data ComfyUIInputValue
  = CUIVInt !Int
  | CUIVFloat !Double
  | CUIVString !Text
  | CUIVBool !Bool
  | CUIVNodeRef !Text !Int  -- ^ node_id, output_index
  deriving stock (Eq, Show, Generic)

-- | ComfyUI node input
data ComfyUIInput = ComfyUIInput
  { cuiName      :: !NonEmptyString
  , cuiInputType :: !ComfyUIInputType
  , cuiValue     :: !ComfyUIInputValue
  } deriving stock (Eq, Show, Generic)

-- | ComfyUI node
data ComfyUINode = ComfyUINode
  { cuiNodeId    :: !NonEmptyString
  , cuiClassType :: !NonEmptyString
  , cuiInputs    :: !(Vector ComfyUIInput)
  } deriving stock (Eq, Show, Generic)

-- | ComfyUI workflow
data ComfyUIWorkflow = ComfyUIWorkflow
  { cuiNodes        :: !(Vector ComfyUINode)
  , cuiOutputNodeId :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Export Types
--------------------------------------------------------------------------------

-- | Main export configuration
data ExportConfig = ExportConfig
  { ecTarget        :: !ExportTarget
  , ecOutputPath    :: !NonEmptyString
  , ecWidth         :: !Int    -- ^ > 0
  , ecHeight        :: !Int    -- ^ > 0
  , ecFps           :: !PositiveFloat
  , ecFrameStart    :: !FrameNumber
  , ecFrameEnd      :: !FrameNumber
  -- Options
  , ecVideoOptions  :: !(Maybe VideoEncoderOptions)
  , ecDepthOptions  :: !(Maybe DepthExportOptions)
  , ecNormalOptions :: !(Maybe NormalExportOptions)
  , ecPoseOptions   :: !(Maybe PoseExportOptions)
  , ecWorkflow      :: !(Maybe ComfyUIWorkflow)
  } deriving stock (Eq, Show, Generic)

-- | Export result
data ExportResult = ExportResult
  { erStatus       :: !ExportStatus
  , erOutputPath   :: !(Maybe NonEmptyString)
  , erFrameCount   :: !Int
  , erDuration     :: !NonNegativeFloat  -- ^ Seconds
  , erFileSize     :: !Int               -- ^ Bytes
  , erErrorMessage :: !(Maybe Text)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default video encoder options
defaultVideoOptions :: PositiveFloat -> VideoEncoderOptions
defaultVideoOptions fps = VideoEncoderOptions
  { veoFormat      = FormatMp4
  , veoCodec       = CodecH264
  , veoQuality     = 23
  , veoBitrate     = Nothing
  , veoPixelFormat = PixelYuv420p
  , veoFps         = fps
  }
