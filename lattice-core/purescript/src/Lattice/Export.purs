-- | Lattice.Export - Export types and ComfyUI integration
-- |
-- | Source: ui/src/types/export.ts (404 lines)
-- |
-- | Export types for video generation models and ComfyUI workflow integration.

module Lattice.Export
  ( ExportTarget(..)
  , VideoFormat(..)
  , VideoCodec(..)
  , PixelFormat(..)
  , DepthFormat(..)
  , NormalFormat(..)
  , PoseFormat(..)
  , FlowFormat(..)
  , ExportStatus(..)
  , ComfyUIInputType(..)
  , VideoEncoderOptions
  , DepthExportOptions
  , NormalExportOptions
  , PoseExportOptions
  , MotionCtrlPose
  , MotionCtrlExportData
  , Wan22CameraKeyframe
  , Wan22CameraMotion
  , Uni3CIntrinsics
  , Uni3CCameraPose
  , Uni3CCameraData
  , ComfyUIInputValue(..)
  , ComfyUIInput
  , ComfyUINode
  , ComfyUIWorkflow
  , ExportConfig
  , ExportResult
  , defaultVideoOptions
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives (NonEmptyString, FrameNumber, FiniteFloat, PositiveFloat, NonNegativeFloat, RGBA)

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

derive instance Eq ExportTarget
derive instance Generic ExportTarget _
instance Show ExportTarget where show = genericShow

-- | Output video format
data VideoFormat
  = FormatMp4   -- ^ H.264/H.265
  | FormatWebm  -- ^ VP9
  | FormatGif   -- ^ Animated GIF
  | FormatPng   -- ^ PNG sequence
  | FormatExr   -- ^ EXR sequence (HDR)

derive instance Eq VideoFormat
derive instance Generic VideoFormat _
instance Show VideoFormat where show = genericShow

-- | Video codec
data VideoCodec
  = CodecH264
  | CodecH265
  | CodecVP9
  | CodecProRes

derive instance Eq VideoCodec
derive instance Generic VideoCodec _
instance Show VideoCodec where show = genericShow

-- | Pixel format
data PixelFormat
  = PixelYuv420p
  | PixelYuv444p
  | PixelRgb24
  | PixelRgba

derive instance Eq PixelFormat
derive instance Generic PixelFormat _
instance Show PixelFormat where show = genericShow

-- | Depth map format
data DepthFormat
  = DepthGrayscale16   -- ^ 16-bit grayscale PNG
  | DepthGrayscale8    -- ^ 8-bit grayscale PNG
  | DepthExr32         -- ^ 32-bit EXR
  | DepthDisparity     -- ^ Inverse depth (disparity)

derive instance Eq DepthFormat
derive instance Generic DepthFormat _
instance Show DepthFormat where show = genericShow

-- | Normal map format
data NormalFormat
  = NormalOpenGL     -- ^ Y+ up
  | NormalDirectX    -- ^ Y- up
  | NormalWorldSpace
  | NormalViewSpace

derive instance Eq NormalFormat
derive instance Generic NormalFormat _
instance Show NormalFormat where show = genericShow

-- | Pose estimation format
data PoseFormat
  = PoseOpenpose18    -- ^ COCO 18 keypoints
  | PoseOpenpose25    -- ^ Body25
  | PoseMediapipe     -- ^ MediaPipe pose
  | PoseDWPose        -- ^ DWPose (133 keypoints)

derive instance Eq PoseFormat
derive instance Generic PoseFormat _
instance Show PoseFormat where show = genericShow

-- | Optical flow format
data FlowFormat
  = FlowFlo     -- ^ Middlebury .flo
  | FlowPng     -- ^ PNG with color coding
  | FlowExr     -- ^ EXR with raw values

derive instance Eq FlowFormat
derive instance Generic FlowFormat _
instance Show FlowFormat where show = genericShow

-- | Export result status
data ExportStatus
  = ExportSuccess
  | ExportFailed
  | ExportCancelled

derive instance Eq ExportStatus
derive instance Generic ExportStatus _
instance Show ExportStatus where show = genericShow

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

derive instance Eq ComfyUIInputType
derive instance Generic ComfyUIInputType _
instance Show ComfyUIInputType where show = genericShow

-- | Video encoder configuration
type VideoEncoderOptions =
  { format      :: VideoFormat
  , codec       :: VideoCodec
  , quality     :: Int              -- ^ 0-51 for H.264 (lower = better)
  , bitrate     :: Maybe Int        -- ^ kbps
  , pixelFormat :: PixelFormat
  , fps         :: PositiveFloat
  }

-- | Depth export configuration
type DepthExportOptions =
  { format           :: DepthFormat
  , minDepth         :: FiniteFloat
  , maxDepth         :: FiniteFloat
  , invertDepth      :: Boolean
  , normalizeToRange :: Boolean
  }

-- | Normal map export configuration
type NormalExportOptions =
  { format :: NormalFormat
  , flipY  :: Boolean
  , flipX  :: Boolean
  }

-- | Pose export configuration
type PoseExportOptions =
  { format          :: PoseFormat
  , drawSkeleton    :: Boolean
  , drawKeypoints   :: Boolean
  , keypointRadius  :: Int    -- ^ > 0
  , lineThickness   :: Int    -- ^ > 0
  , backgroundColor :: RGBA
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Camera Motion Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Single pose for MotionCtrl (18 keypoints)
type MotionCtrlPose =
  { keypoints :: Array { x :: Number, y :: Number, confidence :: Number }  -- ^ 18 keypoints
  }

-- | MotionCtrl export data
type MotionCtrlExportData =
  { poses  :: Array MotionCtrlPose
  , width  :: Int    -- ^ > 0
  , height :: Int    -- ^ > 0
  , fps    :: PositiveFloat
  }

-- | Wan 2.2 camera motion keyframe
type Wan22CameraKeyframe =
  { frame :: FrameNumber
  , pan   :: FiniteFloat  -- ^ -1 to 1
  , tilt  :: FiniteFloat  -- ^ -1 to 1
  , roll  :: FiniteFloat  -- ^ -180 to 180
  , zoom  :: FiniteFloat  -- ^ 0.5 to 2.0
  }

-- | Wan 2.2 camera motion data
type Wan22CameraMotion =
  { keyframes  :: Array Wan22CameraKeyframe
  , frameCount :: FrameNumber
  }

-- | Uni3C camera intrinsics
type Uni3CIntrinsics =
  { fx :: PositiveFloat
  , fy :: PositiveFloat
  , cx :: FiniteFloat
  , cy :: FiniteFloat
  }

-- | Uni3C camera pose (4x4 matrix, row-major)
type Uni3CCameraPose =
  { frame  :: FrameNumber
  , matrix :: Array Number  -- ^ 16 elements
  }

-- | Uni3C export data
type Uni3CCameraData =
  { intrinsics :: Uni3CIntrinsics
  , poses      :: Array Uni3CCameraPose
  , width      :: Int    -- ^ > 0
  , height     :: Int    -- ^ > 0
  , fps        :: PositiveFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- ComfyUI Types
-- ────────────────────────────────────────────────────────────────────────────

-- | ComfyUI node input value
data ComfyUIInputValue
  = CUIVInt Int
  | CUIVFloat Number
  | CUIVString String
  | CUIVBool Boolean
  | CUIVNodeRef String Int  -- ^ node_id, output_index

derive instance Eq ComfyUIInputValue
derive instance Generic ComfyUIInputValue _
instance Show ComfyUIInputValue where show = genericShow

-- | ComfyUI node input
type ComfyUIInput =
  { name      :: NonEmptyString
  , inputType :: ComfyUIInputType
  , value     :: ComfyUIInputValue
  }

-- | ComfyUI node
type ComfyUINode =
  { nodeId    :: NonEmptyString
  , classType :: NonEmptyString
  , inputs    :: Array ComfyUIInput
  }

-- | ComfyUI workflow
type ComfyUIWorkflow =
  { nodes        :: Array ComfyUINode
  , outputNodeId :: NonEmptyString
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Export Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Main export configuration
type ExportConfig =
  { target        :: ExportTarget
  , outputPath    :: NonEmptyString
  , width         :: Int    -- ^ > 0
  , height        :: Int    -- ^ > 0
  , fps           :: PositiveFloat
  , frameStart    :: FrameNumber
  , frameEnd      :: FrameNumber
  -- Options
  , videoOptions  :: Maybe VideoEncoderOptions
  , depthOptions  :: Maybe DepthExportOptions
  , normalOptions :: Maybe NormalExportOptions
  , poseOptions   :: Maybe PoseExportOptions
  , workflow      :: Maybe ComfyUIWorkflow
  }

-- | Export result
type ExportResult =
  { status       :: ExportStatus
  , outputPath   :: Maybe NonEmptyString
  , frameCount   :: Int
  , duration     :: NonNegativeFloat  -- ^ Seconds
  , fileSize     :: Int               -- ^ Bytes
  , errorMessage :: Maybe String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Default Values
-- ────────────────────────────────────────────────────────────────────────────

-- | Default video encoder options
defaultVideoOptions :: PositiveFloat -> VideoEncoderOptions
defaultVideoOptions fps =
  { format: FormatMp4
  , codec: CodecH264
  , quality: 23
  , bitrate: Nothing
  , pixelFormat: PixelYuv420p
  , fps: fps
  }
