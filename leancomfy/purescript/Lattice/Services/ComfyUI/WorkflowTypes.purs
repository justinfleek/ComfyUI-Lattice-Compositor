-- | Lattice.Services.ComfyUI.WorkflowTypes - Workflow generation types
-- |
-- | Pure types for ComfyUI workflow generation.
-- | Node types, connections, and workflow parameters.
-- |
-- | Source: ui/src/services/comfyui/workflowTemplates.ts (types section)

module Lattice.Services.ComfyUI.WorkflowTypes
  ( -- * Core Types
    ComfyUIWorkflow
  , ComfyUINode
  , NodeConnection
  , NodeMeta
    -- * Workflow Parameters
  , WorkflowParams
  , defaultWorkflowParams
    -- * Camera Data Types
  , CameraDataUnion(..)
  , MotionCtrlCameraData
  , MotionCtrlSVDCameraData
  , Uni3CCameraData
  , Wan22FunCameraData
    -- * Motion Data
  , MotionData(..)
  , WanMoveMotionData
  , ATIMotionData
  , TrackPoint
  , TrajectoryPoint
    -- * TTM Layer
  , TTMLayer
  , TTMTrajectoryPoint
    -- * Enums
  , WanModel(..)
  , Wan22CameraMotion(..)
  , Uni3CTrajType(..)
  , MotionCtrlSVDPreset(..)
  , TTMModel(..)
  , OutputFormat(..)
  , ControlType(..)
    -- * Export Target
  , ExportTarget(..)
    -- * Validation
  , ValidationResult
  , ValidationConstants
  , validationConstants
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Foreign (Foreign)

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

-- | ComfyUI workflow is a map from node ID to node
type ComfyUIWorkflow = Foreign  -- Record of nodeId -> ComfyUINode

-- | A single node in the workflow
type ComfyUINode =
  { class_type :: String
  , inputs :: Foreign  -- Record of input name -> value or connection
  , _meta :: Maybe NodeMeta
  }

-- | Node metadata
type NodeMeta = { title :: String }

-- | Connection to another node: [nodeId, outputIndex]
type NodeConnection = Array Foreign  -- [String, Int]

--------------------------------------------------------------------------------
-- Workflow Parameters
--------------------------------------------------------------------------------

-- | Parameters for workflow generation
type WorkflowParams =
  { -- Input images
    referenceImage :: Maybe String
  , lastFrameImage :: Maybe String
  , depthSequence :: Maybe (Array String)
  , controlImages :: Maybe (Array String)
    -- Camera data
  , cameraData :: Maybe CameraDataUnion
    -- Generation settings
  , prompt :: String
  , negativePrompt :: String
  , width :: Int
  , height :: Int
  , frameCount :: Int
  , fps :: Int
  , seed :: Maybe Int
  , steps :: Maybe Int
  , cfgScale :: Maybe Number
  , denoise :: Maybe Number
    -- Model selection
  , checkpoint :: Maybe String
  , vae :: Maybe String
  , controlnetModel :: Maybe String
  , loraModel :: Maybe String
  , loraStrength :: Maybe Number
    -- Wan 2.2 specific
  , wanModel :: Maybe WanModel
  , cameraMotion :: Maybe Wan22CameraMotion
    -- Uni3C specific
  , trajType :: Maybe Uni3CTrajType
  , motionData :: Maybe MotionData
    -- MotionCtrl specific
  , motionPreset :: Maybe MotionCtrlSVDPreset
  , cameraPoses :: Maybe (Array (Array Number))
    -- TTM specific
  , ttmModel :: Maybe TTMModel
  , ttmLayers :: Maybe (Array TTMLayer)
  , ttmCombinedMask :: Maybe String
  , ttmTweakIndex :: Maybe Int
  , ttmTstrongIndex :: Maybe Int
    -- SCAIL specific
  , scailPoseVideo :: Maybe String
  , scailPoseDirectory :: Maybe String
  , scailReferenceImage :: Maybe String
    -- Output settings
  , outputFormat :: Maybe OutputFormat
  , outputFilename :: Maybe String
  }

-- | Default workflow parameters
defaultWorkflowParams :: WorkflowParams
defaultWorkflowParams =
  { referenceImage: Nothing
  , lastFrameImage: Nothing
  , depthSequence: Nothing
  , controlImages: Nothing
  , cameraData: Nothing
  , prompt: ""
  , negativePrompt: ""
  , width: 512
  , height: 512
  , frameCount: 16
  , fps: 24
  , seed: Nothing
  , steps: Nothing
  , cfgScale: Nothing
  , denoise: Nothing
  , checkpoint: Nothing
  , vae: Nothing
  , controlnetModel: Nothing
  , loraModel: Nothing
  , loraStrength: Nothing
  , wanModel: Nothing
  , cameraMotion: Nothing
  , trajType: Nothing
  , motionData: Nothing
  , motionPreset: Nothing
  , cameraPoses: Nothing
  , ttmModel: Nothing
  , ttmLayers: Nothing
  , ttmCombinedMask: Nothing
  , ttmTweakIndex: Nothing
  , ttmTstrongIndex: Nothing
  , scailPoseVideo: Nothing
  , scailPoseDirectory: Nothing
  , scailReferenceImage: Nothing
  , outputFormat: Nothing
  , outputFilename: Nothing
  }

--------------------------------------------------------------------------------
-- Camera Data Types
--------------------------------------------------------------------------------

-- | Union type for camera data variants
data CameraDataUnion
  = CameraDataMotionCtrl MotionCtrlCameraData
  | CameraDataMotionCtrlSVD MotionCtrlSVDCameraData
  | CameraDataUni3C Uni3CCameraData
  | CameraDataWan22Fun Wan22FunCameraData
  | CameraDataMatrices { matrices :: Array (Array Number) }

derive instance Generic CameraDataUnion _
instance Show CameraDataUnion where show = genericShow
instance Eq CameraDataUnion where eq = genericEq

-- | MotionCtrl camera data
type MotionCtrlCameraData =
  { poses :: Array (Array Number)
  }

-- | MotionCtrl SVD camera data
type MotionCtrlSVDCameraData =
  { preset :: MotionCtrlSVDPreset
  }

-- | Uni3C camera data
type Uni3CCameraData =
  { trajType :: Uni3CTrajType
  , custom_trajectory :: Maybe (Array TrajectoryPoint)
  }

-- | Wan 2.2 Fun camera data
type Wan22FunCameraData =
  { motionType :: Wan22CameraMotion
  }

--------------------------------------------------------------------------------
-- Motion Data
--------------------------------------------------------------------------------

-- | Motion data discriminated union
data MotionData
  = MotionDataWanMove WanMoveMotionData
  | MotionDataATI ATIMotionData

derive instance Generic MotionData _
instance Show MotionData where show = genericShow
instance Eq MotionData where eq = genericEq

-- | Wan-Move motion data: tracks of points
type WanMoveMotionData =
  { tracks :: Array (Array TrackPoint)
  }

-- | ATI motion data: trajectories
type ATIMotionData =
  { trajectories :: Array (Array TrajectoryPoint)
  }

-- | A single track point
type TrackPoint = { x :: Number, y :: Number }

-- | A single trajectory point
type TrajectoryPoint = { x :: Number, y :: Number }

--------------------------------------------------------------------------------
-- TTM Types
--------------------------------------------------------------------------------

-- | TTM layer definition
type TTMLayer =
  { layerId :: String
  , layerName :: String
  , motionMask :: String  -- Base64 PNG or filename
  , trajectory :: Array TTMTrajectoryPoint
  }

-- | TTM trajectory point with frame index
type TTMTrajectoryPoint =
  { frame :: Int
  , x :: Number
  , y :: Number
  }

--------------------------------------------------------------------------------
-- Enums
--------------------------------------------------------------------------------

-- | Wan model variants
data WanModel
  = WanI2V480p
  | WanI2V720p
  | WanT2V480p
  | WanT2V720p

derive instance Generic WanModel _
instance Show WanModel where show = genericShow
instance Eq WanModel where eq = genericEq

-- | Wan 2.2 camera motion types
data Wan22CameraMotion
  = CamStatic
  | CamPanLeft
  | CamPanRight
  | CamPanUp
  | CamPanDown
  | CamZoomIn
  | CamZoomOut
  | CamOrbit
  | CamFollow

derive instance Generic Wan22CameraMotion _
instance Show Wan22CameraMotion where show = genericShow
instance Eq Wan22CameraMotion where eq = genericEq

-- | Uni3C trajectory types
data Uni3CTrajType
  = TrajOrbit
  | TrajZoom
  | TrajPan
  | TrajCustom

derive instance Generic Uni3CTrajType _
instance Show Uni3CTrajType where show = genericShow
instance Eq Uni3CTrajType where eq = genericEq

-- | MotionCtrl SVD presets
data MotionCtrlSVDPreset
  = PresetStatic
  | PresetPushIn
  | PresetPullOut
  | PresetPanRight
  | PresetPanLeft
  | PresetOrbitRight
  | PresetOrbitLeft

derive instance Generic MotionCtrlSVDPreset _
instance Show MotionCtrlSVDPreset where show = genericShow
instance Eq MotionCtrlSVDPreset where eq = genericEq

-- | TTM model backend
data TTMModel
  = TTMWan
  | TTMCogVideoX
  | TTMSVD

derive instance Generic TTMModel _
instance Show TTMModel where show = genericShow
instance Eq TTMModel where eq = genericEq

-- | Output format
data OutputFormat
  = FormatMP4
  | FormatWebM
  | FormatGIF
  | FormatImages

derive instance Generic OutputFormat _
instance Show OutputFormat where show = genericShow
instance Eq OutputFormat where eq = genericEq

-- | ControlNet types
data ControlType
  = ControlCanny
  | ControlLineart
  | ControlSoftedge
  | ControlNormal
  | ControlSeg
  | ControlPose

derive instance Generic ControlType _
instance Show ControlType where show = genericShow
instance Eq ControlType where eq = genericEq

--------------------------------------------------------------------------------
-- Export Target
--------------------------------------------------------------------------------

-- | All supported export targets
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
  | TargetControlNetDepth
  | TargetControlNetCanny
  | TargetControlNetLineart
  | TargetAnimateDiffCameraCtrl
  | TargetTTM
  | TargetTTMWan
  | TargetTTMCogVideoX
  | TargetTTMSVD
  | TargetSCAIL
  | TargetLightX
  | TargetWanMove
  | TargetATI
  | TargetControlNetPose
  | TargetCameraComfyUI
  | TargetCustomWorkflow

derive instance Generic ExportTarget _
instance Show ExportTarget where show = genericShow
instance Eq ExportTarget where eq = genericEq

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validation result
type ValidationResult =
  { valid :: Boolean
  , errors :: Array String
  , warnings :: Array String
  }

-- | Validation constants
type ValidationConstants =
  { minDimension :: Int
  , maxDimension :: Int
  , maxFrameCount :: Int
  , maxFps :: Int
  }

-- | Default validation constants
validationConstants :: ValidationConstants
validationConstants =
  { minDimension: 64
  , maxDimension: 8192
  , maxFrameCount: 10000
  , maxFps: 120
  }
