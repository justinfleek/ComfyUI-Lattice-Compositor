-- | Lattice.Services.Export.ExportPipeline.Types - Export pipeline type definitions
-- |
-- | Types for export pipeline orchestration.
-- |
-- | Source: ui/src/services/export/exportPipeline.ts

module Lattice.Services.Export.ExportPipeline.Types
  ( -- * Pipeline Options
    ExportPipelineOptions
  , RenderedFrame
    -- * Export Config
  , ExportConfig
  , defaultExportConfig
    -- * Export Progress
  , ExportProgress
  , ExportStage(..)
  , defaultExportProgress
    -- * Export Result
  , ExportResult
  , OutputFiles
  , defaultExportResult
    -- * Control Types
  , ControlType(..)
  , controlTypeToString
  , controlTypeFromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

import Lattice.Services.Export.DepthRenderer.Types (DepthMapFormat(..))
import Lattice.Services.Export.CameraExport.Types (ExportTarget(..))

--------------------------------------------------------------------------------
-- Pipeline Options
--------------------------------------------------------------------------------

-- | Export pipeline options
type ExportPipelineOptions =
  { layers :: Array LayerRef
  , cameraKeyframes :: Array CameraKeyframeRef
  , config :: ExportConfig
  }

-- | Reference to a layer (opaque in PureScript)
foreign import data LayerRef :: Type

-- | Reference to a camera keyframe (opaque in PureScript)
foreign import data CameraKeyframeRef :: Type

-- | Rendered frame data
type RenderedFrame =
  { frameIndex :: Int
  , timestamp :: Number
  , hasColorCanvas :: Boolean
  , hasDepthCanvas :: Boolean
  , hasDepthBuffer :: Boolean
  }

--------------------------------------------------------------------------------
-- Export Config
--------------------------------------------------------------------------------

-- | Full export configuration
type ExportConfig =
  { target :: ExportTarget
  , width :: Int
  , height :: Int
  , frameCount :: Int
  , fps :: Int
  , startFrame :: Int
  , endFrame :: Int
  , outputDir :: String
  , filenamePrefix :: String
  , exportDepthMap :: Boolean
  , exportControlImages :: Boolean
  , exportCameraData :: Boolean
  , exportReferenceFrame :: Boolean
  , exportLastFrame :: Boolean
  , depthFormat :: DepthMapFormat
  , controlType :: Maybe ControlType
  , prompt :: String
  , negativePrompt :: String
  , autoQueueWorkflow :: Boolean
  , comfyuiServer :: Maybe String
  , seed :: Maybe Int
  , steps :: Maybe Int
  , cfgScale :: Maybe Number
  }

-- | Default export configuration
defaultExportConfig :: ExportConfig
defaultExportConfig =
  { target: TargetControlNetDepth
  , width: 512
  , height: 512
  , frameCount: 24
  , fps: 24
  , startFrame: 0
  , endFrame: 24
  , outputDir: ""
  , filenamePrefix: "export"
  , exportDepthMap: true
  , exportControlImages: false
  , exportCameraData: false
  , exportReferenceFrame: true
  , exportLastFrame: false
  , depthFormat: FormatMiDaS
  , controlType: Nothing
  , prompt: ""
  , negativePrompt: ""
  , autoQueueWorkflow: false
  , comfyuiServer: Nothing
  , seed: Nothing
  , steps: Nothing
  , cfgScale: Nothing
  }

--------------------------------------------------------------------------------
-- Export Progress
--------------------------------------------------------------------------------

-- | Export stage
data ExportStage
  = StagePreparing
  | StageRenderingFrames
  | StageRenderingDepth
  | StageRenderingControl
  | StageExportingCamera
  | StageGeneratingWorkflow
  | StageQueuing
  | StageGenerating
  | StageComplete

derive instance Generic ExportStage _
instance Show ExportStage where show = genericShow
instance Eq ExportStage where eq = genericEq

-- | Export progress
type ExportProgress =
  { stage :: ExportStage
  , stageProgress :: Number
  , overallProgress :: Number
  , message :: String
  , currentFrame :: Maybe Int
  , totalFrames :: Maybe Int
  , preview :: Maybe String
  }

-- | Default export progress
defaultExportProgress :: ExportProgress
defaultExportProgress =
  { stage: StagePreparing
  , stageProgress: 0.0
  , overallProgress: 0.0
  , message: ""
  , currentFrame: Nothing
  , totalFrames: Nothing
  , preview: Nothing
  }

--------------------------------------------------------------------------------
-- Export Result
--------------------------------------------------------------------------------

-- | Output files from export
type OutputFiles =
  { referenceImage :: Maybe String
  , lastImage :: Maybe String
  , depthSequence :: Maybe (Array String)
  , controlSequence :: Maybe (Array String)
  , cameraData :: Maybe String
  , workflowJson :: Maybe String
  , promptId :: Maybe String
  }

-- | Export result
type ExportResult =
  { success :: Boolean
  , outputFiles :: OutputFiles
  , errors :: Array String
  , warnings :: Array String
  , duration :: Int  -- milliseconds
  }

-- | Default export result
defaultExportResult :: ExportResult
defaultExportResult =
  { success: false
  , outputFiles:
      { referenceImage: Nothing
      , lastImage: Nothing
      , depthSequence: Nothing
      , controlSequence: Nothing
      , cameraData: Nothing
      , workflowJson: Nothing
      , promptId: Nothing
      }
  , errors: []
  , warnings: []
  , duration: 0
  }

--------------------------------------------------------------------------------
-- Control Types
--------------------------------------------------------------------------------

-- | Control image preprocessing type
data ControlType
  = ControlDepth
  | ControlCanny
  | ControlLineart
  | ControlSoftEdge
  | ControlNormal

derive instance Generic ControlType _
instance Show ControlType where show = genericShow
instance Eq ControlType where eq = genericEq

-- | Convert control type to string
controlTypeToString :: ControlType -> String
controlTypeToString = case _ of
  ControlDepth -> "depth"
  ControlCanny -> "canny"
  ControlLineart -> "lineart"
  ControlSoftEdge -> "softedge"
  ControlNormal -> "normal"

-- | Parse control type from string
controlTypeFromString :: String -> Maybe ControlType
controlTypeFromString = case _ of
  "depth" -> Just ControlDepth
  "canny" -> Just ControlCanny
  "lineart" -> Just ControlLineart
  "softedge" -> Just ControlSoftEdge
  "normal" -> Just ControlNormal
  _ -> Nothing

