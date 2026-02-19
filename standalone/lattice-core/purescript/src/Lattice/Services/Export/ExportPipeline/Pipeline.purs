-- | Lattice.Services.Export.ExportPipeline.Pipeline - Main pipeline orchestration
-- |
-- | Pure request types for export pipeline execution.
-- | All actual rendering is done by the Haskell backend via Bridge.
-- |
-- | Source: ui/src/services/export/exportPipeline.ts

module Lattice.Services.Export.ExportPipeline.Pipeline
  ( -- * Request Types
    PipelineRequest(..)
  , WorkflowParams
    -- * Request Builders
  , mkExecuteExportRequest
  , mkQuickExportDepthRequest
  , mkQuickExportReferenceRequest
  , mkRenderFrameRequest
  , mkRenderDepthSequenceRequest
  , mkRenderControlSequenceRequest
  , mkExportCameraDataRequest
  , mkGenerateWorkflowRequest
  , mkQueueWorkflowRequest
  , mkUploadToComfyUIRequest
    -- * Pure Helpers
  , toWorkflowParams
  , formatToString
  , targetToString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

import Lattice.Services.Export.ExportPipeline.Types
  ( ExportConfig
  , ExportProgress
  , ExportResult
  , ExportStage(..)
  , LayerData
  , CameraKeyframeData
  )
import Lattice.Services.Export.DepthRenderer.Types (DepthMapFormat(..))
import Lattice.Services.Export.CameraExport.Types (ExportTarget(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Pipeline request - sent to Haskell backend
data PipelineRequest
  = ExecuteExportRequest
      { layers :: Array LayerData
      , cameraKeyframes :: Array CameraKeyframeData
      , config :: ExportConfig
      }
  | QuickExportDepthSequenceRequest
      { layers :: Array LayerData
      , width :: Int
      , height :: Int
      , frameCount :: Int
      , format :: DepthMapFormat
      }
  | QuickExportReferenceFrameRequest
      { layers :: Array LayerData
      , width :: Int
      , height :: Int
      }
  | RenderFrameRequest
      { layers :: Array LayerData
      , frameIndex :: Int
      , width :: Int
      , height :: Int
      , fps :: Int
      }
  | RenderDepthSequenceRequest
      { layers :: Array LayerData
      , startFrame :: Int
      , endFrame :: Int
      , width :: Int
      , height :: Int
      , format :: DepthMapFormat
      , outputDir :: String
      , filenamePrefix :: String
      , comfyuiServer :: Maybe String
      }
  | RenderControlSequenceRequest
      { layers :: Array LayerData
      , startFrame :: Int
      , endFrame :: Int
      , width :: Int
      , height :: Int
      , controlType :: String
      , outputDir :: String
      , filenamePrefix :: String
      , comfyuiServer :: Maybe String
      }
  | ExportCameraDataRequest
      { target :: ExportTarget
      , cameraKeyframes :: Array CameraKeyframeData
      , frameCount :: Int
      , width :: Int
      , height :: Int
      , fps :: Int
      , filenamePrefix :: String
      , comfyuiServer :: Maybe String
      }
  | GenerateWorkflowRequest
      { target :: ExportTarget
      , params :: WorkflowParams
      }
  | QueueWorkflowRequest
      { serverUrl :: String
      , workflowJson :: String
      }
  | UploadToComfyUIRequest
      { serverUrl :: String
      , imageData :: String      -- Base64 encoded
      , filename :: String
      , subfolder :: String
      }

derive instance Generic PipelineRequest _
instance Show PipelineRequest where show = genericShow
instance EncodeJson PipelineRequest where
  encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- Workflow Params
-- ────────────────────────────────────────────────────────────────────────────

-- | Workflow parameters
type WorkflowParams =
  { referenceImage :: Maybe String
  , lastFrameImage :: Maybe String
  , depthSequence :: Maybe (Array String)
  , controlImages :: Maybe (Array String)
  , prompt :: String
  , negativePrompt :: String
  , width :: Int
  , height :: Int
  , frameCount :: Int
  , fps :: Int
  , seed :: Maybe Int
  , steps :: Maybe Int
  , cfgScale :: Maybe Number
  , outputFilename :: String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create export execution request
mkExecuteExportRequest
  :: Array LayerData
  -> Array CameraKeyframeData
  -> ExportConfig
  -> PipelineRequest
mkExecuteExportRequest layers cameraKeyframes config =
  ExecuteExportRequest { layers, cameraKeyframes, config }

-- | Create quick depth export request
mkQuickExportDepthRequest
  :: Array LayerData
  -> Int
  -> Int
  -> Int
  -> DepthMapFormat
  -> PipelineRequest
mkQuickExportDepthRequest layers width height frameCount format =
  QuickExportDepthSequenceRequest { layers, width, height, frameCount, format }

-- | Create quick reference frame export request
mkQuickExportReferenceRequest
  :: Array LayerData
  -> Int
  -> Int
  -> PipelineRequest
mkQuickExportReferenceRequest layers width height =
  QuickExportReferenceFrameRequest { layers, width, height }

-- | Create frame render request
mkRenderFrameRequest
  :: Array LayerData
  -> Int
  -> Int
  -> Int
  -> Int
  -> PipelineRequest
mkRenderFrameRequest layers frameIndex width height fps =
  RenderFrameRequest { layers, frameIndex, width, height, fps }

-- | Create depth sequence render request
mkRenderDepthSequenceRequest
  :: Array LayerData
  -> Int
  -> Int
  -> Int
  -> Int
  -> DepthMapFormat
  -> String
  -> String
  -> Maybe String
  -> PipelineRequest
mkRenderDepthSequenceRequest layers startFrame endFrame width height format outputDir filenamePrefix comfyuiServer =
  RenderDepthSequenceRequest
    { layers, startFrame, endFrame, width, height, format
    , outputDir, filenamePrefix, comfyuiServer
    }

-- | Create control sequence render request
mkRenderControlSequenceRequest
  :: Array LayerData
  -> Int
  -> Int
  -> Int
  -> Int
  -> String
  -> String
  -> String
  -> Maybe String
  -> PipelineRequest
mkRenderControlSequenceRequest layers startFrame endFrame width height controlType outputDir filenamePrefix comfyuiServer =
  RenderControlSequenceRequest
    { layers, startFrame, endFrame, width, height, controlType
    , outputDir, filenamePrefix, comfyuiServer
    }

-- | Create camera data export request
mkExportCameraDataRequest
  :: ExportTarget
  -> Array CameraKeyframeData
  -> Int
  -> Int
  -> Int
  -> Int
  -> String
  -> Maybe String
  -> PipelineRequest
mkExportCameraDataRequest target cameraKeyframes frameCount width height fps filenamePrefix comfyuiServer =
  ExportCameraDataRequest
    { target, cameraKeyframes, frameCount, width, height, fps
    , filenamePrefix, comfyuiServer
    }

-- | Create workflow generation request
mkGenerateWorkflowRequest
  :: ExportTarget
  -> WorkflowParams
  -> PipelineRequest
mkGenerateWorkflowRequest target params =
  GenerateWorkflowRequest { target, params }

-- | Create workflow queue request
mkQueueWorkflowRequest
  :: String
  -> String
  -> PipelineRequest
mkQueueWorkflowRequest serverUrl workflowJson =
  QueueWorkflowRequest { serverUrl, workflowJson }

-- | Create upload request
mkUploadToComfyUIRequest
  :: String
  -> String
  -> String
  -> String
  -> PipelineRequest
mkUploadToComfyUIRequest serverUrl imageData filename subfolder =
  UploadToComfyUIRequest { serverUrl, imageData, filename, subfolder }

-- ────────────────────────────────────────────────────────────────────────────
-- Pure Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert export config to workflow params
toWorkflowParams :: ExportConfig -> Array String -> Array String -> WorkflowParams
toWorkflowParams config depthPaths controlPaths =
  { referenceImage: Nothing   -- Set by backend
  , lastFrameImage: Nothing   -- Set by backend
  , depthSequence: if config.exportDepthMap then Just depthPaths else Nothing
  , controlImages: if config.exportControlImages then Just controlPaths else Nothing
  , prompt: config.prompt
  , negativePrompt: config.negativePrompt
  , width: config.width
  , height: config.height
  , frameCount: config.frameCount
  , fps: config.fps
  , seed: config.seed
  , steps: config.steps
  , cfgScale: config.cfgScale
  , outputFilename: config.filenamePrefix <> "_output"
  }

-- | Convert format to string
formatToString :: DepthMapFormat -> String
formatToString = case _ of
  FormatRaw -> "raw"
  FormatMiDaS -> "midas"
  FormatDepthAnything -> "depth-anything"
  FormatZoeDepth -> "zoe-depth"
  FormatMarigold -> "marigold"
  FormatControlNet -> "controlnet"

-- | Convert target to string
targetToString :: ExportTarget -> String
targetToString = case _ of
  TargetControlNetDepth -> "controlnet-depth"
  TargetControlNetNormal -> "controlnet-normal"
  TargetWanMove -> "wan-move"
  TargetWanCamera -> "wan-camera"
  TargetCogVideoX -> "cogvideo-x"
  TargetFullMatrices -> "full-matrices"
  TargetCustom s -> s
