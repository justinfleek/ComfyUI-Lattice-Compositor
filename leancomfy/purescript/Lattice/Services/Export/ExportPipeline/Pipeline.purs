-- | Lattice.Services.Export.ExportPipeline.Pipeline - Main pipeline orchestration
-- |
-- | FFI bindings for export pipeline execution using browser APIs.
-- |
-- | Source: ui/src/services/export/exportPipeline.ts

module Lattice.Services.Export.ExportPipeline.Pipeline
  ( -- * Pipeline Execution
    executeExport
  , exportToComfyUI
    -- * Quick Export Functions
  , quickExportDepthSequence
  , quickExportReferenceFrame
    -- * Opaque Handles
  , PipelineHandle
  , CanvasHandle
    -- * Frame Rendering
  , renderFrame
  , renderDepthSequence
  , renderControlSequence
    -- * Camera Export
  , exportCameraData
    -- * Workflow Operations
  , generateWorkflow
  , queueWorkflow
    -- * File Operations
  , saveBlob
  , uploadToComfyUI
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Maybe (Maybe(..))

import Lattice.Services.Export.ExportPipeline.Types
  ( ExportConfig
  , ExportProgress
  , ExportResult
  , ExportStage(..)
  , LayerRef
  , CameraKeyframeRef
  )
import Lattice.Services.Export.DepthRenderer.Types (DepthMapFormat)
import Lattice.Services.Export.CameraExport.Types (ExportTarget)

--------------------------------------------------------------------------------
-- Opaque Handles
--------------------------------------------------------------------------------

-- | Opaque handle to export pipeline instance
foreign import data PipelineHandle :: Type

-- | Opaque handle to OffscreenCanvas
foreign import data CanvasHandle :: Type

--------------------------------------------------------------------------------
-- Pipeline Execution
--------------------------------------------------------------------------------

-- | Create and execute an export pipeline
foreign import executeExportImpl
  :: { layers :: Array LayerRef
     , cameraKeyframes :: Array CameraKeyframeRef
     , config :: ExportConfig
     , onProgress :: ExportProgress -> Effect Unit
     }
  -> EffectFnAff ExportResult

executeExport
  :: Array LayerRef
  -> Array CameraKeyframeRef
  -> ExportConfig
  -> (ExportProgress -> Effect Unit)
  -> Aff ExportResult
executeExport layers keyframes config onProgress =
  fromEffectFnAff (executeExportImpl
    { layers
    , cameraKeyframes: keyframes
    , config
    , onProgress
    })

-- | Convenience wrapper for export
exportToComfyUI
  :: Array LayerRef
  -> Array CameraKeyframeRef
  -> ExportConfig
  -> Maybe (ExportProgress -> Effect Unit)
  -> Aff ExportResult
exportToComfyUI layers keyframes config maybeProgress =
  let
    onProgress = case maybeProgress of
      Just fn -> fn
      Nothing -> \_ -> pure unit
  in
    executeExport layers keyframes config onProgress

--------------------------------------------------------------------------------
-- Quick Export Functions
--------------------------------------------------------------------------------

-- | Quick export depth sequence
foreign import quickExportDepthSequenceImpl
  :: { layers :: Array LayerRef
     , width :: Int
     , height :: Int
     , frameCount :: Int
     , format :: String
     , onProgress :: ExportProgress -> Effect Unit
     }
  -> EffectFnAff ExportResult

quickExportDepthSequence
  :: Array LayerRef
  -> Int  -- width
  -> Int  -- height
  -> Int  -- frameCount
  -> DepthMapFormat
  -> Maybe (ExportProgress -> Effect Unit)
  -> Aff ExportResult
quickExportDepthSequence layers w h fc format maybeProgress =
  let
    formatStr = formatToString format
    onProgress = case maybeProgress of
      Just fn -> fn
      Nothing -> \_ -> pure unit
  in
    fromEffectFnAff (quickExportDepthSequenceImpl
      { layers
      , width: w
      , height: h
      , frameCount: fc
      , format: formatStr
      , onProgress
      })

-- | Quick export reference frame
foreign import quickExportReferenceFrameImpl
  :: Array LayerRef
  -> Int  -- width
  -> Int  -- height
  -> EffectFnAff (Maybe String)

quickExportReferenceFrame
  :: Array LayerRef
  -> Int  -- width
  -> Int  -- height
  -> Aff (Maybe String)
quickExportReferenceFrame layers w h =
  fromEffectFnAff (quickExportReferenceFrameImpl layers w h)

--------------------------------------------------------------------------------
-- Frame Rendering
--------------------------------------------------------------------------------

-- | Render a single frame to canvas
foreign import renderFrameImpl
  :: Array LayerRef
  -> Int  -- frameIndex
  -> Int  -- width
  -> Int  -- height
  -> Int  -- fps
  -> Effect CanvasHandle

renderFrame
  :: Array LayerRef
  -> Int  -- frameIndex
  -> Int  -- width
  -> Int  -- height
  -> Int  -- fps
  -> Effect CanvasHandle
renderFrame = renderFrameImpl

-- | Render depth sequence
foreign import renderDepthSequenceImpl
  :: { layers :: Array LayerRef
     , startFrame :: Int
     , endFrame :: Int
     , width :: Int
     , height :: Int
     , format :: String
     , outputDir :: String
     , filenamePrefix :: String
     , comfyuiServer :: Maybe String
     , onProgress :: ExportProgress -> Effect Unit
     }
  -> EffectFnAff (Array String)

renderDepthSequence
  :: Array LayerRef
  -> Int  -- startFrame
  -> Int  -- endFrame
  -> Int  -- width
  -> Int  -- height
  -> DepthMapFormat
  -> String  -- outputDir
  -> String  -- filenamePrefix
  -> Maybe String  -- comfyuiServer
  -> (ExportProgress -> Effect Unit)
  -> Aff (Array String)
renderDepthSequence layers start end w h format outDir prefix server onProgress =
  fromEffectFnAff (renderDepthSequenceImpl
    { layers
    , startFrame: start
    , endFrame: end
    , width: w
    , height: h
    , format: formatToString format
    , outputDir: outDir
    , filenamePrefix: prefix
    , comfyuiServer: server
    , onProgress
    })

-- | Render control sequence
foreign import renderControlSequenceImpl
  :: { layers :: Array LayerRef
     , startFrame :: Int
     , endFrame :: Int
     , width :: Int
     , height :: Int
     , controlType :: String
     , outputDir :: String
     , filenamePrefix :: String
     , comfyuiServer :: Maybe String
     , onProgress :: ExportProgress -> Effect Unit
     }
  -> EffectFnAff (Array String)

renderControlSequence
  :: Array LayerRef
  -> Int  -- startFrame
  -> Int  -- endFrame
  -> Int  -- width
  -> Int  -- height
  -> String  -- controlType
  -> String  -- outputDir
  -> String  -- filenamePrefix
  -> Maybe String  -- comfyuiServer
  -> (ExportProgress -> Effect Unit)
  -> Aff (Array String)
renderControlSequence layers start end w h ctrlType outDir prefix server onProgress =
  fromEffectFnAff (renderControlSequenceImpl
    { layers
    , startFrame: start
    , endFrame: end
    , width: w
    , height: h
    , controlType: ctrlType
    , outputDir: outDir
    , filenamePrefix: prefix
    , comfyuiServer: server
    , onProgress
    })

--------------------------------------------------------------------------------
-- Camera Export
--------------------------------------------------------------------------------

-- | Export camera data to JSON
foreign import exportCameraDataImpl
  :: { target :: String
     , cameraKeyframes :: Array CameraKeyframeRef
     , frameCount :: Int
     , width :: Int
     , height :: Int
     , fps :: Int
     , filenamePrefix :: String
     , comfyuiServer :: Maybe String
     }
  -> EffectFnAff String

exportCameraData
  :: ExportTarget
  -> Array CameraKeyframeRef
  -> Int  -- frameCount
  -> Int  -- width
  -> Int  -- height
  -> Int  -- fps
  -> String  -- filenamePrefix
  -> Maybe String  -- comfyuiServer
  -> Aff String
exportCameraData target keyframes fc w h fps prefix server =
  fromEffectFnAff (exportCameraDataImpl
    { target: targetToString target
    , cameraKeyframes: keyframes
    , frameCount: fc
    , width: w
    , height: h
    , fps
    , filenamePrefix: prefix
    , comfyuiServer: server
    })

--------------------------------------------------------------------------------
-- Workflow Operations
--------------------------------------------------------------------------------

-- | Generate ComfyUI workflow JSON
foreign import generateWorkflowImpl
  :: { target :: String
     , params :: WorkflowParamsRaw
     }
  -> Effect String

generateWorkflow
  :: ExportTarget
  -> WorkflowParams
  -> Effect String
generateWorkflow target params =
  generateWorkflowImpl
    { target: targetToString target
    , params: toWorkflowParamsRaw params
    }

-- | Queue workflow to ComfyUI
foreign import queueWorkflowImpl
  :: { serverUrl :: String
     , workflowJson :: String
     , onProgress :: ExportProgress -> Effect Unit
     }
  -> EffectFnAff { promptId :: String, success :: Boolean }

queueWorkflow
  :: String  -- serverUrl
  -> String  -- workflowJson
  -> (ExportProgress -> Effect Unit)
  -> Aff { promptId :: String, success :: Boolean }
queueWorkflow server workflow onProgress =
  fromEffectFnAff (queueWorkflowImpl
    { serverUrl: server
    , workflowJson: workflow
    , onProgress
    })

--------------------------------------------------------------------------------
-- File Operations
--------------------------------------------------------------------------------

-- | Save blob locally (triggers download)
foreign import saveBlobImpl
  :: CanvasHandle
  -> String  -- filename
  -> String  -- mimeType
  -> Effect String

saveBlob :: CanvasHandle -> String -> String -> Effect String
saveBlob = saveBlobImpl

-- | Upload to ComfyUI server
foreign import uploadToComfyUIImpl
  :: { serverUrl :: String
     , canvas :: CanvasHandle
     , filename :: String
     , subfolder :: String
     }
  -> EffectFnAff String

uploadToComfyUI
  :: String  -- serverUrl
  -> CanvasHandle
  -> String  -- filename
  -> String  -- subfolder
  -> Aff String
uploadToComfyUI server canvas filename subfolder =
  fromEffectFnAff (uploadToComfyUIImpl
    { serverUrl: server
    , canvas
    , filename
    , subfolder
    })

--------------------------------------------------------------------------------
-- Helper Types
--------------------------------------------------------------------------------

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

-- | Raw workflow params for FFI
type WorkflowParamsRaw =
  { referenceImage :: String
  , lastFrameImage :: String
  , depthSequence :: Array String
  , controlImages :: Array String
  , prompt :: String
  , negativePrompt :: String
  , width :: Int
  , height :: Int
  , frameCount :: Int
  , fps :: Int
  , seed :: Int
  , steps :: Int
  , cfgScale :: Number
  , outputFilename :: String
  }

toWorkflowParamsRaw :: WorkflowParams -> WorkflowParamsRaw
toWorkflowParamsRaw params =
  { referenceImage: case params.referenceImage of
      Just s -> s
      Nothing -> ""
  , lastFrameImage: case params.lastFrameImage of
      Just s -> s
      Nothing -> ""
  , depthSequence: case params.depthSequence of
      Just arr -> arr
      Nothing -> []
  , controlImages: case params.controlImages of
      Just arr -> arr
      Nothing -> []
  , prompt: params.prompt
  , negativePrompt: params.negativePrompt
  , width: params.width
  , height: params.height
  , frameCount: params.frameCount
  , fps: params.fps
  , seed: case params.seed of
      Just s -> s
      Nothing -> -1
  , steps: case params.steps of
      Just s -> s
      Nothing -> 20
  , cfgScale: case params.cfgScale of
      Just c -> c
      Nothing -> 7.0
  , outputFilename: params.outputFilename
  }

--------------------------------------------------------------------------------
-- String Conversions
--------------------------------------------------------------------------------

-- | Convert format to string
formatToString :: DepthMapFormat -> String
formatToString format = case format of
  _ -> "midas"  -- Default, actual implementation in Types module

-- | Convert target to string
targetToString :: ExportTarget -> String
targetToString target = case target of
  _ -> "controlnet-depth"  -- Default, actual implementation in Types module

