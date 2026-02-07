-- | Lattice.Services.ComfyUI.Client - ComfyUI HTTP/WebSocket client
-- |
-- | Client for communicating with ComfyUI server.
-- | Handles HTTP API calls and WebSocket connections.
-- |
-- | Source: ui/src/services/comfyui/comfyuiClient.ts

module Lattice.Services.ComfyUI.Client
  ( -- * Client
    ComfyUIClient
  , createClient
  , disposeClient
    -- * Connection
  , checkConnection
  , getBaseUrl
  , getWsUrl
    -- * System
  , getSystemStats
  , getQueueStatus
    -- * Uploads
  , uploadImage
  , uploadMask
  , uploadImageData
  , uploadCanvas
    -- * Execution
  , queuePrompt
  , getHistory
  , getOutput
  , interrupt
  , clearQueue
  , deleteFromQueue
    -- * Models
  , getModels
  , getCheckpoints
  , getLoras
  , getVaes
  , getControlNets
    -- * WebSocket
  , connectWebSocket
  , disconnectWebSocket
  , isWebSocketConnected
  , onMessage
  , offMessage
    -- * Convenience
  , waitForPrompt
  , executeWorkflow
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Foreign (Foreign)

import Lattice.Services.ComfyUI.Types
  ( ComfyUIClientConfig
  , SystemStats
  , QueueStatus
  , UploadResult
  , PromptResponse
  , HistoryEntry
  , OutputImage
  , WebSocketMessage(..)
  , ModelInfo
  , ModelCategory(..)
  , defaultConfig
  )

--------------------------------------------------------------------------------
-- FFI Types
--------------------------------------------------------------------------------

-- | Opaque client handle
foreign import data ComfyUIClient :: Type

-- | Opaque WebSocket handle
foreign import data WebSocketHandle :: Type

-- | Opaque canvas handle
foreign import data CanvasElement :: Type

-- | Opaque ImageData handle
foreign import data ImageData :: Type

--------------------------------------------------------------------------------
-- FFI Imports - Client
--------------------------------------------------------------------------------

-- | Create a new client
foreign import createClientImpl :: ComfyUIClientConfig -> Effect ComfyUIClient

-- | Dispose of client resources
foreign import disposeClientImpl :: ComfyUIClient -> Effect Unit

-- | Get base HTTP URL
foreign import getBaseUrlImpl :: ComfyUIClient -> Effect String

-- | Get WebSocket URL
foreign import getWsUrlImpl :: ComfyUIClient -> Effect String

--------------------------------------------------------------------------------
-- FFI Imports - HTTP API
--------------------------------------------------------------------------------

-- | Check connection
foreign import checkConnectionImpl :: ComfyUIClient -> EffectFnAff Boolean

-- | Get system stats
foreign import getSystemStatsImpl :: ComfyUIClient -> EffectFnAff SystemStats

-- | Get queue status
foreign import getQueueStatusImpl :: ComfyUIClient -> EffectFnAff QueueStatus

-- | Upload image file
foreign import uploadImageImpl
  :: ComfyUIClient
  -> Foreign  -- File or Blob
  -> String   -- filename
  -> String   -- subfolder
  -> Boolean  -- overwrite
  -> EffectFnAff UploadResult

-- | Upload mask file
foreign import uploadMaskImpl
  :: ComfyUIClient
  -> Foreign  -- File or Blob
  -> String   -- filename
  -> String   -- originalRef
  -> EffectFnAff UploadResult

-- | Upload ImageData
foreign import uploadImageDataImpl
  :: ComfyUIClient
  -> ImageData
  -> String   -- filename
  -> EffectFnAff UploadResult

-- | Upload canvas
foreign import uploadCanvasImpl
  :: ComfyUIClient
  -> CanvasElement
  -> String   -- filename
  -> EffectFnAff UploadResult

-- | Queue a prompt
foreign import queuePromptImpl
  :: ComfyUIClient
  -> Foreign  -- workflow JSON
  -> EffectFnAff PromptResponse

-- | Get history
foreign import getHistoryImpl
  :: ComfyUIClient
  -> String   -- promptId (empty for all)
  -> Int      -- maxItems
  -> EffectFnAff (Array HistoryEntry)

-- | Get output images
foreign import getOutputImpl
  :: ComfyUIClient
  -> String   -- filename
  -> String   -- subfolder
  -> String   -- imageType
  -> EffectFnAff Foreign  -- Blob

-- | Interrupt current execution
foreign import interruptImpl :: ComfyUIClient -> EffectFnAff Unit

-- | Clear queue
foreign import clearQueueImpl :: ComfyUIClient -> EffectFnAff Unit

-- | Delete from queue
foreign import deleteFromQueueImpl
  :: ComfyUIClient
  -> String   -- promptId
  -> EffectFnAff Unit

-- | Get models by category
foreign import getModelsImpl
  :: ComfyUIClient
  -> String   -- category
  -> EffectFnAff (Array ModelInfo)

--------------------------------------------------------------------------------
-- FFI Imports - WebSocket
--------------------------------------------------------------------------------

-- | Connect WebSocket
foreign import connectWebSocketImpl :: ComfyUIClient -> EffectFnAff WebSocketHandle

-- | Disconnect WebSocket
foreign import disconnectWebSocketImpl :: ComfyUIClient -> Effect Unit

-- | Check WebSocket connected
foreign import isWebSocketConnectedImpl :: ComfyUIClient -> Effect Boolean

-- | Add message listener
foreign import onMessageImpl
  :: ComfyUIClient
  -> (Foreign -> Effect Unit)
  -> Effect (Effect Unit)  -- returns unsubscribe function

-- | Remove message listener
foreign import offMessageImpl
  :: ComfyUIClient
  -> (Foreign -> Effect Unit)
  -> Effect Unit

--------------------------------------------------------------------------------
-- FFI Imports - Convenience
--------------------------------------------------------------------------------

-- | Wait for prompt completion
foreign import waitForPromptImpl
  :: ComfyUIClient
  -> String   -- promptId
  -> Int      -- timeout ms
  -> EffectFnAff (Array OutputImage)

-- | Execute workflow and wait
foreign import executeWorkflowImpl
  :: ComfyUIClient
  -> Foreign  -- workflow JSON
  -> Int      -- timeout ms
  -> EffectFnAff (Array OutputImage)

--------------------------------------------------------------------------------
-- Public API - Client
--------------------------------------------------------------------------------

-- | Create a new ComfyUI client
createClient :: ComfyUIClientConfig -> Effect ComfyUIClient
createClient = createClientImpl

-- | Create client with default configuration
createDefaultClient :: Effect ComfyUIClient
createDefaultClient = createClientImpl defaultConfig

-- | Dispose of client resources
disposeClient :: ComfyUIClient -> Effect Unit
disposeClient = disposeClientImpl

-- | Get the base HTTP URL for the client
getBaseUrl :: ComfyUIClient -> Effect String
getBaseUrl = getBaseUrlImpl

-- | Get the WebSocket URL for the client
getWsUrl :: ComfyUIClient -> Effect String
getWsUrl = getWsUrlImpl

--------------------------------------------------------------------------------
-- Public API - Connection
--------------------------------------------------------------------------------

-- | Check if ComfyUI server is reachable
checkConnection :: ComfyUIClient -> Aff Boolean
checkConnection client = fromEffectFnAff (checkConnectionImpl client)

--------------------------------------------------------------------------------
-- Public API - System
--------------------------------------------------------------------------------

-- | Get system statistics
getSystemStats :: ComfyUIClient -> Aff SystemStats
getSystemStats client = fromEffectFnAff (getSystemStatsImpl client)

-- | Get queue status
getQueueStatus :: ComfyUIClient -> Aff QueueStatus
getQueueStatus client = fromEffectFnAff (getQueueStatusImpl client)

--------------------------------------------------------------------------------
-- Public API - Uploads
--------------------------------------------------------------------------------

-- | Upload an image file
uploadImage
  :: ComfyUIClient
  -> Foreign      -- File or Blob
  -> String       -- filename
  -> String       -- subfolder
  -> Boolean      -- overwrite
  -> Aff UploadResult
uploadImage client file filename subfolder overwrite =
  fromEffectFnAff (uploadImageImpl client file filename subfolder overwrite)

-- | Upload a mask file
uploadMask
  :: ComfyUIClient
  -> Foreign      -- File or Blob
  -> String       -- filename
  -> String       -- originalRef
  -> Aff UploadResult
uploadMask client file filename originalRef =
  fromEffectFnAff (uploadMaskImpl client file filename originalRef)

-- | Upload ImageData as PNG
uploadImageData
  :: ComfyUIClient
  -> ImageData
  -> String       -- filename
  -> Aff UploadResult
uploadImageData client imageData filename =
  fromEffectFnAff (uploadImageDataImpl client imageData filename)

-- | Upload canvas as PNG
uploadCanvas
  :: ComfyUIClient
  -> CanvasElement
  -> String       -- filename
  -> Aff UploadResult
uploadCanvas client canvas filename =
  fromEffectFnAff (uploadCanvasImpl client canvas filename)

--------------------------------------------------------------------------------
-- Public API - Execution
--------------------------------------------------------------------------------

-- | Queue a prompt for execution
queuePrompt :: ComfyUIClient -> Foreign -> Aff PromptResponse
queuePrompt client workflow =
  fromEffectFnAff (queuePromptImpl client workflow)

-- | Get history for a prompt or all prompts
getHistory :: ComfyUIClient -> Maybe String -> Int -> Aff (Array HistoryEntry)
getHistory client mPromptId maxItems =
  let promptId = case mPromptId of
        Just pid -> pid
        Nothing -> ""
  in fromEffectFnAff (getHistoryImpl client promptId maxItems)

-- | Get output image as Blob
getOutput
  :: ComfyUIClient
  -> String       -- filename
  -> String       -- subfolder
  -> String       -- imageType
  -> Aff Foreign  -- Blob
getOutput client filename subfolder imageType =
  fromEffectFnAff (getOutputImpl client filename subfolder imageType)

-- | Interrupt current execution
interrupt :: ComfyUIClient -> Aff Unit
interrupt client = fromEffectFnAff (interruptImpl client)

-- | Clear the entire queue
clearQueue :: ComfyUIClient -> Aff Unit
clearQueue client = fromEffectFnAff (clearQueueImpl client)

-- | Delete a specific prompt from queue
deleteFromQueue :: ComfyUIClient -> String -> Aff Unit
deleteFromQueue client promptId =
  fromEffectFnAff (deleteFromQueueImpl client promptId)

--------------------------------------------------------------------------------
-- Public API - Models
--------------------------------------------------------------------------------

-- | Get models by category
getModels :: ComfyUIClient -> ModelCategory -> Aff (Array ModelInfo)
getModels client category =
  let categoryStr = case category of
        ModelCheckpoints -> "checkpoints"
        ModelLoras -> "loras"
        ModelVaes -> "vae"
        ModelControlNets -> "controlnet"
        ModelEmbeddings -> "embeddings"
        ModelUpscalers -> "upscale_models"
        ModelClipVision -> "clip_vision"
        ModelOther s -> s
  in fromEffectFnAff (getModelsImpl client categoryStr)

-- | Get checkpoint models
getCheckpoints :: ComfyUIClient -> Aff (Array ModelInfo)
getCheckpoints client = getModels client ModelCheckpoints

-- | Get LoRA models
getLoras :: ComfyUIClient -> Aff (Array ModelInfo)
getLoras client = getModels client ModelLoras

-- | Get VAE models
getVaes :: ComfyUIClient -> Aff (Array ModelInfo)
getVaes client = getModels client ModelVaes

-- | Get ControlNet models
getControlNets :: ComfyUIClient -> Aff (Array ModelInfo)
getControlNets client = getModels client ModelControlNets

--------------------------------------------------------------------------------
-- Public API - WebSocket
--------------------------------------------------------------------------------

-- | Connect to ComfyUI WebSocket
connectWebSocket :: ComfyUIClient -> Aff WebSocketHandle
connectWebSocket client =
  fromEffectFnAff (connectWebSocketImpl client)

-- | Disconnect WebSocket
disconnectWebSocket :: ComfyUIClient -> Effect Unit
disconnectWebSocket = disconnectWebSocketImpl

-- | Check if WebSocket is connected
isWebSocketConnected :: ComfyUIClient -> Effect Boolean
isWebSocketConnected = isWebSocketConnectedImpl

-- | Add message listener, returns unsubscribe function
onMessage
  :: ComfyUIClient
  -> (Foreign -> Effect Unit)
  -> Effect (Effect Unit)
onMessage = onMessageImpl

-- | Remove message listener
offMessage
  :: ComfyUIClient
  -> (Foreign -> Effect Unit)
  -> Effect Unit
offMessage = offMessageImpl

--------------------------------------------------------------------------------
-- Public API - Convenience
--------------------------------------------------------------------------------

-- | Wait for a prompt to complete
waitForPrompt
  :: ComfyUIClient
  -> String       -- promptId
  -> Int          -- timeout ms
  -> Aff (Array OutputImage)
waitForPrompt client promptId timeout =
  fromEffectFnAff (waitForPromptImpl client promptId timeout)

-- | Execute a workflow and wait for results
executeWorkflow
  :: ComfyUIClient
  -> Foreign      -- workflow JSON
  -> Int          -- timeout ms
  -> Aff (Array OutputImage)
executeWorkflow client workflow timeout =
  fromEffectFnAff (executeWorkflowImpl client workflow timeout)
