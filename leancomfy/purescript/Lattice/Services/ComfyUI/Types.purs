-- | Lattice.Services.ComfyUI.Types - ComfyUI client types
-- |
-- | Pure types for ComfyUI server communication.
-- | HTTP and WebSocket protocol types.
-- |
-- | Source: ui/src/services/comfyui/comfyuiClient.ts

module Lattice.Services.ComfyUI.Types
  ( -- * Client Configuration
    ComfyUIClientConfig
  , defaultConfig
    -- * System Types
  , SystemStats
  , DeviceInfo
  , CudaInfo
    -- * Queue Types
  , QueueStatus
  , QueueItem
  , QueueItemPrompt
    -- * Upload Types
  , UploadResult
  , ImageType(..)
    -- * Execution Types
  , PromptResponse
  , HistoryEntry
  , HistoryOutput
  , OutputImage
    -- * WebSocket Types
  , WebSocketMessage(..)
  , ProgressData
  , ExecutingData
  , ExecutedData
  , ExecutionErrorData
    -- * Model Types
  , ModelInfo
  , ModelCategory(..)
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)

--------------------------------------------------------------------------------
-- Client Configuration
--------------------------------------------------------------------------------

-- | ComfyUI client configuration
type ComfyUIClientConfig =
  { host :: String
  , port :: Int
  , secure :: Boolean
  , clientId :: String
  , timeout :: Int          -- milliseconds
  , retryAttempts :: Int
  , retryDelay :: Int       -- milliseconds
  }

-- | Default client configuration
defaultConfig :: ComfyUIClientConfig
defaultConfig =
  { host: "127.0.0.1"
  , port: 8188
  , secure: false
  , clientId: "lattice-compositor"
  , timeout: 30000
  , retryAttempts: 3
  , retryDelay: 1000
  }

--------------------------------------------------------------------------------
-- System Types
--------------------------------------------------------------------------------

-- | System statistics from ComfyUI
type SystemStats =
  { system ::
      { os :: String
      , pythonVersion :: String
      , embeddedPython :: Boolean
      }
  , devices :: Array DeviceInfo
  }

-- | GPU device information
type DeviceInfo =
  { name :: String
  , deviceType :: String
  , index :: Int
  , vramTotal :: Number
  , vramFree :: Number
  , torchVramTotal :: Number
  , torchVramFree :: Number
  }

-- | CUDA information
type CudaInfo =
  { cudaVersion :: String
  , cudnnVersion :: String
  }

--------------------------------------------------------------------------------
-- Queue Types
--------------------------------------------------------------------------------

-- | Queue status from ComfyUI
type QueueStatus =
  { queueRunning :: Array QueueItem
  , queuePending :: Array QueueItem
  }

-- | Individual queue item
type QueueItem =
  { number :: Int
  , promptId :: String
  , prompt :: QueueItemPrompt
  }

-- | Queue item prompt data
type QueueItemPrompt =
  { clientId :: String
  }

--------------------------------------------------------------------------------
-- Upload Types
--------------------------------------------------------------------------------

-- | Result of image upload
type UploadResult =
  { name :: String
  , subfolder :: String
  , imageType :: String
  }

-- | Image type for uploads
data ImageType
  = ImageTypeInput
  | ImageTypeOutput
  | ImageTypeTemp

derive instance Generic ImageType _
instance Show ImageType where show = genericShow
instance Eq ImageType where eq = genericEq

-- | Convert ImageType to string for API
imageTypeToString :: ImageType -> String
imageTypeToString = case _ of
  ImageTypeInput -> "input"
  ImageTypeOutput -> "output"
  ImageTypeTemp -> "temp"

--------------------------------------------------------------------------------
-- Execution Types
--------------------------------------------------------------------------------

-- | Response from queueing a prompt
type PromptResponse =
  { promptId :: String
  , number :: Int
  , nodeErrors :: Array String
  }

-- | History entry for a completed prompt
type HistoryEntry =
  { promptId :: String
  , outputs :: Array HistoryOutput
  , status ::
      { completed :: Boolean
      , statusStr :: String
      }
  }

-- | Output from a history entry
type HistoryOutput =
  { nodeId :: String
  , images :: Array OutputImage
  }

-- | Output image reference
type OutputImage =
  { filename :: String
  , subfolder :: String
  , imageType :: String
  }

--------------------------------------------------------------------------------
-- WebSocket Types
--------------------------------------------------------------------------------

-- | WebSocket message types from ComfyUI
data WebSocketMessage
  = WsStatus { queueRemaining :: Int }
  | WsProgress ProgressData
  | WsExecuting ExecutingData
  | WsExecuted ExecutedData
  | WsExecutionError ExecutionErrorData
  | WsExecutionCached { nodes :: Array String, promptId :: String }
  | WsExecutionStart { promptId :: String }
  | WsExecutionInterrupted { promptId :: String }
  | WsUnknown String

derive instance Generic WebSocketMessage _
instance Show WebSocketMessage where show = genericShow
instance Eq WebSocketMessage where eq = genericEq

-- | Progress data for a node
type ProgressData =
  { value :: Int
  , max :: Int
  , promptId :: String
  , nodeId :: String
  }

-- | Executing node data
type ExecutingData =
  { nodeId :: Maybe String
  , promptId :: String
  }

-- | Executed node data
type ExecutedData =
  { nodeId :: String
  , promptId :: String
  , output :: Array OutputImage
  }

-- | Execution error data
type ExecutionErrorData =
  { promptId :: String
  , nodeId :: String
  , nodeType :: String
  , exceptionMessage :: String
  , exceptionType :: String
  , traceback :: Array String
  }

--------------------------------------------------------------------------------
-- Model Types
--------------------------------------------------------------------------------

-- | Model information
type ModelInfo =
  { name :: String
  , path :: String
  , category :: ModelCategory
  }

-- | Model categories in ComfyUI
data ModelCategory
  = ModelCheckpoints
  | ModelLoras
  | ModelVaes
  | ModelControlNets
  | ModelEmbeddings
  | ModelUpscalers
  | ModelClipVision
  | ModelOther String

derive instance Generic ModelCategory _
instance Show ModelCategory where show = genericShow
instance Eq ModelCategory where eq = genericEq

-- | Convert category to API string
modelCategoryToString :: ModelCategory -> String
modelCategoryToString = case _ of
  ModelCheckpoints -> "checkpoints"
  ModelLoras -> "loras"
  ModelVaes -> "vae"
  ModelControlNets -> "controlnet"
  ModelEmbeddings -> "embeddings"
  ModelUpscalers -> "upscale_models"
  ModelClipVision -> "clip_vision"
  ModelOther s -> s
