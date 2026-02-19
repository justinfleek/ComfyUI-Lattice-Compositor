-- | Lattice.Services.RenderQueue.Manager.Types - Manager types
-- |
-- | @module Lattice.Services.RenderQueue.Manager.Types
-- | @description Core types for the render queue manager.
-- |
-- | Timing and ID generation are provided as pure types/requests.
-- | Actual timing is handled by the runtime or backend.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts

module Lattice.Services.RenderQueue.Manager.Types
  ( -- * Types
    RenderQueueManager
  , FrameRenderer
  , ManagerState
    -- * Request Types
  , TimerRequest(..)
  , TimerAction(..)
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Services.RenderQueue.Types
  ( RenderJob
  , RenderJobProgress
  , RenderedFrame
  , RenderQueueConfig
  )
import Lattice.Services.RenderQueue.Database (RenderQueueDB)

-- | Frame renderer callback type
-- |
-- | @param compositionId ID of composition to render
-- | @param frame Frame number to render
-- | @param width Output width in pixels
-- | @param height Output height in pixels
-- | @returns Base64-encoded rendered frame
-- |
-- | @example
-- | ```purescript
-- | renderer :: FrameRenderer
-- | renderer compId frame w h = do
-- |   -- Render frame using LatticeEngine
-- |   engine.renderFrame compId frame w h
-- | ```
type FrameRenderer = String -> Int -> Int -> Int -> Aff String

-- | Manager state (internal)
-- |
-- | @field jobs Map of job ID to job
-- | @field activeJobId Currently rendering job (if any)
-- | @field isRunning Whether queue is processing
-- | @field isPaused Whether queue is paused
-- | @field startTime When current job started
-- | @field framesRenderedThisSession Frames rendered since queue started
type ManagerState =
  { jobs :: Map String RenderJob
  , activeJobId :: Maybe String
  , isRunning :: Boolean
  , isPaused :: Boolean
  , startTime :: Number
  , framesRenderedThisSession :: Int
  }

-- | Render queue manager
-- |
-- | @field config Queue configuration
-- | @field db Database reference
-- | @field state Mutable manager state
-- | @field frameRenderer User-provided frame renderer
-- | @field onProgressCb Progress callback
-- | @field onJobCompleteCb Job complete callback
-- | @field onJobErrorCb Job error callback
-- | @field onQueueEmptyCb Queue empty callback
-- | @field autoSaveTimer Auto-save interval timer ID
type RenderQueueManager =
  { config :: RenderQueueConfig
  , db :: Ref (Maybe RenderQueueDB)
  , state :: Ref ManagerState
  , frameRenderer :: Ref (Maybe FrameRenderer)
  , onProgressCb :: Ref (Maybe (String -> RenderJobProgress -> Effect Unit))
  , onJobCompleteCb :: Ref (Maybe (String -> Array RenderedFrame -> Effect Unit))
  , onJobErrorCb :: Ref (Maybe (String -> String -> Effect Unit))
  , onQueueEmptyCb :: Ref (Maybe (Effect Unit))
  , autoSaveTimer :: Ref (Maybe Int)
  }

-- | Timer actions
data TimerAction
  = SetInterval
  | ClearInterval

derive instance Eq TimerAction
derive instance Generic TimerAction _
instance Show TimerAction where show = genericShow

-- | Request to manage a timer
-- |
-- | The runtime handles actual timer management.
-- | This is a pure representation of the request.
data TimerRequest = TimerRequest
  { action :: TimerAction
  , intervalMs :: Maybe Int      -- For SetInterval
  , timerId :: Maybe Int         -- For ClearInterval
  }

derive instance Eq TimerRequest
derive instance Generic TimerRequest _
instance Show TimerRequest where show = genericShow
