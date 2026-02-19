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
    -- * Re-exports
  , module Effect.Timer
    -- * Request Types
  , TimerRequest(..)
  , TimerAction(..)
    -- * Timer Operations
  , setIntervalImpl
  , clearIntervalImpl
    -- * Time Operations
  , now
    -- * ID Generation
  , generateId
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Now as Now
import Effect.Timer (IntervalId, setInterval, clearInterval)
import Data.DateTime.Instant (unInstant)
import Data.Time.Duration (Milliseconds(..))
import Data.Map (Map)
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Int (round)

import Lattice.Utils.Uuid5.Core (uuid5Default)
import Lattice.Utils.Uuid5.EntityType (EntityType(..))


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
  , autoSaveTimer :: Ref (Maybe IntervalId)
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

-- ────────────────────────────────────────────────────────────────────────────
-- Timer Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Set an interval timer
-- |
-- | @param callback The callback to run on each interval
-- | @param ms The interval in milliseconds
-- | @returns The timer ID (use with clearIntervalImpl to cancel)
-- |
-- | Note: This wraps Effect.Timer.setInterval. For strict Zero FFI compliance,
-- | timer operations could be routed through the Bridge to Haskell backend.
setIntervalImpl :: Effect Unit -> Int -> Effect IntervalId
setIntervalImpl callback ms = setInterval ms callback

-- | Clear an interval timer
-- |
-- | @param timerId The timer ID returned from setIntervalImpl
clearIntervalImpl :: IntervalId -> Effect Unit
clearIntervalImpl = clearInterval

-- ────────────────────────────────────────────────────────────────────────────
-- Time Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Get current time as milliseconds since epoch
-- |
-- | This is a read-only browser query, which is allowed per Zero FFI rules.
-- | Uses Effect.Now from the standard library.
now :: Effect Number
now = do
  instant <- Now.now
  let (Milliseconds ms) = unInstant instant
  pure ms

-- ────────────────────────────────────────────────────────────────────────────
-- ID Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate a unique job ID
-- |
-- | Uses UUID5 (deterministic) with current timestamp as the name.
-- | This produces unique IDs as long as timestamps differ.
-- | Pure computation - no FFI required.
generateId :: Effect String
generateId = do
  instant <- Now.now
  let (Milliseconds ms) = unInstant instant
      -- Use timestamp + "job" prefix as the name for UUID5
      name = "job:" <> show (round ms :: Int)
  pure (uuid5Default name)
