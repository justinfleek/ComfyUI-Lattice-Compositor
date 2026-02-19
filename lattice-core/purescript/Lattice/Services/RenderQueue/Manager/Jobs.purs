-- | Lattice.Services.RenderQueue.Manager.Jobs - Job management
-- |
-- | @module Lattice.Services.RenderQueue.Manager.Jobs
-- | @description Add, remove, get, and update render jobs.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts

module Lattice.Services.RenderQueue.Manager.Jobs
  ( addJob
  , removeJob
  , getJob
  , getAllJobs
  , updatePriority
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Data.Array (filter, sortBy, fromFoldable) as Array
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Ord (comparing)

import Lattice.Services.RenderQueue.Types
  ( RenderJob
  , RenderJobConfig
  , defaultJobProgress
  )
import Lattice.Services.RenderQueue.Database as DB
import Lattice.Services.RenderQueue.Manager.Types
  ( RenderQueueManager
  , now
  , generateId
  )
import Lattice.Services.RenderQueue.Manager.QueueControl (startQueue, cancelCurrentJob)

--------------------------------------------------------------------------------
-- Job Management
--------------------------------------------------------------------------------

-- | Add a new render job to the queue
-- |
-- | @param mgr Manager instance
-- | @param config Job configuration
-- | @returns Job ID for tracking
-- |
-- | @postcondition Job is persisted to database
-- | @postcondition Queue starts automatically if not running
-- |
-- | @example
-- | ```purescript
-- | jobId <- addJob manager
-- |   { name: "Main Comp Export"
-- |   , compositionId: "comp-123"
-- |   , startFrame: 0
-- |   , endFrame: 299
-- |   , width: 1920
-- |   , height: 1080
-- |   , fps: 30.0
-- |   , format: FormatPNG
-- |   , quality: 1.0
-- |   , priority: 0
-- |   }
-- | ```
addJob :: RenderQueueManager -> RenderJobConfig -> Aff String
addJob mgr config = do
  jobId <- liftEffect generateId
  timestamp <- liftEffect now

  let job :: RenderJob
      job =
        { id: jobId
        , name: config.name
        , compositionId: config.compositionId
        , startFrame: config.startFrame
        , endFrame: config.endFrame
        , width: config.width
        , height: config.height
        , fps: config.fps
        , format: config.format
        , quality: config.quality
        , priority: config.priority
        , progress: defaultJobProgress config.startFrame config.endFrame
        , createdAt: timestamp
        , startedAt: Nothing
        , completedAt: Nothing
        , checkpointFrame: Nothing
        }

  -- Save to database
  maybeDb <- liftEffect $ Ref.read mgr.db
  case maybeDb of
    Just db -> DB.saveJob db job
    Nothing -> pure unit

  -- Add to state
  liftEffect $ Ref.modify_ (\s -> s { jobs = Map.insert jobId job s.jobs }) mgr.state

  -- Auto-start if not running
  currentState <- liftEffect $ Ref.read mgr.state
  when (not currentState.isRunning && not currentState.isPaused) $
    liftEffect $ startQueue mgr

  pure jobId

-- | Remove a job from the queue
-- |
-- | @param mgr Manager instance
-- | @param jobId Job ID to remove
-- |
-- | @postcondition If job is active, it is cancelled first
-- | @postcondition Job is removed from database
removeJob :: RenderQueueManager -> String -> Aff Unit
removeJob mgr jobId = do
  state <- liftEffect $ Ref.read mgr.state

  -- Cancel if currently rendering
  when (state.activeJobId == Just jobId) $
    liftEffect $ cancelCurrentJob mgr

  -- Remove from state
  liftEffect $ Ref.modify_ (\s -> s { jobs = Map.delete jobId s.jobs }) mgr.state

  -- Delete from database
  maybeDb <- liftEffect $ Ref.read mgr.db
  case maybeDb of
    Just db -> DB.deleteJob db jobId
    Nothing -> pure unit

-- | Get a job by ID
-- |
-- | @param mgr Manager instance
-- | @param jobId Job ID to find
-- | @returns Just job if found, Nothing otherwise
getJob :: RenderQueueManager -> String -> Effect (Maybe RenderJob)
getJob mgr jobId = do
  state <- Ref.read mgr.state
  pure $ Map.lookup jobId state.jobs

-- | Get all jobs sorted by priority
-- |
-- | @param mgr Manager instance
-- | @returns Array of all jobs, highest priority first
getAllJobs :: RenderQueueManager -> Effect (Array RenderJob)
getAllJobs mgr = do
  state <- Ref.read mgr.state
  let jobs = Array.fromFoldable (Map.values state.jobs)
  pure $ Array.sortBy (comparing _.priority) jobs

-- | Update job priority
-- |
-- | @param mgr Manager instance
-- | @param jobId Job ID to update
-- | @param priority New priority (lower = higher priority)
updatePriority :: RenderQueueManager -> String -> Int -> Aff Unit
updatePriority mgr jobId priority = do
  maybeJob <- liftEffect $ getJob mgr jobId
  case maybeJob of
    Nothing -> pure unit
    Just job -> do
      let updatedJob = job { priority = priority }
      liftEffect $ Ref.modify_ (\s -> s { jobs = Map.insert jobId updatedJob s.jobs }) mgr.state
      maybeDb <- liftEffect $ Ref.read mgr.db
      case maybeDb of
        Just db -> DB.saveJob db updatedJob
        Nothing -> pure unit
