-- | Lattice.Services.RenderQueue.Manager.QueueControl - Queue control
-- |
-- | @module Lattice.Services.RenderQueue.Manager.QueueControl
-- | @description Start, pause, resume, stop, and cancel queue operations.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts

module Lattice.Services.RenderQueue.Manager.QueueControl
  ( startQueue
  , pauseQueue
  , resumeQueue
  , stopQueue
  , cancelCurrentJob
  , notifyProgress
  , startAutoSave
  , stopAutoSave
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Ref as Ref
import Data.Map as Map
import Data.Maybe (Maybe(..))

import Lattice.Services.RenderQueue.Types
  ( RenderJobProgress
  , RenderJobStatus(..)
  )
import Lattice.Services.RenderQueue.Manager.Types
  ( RenderQueueManager
  , now
  , setIntervalImpl
  , clearIntervalImpl
  )
import Lattice.Services.RenderQueue.Manager.Rendering (processNextJob, autoSaveCallback)

-- ────────────────────────────────────────────────────────────────────────────
-- Queue Control
-- ────────────────────────────────────────────────────────────────────────────

-- | Start processing the queue
-- |
-- | @param mgr Manager instance
-- |
-- | @precondition Frame renderer must be set
-- | @postcondition Queue begins processing pending jobs
startQueue :: RenderQueueManager -> Effect Unit
startQueue mgr = do
  state <- Ref.read mgr.state
  when (not state.isRunning) $ do
    Ref.modify_ (\s -> s { isRunning = true, isPaused = false }) mgr.state
    startAutoSave mgr
    launchAff_ $ processNextJob mgr

-- | Pause the queue
-- |
-- | @param mgr Manager instance
-- |
-- | @postcondition Active job status changes to StatusPaused
-- | @postcondition Queue stops processing new frames
pauseQueue :: RenderQueueManager -> Effect Unit
pauseQueue mgr = do
  Ref.modify_ (\s -> s { isPaused = true }) mgr.state
  state <- Ref.read mgr.state
  case state.activeJobId of
    Just jobId -> do
      jobs <- Ref.read mgr.state
      case Map.lookup jobId jobs.jobs of
        Just job -> do
          let pausedJob = job { progress = job.progress { status = StatusPaused } }
          Ref.modify_ (\s -> s { jobs = Map.insert jobId pausedJob s.jobs }) mgr.state
          notifyProgress mgr jobId pausedJob.progress
        Nothing -> pure unit
    Nothing -> pure unit

-- | Resume the queue
-- |
-- | @param mgr Manager instance
-- |
-- | @precondition Queue must be paused
-- | @postcondition Queue continues processing from where it left off
resumeQueue :: RenderQueueManager -> Effect Unit
resumeQueue mgr = do
  state <- Ref.read mgr.state
  when state.isPaused $ do
    Ref.modify_ (\s -> s { isPaused = false }) mgr.state
    case state.activeJobId of
      Just jobId -> do
        jobs <- Ref.read mgr.state
        case Map.lookup jobId jobs.jobs of
          Just job -> do
            let resumedJob = job { progress = job.progress { status = StatusRendering } }
            Ref.modify_ (\s -> s { jobs = Map.insert jobId resumedJob s.jobs }) mgr.state
            notifyProgress mgr jobId resumedJob.progress
          Nothing -> pure unit
      Nothing -> pure unit
    launchAff_ $ processNextJob mgr

-- | Stop the queue entirely
-- |
-- | @param mgr Manager instance
-- |
-- | @postcondition Queue stops, active job remains in current state
stopQueue :: RenderQueueManager -> Effect Unit
stopQueue mgr = do
  Ref.modify_ (\s -> s { isRunning = false, isPaused = false, activeJobId = Nothing }) mgr.state
  stopAutoSave mgr

-- | Cancel the currently rendering job
-- |
-- | @param mgr Manager instance
-- |
-- | @postcondition Active job status changes to StatusCancelled
cancelCurrentJob :: RenderQueueManager -> Effect Unit
cancelCurrentJob mgr = do
  state <- Ref.read mgr.state
  case state.activeJobId of
    Just jobId -> do
      timestamp <- now
      case Map.lookup jobId state.jobs of
        Just job -> do
          let cancelledJob = job
                { progress = job.progress { status = StatusCancelled }
                , completedAt = Just timestamp
                }
          Ref.modify_ (\s -> s
            { jobs = Map.insert jobId cancelledJob s.jobs
            , activeJobId = Nothing
            }) mgr.state
          notifyProgress mgr jobId cancelledJob.progress
        Nothing -> pure unit
    Nothing -> pure unit

-- ────────────────────────────────────────────────────────────────────────────
-- Notifications
-- ────────────────────────────────────────────────────────────────────────────

-- | Notify progress callback
-- |
-- | @internal Called after each frame is rendered
notifyProgress :: RenderQueueManager -> String -> RenderJobProgress -> Effect Unit
notifyProgress mgr jobId progress = do
  maybeCb <- Ref.read mgr.onProgressCb
  case maybeCb of
    Just cb -> cb jobId progress
    Nothing -> pure unit

-- ────────────────────────────────────────────────────────────────────────────
-- Auto-save
-- ────────────────────────────────────────────────────────────────────────────

-- | Start auto-save timer
-- |
-- | @internal Periodically saves active job progress to database
startAutoSave :: RenderQueueManager -> Effect Unit
startAutoSave mgr = do
  maybeTimer <- Ref.read mgr.autoSaveTimer
  case maybeTimer of
    Just _ -> pure unit  -- Already running
    Nothing -> do
      timer <- setIntervalImpl (autoSaveCallback mgr) mgr.config.autoSaveInterval
      Ref.write (Just timer) mgr.autoSaveTimer

-- | Stop auto-save timer
-- |
-- | @internal Called when queue stops
stopAutoSave :: RenderQueueManager -> Effect Unit
stopAutoSave mgr = do
  maybeTimer <- Ref.read mgr.autoSaveTimer
  case maybeTimer of
    Just timer -> do
      clearIntervalImpl timer
      Ref.write Nothing mgr.autoSaveTimer
    Nothing -> pure unit
