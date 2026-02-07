-- | Lattice.Services.RenderQueue.Manager.Stats - Statistics and frame access
-- |
-- | @module Lattice.Services.RenderQueue.Manager.Stats
-- | @description Get queue statistics and access rendered frames.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts

module Lattice.Services.RenderQueue.Manager.Stats
  ( getStats
  , getFrames
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Data.Array (filter, length, foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..))

import Lattice.Services.RenderQueue.Types
  ( RenderJob
  , RenderJobStatus(..)
  , RenderQueueStats
  , RenderedFrame
  )
import Lattice.Services.RenderQueue.Database as DB
import Lattice.Services.RenderQueue.Manager.Types (RenderQueueManager)

--------------------------------------------------------------------------------
-- Frame Access
--------------------------------------------------------------------------------

-- | Get all rendered frames for a job
-- |
-- | @param mgr Manager instance
-- | @param jobId Job ID to get frames for
-- | @returns Array of rendered frames (may be empty)
getFrames :: RenderQueueManager -> String -> Aff (Array RenderedFrame)
getFrames mgr jobId = do
  maybeDb <- liftEffect $ Ref.read mgr.db
  case maybeDb of
    Just db -> DB.getFrames db jobId
    Nothing -> pure []

--------------------------------------------------------------------------------
-- Stats
--------------------------------------------------------------------------------

-- | Get queue statistics
-- |
-- | @param mgr Manager instance
-- | @returns Current queue statistics
getStats :: RenderQueueManager -> Effect RenderQueueStats
getStats mgr = do
  state <- Ref.read mgr.state
  let jobs = Map.values state.jobs
      activeJobs = filter (\j -> j.progress.status == StatusRendering) jobs
      pendingJobs = filter (\j -> j.progress.status == StatusPending) jobs
      completedJobs = filter (\j -> j.progress.status == StatusCompleted) jobs
      failedJobs = filter (\j -> j.progress.status == StatusFailed) jobs

      totalFramesRendered = foldl countFrames 0 jobs

      avgFps = case state.activeJobId of
        Nothing -> 0.0
        Just jobId -> case Map.lookup jobId state.jobs of
          Nothing -> 0.0
          Just job -> job.progress.framesPerSecond

  pure
    { totalJobs: length jobs
    , activeJobs: length activeJobs
    , pendingJobs: length pendingJobs
    , completedJobs: length completedJobs
    , failedJobs: length failedJobs
    , totalFramesRendered
    , averageFps: avgFps
    }
  where
    countFrames :: Int -> RenderJob -> Int
    countFrames acc job =
      if job.progress.status == StatusCompleted
        then acc + job.progress.totalFrames
        else acc + (job.progress.currentFrame - job.startFrame)
