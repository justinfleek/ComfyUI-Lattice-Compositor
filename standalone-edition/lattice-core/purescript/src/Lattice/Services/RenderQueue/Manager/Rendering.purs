-- | Lattice.Services.RenderQueue.Manager.Rendering - Frame rendering
-- |
-- | @module Lattice.Services.RenderQueue.Manager.Rendering
-- | @description Process jobs and render frames.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts

module Lattice.Services.RenderQueue.Manager.Rendering
  ( processNextJob
  , autoSaveCallback
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Data.Array (filter, sortBy, head, fromFoldable) as Array
import Data.Int (floor, toNumber)
import Data.Map as Map
import Data.Maybe (Maybe(..), isNothing)
import Data.Ord (comparing)

import Lattice.Services.RenderQueue.Types
  ( RenderJob
  , RenderJobProgress
  , RenderJobStatus(..)
  , RenderedFrame
  )
import Lattice.Services.RenderQueue.Database as DB
import Lattice.Services.RenderQueue.Manager.Types
  ( RenderQueueManager
  , FrameRenderer
  )

-- | Process the next job in the queue
-- |
-- | @internal Called automatically by queue control functions
processNextJob :: RenderQueueManager -> Number -> Aff Unit
processNextJob mgr currentTime = do
  state <- liftEffect $ Ref.read mgr.state
  when (state.isRunning && not state.isPaused && isNothing state.activeJobId) $ do
    -- Find next pending job
    let jobs = Array.fromFoldable (Map.values state.jobs)
        pendingJobs = Array.filter isPendingOrPaused jobs
        sortedJobs = Array.sortBy (comparing _.priority) pendingJobs

    case Array.head sortedJobs of
      Nothing -> do
        -- No more jobs - queue is empty
        liftEffect $ Ref.modify_ (\s -> s { isRunning = false }) mgr.state
        liftEffect $ Ref.write Nothing mgr.autoSaveTimer
        maybeCb <- liftEffect $ Ref.read mgr.onQueueEmptyCb
        case maybeCb of
          Just cb -> liftEffect cb
          Nothing -> pure unit
      Just job ->
        startJob mgr job currentTime
  where
    isPendingOrPaused :: RenderJob -> Boolean
    isPendingOrPaused job =
      job.progress.status == StatusPending || job.progress.status == StatusPaused

-- | Start rendering a job
-- |
-- | @internal Called by processNextJob
startJob :: RenderQueueManager -> RenderJob -> Number -> Aff Unit
startJob mgr job timestamp = do
  maybeRenderer <- liftEffect $ Ref.read mgr.frameRenderer
  case maybeRenderer of
    Nothing -> pure unit  -- No renderer set - cannot process
    Just renderer -> do
      -- Update state to mark job as active
      liftEffect $ Ref.modify_ (\s -> s
        { activeJobId = Just job.id
        , startTime = timestamp
        , framesRenderedThisSession = 0
        }) mgr.state

      -- Update job status
      let startedJob = job
            { progress = job.progress { status = StatusRendering }
            , startedAt = case job.startedAt of
                Just t -> Just t
                Nothing -> Just timestamp
            }

      liftEffect $ Ref.modify_ (\s -> s { jobs = Map.insert job.id startedJob s.jobs }) mgr.state

      -- Begin render loop
      renderLoop mgr job.id renderer timestamp

-- | Main render loop
-- |
-- | @internal Iterates through frames, rendering each one
renderLoop :: RenderQueueManager -> String -> FrameRenderer -> Number -> Aff Unit
renderLoop mgr jobId renderer currentTime = do
  state <- liftEffect $ Ref.read mgr.state

  -- Check if we should continue
  when (state.isRunning && not state.isPaused && state.activeJobId == Just jobId) $ do
    case Map.lookup jobId state.jobs of
      Nothing -> pure unit  -- Job was removed
      Just job -> do
        let currentFrame = job.progress.currentFrame
            endFrame = job.endFrame

        if currentFrame > endFrame
          then do
            -- Job complete
            let completedJob = job
                  { progress = job.progress { status = StatusCompleted }
                  , completedAt = Just currentTime
                  }
            liftEffect $ Ref.modify_ (\s -> s
              { jobs = Map.insert jobId completedJob s.jobs
              , activeJobId = Nothing
              }) mgr.state

            -- Save to database
            maybeDb <- liftEffect $ Ref.read mgr.db
            case maybeDb of
              Just db -> DB.saveJob db completedJob
              Nothing -> pure unit

            -- Notify complete
            frames <- getFramesInternal mgr jobId
            maybeCb <- liftEffect $ Ref.read mgr.onJobCompleteCb
            case maybeCb of
              Just cb -> liftEffect $ cb jobId frames
              Nothing -> pure unit

            -- Process next job
            processNextJob mgr currentTime

          else do
            -- Render current frame
            frameData <- renderer job.compositionId currentFrame job.width job.height

            -- Update progress
            let newFrame = currentFrame + 1
                framesComplete = newFrame - job.startFrame
                totalFrames' = job.endFrame - job.startFrame + 1
                pct = if totalFrames' > 0
                  then floor (toNumber framesComplete / toNumber totalFrames' * 100.0)
                  else 0

                updatedProgress = job.progress
                  { currentFrame = newFrame
                  , totalFrames = totalFrames'
                  , percentage = pct
                  }
                updatedJob = job { progress = updatedProgress }

            liftEffect $ Ref.modify_ (\s -> s
              { jobs = Map.insert jobId updatedJob s.jobs
              , framesRenderedThisSession = s.framesRenderedThisSession + 1
              }) mgr.state

            -- Notify progress
            liftEffect $ notifyProgressInternal mgr jobId updatedProgress

            -- Continue loop
            renderLoop mgr jobId renderer currentTime

-- | Get frames (internal to avoid circular dependency)
getFramesInternal :: RenderQueueManager -> String -> Aff (Array RenderedFrame)
getFramesInternal mgr jobId = do
  maybeDb <- liftEffect $ Ref.read mgr.db
  case maybeDb of
    Just db -> DB.getFrames db jobId
    Nothing -> pure []

-- | Notify progress (internal)
notifyProgressInternal :: RenderQueueManager -> String -> RenderJobProgress -> Effect Unit
notifyProgressInternal mgr jobId progress = do
  maybeCb <- Ref.read mgr.onProgressCb
  case maybeCb of
    Just cb -> cb jobId progress
    Nothing -> pure unit

-- | Auto-save callback
-- |
-- | @internal Saves checkpoint frame for active job
autoSaveCallback :: RenderQueueManager -> Effect Unit
autoSaveCallback mgr = launchAff_ $ do
  state <- liftEffect $ Ref.read mgr.state
  case state.activeJobId of
    Nothing -> pure unit
    Just jobId -> case Map.lookup jobId state.jobs of
      Nothing -> pure unit
      Just job -> do
        let checkpointedJob = job { checkpointFrame = Just job.progress.currentFrame }
        maybeDb <- liftEffect $ Ref.read mgr.db
        case maybeDb of
          Just db -> DB.saveJob db checkpointedJob
          Nothing -> pure unit
