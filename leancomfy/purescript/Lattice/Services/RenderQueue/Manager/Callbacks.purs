-- | Lattice.Services.RenderQueue.Manager.Callbacks - Callback setters
-- |
-- | @module Lattice.Services.RenderQueue.Manager.Callbacks
-- | @description Set callbacks for progress, completion, errors, and queue events.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts

module Lattice.Services.RenderQueue.Manager.Callbacks
  ( onProgress
  , onJobComplete
  , onJobError
  , onQueueEmpty
  , setFrameRenderer
  ) where

import Prelude
import Effect (Effect)
import Effect.Ref as Ref

import Lattice.Services.RenderQueue.Types
  ( RenderJobProgress
  , RenderedFrame
  )
import Lattice.Services.RenderQueue.Manager.Types
  ( RenderQueueManager
  , FrameRenderer
  )

--------------------------------------------------------------------------------
-- Callbacks
--------------------------------------------------------------------------------

-- | Set progress callback
-- |
-- | @param mgr Manager instance
-- | @param cb Callback receiving (jobId, progress)
onProgress :: RenderQueueManager -> (String -> RenderJobProgress -> Effect Unit) -> Effect Unit
onProgress mgr cb = Ref.write (Just cb) mgr.onProgressCb

-- | Set job complete callback
-- |
-- | @param mgr Manager instance
-- | @param cb Callback receiving (jobId, renderedFrames)
onJobComplete :: RenderQueueManager -> (String -> Array RenderedFrame -> Effect Unit) -> Effect Unit
onJobComplete mgr cb = Ref.write (Just cb) mgr.onJobCompleteCb

-- | Set job error callback
-- |
-- | @param mgr Manager instance
-- | @param cb Callback receiving (jobId, errorMessage)
onJobError :: RenderQueueManager -> (String -> String -> Effect Unit) -> Effect Unit
onJobError mgr cb = Ref.write (Just cb) mgr.onJobErrorCb

-- | Set queue empty callback
-- |
-- | @param mgr Manager instance
-- | @param cb Callback called when all jobs complete
onQueueEmpty :: RenderQueueManager -> Effect Unit -> Effect Unit
onQueueEmpty mgr cb = Ref.write (Just cb) mgr.onQueueEmptyCb

--------------------------------------------------------------------------------
-- Frame Renderer
--------------------------------------------------------------------------------

-- | Set the frame renderer callback
-- |
-- | @param mgr Manager instance
-- | @param renderer Frame rendering function
-- |
-- | @postcondition Renderer is available for job processing
setFrameRenderer :: RenderQueueManager -> FrameRenderer -> Effect Unit
setFrameRenderer mgr renderer = Ref.write (Just renderer) mgr.frameRenderer
