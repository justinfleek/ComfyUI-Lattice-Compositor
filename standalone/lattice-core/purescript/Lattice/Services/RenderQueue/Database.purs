-- | Lattice.Services.RenderQueue.Database - IndexedDB persistence
-- |
-- | IndexedDB storage for render job persistence and resume capability.
-- | Uses FFI for IndexedDB operations.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts (database section)

module Lattice.Services.RenderQueue.Database
  ( -- * Database Handle
    RenderQueueDB
  , openDatabase
  , closeDatabase
    -- * Job Operations
  , saveJob
  , getJob
  , getAllJobs
  , deleteJob
    -- * Frame Operations
  , saveFrame
  , getFrames
  , clearCompletedFrames
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Maybe (Maybe)

import Lattice.Services.RenderQueue.Types
  ( RenderJob
  , RenderedFrame
  )

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // ffi // t
-- ────────────────────────────────────────────────────────────────────────────

-- | Opaque IndexedDB handle
foreign import data RenderQueueDB :: Type

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // ffi // i
-- ────────────────────────────────────────────────────────────────────────────

-- | Open database
foreign import openDatabaseImpl :: String -> EffectFnAff RenderQueueDB

-- | Close database
foreign import closeDatabaseImpl :: RenderQueueDB -> Effect Unit

-- | Save job to database
foreign import saveJobImpl :: RenderQueueDB -> RenderJob -> EffectFnAff Unit

-- | Get job by ID
foreign import getJobImpl :: RenderQueueDB -> String -> EffectFnAff (Maybe RenderJob)

-- | Get all jobs
foreign import getAllJobsImpl :: RenderQueueDB -> EffectFnAff (Array RenderJob)

-- | Delete job by ID
foreign import deleteJobImpl :: RenderQueueDB -> String -> EffectFnAff Unit

-- | Save rendered frame
foreign import saveFrameImpl :: RenderQueueDB -> String -> RenderedFrame -> EffectFnAff Unit

-- | Get all frames for a job
foreign import getFramesImpl :: RenderQueueDB -> String -> EffectFnAff (Array RenderedFrame)

-- | Clear completed frames for a job
foreign import clearCompletedFramesImpl :: RenderQueueDB -> String -> EffectFnAff Unit

-- ────────────────────────────────────────────────────────────────────────────
-- Public API
-- ────────────────────────────────────────────────────────────────────────────

-- | Open the render queue database
openDatabase :: String -> Aff RenderQueueDB
openDatabase dbName = fromEffectFnAff (openDatabaseImpl dbName)

-- | Close the database connection
closeDatabase :: RenderQueueDB -> Effect Unit
closeDatabase = closeDatabaseImpl

-- | Save a render job to the database
saveJob :: RenderQueueDB -> RenderJob -> Aff Unit
saveJob db job = fromEffectFnAff (saveJobImpl db job)

-- | Get a job by ID
getJob :: RenderQueueDB -> String -> Aff (Maybe RenderJob)
getJob db jobId = fromEffectFnAff (getJobImpl db jobId)

-- | Get all jobs from the database
getAllJobs :: RenderQueueDB -> Aff (Array RenderJob)
getAllJobs db = fromEffectFnAff (getAllJobsImpl db)

-- | Delete a job and its associated frames
deleteJob :: RenderQueueDB -> String -> Aff Unit
deleteJob db jobId = fromEffectFnAff (deleteJobImpl db jobId)

-- | Save a rendered frame to the database
saveFrame :: RenderQueueDB -> String -> RenderedFrame -> Aff Unit
saveFrame db jobId frame = fromEffectFnAff (saveFrameImpl db jobId frame)

-- | Get all frames for a job
getFrames :: RenderQueueDB -> String -> Aff (Array RenderedFrame)
getFrames db jobId = fromEffectFnAff (getFramesImpl db jobId)

-- | Clear all frames for a completed job
clearCompletedFrames :: RenderQueueDB -> String -> Aff Unit
clearCompletedFrames db jobId = fromEffectFnAff (clearCompletedFramesImpl db jobId)
