-- | Lattice.Services.RenderQueue.Manager.Lifecycle - Manager lifecycle
-- |
-- | @module Lattice.Services.RenderQueue.Manager.Lifecycle
-- | @description Create, initialize, and dispose render queue managers.
-- |
-- | Source: ui/src/services/renderQueue/RenderQueueManager.ts

module Lattice.Services.RenderQueue.Manager.Lifecycle
  ( createManager
  , initializeManager
  , disposeManager
  , initialState
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Traversable (for_)
import Data.Tuple (Tuple(..))

import Lattice.Services.RenderQueue.Types
  ( RenderJob
  , RenderJobStatus(..)
  , RenderQueueConfig
  )
import Lattice.Services.RenderQueue.Database as DB
import Lattice.Services.RenderQueue.Manager.Types
  ( RenderQueueManager
  , ManagerState
  , clearIntervalImpl
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Lifecycle
-- ────────────────────────────────────────────────────────────────────────────

-- | Initial manager state
initialState :: ManagerState
initialState =
  { jobs: Map.empty
  , activeJobId: Nothing
  , isRunning: false
  , isPaused: false
  , startTime: 0.0
  , framesRenderedThisSession: 0
  }

-- | Create a new render queue manager
-- |
-- | @param config Queue configuration
-- | @returns New manager instance (not yet initialized)
-- |
-- | @postcondition Manager must be initialized with initializeManager before use
-- |
-- | @example
-- | ```purescript
-- | manager <- createManager
-- |   { dbName: "render-queue"
-- |   , maxConcurrentJobs: 1
-- |   , autoSaveInterval: 5000
-- |   , retryAttempts: 3
-- |   }
-- | ```
createManager :: RenderQueueConfig -> Effect RenderQueueManager
createManager config = do
  dbRef <- Ref.new Nothing
  stateRef <- Ref.new initialState
  frameRendererRef <- Ref.new Nothing
  onProgressRef <- Ref.new Nothing
  onJobCompleteRef <- Ref.new Nothing
  onJobErrorRef <- Ref.new Nothing
  onQueueEmptyRef <- Ref.new Nothing
  autoSaveRef <- Ref.new Nothing

  pure
    { config
    , db: dbRef
    , state: stateRef
    , frameRenderer: frameRendererRef
    , onProgressCb: onProgressRef
    , onJobCompleteCb: onJobCompleteRef
    , onJobErrorCb: onJobErrorRef
    , onQueueEmptyCb: onQueueEmptyRef
    , autoSaveTimer: autoSaveRef
    }

-- | Initialize the manager (open database, load jobs)
-- |
-- | @param mgr Manager to initialize
-- | @returns Aff that completes when database is ready
-- |
-- | @precondition Manager created with createManager
-- | @postcondition Database is open, saved jobs are loaded
initializeManager :: RenderQueueManager -> Aff Unit
initializeManager mgr = do
  -- Open database
  db <- DB.openDatabase mgr.config.dbName
  liftEffect $ Ref.write (Just db) mgr.db

  -- Load existing jobs
  savedJobs <- DB.getAllJobs db
  let jobMap = Map.fromFoldable (map (\j -> Tuple j.id j) savedJobs)

  -- Reset interrupted jobs to pending
  for_ savedJobs $ \job ->
    when (job.progress.status == StatusRendering) $
      DB.saveJob db (job { progress = job.progress { status = StatusPending } })

  liftEffect $ Ref.modify_ (\s -> s { jobs = jobMap }) mgr.state

-- | Dispose the manager (stop queue, close database)
-- |
-- | @param mgr Manager to dispose
-- |
-- | @postcondition Queue is stopped, database is closed, timers are cleared
disposeManager :: RenderQueueManager -> Effect Unit
disposeManager mgr = do
  -- Stop auto-save
  maybeTimer <- Ref.read mgr.autoSaveTimer
  case maybeTimer of
    Just timer -> clearIntervalImpl timer
    Nothing -> pure unit
  Ref.write Nothing mgr.autoSaveTimer

  -- Stop queue
  Ref.modify_ (\s -> s { isRunning = false, isPaused = false }) mgr.state

  -- Close database
  maybeDb <- Ref.read mgr.db
  case maybeDb of
    Just db -> DB.closeDatabase db
    Nothing -> pure unit
  Ref.write Nothing mgr.db
