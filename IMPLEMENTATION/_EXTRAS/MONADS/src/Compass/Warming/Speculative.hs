{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- |
-- Module      : Compass.Warming.Speculative
-- Description : Speculative CAS warming for COMPASS widget pre-population
-- License     : Proprietary (Weyl AI)
--
-- Predicts upcoming user queries based on usage history, role patterns,
-- time-of-day distributions, and session context, then pre-executes
-- agent inference and warms the content-addressed cache.
--
-- The warming system operates on three timescales:
--
-- @
--   Session Warm   — On login: pre-warm top-N predicted queries (~2-5s budget)
--   Anticipatory   — During session: predict next query from current context (~500ms budget)
--   Merkle Cascade — On data update: re-warm all widgets affected by changed subtree (~1s budget)
-- @
--
-- Key property: warming is idempotent. Because the agent cache is
-- content-addressed (key = hash(query, merkle_root)), warming the same
-- query against the same data state is a no-op. This means aggressive
-- warming has zero cost when the prediction is redundant.
--
-- Lean4 verification target:
-- @
-- theorem warming_idempotency (q : QueryIntent) (r : MerkleRoot) :
--   warm q r >> warm q r ≡ warm q r
-- @

module Compass.Warming.Speculative
  ( -- * Warming Engine
    WarmingEngine (..)
  , WarmingConfig (..)
  , defaultWarmingConfig
  , newWarmingEngine
  , shutdownWarmingEngine

    -- * Warming Strategies
  , WarmingStrategy (..)
  , SessionWarm (..)
  , AnticipatoryWarm (..)
  , MerkleCascadeWarm (..)

    -- * Query Prediction
  , QueryPredictor (..)
  , PredictedQuery (..)
  , Prediction (..)
  , predictSessionQueries
  , predictNextQuery
  , predictAffectedWidgets

    -- * Warming Execution
  , warmSession
  , warmAnticipatory
  , warmMerkleCascade
  , warmSpecificQueries

    -- * Budget Management
  , WarmingBudget (..)
  , BudgetAllocation (..)
  , allocateBudget
  , budgetRemaining

    -- * Monitoring
  , WarmingMetrics (..)
  , WarmingOutcome (..)
  , getWarmingMetrics
  , predictionAccuracy
  ) where

import           Control.Concurrent (ThreadId, forkIO, killThread, threadDelay)
import           Control.Concurrent.Async (Async, async, cancel, wait,
                                           forConcurrently, forConcurrently_,
                                           race, withAsync, mapConcurrently)
import           Control.Concurrent.MVar
import           Control.Concurrent.STM
import           Control.Exception (SomeException, try, bracket, finally, mask)
import           Control.Monad (when, unless, void, forM_, forM, forever)
import           Data.Foldable (for_)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import           Data.IORef
import           Data.List (sortOn)
import qualified Data.Map.Strict as Map
import           Data.Map.Strict (Map)
import           Data.Ord (Down (..))
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Time.Clock (UTCTime, NominalDiffTime, getCurrentTime,
                                  diffUTCTime, addUTCTime)
import           Data.Word (Word64)
import           GHC.Generics (Generic)

import           Compass.Core.Types
import           Compass.Inference.TieredRouter

-- ────────────────────────────────────────────────────────────────────────────
-- Warming Engine
-- ────────────────────────────────────────────────────────────────────────────

-- | The speculative warming engine. Runs as a background service
-- alongside the main COMPASS request path.
--
-- Architecture:
--   - Prediction thread: continuously updates predicted query set
--   - Worker pool: executes warming tasks within budget constraints
--   - Cascade listener: subscribes to Merkle root updates
data WarmingEngine = WarmingEngine
  { weConfig       :: WarmingConfig
  , weRouter       :: Router                -- shared with hot path
  , wePredictor    :: QueryPredictor
  , weWorkers      :: TVar [Async ()]       -- active warming tasks
  , weTaskQueue    :: TBQueue WarmingTask    -- bounded task queue
  , weCascadeChan  :: TChan MerkleUpdate     -- Merkle update notifications
  , weMetrics      :: IORef WarmingMetrics
  , weShutdown     :: TVar Bool
  , weSessionState :: TVar (HashMap Text SessionContext)  -- userId → context
  }

-- | Configuration for the warming engine
data WarmingConfig = WarmingConfig
  { wcSessionBudgetMs     :: Double
    -- ^ Total time budget for session warming (ms). Default: 3000ms.
    -- This is the time between user login and first interaction.

  , wcAnticipatoryBudgetMs :: Double
    -- ^ Time budget for anticipatory warming per prediction cycle (ms).
    -- Default: 500ms. Must complete before user's next click.

  , wcCascadeBudgetMs      :: Double
    -- ^ Time budget for cascade re-warming per Merkle update (ms).
    -- Default: 1000ms.

  , wcMaxConcurrentWarms   :: Int
    -- ^ Maximum parallel warming tasks. Default: 8.
    -- Bounded to avoid starving the hot path of resources.

  , wcSessionTopN          :: Int
    -- ^ Number of predicted queries to warm on session start. Default: 10.

  , wcAnticipatoryTopN     :: Int
    -- ^ Number of next-query predictions to warm. Default: 3.

  , wcMinPredictionConf    :: Double
    -- ^ Minimum confidence threshold for warming a prediction. Default: 0.3.
    -- Below this, the warming cost isn't worth the speculative benefit.

  , wcTaskQueueDepth       :: Int
    -- ^ Bounded queue depth for warming tasks. Default: 100.
    -- Back-pressure: if full, lowest-confidence tasks are dropped.

  , wcEnableCascade        :: Bool
    -- ^ Whether to enable Merkle cascade warming. Default: True.

  , wcWarmingCooldown      :: NominalDiffTime
    -- ^ Minimum time between warming the same (query, root) pair.
    -- Prevents thrashing. Default: 30s.
    -- Note: due to CAS idempotency, redundant warms are cheap,
    -- but this saves the inference cost for Tier 2+ queries.
  } deriving stock (Show, Generic)

defaultWarmingConfig :: WarmingConfig
defaultWarmingConfig = WarmingConfig
  { wcSessionBudgetMs      = 3000.0
  , wcAnticipatoryBudgetMs = 500.0
  , wcCascadeBudgetMs      = 1000.0
  , wcMaxConcurrentWarms   = 8
  , wcSessionTopN          = 10
  , wcAnticipatoryTopN     = 3
  , wcMinPredictionConf    = 0.3
  , wcTaskQueueDepth       = 100
  , wcEnableCascade        = True
  , wcWarmingCooldown      = 30
  }

-- | Initialize and start the warming engine
newWarmingEngine :: WarmingConfig -> Router -> IO WarmingEngine
newWarmingEngine cfg router = do
  predictor    <- newQueryPredictor
  workers      <- newTVarIO []
  taskQueue    <- newTBQueueIO (wcTaskQueueDepth cfg)
  cascadeChan  <- newBroadcastTChanIO
  metrics      <- newIORef emptyWarmingMetrics
  shutdown     <- newTVarIO False
  sessionState <- newTVarIO HM.empty

  let engine = WarmingEngine
        { weConfig       = cfg
        , weRouter       = router
        , wePredictor    = predictor
        , weWorkers      = workers
        , weTaskQueue    = taskQueue
        , weCascadeChan  = cascadeChan
        , weMetrics      = metrics
        , weShutdown     = shutdown
        , weSessionState = sessionState
        }

  -- Start worker pool
  workerThreads <- forM [1.. wcMaxConcurrentWarms cfg] $ \workerId ->
    async $ workerLoop engine workerId

  atomically $ writeTVar workers workerThreads

  -- Start cascade listener (if enabled)
  when (wcEnableCascade cfg) $ do
    void $ async $ cascadeListener engine

  pure engine

-- | Gracefully shutdown the warming engine
shutdownWarmingEngine :: WarmingEngine -> IO ()
shutdownWarmingEngine engine = do
  atomically $ writeTVar (weShutdown engine) True
  workers <- atomically $ readTVar (weWorkers engine)
  mapM_ cancel workers

-- ────────────────────────────────────────────────────────────────────────────
-- Warming Strategies
-- ────────────────────────────────────────────────────────────────────────────

-- | A warming task to be executed by the worker pool
data WarmingTask = WarmingTask
  { wtQuery      :: QueryIntent
  , wtMerkleRoot :: MerkleRoot
  , wtStrategy   :: WarmingStrategy
  , wtPriority   :: Double          -- higher = warm first
  , wtDeadline   :: UTCTime         -- hard cutoff (from budget)
  , wtCreated    :: UTCTime
  } deriving stock (Show, Generic)

-- | Which warming strategy produced this task
data WarmingStrategy
  = SessionWarmStrategy
  | AnticipatoryStrategy
  | MerkleCascadeStrategy
  deriving stock (Eq, Ord, Show, Generic)

-- | Session warming context
data SessionWarm = SessionWarm
  { swUserProfile :: UserProfile
  , swCurrentRoot :: MerkleRoot
  , swBudget      :: WarmingBudget
  } deriving stock (Generic)

-- | Anticipatory warming context (during active session)
data AnticipatoryWarm = AnticipatoryWarm
  { awUserProfile   :: UserProfile
  , awRecentQueries :: [QueryIntent]     -- last N queries in this session
  , awCurrentRoot   :: MerkleRoot
  , awBudget        :: WarmingBudget
  } deriving stock (Generic)

-- | Merkle cascade warming context (on data update)
data MerkleCascadeWarm = MerkleCascadeWarm
  { mcwUpdatedAddrs :: Set ContentAddr   -- cells that changed
  , mcwOldRoot      :: MerkleRoot
  , mcwNewRoot      :: MerkleRoot
  , mcwBudget       :: WarmingBudget
  } deriving stock (Generic)

-- | Notification of a Merkle DAG update (from scraper/ingestion)
data MerkleUpdate = MerkleUpdate
  { muOldRoot      :: MerkleRoot
  , muNewRoot      :: MerkleRoot
  , muChangedAddrs :: Set ContentAddr
  , muTimestamp    :: UTCTime
  } deriving stock (Show, Generic)

-- | Active session context tracked per user
data SessionContext = SessionContext
  { scProfile      :: UserProfile
  , scLoginTime    :: UTCTime
  , scRecentQueries :: [QueryIntent]   -- most recent first
  , scWarmCache    :: HashSet ContentAddr  -- what we've already warmed
  } deriving stock (Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Query Prediction
-- ────────────────────────────────────────────────────────────────────────────

-- | The query prediction model. Combines multiple signals:
--   1. Historical frequency (what does this user usually ask?)
--   2. Time-of-day patterns (CMOs check dashboards in the morning)
--   3. Role-based priors (brand managers care about brand, not strategy)
--   4. Session context (what have they asked so far → what's next?)
--   5. Merkle DAG freshness (what data recently changed → likely to be queried)
data QueryPredictor = QueryPredictor
  { qpFrequencyModel   :: IORef (HashMap Text (HashMap QueryIntent Double))
    -- ^ Per-user query frequency distribution (normalized)
  , qpTimeModel        :: IORef (HashMap Int [PredictedQuery])
    -- ^ Hour-of-day → typical queries (aggregated across users with same role)
  , qpTransitionModel  :: IORef (HashMap QueryIntent [PredictedQuery])
    -- ^ Markov chain: given last query, predict next
  , qpRolePriors       :: HashMap Text [PredictedQuery]
    -- ^ Role → default queries (static config)
  }

-- | A predicted query with confidence score
data PredictedQuery = PredictedQuery
  { pqIntent     :: QueryIntent
  , pqConfidence :: Double        -- [0.0, 1.0]
  , pqSource     :: PredictionSource
  } deriving stock (Show, Generic)

-- | Which prediction signal contributed
data PredictionSource
  = FrequencyBased       -- user's historical pattern
  | TimeBased            -- time-of-day correlation
  | TransitionBased      -- Markov chain from last query
  | RoleBased            -- default for user's role
  | FreshnessBased       -- recently updated data likely to be queried
  deriving stock (Eq, Ord, Show, Generic)

-- | Prediction outcome for accuracy tracking
data Prediction = Prediction
  { predQuery      :: QueryIntent
  , predConfidence :: Double
  , predSource     :: PredictionSource
  , predTimestamp  :: UTCTime
  , predOutcome    :: Maybe PredictionOutcome
  } deriving stock (Show, Generic)

data PredictionOutcome
  = PredictionHit           -- user actually queried this
  | PredictionMiss          -- user never queried this in session
  | PredictionPartial       -- user queried something similar
  deriving stock (Eq, Ord, Show, Generic)

newQueryPredictor :: IO QueryPredictor
newQueryPredictor = QueryPredictor
  <$> newIORef HM.empty
  <*> newIORef HM.empty
  <*> newIORef HM.empty
  <*> pure defaultRolePriors

-- | Predict queries for session start.
-- Combines all signals, de-duplicates, and ranks by confidence.
--
-- Returns top-N predictions above the minimum confidence threshold.
predictSessionQueries
  :: QueryPredictor
  -> WarmingConfig
  -> UserProfile
  -> UTCTime          -- ^ current time (for time-of-day model)
  -> IO [PredictedQuery]
predictSessionQueries predictor cfg profile now = do
  let userId = upUserId profile
      role   = upRole profile
      hour   = timeToHour now
      topN   = wcSessionTopN cfg
      minConf = wcMinPredictionConf cfg

  -- Signal 1: Historical frequency
  freqModel <- readIORef (qpFrequencyModel predictor)
  let freqPreds = case HM.lookup userId freqModel of
        Nothing   -> []
        Just dist -> [ PredictedQuery qi (conf * 0.4) FrequencyBased
                     | (qi, conf) <- sortOn (Down . snd) (HM.toList dist)
                     , conf > minConf
                     ]

  -- Signal 2: Time-of-day
  timeModel <- readIORef (qpTimeModel predictor)
  let timePreds = case HM.lookup hour timeModel of
        Nothing   -> []
        Just pqs  -> map (\pq -> pq { pqConfidence = pqConfidence pq * 0.25 }) pqs

  -- Signal 3: Last session continuation
  let lastSessionPreds = case uhLastSession (upHistory profile) of
        []   -> []
        prev -> [ PredictedQuery qi 0.6 FrequencyBased
                | qi <- take 5 prev
                ]

  -- Signal 4: Role-based priors
  let rolePreds = case HM.lookup role (qpRolePriors predictor) of
        Nothing   -> []
        Just pqs  -> map (\pq -> pq { pqConfidence = pqConfidence pq * 0.15 }) pqs

  -- Combine, deduplicate by intent (keep highest confidence), rank
  let allPreds = freqPreds ++ timePreds ++ lastSessionPreds ++ rolePreds
      deduped  = HM.elems $ HM.fromListWith keepHigher
        [ (pqIntent pq, pq) | pq <- allPreds ]
      ranked   = take topN $ sortOn (Down . pqConfidence) deduped

  pure $ filter (\pq -> pqConfidence pq >= minConf) ranked
  where
    keepHigher a b
      | pqConfidence a >= pqConfidence b = a
      | otherwise = b

-- | Predict the next query during an active session.
-- Uses Markov transition model + recency weighting.
predictNextQuery
  :: QueryPredictor
  -> WarmingConfig
  -> UserProfile
  -> [QueryIntent]     -- ^ recent queries (most recent first)
  -> IO [PredictedQuery]
predictNextQuery predictor cfg _profile recentQueries = do
  transModel <- readIORef (qpTransitionModel predictor)
  let topN   = wcAnticipatoryTopN cfg
      minConf = wcMinPredictionConf cfg

  case recentQueries of
    [] -> pure []
    (lastQuery:_) -> do
      -- Markov transition from last query
      let transitions = case HM.lookup lastQuery transModel of
            Nothing  -> []
            Just pqs -> map (\pq -> pq { pqConfidence = pqConfidence pq * 0.7
                                       , pqSource = TransitionBased
                                       }) pqs

      -- Also consider frequency-weighted predictions (less weight)
      -- (omitted for brevity — same pattern as session prediction)

      pure $ take topN
           $ filter (\pq -> pqConfidence pq >= minConf)
           $ sortOn (Down . pqConfidence) transitions

-- | Given a set of changed CAS addresses, predict which widgets
-- and queries will be affected and need re-warming.
--
-- This walks the reverse dependency index in the Merkle DAG
-- to find all reachable widgets from the changed cells.
predictAffectedWidgets
  :: MerkleDAG
  -> Set ContentAddr     -- ^ changed addresses
  -> [(WidgetId, QueryIntent)]
predictAffectedWidgets dag changedAddrs =
  let -- Walk reverse deps from each changed address to find affected widgets
      affected = foldMap (walkReverseDeps dag) (Set.toList changedAddrs)
  in Set.toList affected

-- | Walk reverse dependencies from a changed cell to all affected widgets
walkReverseDeps :: MerkleDAG -> ContentAddr -> Set (WidgetId, QueryIntent)
walkReverseDeps dag addr =
  case HM.lookup addr (mdDeps dag) of
    Nothing   -> Set.empty
    Just deps -> foldMap (\dep -> walkReverseDeps dag dep) (HS.toList deps)
    -- In production, terminal nodes in the reverse dep walk are widgets
    -- This placeholder recurses; real impl checks if dep is a widget registration

-- ────────────────────────────────────────────────────────────────────────────
-- Warming Execution
-- ────────────────────────────────────────────────────────────────────────────

-- | Warm the cache for a user's session start.
-- Called on login/session-resume. Runs within the session budget.
--
-- Strategy:
--   1. Predict top-N queries
--   2. Build Selective prefetch plans for each
--   3. Execute all CAS prefetches in parallel (cheap, ~2-3ms)
--   4. Route predicted queries through tiered inference
--   5. Results land in agent cache — keyed by (query, current merkle root)
--   6. When user actually queries, it's a cache hit → ~0.2ms
warmSession :: WarmingEngine -> UserProfile -> MerkleRoot -> IO WarmingMetrics
warmSession engine profile root = do
  now <- getCurrentTime
  let cfg    = weConfig engine
      budget = WarmingBudget
        { wbTotalMs   = wcSessionBudgetMs cfg
        , wbStartTime = now
        , wbDeadline  = addUTCTime (realToFrac $ wcSessionBudgetMs cfg / 1000.0) now
        }

  -- Register session context
  atomically $ modifyTVar' (weSessionState engine) $
    HM.insert (upUserId profile) SessionContext
      { scProfile       = profile
      , scLoginTime     = now
      , scRecentQueries = []
      , scWarmCache     = HS.empty
      }

  -- Step 1: Predict
  predictions <- predictSessionQueries (wePredictor engine) cfg profile now

  -- Step 2: Build prefetch plans
  let plans = map (\pq -> (pq, buildPrefetchPlan (rConfig $ weRouter engine) (pqIntent pq)))
                  predictions

  -- Step 3: Batch all CAS prefetches (parallel)
  let allAddrs = foldMap (\(_, plan) -> ppRequired plan `Set.union` ppConditional plan) plans
  prefetchedData <- executePrefetch (rCASBackend $ weRouter engine)
    PrefetchPlan { ppRequired = allAddrs, ppConditional = Set.empty, ppEstimatedTier = Tier0_CASLookup }

  -- Step 4: Build CAS state from prefetched data
  let casState = buildCASStateFromPrefetch prefetchedData

  -- Step 5: Enqueue warming tasks, prioritized by confidence
  forM_ (zip [1..] predictions) $ \(idx, pq) -> do
    let task = WarmingTask
          { wtQuery      = pqIntent pq
          , wtMerkleRoot = root
          , wtStrategy   = SessionWarmStrategy
          , wtPriority   = pqConfidence pq
          , wtDeadline   = wbDeadline budget
          , wtCreated    = now
          }
    enqueueTask engine task

  -- Step 6: Wait for budget to expire or all tasks to complete
  waitForBudget budget

  -- Record outcomes
  readIORef (weMetrics engine)

-- | Anticipatory warming during an active session.
-- Called after each user query to predict and pre-warm the next one.
--
-- This runs in the background while the user reads the current widget.
-- Budget is tight (~500ms) because the user might click again quickly.
warmAnticipatory :: WarmingEngine -> Text -> QueryIntent -> MerkleRoot -> IO ()
warmAnticipatory engine userId currentQuery root = do
  now <- getCurrentTime
  let cfg = weConfig engine

  -- Update session context with the new query
  atomically $ modifyTVar' (weSessionState engine) $
    HM.adjust (\sc -> sc { scRecentQueries = currentQuery : take 20 (scRecentQueries sc) })
              userId

  -- Get updated session context
  mCtx <- atomically $ HM.lookup userId <$> readTVar (weSessionState engine)
  case mCtx of
    Nothing -> pure ()  -- no session, skip
    Just ctx -> do
      -- Predict next queries
      predictions <- predictNextQuery (wePredictor engine) cfg (scProfile ctx) (scRecentQueries ctx)

      let budget = WarmingBudget
            { wbTotalMs   = wcAnticipatoryBudgetMs cfg
            , wbStartTime = now
            , wbDeadline  = addUTCTime (realToFrac $ wcAnticipatoryBudgetMs cfg / 1000.0) now
            }

      -- Only warm predictions we haven't already warmed in this session
      let newPreds = filter (\pq -> not $ isAlreadyWarmed ctx (pqIntent pq) root) predictions

      -- Enqueue tasks
      forM_ newPreds $ \pq -> do
        let task = WarmingTask
              { wtQuery      = pqIntent pq
              , wtMerkleRoot = root
              , wtStrategy   = AnticipatoryStrategy
              , wtPriority   = pqConfidence pq
              , wtDeadline   = wbDeadline budget
              , wtCreated    = now
              }
        enqueueTask engine task

      -- Mark as warmed in session context
      let warmedKeys = HS.fromList
            [ deriveAgentCacheKey (pqIntent pq) root | pq <- newPreds ]
      atomically $ modifyTVar' (weSessionState engine) $
        HM.adjust (\sc -> sc { scWarmCache = scWarmCache sc `HS.union` warmedKeys })
                  userId

-- | Merkle cascade warming: when scraper updates data, re-warm all
-- affected widgets.
--
-- This is triggered by the cascade listener when it receives a
-- MerkleUpdate notification from the ingestion pipeline.
warmMerkleCascade :: WarmingEngine -> MerkleUpdate -> MerkleDAG -> IO ()
warmMerkleCascade engine update dag = do
  now <- getCurrentTime
  let cfg = weConfig engine
      budget = WarmingBudget
        { wbTotalMs   = wcCascadeBudgetMs cfg
        , wbStartTime = now
        , wbDeadline  = addUTCTime (realToFrac $ wcCascadeBudgetMs cfg / 1000.0) now
        }

  -- Find all widgets affected by the changed addresses
  let affected = predictAffectedWidgets dag (muChangedAddrs update)

  -- For each affected widget, check if any active session cares about it
  sessions <- atomically $ readTVar (weSessionState engine)

  -- Build warming tasks: only for widgets in active sessions
  let tasks = do
        (widgetId, queryIntent) <- affected
        -- Check if any session has this in their warm cache
        (_userId, session) <- HM.toList sessions
        let cacheKey = deriveAgentCacheKey queryIntent (muNewRoot update)
        -- Re-warm even if previously warmed — the Merkle root changed,
        -- so the cache key is different (content-addressed!)
        pure WarmingTask
          { wtQuery      = queryIntent
          , wtMerkleRoot = muNewRoot update
          , wtStrategy   = MerkleCascadeStrategy
          , wtPriority   = 0.8  -- high priority — user is likely viewing this
          , wtDeadline   = wbDeadline budget
          , wtCreated    = now
          }

  -- Deduplicate by (query, root) and enqueue
  let dedupedTasks = Map.elems $ Map.fromListWith keepHigherPriority
        [ ((wtQuery t, wtMerkleRoot t), t) | t <- tasks ]

  forM_ dedupedTasks $ enqueueTask engine

-- | Directly warm specific queries (for external callers / testing)
warmSpecificQueries :: WarmingEngine -> [QueryIntent] -> MerkleRoot -> IO ()
warmSpecificQueries engine queries root = do
  now <- getCurrentTime
  forM_ queries $ \qi -> do
    let task = WarmingTask
          { wtQuery      = qi
          , wtMerkleRoot = root
          , wtStrategy   = SessionWarmStrategy
          , wtPriority   = 1.0   -- explicit = max priority
          , wtDeadline   = addUTCTime 10.0 now  -- generous budget
          , wtCreated    = now
          }
    enqueueTask engine task

-- ────────────────────────────────────────────────────────────────────────────
-- Worker Pool
-- ────────────────────────────────────────────────────────────────────────────

-- | Worker loop: pull tasks from the queue and execute them.
-- Each worker runs warming through the tiered router, which
-- populates the agent cache.
workerLoop :: WarmingEngine -> Int -> IO ()
workerLoop engine _workerId = do
  let loop = do
        shutdown <- atomically $ readTVar (weShutdown engine)
        unless shutdown $ do
          -- Block until a task is available
          task <- atomically $ readTBQueue (weTaskQueue engine)
          now <- getCurrentTime

          -- Check if still within budget
          if now > wtDeadline task
            then do
              -- Budget expired — drop the task
              recordWarmingOutcome engine (wtQuery task) (wtStrategy task) WarmingDropped
              loop
            else do
              -- Execute warming through the router
              outcome <- executeWarmingTask engine task
              recordWarmingOutcome engine (wtQuery task) (wtStrategy task) outcome
              loop
  loop

-- | Execute a single warming task through the tiered router
executeWarmingTask :: WarmingEngine -> WarmingTask -> IO WarmingOutcome
executeWarmingTask engine task = do
  let router = weRouter engine

  -- Build CAS state (quick: just check freshness metadata)
  casState <- buildCASStateQuick router (wtQuery task)

  -- Route through tiered inference — result automatically cached
  result <- try @SomeException $
    routeQuery router (wtQuery task) casState (wtMerkleRoot task)

  case result of
    Right (wd, prov, tier) -> do
      recordWarmingTier engine tier
      pure WarmingSuccess
    Left err -> do
      pure WarmingFailed

-- | Enqueue a warming task with back-pressure.
-- If queue is full, attempt to drop the lowest-priority task.
enqueueTask :: WarmingEngine -> WarmingTask -> IO ()
enqueueTask engine task = do
  success <- atomically $ do
    full <- isFullTBQueue (weTaskQueue engine)
    if full
      then pure False  -- simplified: in production, evict lowest priority
      else do
        writeTBQueue (weTaskQueue engine) task
        pure True
  unless success $
    recordWarmingOutcome engine (wtQuery task) (wtStrategy task) WarmingDropped

-- | Cascade listener: subscribes to Merkle update channel
-- and triggers cascade warming on each update.
cascadeListener :: WarmingEngine -> IO ()
cascadeListener engine = do
  readChan <- atomically $ dupTChan (weCascadeChan engine)
  let loop = do
        shutdown <- atomically $ readTVar (weShutdown engine)
        unless shutdown $ do
          update <- atomically $ readTChan readChan
          -- Build the current DAG (in production, this is a lookup, not construction)
          let dag = error "Compass.Warming.Speculative.cascadeListener: get current MerkleDAG"
          warmMerkleCascade engine update dag
          loop
  loop

-- ────────────────────────────────────────────────────────────────────────────
-- Budget Management
-- ────────────────────────────────────────────────────────────────────────────

-- | Time budget for a warming phase
data WarmingBudget = WarmingBudget
  { wbTotalMs   :: Double       -- total budget in milliseconds
  , wbStartTime :: UTCTime      -- when this budget started
  , wbDeadline  :: UTCTime      -- hard cutoff
  } deriving stock (Show, Generic)

-- | How budget was allocated across tiers
data BudgetAllocation = BudgetAllocation
  { baPerTier :: Map InferenceTier (Double, Int)  -- (ms allocated, task count)
  , baTotal   :: Double                           -- total ms allocated
  } deriving stock (Show, Generic)

-- | Allocate budget across predicted queries.
-- Higher-confidence predictions get budget first.
-- Tier 0-1 queries are essentially free, so they always get budget.
allocateBudget :: WarmingBudget -> [PredictedQuery] -> BudgetAllocation
allocateBudget budget predictions =
  let ranked = sortOn (Down . pqConfidence) predictions
      (_, _, alloc) = foldl allocateOne (wbTotalMs budget, Map.empty, 0) ranked
  in BudgetAllocation
      { baPerTier = alloc
      , baTotal   = wbTotalMs budget
      }
  where
    allocateOne (remaining, tierMap, totalUsed) pq =
      let tier = Tier0_CASLookup  -- placeholder: would use classifyTier
          (_, typical, _) = tierLatencyBounds tier
      in if remaining >= typical
         then ( remaining - typical
              , Map.insertWith (\(a1,b1) (a2,b2) -> (a1+a2, b1+b2))
                  tier (typical, 1) tierMap
              , totalUsed + typical
              )
         else (remaining, tierMap, totalUsed)  -- skip, no budget

-- | Check remaining budget
budgetRemaining :: WarmingBudget -> IO Double
budgetRemaining budget = do
  now <- getCurrentTime
  let elapsed = realToFrac (diffUTCTime now (wbStartTime budget)) * 1000.0
  pure $ max 0 (wbTotalMs budget - elapsed)

-- | Block until budget is exhausted
waitForBudget :: WarmingBudget -> IO ()
waitForBudget budget = do
  remaining <- budgetRemaining budget
  when (remaining > 0) $ do
    threadDelay (round $ remaining * 1000)  -- microseconds

-- ────────────────────────────────────────────────────────────────────────────
-- Monitoring
-- ────────────────────────────────────────────────────────────────────────────

-- | Warming outcome for a single task
data WarmingOutcome
  = WarmingSuccess     -- task completed within budget
  | WarmingFailed      -- inference error
  | WarmingDropped     -- budget expired or queue full
  | WarmingRedundant   -- cache already had this (idempotency)
  deriving stock (Eq, Ord, Show, Generic)

-- | Aggregate warming metrics
data WarmingMetrics = WarmingMetrics
  { wmSessionWarms      :: Word64
  , wmAnticipatoryWarms :: Word64
  , wmCascadeWarms      :: Word64
  , wmOutcomes          :: Map WarmingOutcome Word64
  , wmTierDistribution  :: Map InferenceTier Word64
  , wmPredictions       :: [Prediction]   -- rolling window for accuracy calc
  , wmAvgSessionWarmMs  :: Double
  , wmAvgAnticipMs      :: Double
  , wmAvgCascadeMs      :: Double
  } deriving stock (Show, Generic)

emptyWarmingMetrics :: WarmingMetrics
emptyWarmingMetrics = WarmingMetrics
  { wmSessionWarms      = 0
  , wmAnticipatoryWarms = 0
  , wmCascadeWarms      = 0
  , wmOutcomes          = Map.empty
  , wmTierDistribution  = Map.empty
  , wmPredictions       = []
  , wmAvgSessionWarmMs  = 0
  , wmAvgAnticipMs      = 0
  , wmAvgCascadeMs      = 0
  }

getWarmingMetrics :: WarmingEngine -> IO WarmingMetrics
getWarmingMetrics = readIORef . weMetrics

-- | Compute prediction accuracy over recent predictions.
-- Accuracy = (hits + 0.5 * partials) / total predictions
predictionAccuracy :: WarmingMetrics -> Double
predictionAccuracy wm =
  let preds = wmPredictions wm
      total = fromIntegral (length preds)
      hits  = fromIntegral $ length [p | p <- preds, predOutcome p == Just PredictionHit]
      parts = fromIntegral $ length [p | p <- preds, predOutcome p == Just PredictionPartial]
  in if total == 0 then 0.0
     else (hits + 0.5 * parts) / total

-- | Record a warming outcome
recordWarmingOutcome :: WarmingEngine -> QueryIntent -> WarmingStrategy -> WarmingOutcome -> IO ()
recordWarmingOutcome engine _query strategy outcome =
  modifyIORef' (weMetrics engine) $ \wm -> wm
    { wmOutcomes = Map.insertWith (+) outcome 1 (wmOutcomes wm)
    , wmSessionWarms = case strategy of
        SessionWarmStrategy   -> wmSessionWarms wm + 1
        _                     -> wmSessionWarms wm
    , wmAnticipatoryWarms = case strategy of
        AnticipatoryStrategy  -> wmAnticipatoryWarms wm + 1
        _                     -> wmAnticipatoryWarms wm
    , wmCascadeWarms = case strategy of
        MerkleCascadeStrategy -> wmCascadeWarms wm + 1
        _                     -> wmCascadeWarms wm
    }

recordWarmingTier :: WarmingEngine -> InferenceTier -> IO ()
recordWarmingTier engine tier =
  modifyIORef' (weMetrics engine) $ \wm -> wm
    { wmTierDistribution = Map.insertWith (+) tier 1 (wmTierDistribution wm)
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Internal Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if a (query, root) pair has already been warmed in this session
isAlreadyWarmed :: SessionContext -> QueryIntent -> MerkleRoot -> Bool
isAlreadyWarmed ctx qi root =
  HS.member (deriveAgentCacheKey qi root) (scWarmCache ctx)

-- | Build a quick CAS state snapshot for tier classification
buildCASStateQuick :: Router -> QueryIntent -> IO CASState
buildCASStateQuick = error "Compass.Warming.Speculative.buildCASStateQuick: query freshness metadata"

-- | Build CAS state from prefetched data
buildCASStateFromPrefetch :: HashMap ContentAddr (Latticed WidgetData) -> CASState
buildCASStateFromPrefetch prefetched = CASState
  { cassFreshness = HM.fromList
      [ (addrToCASKey addr, latticedToFreshness val)
      | (addr, val) <- HM.toList prefetched
      ]
  , cassCached = HS.fromList
      [ addrToCASKey addr | addr <- HM.keys prefetched ]
  }

-- | Convert ContentAddr to CASKey (domain-specific mapping)
addrToCASKey :: ContentAddr -> CASKey
addrToCASKey = error "Compass.Warming.Speculative.addrToCASKey: reverse lookup from addr registry"

-- | Extract freshness from a latticed value
latticedToFreshness :: Latticed WidgetData -> Freshness
latticedToFreshness l = Freshness
  { freshnessLastUpdate = latticedUpdated l
  , freshnessSource     = error "extract from provenance"
  , freshnessVersion    = latticedVersion l
  }

keepHigherPriority :: WarmingTask -> WarmingTask -> WarmingTask
keepHigherPriority a b
  | wtPriority a >= wtPriority b = a
  | otherwise = b

-- | Default role-based query priors
defaultRolePriors :: HashMap Text [PredictedQuery]
defaultRolePriors = HM.fromList
  [ ("CMO", [ PredictedQuery (ShowMetrics (CampaignId $ error "latest") YTD) 0.9 RoleBased
            , PredictedQuery (BrandOverview (BrandId $ error "primary")) 0.8 RoleBased
            ])
  , ("Brand Manager", [ PredictedQuery (BrandOverview (BrandId $ error "primary")) 0.9 RoleBased
                       , PredictedQuery (SocialCalendar (BrandId $ error "primary") YTD) 0.7 RoleBased
                       ])
  , ("Campaign Manager", [ PredictedQuery (ShowMetrics (CampaignId $ error "latest") YTD) 0.95 RoleBased
                          , PredictedQuery (SummarizeMetrics (CampaignId $ error "latest") YTD) 0.7 RoleBased
                          ])
  ]

-- | Extract hour from UTCTime
timeToHour :: UTCTime -> Int
timeToHour = error "Compass.Warming.Speculative.timeToHour: extract hour from UTCTime"

-- | Check if a TBQueue is full
isFullTBQueue :: TBQueue a -> STM Bool
isFullTBQueue = error "Compass.Warming.Speculative.isFullTBQueue: check queue capacity"
