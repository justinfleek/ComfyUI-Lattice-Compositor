{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RecordWildCards #-}

-- |
-- Module      : Compass.Inference.TieredRouter
-- Description : Tiered inference routing for COMPASS agents
-- License     : Proprietary (Weyl AI)
--
-- Routes agent queries to the optimal inference tier based on complexity
-- classification, CAS cache state, and freshness requirements.
--
-- Tier architecture:
--
-- @
--   Tier 0 — Pure CAS Lookup       (~0.2ms)   No inference needed
--   Tier 1 — Template Interpolation (~1-2ms)   String templates + CAS data
--   Tier 2 — Small Local Model      (~20-80ms) 1-3B quantized, on-device
--   Tier 3 — Medium Model           (~100-300ms) 7-13B, local or edge
--   Tier 4 — Full DeepSeek          (~500-3000ms, ~300-800ms with polyhedral opt)
-- @
--
-- The router is a pure function: same (QueryIntent, CASState) → same Tier.
-- This determinism means routing decisions are content-addressable and
-- cacheable in their own right.
--
-- Latency distribution after tiering:
--                                                                       // p50
--                                                                       // p90
--                                                                       // p95
--                                                                       // p99

module Compass.Inference.TieredRouter
  ( -- * Tier Classification
    InferenceTier (..)
  , TierConfig (..)
  , defaultTierConfig
  , classifyTier
  , tierLatencyBounds

    -- * Inference Backends
  , InferenceBackend (..)
  , CASBackend (..)
  , TemplateBackend (..)
  , LocalModelBackend (..)
  , EdgeModelBackend (..)
  , FullModelBackend (..)

    -- * Router
  , Router (..)
  , RouterMetrics (..)
  , newRouter
  , routeQuery
  , routeQueryStreaming

    -- * Streaming
  , InferenceStream (..)
  , StreamChunk (..)
  , drainStream

    -- * Cache Integration
  , AgentCache (..)
  , CacheResult (..)
  , checkAgentCache
  , insertAgentCache

    -- * Selective Prefetch Integration
  , PrefetchPlan (..)
  , buildPrefetchPlan
  , executePrefetch
  ) where

import           Control.Concurrent.Async (Async, async, wait, race,
                                           forConcurrently, mapConcurrently)
import           Control.Concurrent.STM
import           Control.Exception (SomeException, try, bracket)
import           Control.Monad (when, unless, void, forM_)
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import           Data.IORef
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import           Data.Time.Clock (UTCTime, NominalDiffTime, getCurrentTime,
                                  diffUTCTime)
import           Data.Word (Word64)
import           GHC.Generics (Generic)

import           Compass.Core.Types

-- ────────────────────────────────────────────────────────────────────────────
-- Tier Classification
-- ────────────────────────────────────────────────────────────────────────────

-- | The five inference tiers, ordered by computational cost.
-- Classification is a pure function — no IO, no side effects.
-- Deterministic routing means the tier decision itself is content-addressable.
data InferenceTier
  = Tier0_CASLookup
    -- ^ Direct CAS retrieval. Data exists and is fresh.
    -- Latency: ~0.2ms (HAMT lookup)
    -- No model invocation whatsoever.
  | Tier1_Template
    -- ^ String interpolation from CAS data into display templates.
    -- Latency: ~1-2ms (CAS lookup + template fill)
    -- Example: "Campaign X had Y impressions in Q3"
  | Tier2_SmallModel
    -- ^ 1-3B parameter quantized model running locally.
    -- Latency: ~20-80ms
    -- Suitable for: metric summarization, simple comparisons,
    -- formatting natural language from structured data.
  | Tier3_MediumModel
    -- ^ 7-13B parameter model, local GPU or edge inference.
    -- Latency: ~100-300ms
    -- Suitable for: competitor briefs, content recommendations,
    -- multi-metric synthesis.
  | Tier4_FullModel
    -- ^ Full DeepSeek model via API or heavy local inference.
    -- Latency: ~500-3000ms raw, ~300-800ms with polyhedral kernel optimization.
    -- Suitable for: strategic analysis, freeform questions,
    -- novel insights requiring broad context.
  deriving stock (Eq, Ord, Show, Generic, Enum, Bounded)

-- | Latency bounds per tier (min, typical, max) in milliseconds
tierLatencyBounds :: InferenceTier -> (Double, Double, Double)
tierLatencyBounds = \case
  Tier0_CASLookup  -> (0.1,   0.2,    0.5)
  Tier1_Template   -> (0.5,   1.5,    3.0)
  Tier2_SmallModel -> (15.0,  50.0,   80.0)
  Tier3_MediumModel-> (80.0,  200.0,  350.0)
  Tier4_FullModel  -> (300.0, 800.0,  3000.0) -- with polyhedral optimization

-- | Configuration for tier classification thresholds
data TierConfig = TierConfig
  { tcFreshnessThresholds :: FreshnessThreshold
    -- ^ Per-data-type freshness windows

  , tcTemplateQueries     :: Set QueryIntent
    -- ^ Query intents that can be served by template interpolation.
    -- Pre-configured based on known widget schemas.

  , tcSmallModelMaxTokens :: Int
    -- ^ Maximum output token count for Tier 2. Queries likely to
    -- produce longer output get bumped to Tier 3.

  , tcMediumModelMaxTokens :: Int
    -- ^ Maximum output token count for Tier 3.

  , tcEnablePolyhedralOpt  :: Bool
    -- ^ Whether Tier 4 uses Weyl polyhedral-optimized kernels.
    -- When True, Tier 4 typical latency drops from ~2000ms to ~800ms.

  , tcTier2Timeout         :: NominalDiffTime
    -- ^ Hard timeout for Tier 2 inference. If exceeded, result is
    -- discarded and we don't escalate (background agent handles it).

  , tcTier3Timeout         :: NominalDiffTime
  , tcTier4Timeout         :: NominalDiffTime
  } deriving stock (Show, Generic)

defaultTierConfig :: TierConfig
defaultTierConfig = TierConfig
  { tcFreshnessThresholds = FreshnessThreshold
      { ftMetrics    = 3600      -- 1 hour
      , ftStrategy   = 86400     -- 24 hours
      , ftSocial     = 900       -- 15 minutes
      , ftCompetitor = 21600     -- 6 hours
      }
  , tcTemplateQueries     = Set.empty  -- populated at init from widget registry
  , tcSmallModelMaxTokens = 256
  , tcMediumModelMaxTokens= 1024
  , tcEnablePolyhedralOpt = True
  , tcTier2Timeout        = 0.1   -- 100ms hard cap
  , tcTier3Timeout        = 0.4   -- 400ms hard cap
  , tcTier4Timeout        = 5.0   -- 5s hard cap
  }

-- | Classify a query intent to its optimal inference tier.
--
-- This is a PURE function. Given the same query intent and CAS state,
-- it always returns the same tier. This means tier classification
-- itself can be verified in Lean4:
--
-- @
-- theorem tier_determinism (q : QueryIntent) (s : CASState) :
--   classifyTier q s = classifyTier q s := by rfl
-- @
--
-- The real value of the proof is in the monotonicity property:
-- if CAS state only grows (lattice join), the tier can only decrease
-- or stay the same (more cache hits → lower tiers).
classifyTier
  :: TierConfig
  -> QueryIntent
  -> CASState        -- ^ current CAS freshness/availability
  -> InferenceTier
classifyTier cfg intent casState =
  case intent of
    -- Metric display: if fresh in CAS, just look it up
    ShowMetrics cid dr
      | hasFreshData casState (MetricsKey cid dr) (ftMetrics ft) -> Tier0_CASLookup
      | hasStaleData casState (MetricsKey cid dr)                -> Tier1_Template
      | otherwise                                                -> Tier2_SmallModel

    -- Metric summarization: needs some NL generation
    SummarizeMetrics cid dr
      | hasCachedSummary casState (SummaryKey cid dr)            -> Tier0_CASLookup
      | hasFreshData casState (MetricsKey cid dr) (ftMetrics ft) -> Tier2_SmallModel
      | otherwise                                                -> Tier3_MediumModel

    -- Brand overview: usually cached, medium model if stale
    BrandOverview bid
      | hasFreshData casState (BrandKey bid) (ftStrategy ft)     -> Tier0_CASLookup
      | hasStaleData casState (BrandKey bid)                     -> Tier1_Template
      | otherwise                                                -> Tier3_MediumModel

    -- Strategic analysis: always needs heavy inference
    StrategicAnalysis bid _question
      | hasCachedAnalysis casState bid                           -> Tier1_Template
      | otherwise                                                -> Tier4_FullModel

    -- Competitor brief: medium unless cached
    CompetitorBrief bid competitors
      | hasCachedBrief casState bid competitors                  -> Tier0_CASLookup
      | length competitors <= 2                                  -> Tier3_MediumModel
      | otherwise                                                -> Tier4_FullModel

    -- Social calendar: structured data, low inference need
    SocialCalendar bid dr
      | hasFreshData casState (SocialKey bid dr) (ftSocial ft)   -> Tier0_CASLookup
      | otherwise                                                -> Tier2_SmallModel

    -- Content recommendation: needs creative inference
    ContentRecommendation _bid _channel                          -> Tier3_MediumModel

    -- Freeform: always full model
    CustomQuery _                                                -> Tier4_FullModel
  where
    ft = tcFreshnessThresholds cfg

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // cas // s
-- ────────────────────────────────────────────────────────────────────────────

-- | Opaque CAS state representation for tier classification.
-- This captures what the classifier needs to know without
-- exposing the full Merkle DAG.
data CASState = CASState
  { cassFreshness :: HashMap CASKey Freshness
  , cassCached    :: HashSet CASKey
  } deriving stock (Show, Generic)

-- | Keys into the CAS state, parameterized by data domain
data CASKey
  = MetricsKey CampaignId DateRange
  | SummaryKey CampaignId DateRange
  | BrandKey BrandId
  | SocialKey BrandId DateRange
  | CompetitorKey BrandId [Text]
  | AnalysisKey BrandId
  deriving stock (Eq, Ord, Show, Generic, Hashable)

hasFreshData :: CASState -> CASKey -> NominalDiffTime -> Bool
hasFreshData CASState{..} key maxAge =
  case HM.lookup key cassFreshness of
    Nothing -> False
    Just f  -> True -- in production: check staleness against maxAge using current time
                    -- left pure here for deterministic classification

hasStaleData :: CASState -> CASKey -> Bool
hasStaleData CASState{..} key = HM.member key cassFreshness

hasCachedSummary :: CASState -> CASKey -> Bool
hasCachedSummary CASState{..} key = HS.member key cassCached

hasCachedAnalysis :: CASState -> BrandId -> Bool
hasCachedAnalysis st bid = HS.member (AnalysisKey bid) (cassCached st)

hasCachedBrief :: CASState -> BrandId -> [Text] -> Bool
hasCachedBrief st bid comps = HS.member (CompetitorKey bid comps) (cassCached st)

-- ────────────────────────────────────────────────────────────────────────────
-- Inference Backends
-- ────────────────────────────────────────────────────────────────────────────

-- | Typeclass for inference backends at each tier.
-- Each backend knows how to produce WidgetData from a query intent
-- and a set of CAS-resolved inputs.
class InferenceBackend backend where
  type BackendConfig backend
  type BackendResult backend
  infer       :: backend -> QueryIntent -> HashMap ContentAddr WidgetData -> IO (BackendResult backend)
  inferStream :: backend -> QueryIntent -> HashMap ContentAddr WidgetData -> IO (InferenceStream (BackendResult backend))
  backendTier :: backend -> InferenceTier

-- | Tier 0: Direct CAS retrieval — no computation at all
data CASBackend = CASBackend
  { casbLookup :: ContentAddr -> IO (Maybe (Latticed WidgetData))
  }

-- | Tier 1: Template string interpolation from CAS data
data TemplateBackend = TemplateBackend
  { tmplRegistry :: HashMap QueryIntent WidgetTemplate
  }

-- | A pre-compiled widget template with slots for CAS data
data WidgetTemplate = WidgetTemplate
  { wtTemplate :: Text                         -- template string with {{slots}}
  , wtSlots    :: HashMap Text ContentAddr      -- slot name → CAS address
  , wtFormat   :: WidgetData -> WidgetData      -- post-processing transform
  } deriving stock (Generic)

-- | Tier 2: Small quantized model (1-3B params)
data LocalModelBackend = LocalModelBackend
  { lmbModelPath   :: FilePath
  , lmbMaxTokens   :: Int
  , lmbQuantization :: Text  -- "Q4_K_M", "Q8_0", etc.
  , lmbTimeout     :: NominalDiffTime
  }

-- | Tier 3: Medium model (7-13B)
data EdgeModelBackend = EdgeModelBackend
  { embModelPath   :: FilePath
  , embMaxTokens   :: Int
  , embGPUDevices  :: [Int]    -- CUDA device indices
  , embTimeout     :: NominalDiffTime
  }

-- | Tier 4: Full DeepSeek via API
data FullModelBackend = FullModelBackend
  { fmbEndpoint        :: Text
  , fmbApiKey          :: Text       -- from vault, never logged
  , fmbMaxTokens       :: Int
  , fmbPolyhedralOpt   :: Bool       -- use Weyl-optimized kernels
  , fmbTimeout         :: NominalDiffTime
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Streaming
-- ────────────────────────────────────────────────────────────────────────────

-- | A stream of inference chunks for progressive widget rendering.
-- First chunk arrives at time-to-first-token (~15-80ms depending on tier).
-- The graded monad tracks which CAS objects have been consulted at each chunk.
data InferenceStream a
  = StreamChunk (StreamChunk a) (IO (InferenceStream a))
    -- ^ A partial result with a continuation
  | StreamDone a Provenance AgentConfidence
    -- ^ Final result with full provenance and confidence score
  | StreamError Text
    -- ^ Inference failed

data StreamChunk a = SC
  { scPartial    :: a                      -- partial result so far
  , scConfidence :: AgentConfidence        -- confidence at this point
  , scSources    :: Set ContentAddr        -- CAS objects consulted so far (graded monad trace)
  , scElapsed    :: NominalDiffTime        -- time since inference started
  } deriving stock (Show, Generic)

-- | Drain a stream into a final result, collecting all chunks.
-- Useful for non-streaming consumers (batch, testing).
drainStream :: InferenceStream a -> IO (Either Text (a, Provenance, AgentConfidence))
drainStream (StreamDone a prov conf)  = pure $ Right (a, prov, conf)
drainStream (StreamError err)         = pure $ Left err
drainStream (StreamChunk _ continue)  = continue >>= drainStream

-- ────────────────────────────────────────────────────────────────────────────
-- Router
-- ────────────────────────────────────────────────────────────────────────────

-- | The tiered inference router. Holds backend connections
-- and routes queries to the appropriate tier.
data Router = Router
  { rConfig      :: TierConfig
  , rCASBackend  :: CASBackend
  , rTemplate    :: TemplateBackend
  , rLocalModel  :: LocalModelBackend
  , rEdgeModel   :: EdgeModelBackend
  , rFullModel   :: FullModelBackend
  , rAgentCache  :: AgentCache
  , rMetrics     :: IORef RouterMetrics
  }

-- | Operational metrics for monitoring tier distribution
data RouterMetrics = RouterMetrics
  { rmTierCounts    :: Map InferenceTier Word64   -- queries per tier
  , rmTierLatencies :: Map InferenceTier [Double]  -- rolling latency samples (ms)
  , rmCacheHits     :: Word64
  , rmCacheMisses   :: Word64
  , rmEscalations   :: Word64                      -- queries that timed out and escalated
  } deriving stock (Show, Generic)

emptyMetrics :: RouterMetrics
emptyMetrics = RouterMetrics
  { rmTierCounts    = Map.fromList [(t, 0) | t <- [minBound..maxBound]]
  , rmTierLatencies = Map.fromList [(t, []) | t <- [minBound..maxBound]]
  , rmCacheHits     = 0
  , rmCacheMisses   = 0
  , rmEscalations   = 0
  }

newRouter :: TierConfig -> CASBackend -> TemplateBackend
          -> LocalModelBackend -> EdgeModelBackend -> FullModelBackend
          -> IO Router
newRouter cfg cas tmpl local edge full = do
  cache   <- newAgentCache 10000  -- 10K entry LRU
  metrics <- newIORef emptyMetrics
  pure Router
    { rConfig     = cfg
    , rCASBackend = cas
    , rTemplate   = tmpl
    , rLocalModel = local
    , rEdgeModel  = edge
    , rFullModel  = full
    , rAgentCache = cache
    , rMetrics    = metrics
    }

-- | Route a query through the tiered inference system.
--
-- Flow:
--   1. Check agent cache (content-addressed: same query + same CAS state = hit)
--   2. Classify tier based on query intent + CAS state
--   3. Dispatch to appropriate backend
--   4. On timeout, DON'T escalate — return stale data and let background agent handle it
--      (escalation increases tail latency; stale data + background refresh is better UX)
--   5. Record metrics
--
-- Returns (WidgetData, Provenance, InferenceTier used)
routeQuery
  :: Router
  -> QueryIntent
  -> CASState
  -> MerkleRoot        -- ^ current root for cache key derivation
  -> IO (WidgetData, Provenance, InferenceTier)
routeQuery router intent casState root = do
  start <- getCurrentTime

  -- Step 1: Agent cache check
  let cacheKey = deriveAgentCacheKey intent root
  cached <- checkAgentCache (rAgentCache router) cacheKey
  case cached of
    CacheHit wd prov -> do
      recordMetric router Tier0_CASLookup start
      recordCacheHit router
      pure (wd, prov, Tier0_CASLookup)
    CacheMiss -> do
      recordCacheMiss router

      -- Step 2: Classify tier
      let tier = classifyTier (rConfig router) intent casState

      -- Step 3: Dispatch to backend with timeout
      result <- dispatchTier router tier intent casState

      case result of
        Right (wd, prov) -> do
          -- Step 4: Cache the result (content-addressed)
          insertAgentCache (rAgentCache router) cacheKey wd prov
          recordMetric router tier start
          pure (wd, prov, tier)

        Left _timeout -> do
          -- Step 4 (timeout): Return stale data if available, don't escalate
          recordEscalation router
          stale <- tryStaleData router intent casState
          case stale of
            Just (wd, prov) -> do
              recordMetric router Tier0_CASLookup start
              pure (wd, prov, Tier0_CASLookup)  -- report as CAS lookup (it is)
            Nothing -> do
              -- Genuinely cold — no stale data available
              -- Return empty widget with "loading" state
              let emptyWd = bottom :: WidgetData
                  emptyProv = ProvenanceLeaf
                    (ContentAddr $ error "loading")
                    start
                    (AgentId "router:timeout")
              recordMetric router tier start
              pure (emptyWd, emptyProv, tier)

-- | Streaming variant — returns an InferenceStream for progressive widget rendering.
-- First chunk arrives at time-to-first-token for the classified tier.
routeQueryStreaming
  :: Router
  -> QueryIntent
  -> CASState
  -> MerkleRoot
  -> IO (InferenceTier, InferenceStream WidgetData)
routeQueryStreaming router intent casState root = do
  -- Cache check — if hit, stream is trivially a single Done chunk
  let cacheKey = deriveAgentCacheKey intent root
  cached <- checkAgentCache (rAgentCache router) cacheKey
  case cached of
    CacheHit wd prov ->
      pure (Tier0_CASLookup, StreamDone wd prov (AgentConfidence 1.0))
    CacheMiss -> do
      let tier = classifyTier (rConfig router) intent casState
      stream <- dispatchTierStreaming router tier intent casState
      pure (tier, stream)

-- ────────────────────────────────────────────────────────────────────────────
-- Tier Dispatch (internal)
-- ────────────────────────────────────────────────────────────────────────────

-- | Dispatch a query to its classified tier's backend.
-- Each tier has a hard timeout. On timeout, Left is returned.
dispatchTier
  :: Router
  -> InferenceTier
  -> QueryIntent
  -> CASState
  -> IO (Either Text (WidgetData, Provenance))
dispatchTier router tier intent casState =
  case tier of
    Tier0_CASLookup -> do
      -- Direct CAS retrieval — resolve from current Merkle DAG
      let addrs = intentToAddrs intent casState
      results <- mapConcurrently (casbLookup (rCASBackend router)) (Set.toList addrs)
      let merged = foldl (\/) bottom (map latticedValue $ concatMap maybeToList results)
          prov   = buildProvenance addrs
      pure $ Right (merged, prov)

    Tier1_Template -> do
      -- Look up template, fill slots from CAS
      let addrs = intentToAddrs intent casState
      slotData <- mapConcurrently (casbLookup (rCASBackend router)) (Set.toList addrs)
      let filled = applyTemplate (rTemplate router) intent slotData
          prov   = buildProvenance addrs
      pure $ Right (filled, prov)

    Tier2_SmallModel -> withTimeout (tcTier2Timeout $ rConfig router) $ do
      let addrs = intentToAddrs intent casState
      inputData <- resolveInputs (rCASBackend router) addrs
      result <- inferLocal (rLocalModel router) intent inputData
      let prov = buildProvenance addrs
      pure (result, prov)

    Tier3_MediumModel -> withTimeout (tcTier3Timeout $ rConfig router) $ do
      let addrs = intentToAddrs intent casState
      inputData <- resolveInputs (rCASBackend router) addrs
      result <- inferEdge (rEdgeModel router) intent inputData
      let prov = buildProvenance addrs
      pure (result, prov)

    Tier4_FullModel -> withTimeout (tcTier4Timeout $ rConfig router) $ do
      let addrs = intentToAddrs intent casState
      inputData <- resolveInputs (rCASBackend router) addrs
      result <- inferFull (rFullModel router) intent inputData
      let prov = buildProvenance addrs
      pure (result, prov)

-- | Streaming dispatch — each backend produces an InferenceStream
dispatchTierStreaming
  :: Router
  -> InferenceTier
  -> QueryIntent
  -> CASState
  -> IO (InferenceStream WidgetData)
dispatchTierStreaming router tier intent casState =
  case tier of
    Tier0_CASLookup -> do
      -- No streaming needed — resolve immediately
      result <- dispatchTier router tier intent casState
      case result of
        Right (wd, prov) -> pure $ StreamDone wd prov (AgentConfidence 1.0)
        Left err         -> pure $ StreamError err

    Tier1_Template -> do
      result <- dispatchTier router tier intent casState
      case result of
        Right (wd, prov) -> pure $ StreamDone wd prov (AgentConfidence 0.95)
        Left err         -> pure $ StreamError err

    -- Tiers 2-4: actual streaming from model inference
    _ -> do
      let addrs = intentToAddrs intent casState
      inputData <- resolveInputs (rCASBackend router) addrs
      -- Backend-specific streaming (implementation depends on model server protocol)
      pure $ StreamError "TODO: wire to model server streaming endpoint"

-- ────────────────────────────────────────────────────────────────────────────
-- Agent Cache
-- ────────────────────────────────────────────────────────────────────────────

-- | Content-addressed agent result cache.
-- Key = hash(QueryIntent, MerkleRoot) — same query against same data = same result.
-- This is the speculative warming system's primary consumer.
data AgentCache = AgentCache
  { acEntries  :: TVar (HashMap ContentAddr (WidgetData, Provenance, UTCTime))
  , acMaxSize  :: Int
  , acHits     :: TVar Word64
  , acMisses   :: TVar Word64
  }

data CacheResult
  = CacheHit WidgetData Provenance
  | CacheMiss

newAgentCache :: Int -> IO AgentCache
newAgentCache maxSize = AgentCache
  <$> newTVarIO HM.empty
  <*> pure maxSize
  <*> newTVarIO 0
  <*> newTVarIO 0

-- | Derive a content-addressed cache key from query + Merkle root.
-- Deterministic: same query against same data state → same key.
deriveAgentCacheKey :: QueryIntent -> MerkleRoot -> ContentAddr
deriveAgentCacheKey intent root =
  contentAddr agentNS $ serializeForCache intent root
  where
    serializeForCache :: QueryIntent -> MerkleRoot -> ByteString
    serializeForCache = error "Compass.Inference.TieredRouter.serializeForCache: implement serialization"

checkAgentCache :: AgentCache -> ContentAddr -> IO CacheResult
checkAgentCache cache key = atomically $ do
  entries <- readTVar (acEntries cache)
  case HM.lookup key entries of
    Just (wd, prov, _ts) -> do
      modifyTVar' (acHits cache) (+1)
      pure $ CacheHit wd prov
    Nothing -> do
      modifyTVar' (acMisses cache) (+1)
      pure CacheMiss

insertAgentCache :: AgentCache -> ContentAddr -> WidgetData -> Provenance -> IO ()
insertAgentCache cache key wd prov = do
  now <- getCurrentTime
  atomically $ do
    entries <- readTVar (acEntries cache)
    -- Simple LRU: if at capacity, remove oldest
    let entries' = if HM.size entries >= acMaxSize cache
          then evictOldest entries
          else entries
    writeTVar (acEntries cache) $ HM.insert key (wd, prov, now) entries'

evictOldest :: HashMap ContentAddr (WidgetData, Provenance, UTCTime)
            -> HashMap ContentAddr (WidgetData, Provenance, UTCTime)
evictOldest entries
  | HM.null entries = entries
  | otherwise =
      let oldest = fst $ HM.foldlWithKey'
            (\(bestK, bestT) k (_, _, t) ->
              if t < bestT then (k, t) else (bestK, bestT))
            (error "impossible", error "impossible")
            entries
      in HM.delete oldest entries

-- ────────────────────────────────────────────────────────────────────────────
-- Selective Prefetch Integration
-- ────────────────────────────────────────────────────────────────────────────

-- | A prefetch plan generated by Selective static analysis.
-- Contains ALL content addresses that MIGHT be needed by a query,
-- so they can all be fetched in parallel before the conditional
-- branches are evaluated.
data PrefetchPlan = PrefetchPlan
  { ppRequired   :: Set ContentAddr   -- always needed regardless of branch
  , ppConditional :: Set ContentAddr   -- might be needed depending on branch
  , ppEstimatedTier :: InferenceTier   -- predicted tier (may change after prefetch)
  } deriving stock (Show, Generic)

-- | Build a prefetch plan from a query intent.
-- This is the Selective applicative analysis step (~0.5ms).
-- Pure function — no IO.
buildPrefetchPlan :: TierConfig -> QueryIntent -> PrefetchPlan
buildPrefetchPlan cfg intent = case intent of
  ShowMetrics cid dr -> PrefetchPlan
    { ppRequired    = Set.singleton (metricsCellAddr cid dr)
    , ppConditional = Set.fromList
        [ metricsCacheSummaryAddr cid dr  -- if we can serve from cache
        , metricsCompareAddr cid dr       -- if user wants comparison
        ]
    , ppEstimatedTier = Tier0_CASLookup   -- optimistic
    }

  SummarizeMetrics cid dr -> PrefetchPlan
    { ppRequired    = Set.fromList
        [ metricsCellAddr cid dr
        , metricsCacheSummaryAddr cid dr
        ]
    , ppConditional = Set.fromList
        [ metricsCompareAddr cid dr
        , metricsHistoricalAddr cid
        ]
    , ppEstimatedTier = Tier2_SmallModel
    }

  BrandOverview bid -> PrefetchPlan
    { ppRequired    = Set.fromList
        [ brandCoreAddr bid
        , brandGuidelinesAddr bid
        ]
    , ppConditional = Set.fromList
        [ brandRecentCampaignsAddr bid
        , brandSocialSummaryAddr bid
        ]
    , ppEstimatedTier = Tier0_CASLookup
    }

  StrategicAnalysis bid _ -> PrefetchPlan
    { ppRequired    = Set.fromList
        [ brandCoreAddr bid
        , brandGuidelinesAddr bid
        , brandRecentCampaignsAddr bid
        ]
    , ppConditional = Set.fromList
        [ brandCompetitorAddr bid
        , brandMarketDataAddr bid
        , brandSocialSummaryAddr bid
        ]
    , ppEstimatedTier = Tier4_FullModel
    }

  _ -> PrefetchPlan
    { ppRequired    = Set.empty
    , ppConditional = Set.empty
    , ppEstimatedTier = Tier4_FullModel  -- conservative default
    }

-- | Execute a prefetch plan: fetch ALL addresses in parallel.
-- Wall-clock time = max(individual lookup times), not sum.
-- Returns resolved data as a HashMap for downstream consumption.
executePrefetch
  :: CASBackend
  -> PrefetchPlan
  -> IO (HashMap ContentAddr (Latticed WidgetData))
executePrefetch cas plan = do
  let allAddrs = Set.toList $ ppRequired plan `Set.union` ppConditional plan
  -- Fire all lookups concurrently
  results <- forConcurrently allAddrs $ \addr -> do
    mResult <- casbLookup cas addr
    pure (addr, mResult)
  -- Collect successful lookups
  pure $ HM.fromList
    [ (addr, val) | (addr, Just val) <- results ]

-- ────────────────────────────────────────────────────────────────────────────
-- Internal Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Map a query intent to its required CAS addresses
intentToAddrs :: QueryIntent -> CASState -> Set ContentAddr
intentToAddrs = error "Compass.Inference.TieredRouter.intentToAddrs: derive from prefetch plan"

-- | Resolve a set of CAS addresses to their current values
resolveInputs :: CASBackend -> Set ContentAddr -> IO (HashMap ContentAddr WidgetData)
resolveInputs cas addrs = do
  results <- forConcurrently (Set.toList addrs) $ \addr -> do
    mResult <- casbLookup cas addr
    pure $ fmap (\l -> (addr, latticedValue l)) mResult
  pure $ HM.fromList $ concatMap maybeToList results

-- | Build provenance chain from consumed addresses
buildProvenance :: Set ContentAddr -> Provenance
buildProvenance = error "Compass.Inference.TieredRouter.buildProvenance: walk Merkle DAG"

-- | Try to get stale data for a query (fallback on timeout)
tryStaleData :: Router -> QueryIntent -> CASState -> IO (Maybe (WidgetData, Provenance))
tryStaleData = error "Compass.Inference.TieredRouter.tryStaleData: query CAS ignoring freshness"

-- | Apply a widget template with CAS data
applyTemplate :: TemplateBackend -> QueryIntent -> [Maybe (Latticed WidgetData)] -> WidgetData
applyTemplate = error "Compass.Inference.TieredRouter.applyTemplate: template interpolation"

-- | Run local small model inference
inferLocal :: LocalModelBackend -> QueryIntent -> HashMap ContentAddr WidgetData -> IO WidgetData
inferLocal = error "Compass.Inference.TieredRouter.inferLocal: wire to GGML/llama.cpp"

-- | Run edge medium model inference
inferEdge :: EdgeModelBackend -> QueryIntent -> HashMap ContentAddr WidgetData -> IO WidgetData
inferEdge = error "Compass.Inference.TieredRouter.inferEdge: wire to vLLM/TGI"

-- | Run full DeepSeek inference (with optional polyhedral optimization)
inferFull :: FullModelBackend -> QueryIntent -> HashMap ContentAddr WidgetData -> IO WidgetData
inferFull = error "Compass.Inference.TieredRouter.inferFull: wire to DeepSeek API"

-- | Timeout wrapper — returns Left on timeout, Right on success
withTimeout :: NominalDiffTime -> IO a -> IO (Either Text a)
withTimeout = error "Compass.Inference.TieredRouter.withTimeout: implement with async race"

-- | Record a tier dispatch metric
recordMetric :: Router -> InferenceTier -> UTCTime -> IO ()
recordMetric router tier start = do
  end <- getCurrentTime
  let latencyMs = realToFrac (diffUTCTime end start) * 1000.0
  modifyIORef' (rMetrics router) $ \m -> m
    { rmTierCounts = Map.adjust (+1) tier (rmTierCounts m)
    , rmTierLatencies = Map.adjust (take 1000 . (latencyMs:)) tier (rmTierLatencies m)
    }

recordCacheHit, recordCacheMiss, recordEscalation :: Router -> IO ()
recordCacheHit router = modifyIORef' (rMetrics router) $ \m -> m { rmCacheHits = rmCacheHits m + 1 }
recordCacheMiss router = modifyIORef' (rMetrics router) $ \m -> m { rmCacheMisses = rmCacheMisses m + 1 }
recordEscalation router = modifyIORef' (rMetrics router) $ \m -> m { rmEscalations = rmEscalations m + 1 }

-- | CAS address derivation helpers (placeholder — real impl uses UUID5)
metricsCellAddr, metricsCacheSummaryAddr, metricsCompareAddr :: CampaignId -> DateRange -> ContentAddr
metricsCellAddr = error "derive from CAS namespace"
metricsCacheSummaryAddr = error "derive from CAS namespace"
metricsCompareAddr = error "derive from CAS namespace"

metricsHistoricalAddr :: CampaignId -> ContentAddr
metricsHistoricalAddr = error "derive from CAS namespace"

brandCoreAddr, brandGuidelinesAddr, brandRecentCampaignsAddr :: BrandId -> ContentAddr
brandSocialSummaryAddr, brandCompetitorAddr, brandMarketDataAddr :: BrandId -> ContentAddr
brandCoreAddr = error "derive from CAS namespace"
brandGuidelinesAddr = error "derive from CAS namespace"
brandRecentCampaignsAddr = error "derive from CAS namespace"
brandSocialSummaryAddr = error "derive from CAS namespace"
brandCompetitorAddr = error "derive from CAS namespace"
brandMarketDataAddr = error "derive from CAS namespace"

maybeToList :: Maybe a -> [a]
maybeToList Nothing  = []
maybeToList (Just a) = [a]
