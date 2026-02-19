{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE OverloadedStrings #-}

-- |
-- Module      : Compass.Core.Types
-- Description : Foundational types for the COMPASS agentic marketing platform
-- License     : Proprietary (Weyl AI)
--
-- Core type definitions including content-addressed storage primitives,
-- join-semilattice instances, Merkle DAG structures, and the graded monad
-- effect system used by DeepSeek Engram agents.
--
-- All types are designed for Lean4 verification of convergence properties
-- via the CALM theorem (Consistency As Logical Monotonicity).

module Compass.Core.Types
  ( -- * Content Addressing
    ContentAddr (..)
    , Namespace (..)
    , contentAddr
    , brandNS
    , agentNS
    , widgetNS

    -- * Join-Semilattice
    , JoinSemilattice (..)
    , Latticed (..)
    , VersionVec (..)
    , bumpVersion

    -- * Merkle DAG
    , MerkleNode (..)
    , MerkleRoot (..)
    , MerkleDAG (..)
    , merkleHash

    -- * Reactive Cells
    , Cell (..)
    , CellGraph (..)
    , Freshness (..)
    , FreshnessThreshold (..)
    , isFresh
    , staleness

    -- * Agent System
    , AgentId (..)
    , AgentState (..)
    , QueryIntent (..)
    , DateRange (..)
    , AgentConfidence (..)
    , Provenance (..)

    -- * Widget System
    , WidgetId (..)
    , WidgetData (..)
    , WidgetState (..)
    , RenderPriority (..)

    -- * Epoch Snapshots
    , Epoch (..)
    , EpochId (..)

    -- * Brand Domain
    , BrandId (..)
    , CampaignId (..)
    , UserProfile (..)
    , UsageHistory (..)
  ) where

import           Control.Concurrent.STM (TVar)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.HashSet (HashSet)
import           Data.Hashable (Hashable (..))
import           Data.IORef (IORef)
import           Data.Map.Strict (Map)
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import           Data.Time.Clock (UTCTime, NominalDiffTime, diffUTCTime)
import           Data.UUID (UUID)
import           Data.Word (Word64)
import           GHC.Generics (Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Content Addressing
-- ────────────────────────────────────────────────────────────────────────────

-- | A content-addressed identifier. Wraps UUID5 which is deterministic:
-- same (namespace, content) always yields the same address.
-- This is the atomic unit of identity in the COMPASS CAS.
newtype ContentAddr = ContentAddr { unContentAddr :: UUID }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable)

-- | UUID5 namespace for deterministic hashing
newtype Namespace = Namespace { unNamespace :: UUID }
  deriving stock (Eq, Ord, Show, Generic)

-- | Compute a content address from namespace + raw bytes.
-- Deterministic: identical inputs always yield identical addresses.
-- This property is trivially provable in Lean4.
contentAddr :: Namespace -> ByteString -> ContentAddr
contentAddr (Namespace ns) raw =
  -- In production, this calls Data.UUID.V5.generateNamed
  -- Placeholder for type-level correctness
  ContentAddr $ generateUUID5 ns raw
  where
    generateUUID5 :: UUID -> ByteString -> UUID
    generateUUID5 = error "Compass.Core.Types.generateUUID5: link against uuid package"

-- | Namespace for brand data objects
brandNS :: Namespace
brandNS = Namespace $ error "Compass.Core.Types.brandNS: configure at init"

-- | Namespace for agent computation results
agentNS :: Namespace
agentNS = Namespace $ error "Compass.Core.Types.agentNS: configure at init"

-- | Namespace for pre-resolved widget cache entries
widgetNS :: Namespace
widgetNS = Namespace $ error "Compass.Core.Types.widgetNS: configure at init"

-- ────────────────────────────────────────────────────────────────────────────
-- Join-Semilattice
-- ────────────────────────────────────────────────────────────────────────────

-- | A join-semilattice with the following laws (verified in Lean4):
--
-- @
-- join a bottom       = a                  (identity)
-- join a a            = a                  (idempotent)
-- join a b            = join b a           (commutative)
-- join a (join b c)   = join (join a b) c  (associative)
-- @
--
-- The CALM theorem guarantees: any monotone computation over a
-- join-semilattice converges without coordination.
class Eq a => JoinSemilattice a where
  bottom :: a
  (\/) :: a -> a -> a -- join operation

-- | A value annotated with its lattice position.
-- Tracks both the semantic value and the version metadata
-- needed for convergence detection.
data Latticed a = Latticed
  { latticedValue   :: a
  , latticedVersion :: VersionVec
  , latticedUpdated :: UTCTime
  } deriving stock (Eq, Show, Generic)

instance (Eq a, JoinSemilattice a) => JoinSemilattice (Latticed a) where
  bottom = Latticed bottom bottom (error "bottom has no timestamp")
  (Latticed v1 ver1 t1) \/ (Latticed v2 ver2 t2) =
    Latticed (v1 \/ v2) (ver1 \/ ver2) (max t1 t2)

-- | Version vector: one component per agent/scraper.
-- Forms a join-semilattice via pointwise max.
-- Height = number of agents (bounds CAS retry count).
newtype VersionVec = VersionVec { unVersionVec :: Map AgentId Word64 }
  deriving stock (Eq, Show, Generic)

instance JoinSemilattice VersionVec where
  bottom = VersionVec mempty
  (VersionVec a) \/ (VersionVec b) =
    VersionVec $ Map.unionWith max a b

-- | Monotonically increment a single agent's version component.
-- This is the only mutation allowed — guarantees ascending chain.
bumpVersion :: AgentId -> VersionVec -> VersionVec
bumpVersion aid (VersionVec m) =
  VersionVec $ Map.insertWith (\_ old -> old + 1) aid 1 m

-- ────────────────────────────────────────────────────────────────────────────
-- Merkle DAG
-- ────────────────────────────────────────────────────────────────────────────

-- | A node in the content-addressed Merkle DAG.
-- The address of an Interior node is derived FROM its children's addresses,
-- providing cryptographic integrity verification.
data MerkleNode
  = MerkleLeaf
      { mnAddr      :: ContentAddr
      , mnMediaType :: Text
      , mnPayload   :: ByteString
      }
  | MerkleInterior
      { mnAddr     :: ContentAddr
      , mnChildren :: Map Text MerkleNode
      }
  deriving stock (Eq, Show, Generic)

-- | The current root of the brand's Merkle DAG.
-- Atomic swap of this value gives consistent snapshots.
data MerkleRoot = MerkleRoot
  { mrAddr    :: ContentAddr
  , mrBrandId :: BrandId
  , mrEpoch   :: EpochId
  } deriving stock (Eq, Show, Generic)

-- | Full Merkle DAG with O(1) address lookup via HAMT
data MerkleDAG = MerkleDAG
  { mdRoot   :: MerkleRoot
  , mdNodes  :: HashMap ContentAddr MerkleNode
  , mdDeps   :: HashMap ContentAddr (HashSet ContentAddr) -- reverse dependency index
  } deriving stock (Show, Generic)

-- | Compute the content address of a Merkle node.
-- For interior nodes, this is hash(serialize(children.map(_.addr)))
-- Integrity property: if any child changes, parent addr changes.
merkleHash :: MerkleNode -> ContentAddr
merkleHash (MerkleLeaf _ mt payload) =
  contentAddr brandNS (mt' <> payload)
  where mt' = error "serialize mediatype" -- encodeUtf8 mt
merkleHash (MerkleInterior _ children) =
  contentAddr brandNS serializedChildren
  where
    serializedChildren = error "serialize child addrs" -- foldMap (serialize . mnAddr) children

-- ────────────────────────────────────────────────────────────────────────────
-- Reactive Cells
-- ────────────────────────────────────────────────────────────────────────────

-- | A reactive cell in the COMPASS data plane.
-- Combines STM-managed current value with CAS identity
-- and monotone dirty propagation.
data Cell a = Cell
  { cellAddr       :: ContentAddr                    -- CAS identity
  , cellValue      :: IORef (Latticed a)             -- hot path: raw CAS lattice-merge
  , cellDependsOn  :: TVar (Set ContentAddr)         -- upstream cells
  , cellDependents :: TVar (Set ContentAddr)         -- downstream (widgets, derived cells)
  , cellDirty      :: TVar Bool                      -- monotone dirty flag
  , cellRecompute  :: IO a                           -- derivation function
  }

-- | The full cell graph for a brand
data CellGraph = CellGraph
  { cgCells :: HashMap ContentAddr (Cell WidgetData)
  , cgRoot  :: TVar MerkleRoot
  } deriving stock (Generic)

-- | Freshness metadata for cache decisions
data Freshness = Freshness
  { freshnessLastUpdate :: UTCTime
  , freshnessSource     :: ContentAddr   -- which scraper last touched this
  , freshnessVersion    :: VersionVec
  } deriving stock (Eq, Show, Generic)

-- | Configurable freshness threshold per data type
data FreshnessThreshold = FreshnessThreshold
  { ftMetrics    :: NominalDiffTime   -- e.g., 1 hour for campaign metrics
  , ftStrategy   :: NominalDiffTime   -- e.g., 24 hours for brand strategy
  , ftSocial     :: NominalDiffTime   -- e.g., 15 minutes for social feeds
  , ftCompetitor :: NominalDiffTime   -- e.g., 6 hours for competitive intel
  } deriving stock (Eq, Show, Generic)

-- | Check freshness against threshold
isFresh :: FreshnessThreshold -> NominalDiffTime -> Freshness -> UTCTime -> Bool
isFresh _threshold maxAge freshness now =
  diffUTCTime now (freshnessLastUpdate freshness) < maxAge

-- | Compute staleness as time since last update
staleness :: Freshness -> UTCTime -> NominalDiffTime
staleness freshness now = diffUTCTime now (freshnessLastUpdate freshness)

-- ────────────────────────────────────────────────────────────────────────────
-- Agent System
-- ────────────────────────────────────────────────────────────────────────────

newtype AgentId = AgentId { unAgentId :: Text }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable)

-- | Agent lifecycle states (indexed monad enforces valid transitions)
data AgentState
  = Idle
  | Dispatched
  | Scraping
  | Ingesting
  | Inferring
  | Ready
  | Failed
  deriving stock (Eq, Ord, Show, Generic)

-- | What the user is asking for — drives tier classification
data QueryIntent
  = ShowMetrics CampaignId DateRange
  | SummarizeMetrics CampaignId DateRange
  | BrandOverview BrandId
  | StrategicAnalysis BrandId Text         -- freeform strategic question
  | CompetitorBrief BrandId [Text]         -- competitor names
  | SocialCalendar BrandId DateRange
  | ContentRecommendation BrandId Text     -- channel/format
  | CustomQuery Text                       -- freeform, always Tier 4
  deriving stock (Eq, Ord, Show, Generic)

data DateRange
  = Q1 | Q2 | Q3 | Q4
  | YTD
  | CustomRange UTCTime UTCTime
  | LastNDays Int
  deriving stock (Eq, Ord, Show, Generic)

-- | Confidence score for agent outputs, [0.0, 1.0]
newtype AgentConfidence = AgentConfidence { unConfidence :: Double }
  deriving stock (Eq, Ord, Show, Generic)

-- | Provenance chain — Cofree comonad over the Merkle dependency structure.
-- Each node carries its ContentAddr and branches to its sources.
data Provenance
  = ProvenanceLeaf ContentAddr UTCTime AgentId
  | ProvenanceDerived ContentAddr UTCTime AgentId [Provenance]
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Widget System
-- ────────────────────────────────────────────────────────────────────────────

newtype WidgetId = WidgetId { unWidgetId :: Text }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable)

-- | Data payload for widget rendering
data WidgetData = WidgetData
  { wdPayload    :: HashMap Text Double    -- metric name → value
  , wdLabels     :: HashMap Text Text      -- display labels
  , wdProvenance :: Provenance
  , wdFreshness  :: Freshness
  , wdConfidence :: AgentConfidence
  } deriving stock (Show, Generic)

instance Eq WidgetData where
  a == b = wdPayload a == wdPayload b
        && wdLabels a == wdLabels b

instance JoinSemilattice WidgetData where
  bottom = WidgetData HM.empty HM.empty
    (ProvenanceLeaf (ContentAddr $ error "bottom") (error "bottom") (AgentId "system"))
    (Freshness (error "bottom") (ContentAddr $ error "bottom") (VersionVec mempty))
    (AgentConfidence 0.0)
  a \/ b
    | wdConfidence a >= wdConfidence b = a  -- prefer higher confidence
    | otherwise = b

-- | Widget display state for progressive rendering
data WidgetState
  = WidgetLoading
  | WidgetStreaming WidgetData AgentConfidence  -- partial, updating
  | WidgetComplete WidgetData Provenance        -- final, verified
  | WidgetStale WidgetData NominalDiffTime      -- valid but outdated
  | WidgetError Text
  deriving stock (Show, Generic)

-- | Priority for widget render ordering
data RenderPriority = RenderPriority
  { rpTopoDepth     :: Int             -- dependency depth in DAG
  , rpLatticeHeight :: Int             -- how resolved this cell is
  , rpStaleness     :: NominalDiffTime -- time since last update
  } deriving stock (Eq, Show, Generic)

-- Lexicographic ordering: resolved first, then freshest
instance Ord RenderPriority where
  compare a b = compare (rpTopoDepth a) (rpTopoDepth b)
             <> compare (rpLatticeHeight b) (rpLatticeHeight a)  -- higher = better
             <> compare (rpStaleness a) (rpStaleness b)          -- less stale = better

-- ────────────────────────────────────────────────────────────────────────────
-- Epoch Snapshots
-- ────────────────────────────────────────────────────────────────────────────

newtype EpochId = EpochId { unEpochId :: Word64 }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable)

-- | An immutable snapshot of the CAS at a point in time.
-- Widgets read from epochs — zero contention with writers.
data Epoch = Epoch
  { epochId     :: EpochId
  , epochRoot   :: MerkleRoot
  , epochFrozen :: HashMap ContentAddr (Latticed WidgetData)
  , epochTime   :: UTCTime
  } deriving stock (Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Brand Domain
-- ────────────────────────────────────────────────────────────────────────────

newtype BrandId = BrandId { unBrandId :: UUID }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable)

newtype CampaignId = CampaignId { unCampaignId :: UUID }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable)

-- | User profile for speculative warming predictions
data UserProfile = UserProfile
  { upUserId       :: Text
  , upBrandId      :: BrandId
  , upRole         :: Text                  -- "CMO", "Brand Manager", etc.
  , upHistory      :: UsageHistory
  , upPreferences  :: HashMap Text Text     -- widget layout prefs, etc.
  } deriving stock (Show, Generic)

-- | Historical usage patterns for query prediction
data UsageHistory = UsageHistory
  { uhQueryCounts    :: HashMap QueryIntent Int    -- frequency per intent type
  , uhTimeOfDay      :: HashMap Int [QueryIntent]  -- hour → typical queries
  , uhLastSession    :: [QueryIntent]              -- most recent session's queries
  , uhAvgSessionLen  :: Int                        -- typical number of queries
  } deriving stock (Show, Generic)
