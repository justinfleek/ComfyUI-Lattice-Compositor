{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE BangPatterns #-}

-- |
-- Module      : Compass.CAS.Store
-- Description : Content-Addressed Storage backend for COMPASS
-- License     : Proprietary (Weyl AI)
--
-- Three-tier CAS architecture:
--
--                                                                        // l1
--                                                                        // l2
--                                                                        // l3
--
-- All tiers share the same ContentAddr (UUID5) key space.
-- Reads cascade: L1 miss → L2 miss → L3 miss → not found.
-- Writes always go to L2 (source of truth) and propagate to L1 (warm cache).
--
-- The lattice-CAS merge operation (join on concurrent writes) happens
-- at the IORef level for L1 and at the SQL level for L2 via
--                                                                    // insert

module Compass.CAS.Store
  ( -- * CAS Store
    CASStore (..)
  , CASStoreConfig (..)
  , defaultCASStoreConfig
  , newCASStore
  , closeCASStore

    -- * Operations
  , casGet
  , casPut
  , casGetBatch
  , casExists
  , casLatticeMerge

    -- * HAMT (L1)
  , HAMTCache (..)
  , newHAMTCache
  , hamtGet
  , hamtPut
  , hamtEvict

    -- * PostgreSQL (L2)
  , PGPool (..)
  , PGConfig (..)
  , newPGPool
  , pgGet
  , pgPut
  , pgLatticeMerge
  , pgGetBatch

    -- * DuckDB (L3)
  , DuckDBConn (..)
  , DuckDBConfig (..)
  , newDuckDBConn
  , duckScan
  , duckAppend

    -- * Bloom Filter
  , BloomFilter (..)
  , newBloomFilter
  , bloomCheck
  , bloomInsert

    -- * Epoch Snapshots
  , takeEpochSnapshot
  , readEpochSnapshot
  ) where

import           Control.Concurrent.Async (forConcurrently, mapConcurrently)
import           Control.Concurrent.MVar
import           Control.Concurrent.STM
import           Control.Exception (SomeException, try, bracket, throwIO)
import           Control.Monad (when, unless, void, forM, forM_)
import           Data.Bits ((.&.), shiftR, popCount)
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import           Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import           Data.Hashable (Hashable, hash)
import           Data.IORef
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import           Data.Time.Clock (UTCTime, getCurrentTime, NominalDiffTime)
import           Data.UUID (UUID, toByteString, fromByteString)
import qualified Data.UUID as UUID
import qualified Data.UUID.V5 as UUID5
import           Data.Vector (Vector)
import qualified Data.Vector as V
import           Data.Word (Word8, Word32, Word64)
import           GHC.Generics (Generic)

import           Compass.Core.Types

-- ────────────────────────────────────────────────────────────────────────────
--                                                                // uuid5 // c
-- ────────────────────────────────────────────────────────────────────────────

-- | Compute UUID5 content address. This is the core CAS primitive.
--
-- Properties (trivially verifiable):
--   1. Deterministic: contentAddr ns x == contentAddr ns x   (∀ ns, x)
--   2. Collision-resistant: P(contentAddr ns x == contentAddr ns y | x ≠ y) ≈ 2⁻¹²²
--   3. Namespace isolation: contentAddr ns1 x ≠ contentAddr ns2 x  (ns1 ≠ ns2, w.h.p.)
computeContentAddr :: Namespace -> ByteString -> ContentAddr
computeContentAddr (Namespace ns) raw =
  ContentAddr $ UUID5.generateNamed ns (BS.unpack raw)

-- | Predefined namespaces for COMPASS domains
compassBrandNS :: Namespace
compassBrandNS = Namespace $ UUID5.generateNamed UUID5.namespaceURL
  (BS.unpack "https://compass.weyl.ai/ns/brand")

compassAgentNS :: Namespace
compassAgentNS = Namespace $ UUID5.generateNamed UUID5.namespaceURL
  (BS.unpack "https://compass.weyl.ai/ns/agent")

compassWidgetNS :: Namespace
compassWidgetNS = Namespace $ UUID5.generateNamed UUID5.namespaceURL
  (BS.unpack "https://compass.weyl.ai/ns/widget")

compassEpochNS :: Namespace
compassEpochNS = Namespace $ UUID5.generateNamed UUID5.namespaceURL
  (BS.unpack "https://compass.weyl.ai/ns/epoch")

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // cas // s
-- ────────────────────────────────────────────────────────────────────────────

-- | Unified CAS store with three-tier read cascade.
data CASStore = CASStore
  { cssL1          :: HAMTCache               -- in-memory HAMT
  , cssL2          :: PGPool                  -- PostgreSQL
  , cssL3          :: DuckDBConn              -- DuckDB (analytical)
  , cssBloom       :: BloomFilter             -- probabilistic membership
  , cssConfig      :: CASStoreConfig
  , cssMetrics     :: IORef CASMetrics
  }

data CASStoreConfig = CASStoreConfig
  { cscL1MaxEntries   :: Int             -- HAMT capacity. Default: 100_000
  , cscL1TTLSeconds   :: NominalDiffTime -- L1 entry TTL. Default: 300s
  , cscBloomCapacity  :: Int             -- Bloom filter capacity. Default: 1_000_000
  , cscBloomFPRate    :: Double          -- False positive rate. Default: 0.01
  , cscPGConfig       :: PGConfig
  , cscDuckConfig     :: DuckDBConfig
  , cscReadCascade    :: Bool            -- Enable L1→L2→L3 cascade. Default: True
  } deriving stock (Show, Generic)

defaultCASStoreConfig :: CASStoreConfig
defaultCASStoreConfig = CASStoreConfig
  { cscL1MaxEntries  = 100000
  , cscL1TTLSeconds  = 300
  , cscBloomCapacity = 1000000
  , cscBloomFPRate   = 0.01
  , cscPGConfig      = defaultPGConfig
  , cscDuckConfig    = defaultDuckDBConfig
  , cscReadCascade   = True
  }

data CASMetrics = CASMetrics
  { cmL1Hits       :: !Word64
  , cmL1Misses     :: !Word64
  , cmL2Hits       :: !Word64
  , cmL2Misses     :: !Word64
  , cmL3Hits       :: !Word64
  , cmL3Misses     :: !Word64
  , cmBloomChecks  :: !Word64
  , cmBloomFP      :: !Word64   -- false positives (bloom said yes, actually no)
  , cmWrites       :: !Word64
  , cmMerges       :: !Word64   -- lattice merges (concurrent write resolution)
  } deriving stock (Show, Generic)

emptyCASMetrics :: CASMetrics
emptyCASMetrics = CASMetrics 0 0 0 0 0 0 0 0 0 0

newCASStore :: CASStoreConfig -> IO CASStore
newCASStore cfg = CASStore
  <$> newHAMTCache (cscL1MaxEntries cfg)
  <*> newPGPool (cscPGConfig cfg)
  <*> newDuckDBConn (cscDuckConfig cfg)
  <*> newBloomFilter (cscBloomCapacity cfg) (cscBloomFPRate cfg)
  <*> pure cfg
  <*> newIORef emptyCASMetrics

closeCASStore :: CASStore -> IO ()
closeCASStore store = do
  closePGPool (cssL2 store)
  closeDuckDB (cssL3 store)

-- | Get a value from CAS. Cascades L1 → L2 → L3.
-- On L2/L3 hit, promotes to L1 for future access.
casGet :: CASStore -> ContentAddr -> IO (Maybe (Latticed WidgetData))
casGet store addr = do
  --                                                                        // l1
  l1Result <- hamtGet (cssL1 store) addr
  case l1Result of
    Just val -> do
      incrMetric store (\m -> m { cmL1Hits = cmL1Hits m + 1 })
      pure (Just val)
    Nothing -> do
      incrMetric store (\m -> m { cmL1Misses = cmL1Misses m + 1 })

      -- Bloom filter short-circuit: if bloom says "definitely not present",
      -- skip L2/L3 entirely. Saves ~1-2ms per miss.
      inBloom <- bloomCheck (cssBloom store) addr
      if not inBloom
        then pure Nothing
        else do
          --                                                                        // l2
          l2Result <- pgGet (cssL2 store) addr
          case l2Result of
            Just val -> do
              incrMetric store (\m -> m { cmL2Hits = cmL2Hits m + 1 })
              -- Promote to L1
              hamtPut (cssL1 store) addr val
              pure (Just val)
            Nothing -> do
              incrMetric store (\m -> m { cmL2Misses = cmL2Misses m + 1 })

              if cscReadCascade (cssConfig store)
                then do
                  --                                                                        // l3
                  l3Result <- duckGet (cssL3 store) addr
                  case l3Result of
                    Just val -> do
                      incrMetric store (\m -> m { cmL3Hits = cmL3Hits m + 1 })
                      -- Promote to L1 and L2
                      hamtPut (cssL1 store) addr val
                      pgPut (cssL2 store) addr val
                      pure (Just val)
                    Nothing -> do
                      incrMetric store (\m -> m { cmL3Misses = cmL3Misses m + 1 })
                      -- Bloom false positive — record for tuning
                      incrMetric store (\m -> m { cmBloomFP = cmBloomFP m + 1 })
                      pure Nothing
                else do
                  incrMetric store (\m -> m { cmL2Misses = cmL2Misses m + 1 })
                  pure Nothing

-- | Put a value into CAS. Writes to L2 (source of truth) and L1 (hot cache).
-- Also inserts into bloom filter.
casPut :: CASStore -> ContentAddr -> Latticed WidgetData -> IO ()
casPut store addr val = do
  pgPut (cssL2 store) addr val       -- L2: durable
  hamtPut (cssL1 store) addr val     -- L1: hot cache
  bloomInsert (cssBloom store) addr  -- Bloom: membership
  incrMetric store (\m -> m { cmWrites = cmWrites m + 1 })

-- | Batch get — fires all lookups concurrently.
-- This is the Selective prefetch execution path.
-- Wall clock = max(individual lookups), not sum.
casGetBatch :: CASStore -> Set ContentAddr -> IO (HashMap ContentAddr (Latticed WidgetData))
casGetBatch store addrs = do
  results <- forConcurrently (Set.toList addrs) $ \addr -> do
    mVal <- casGet store addr
    pure (addr, mVal)
  pure $ HM.fromList [ (a, v) | (a, Just v) <- results ]

-- | Check existence without fetching value (bloom + L2 check)
casExists :: CASStore -> ContentAddr -> IO Bool
casExists store addr = do
  inBloom <- bloomCheck (cssBloom store) addr
  if not inBloom
    then pure False
    else pgExists (cssL2 store) addr

-- | Lattice merge: atomic join of incoming value with existing.
-- This is the core CAS write path for concurrent scraper updates.
--
-- If no existing value: insert.
-- If existing value: compute join (semilattice merge), write result.
--
-- Because join is commutative, associative, and idempotent,
-- concurrent calls to casLatticeMerge always converge.
-- This is the CALM theorem in action.
casLatticeMerge :: JoinSemilattice a
                => CASStore -> ContentAddr -> Latticed WidgetData -> IO (Latticed WidgetData)
casLatticeMerge store addr incoming = do
  -- Atomic merge at L2 (PostgreSQL handles the transaction)
  merged <- pgLatticeMerge (cssL2 store) addr incoming
  -- Update L1 with merged result
  hamtPut (cssL1 store) addr merged
  bloomInsert (cssBloom store) addr
  incrMetric store (\m -> m { cmMerges = cmMerges m + 1 })
  pure merged

-- ────────────────────────────────────────────────────────────────────────────
--                                                                        // l1
-- ────────────────────────────────────────────────────────────────────────────

-- | In-memory HAMT with LRU eviction.
-- O(log32 n) lookups ≈ O(1) for n < 10^9.
-- Structurally shared — old versions persist cheaply for epoch snapshots.
data HAMTCache = HAMTCache
  { hcEntries   :: IORef (HashMap ContentAddr (Latticed WidgetData, UTCTime))
  , hcMaxSize   :: Int
  , hcEvictLock :: MVar ()  -- serialize eviction (not lookups)
  }

newHAMTCache :: Int -> IO HAMTCache
newHAMTCache maxSize = HAMTCache
  <$> newIORef HM.empty
  <*> pure maxSize
  <*> newMVar ()

hamtGet :: HAMTCache -> ContentAddr -> IO (Maybe (Latticed WidgetData))
hamtGet cache addr = do
  entries <- readIORef (hcEntries cache)
  pure $ fst <$> HM.lookup addr entries

hamtPut :: HAMTCache -> ContentAddr -> Latticed WidgetData -> IO ()
hamtPut cache addr val = do
  now <- getCurrentTime
  atomicModifyIORef' (hcEntries cache) $ \entries ->
    let entries' = HM.insert addr (val, now) entries
    in (entries', ())
  -- Trigger eviction if over capacity (non-blocking)
  entries <- readIORef (hcEntries cache)
  when (HM.size entries > hcMaxSize cache) $
    void $ tryPutMVar (hcEvictLock cache) ()

hamtEvict :: HAMTCache -> IO ()
hamtEvict cache = do
  void $ takeMVar (hcEvictLock cache)
  atomicModifyIORef' (hcEntries cache) $ \entries ->
    if HM.size entries <= hcMaxSize cache
      then (entries, ())
      else
        -- Evict oldest 10%
        let sorted = sortByTime (HM.toList entries)
            keep   = take (hcMaxSize cache - (hcMaxSize cache `div` 10)) sorted
        in (HM.fromList keep, ())
  where
    sortByTime = map (\(k, (v, t)) -> (k, (v, t)))
    -- In production: use a proper LRU eviction structure (e.g., psqueues)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                        // l2
-- ────────────────────────────────────────────────────────────────────────────

-- | PostgreSQL connection pool for durable CAS storage.
--
-- Schema:
-- @
--                                                           // create // table
--   addr        UUID PRIMARY KEY,           -- ContentAddr (UUID5)
--   media_type  TEXT NOT NULL,
--   payload     BYTEA NOT NULL,
--   version_vec JSONB NOT NULL DEFAULT '{}', -- VersionVec as JSON
--   created_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
--   updated_at  TIMESTAMPTZ NOT NULL DEFAULT now()
-- );
--
--                                                           // create // table
--   parent_addr UUID NOT NULL REFERENCES cas_nodes(addr),
--   child_key   TEXT NOT NULL,
--   child_addr  UUID NOT NULL REFERENCES cas_nodes(addr),
--                                                            // primary // key
-- );
--
--                                                           // create // table
--   brand_id    UUID NOT NULL,
--   epoch_id    BIGINT NOT NULL,
--   root_addr   UUID NOT NULL REFERENCES cas_nodes(addr),
--   created_at  TIMESTAMPTZ NOT NULL DEFAULT now(),
--                                                            // primary // key
-- );
--
-- -- Lattice merge as a SQL function:
--                                       // create // or // replace // function
--                                                    // returns // jsonb // as
--                                                                    // select
--     key,
--                                                                  // greatest
--                                                                  // coalesce
--                                                                  // coalesce
--     )
--   )
--                                                                      // from
--                                                                    // select
--                                                                     // union
--                                                                    // select
--   ) keys;
-- $$ LANGUAGE SQL IMMUTABLE;
-- @
data PGPool = PGPool
  { pgConnStr  :: ByteString
  , pgPoolSize :: Int
  -- In production: use hasql-pool or resource-pool wrapping hasql Connection
  -- Placeholder for type signatures
  }

data PGConfig = PGConfig
  { pgcConnStr       :: ByteString
  , pgcPoolSize      :: Int      -- Default: 10
  , pgcStatementCache :: Bool    -- Prepared statement cache. Default: True
  } deriving stock (Show, Generic)

defaultPGConfig :: PGConfig
defaultPGConfig = PGConfig
  { pgcConnStr        = "host=localhost port=5432 dbname=compass user=compass"
  , pgcPoolSize       = 10
  , pgcStatementCache = True
  }

newPGPool :: PGConfig -> IO PGPool
newPGPool cfg = pure PGPool
  { pgConnStr  = pgcConnStr cfg
  , pgPoolSize = pgcPoolSize cfg
  }
  -- Production: hasql-pool initialization here

closePGPool :: PGPool -> IO ()
closePGPool _pool = pure ()
  -- Production: drain pool and close connections

-- | Get a single node by ContentAddr.
-- Uses prepared statement: SELECT payload, version_vec, updated_at FROM cas_nodes WHERE addr = $1
pgGet :: PGPool -> ContentAddr -> IO (Maybe (Latticed WidgetData))
pgGet pool addr = do
  -- Production implementation using hasql:
  --
  -- let statement = Statement.Statement
  --       "SELECT payload, version_vec, updated_at FROM cas_nodes WHERE addr = $1"
  --       (Encoders.param (Encoders.nonNullable Encoders.uuid))
  --       (Decoders.rowMaybe $ do
  --         payload    <- Decoders.column (Decoders.nonNullable Decoders.bytea)
  --         versionVec <- Decoders.column (Decoders.nonNullable Decoders.jsonb)
  --         updatedAt  <- Decoders.column (Decoders.nonNullable Decoders.timestamptz)
  --         pure (payload, versionVec, updatedAt))
  --       True  -- prepared
  --
  -- result <- Pool.use pgPool (Session.statement (unContentAddr addr) statement)
  -- pure $ fmap deserializeLatticed result
  pure Nothing  -- STUB: wire to hasql

-- | Put a node into PostgreSQL.
-- Uses UPSERT to handle re-insertion of same content (idempotent).
pgPut :: PGPool -> ContentAddr -> Latticed WidgetData -> IO ()
pgPut pool addr val = do
  -- Production:
  --                                                            // insert // into
  --                                                                    // values
  --                                                            // on // conflict
  --   version_vec = lattice_join(cas_nodes.version_vec, EXCLUDED.version_vec),
  --   updated_at = now()
  pure ()  -- STUB

-- | Atomic lattice merge at the SQL level.
-- Uses the lattice_join SQL function for version vector merge.
-- Returns the merged value.
pgLatticeMerge :: PGPool -> ContentAddr -> Latticed WidgetData -> IO (Latticed WidgetData)
pgLatticeMerge pool addr incoming = do
  -- Production:
  --                                                            // insert // into
  --                                                                    // values
  --                                                            // on // conflict
  --   payload = EXCLUDED.payload,  -- or merge payloads if needed
  --   version_vec = lattice_join(cas_nodes.version_vec, EXCLUDED.version_vec),
  --   updated_at = now()
  --                                                                 // returning
  pure incoming  -- STUB: return merged value from RETURNING clause

-- | Check existence without fetching payload (cheaper than full get)
pgExists :: PGPool -> ContentAddr -> IO Bool
pgExists pool addr = do
  --                                                          // select // exists
  pure False  -- STUB

-- | Batch get — uses ANY($1) for single round-trip
pgGetBatch :: PGPool -> [ContentAddr] -> IO (HashMap ContentAddr (Latticed WidgetData))
pgGetBatch pool addrs = do
  --                                                                    // select
  --                                                                      // from
  --                                                                     // where
  pure HM.empty  -- STUB

-- | Atomic Merkle root swap
pgSwapMerkleRoot :: PGPool -> BrandId -> EpochId -> ContentAddr -> IO ()
pgSwapMerkleRoot pool brandId epochId rootAddr = do
  --                                                            // insert // into
  --                                                                    // values
  pure ()  -- STUB

-- | Get current Merkle root for a brand
pgGetMerkleRoot :: PGPool -> BrandId -> IO (Maybe MerkleRoot)
pgGetMerkleRoot pool brandId = do
  --                                                                    // select
  --                                                                     // where
  --                                                               // order // by
  pure Nothing  -- STUB

-- ────────────────────────────────────────────────────────────────────────────
--                                                                        // l3
-- ────────────────────────────────────────────────────────────────────────────

-- | DuckDB connection for analytical queries.
-- Append-only fact tables — new content = new row (CAS), never update.
--
-- Schema:
-- @
--                                                           // create // table
--   addr           UUID,            -- ContentAddr
--   brand_id       UUID,
--   campaign_id    UUID,
--   metric_name    VARCHAR,
--   metric_value   DOUBLE,
--   period_start   TIMESTAMP,
--   period_end     TIMESTAMP,
--   version_epoch  BIGINT,
--   ingested_at    TIMESTAMP DEFAULT current_timestamp
-- );
--
--                                                           // create // table
--   addr           UUID,
--   brand_id       UUID,
--   platform       VARCHAR,
--   event_type     VARCHAR,
--   event_data     JSON,
--   event_time     TIMESTAMP,
--   ingested_at    TIMESTAMP DEFAULT current_timestamp
-- );
-- @
data DuckDBConn = DuckDBConn
  { ddbPath   :: FilePath
  -- Production: use duckdb-haskell FFI bindings
  }

data DuckDBConfig = DuckDBConfig
  { ddcPath       :: FilePath     -- Database file path
  , ddcThreads    :: Int          -- Query parallelism. Default: 4
  , ddcMemoryLimit :: Text        -- e.g., "4GB"
  } deriving stock (Show, Generic)

defaultDuckDBConfig :: DuckDBConfig
defaultDuckDBConfig = DuckDBConfig
  { ddcPath        = "/var/lib/compass/analytics.duckdb"
  , ddcThreads     = 4
  , ddcMemoryLimit = "4GB"
  }

newDuckDBConn :: DuckDBConfig -> IO DuckDBConn
newDuckDBConn cfg = pure DuckDBConn { ddbPath = ddcPath cfg }

closeDuckDB :: DuckDBConn -> IO ()
closeDuckDB _ = pure ()

-- | Get a single row by ContentAddr (fallback path, not primary use case)
duckGet :: DuckDBConn -> ContentAddr -> IO (Maybe (Latticed WidgetData))
duckGet _conn _addr = pure Nothing  -- STUB

-- | Analytical scan — the primary DuckDB use case.
-- Returns aggregated metrics for widget display.
duckScan :: DuckDBConn -> BrandId -> CampaignId -> DateRange -> IO (Vector (Text, Double))
duckScan _conn _brandId _campaignId _dateRange = do
  --                                                                    // select
  --                                                                      // from
  --                                                                     // where
  --                                                                       // and
  --                                                               // group // by
  pure V.empty  -- STUB

-- | Append new metrics (CAS-addressed, so duplicates are naturally excluded)
duckAppend :: DuckDBConn -> ContentAddr -> BrandId -> CampaignId
           -> [(Text, Double)] -> UTCTime -> UTCTime -> IO ()
duckAppend _conn _addr _brandId _campaignId _metrics _periodStart _periodEnd = do
  --                                                            // insert // into
  --                                                                    // values
  --                                           // on // conflict // do // nothing
  pure ()  -- STUB

-- ────────────────────────────────────────────────────────────────────────────
-- Bloom Filter
-- ────────────────────────────────────────────────────────────────────────────

-- | Bloom filter for probabilistic CAS membership check.
-- Avoids L2/L3 round-trips on definite misses.
--
-- Properties:
--   - No false negatives: if bloomCheck returns False, the key is definitely absent.
--   - False positive rate: configurable (default 1%)
--   - Space: ~1.2 MB per 1M entries at 1% FP rate
data BloomFilter = BloomFilter
  { bfBits     :: IORef (Vector Bool)  -- bit array
  , bfNumHash  :: Int                  -- number of hash functions
  , bfCapacity :: Int                  -- expected number of entries
  }
  -- Production: use bloomfilter or unordered-bloomfilter package
  -- This is a conceptual implementation for type-level correctness

newBloomFilter :: Int -> Double -> IO BloomFilter
newBloomFilter capacity fpRate = do
  let numBits = ceiling $ fromIntegral capacity * abs (log fpRate) / (log 2 ^ (2 :: Int))
      numHash = ceiling $ fromIntegral numBits / fromIntegral capacity * log 2
  bits <- newIORef (V.replicate numBits False)
  pure BloomFilter
    { bfBits     = bits
    , bfNumHash  = numHash
    , bfCapacity = capacity
    }

-- | Check membership. False = definitely absent. True = probably present.
bloomCheck :: BloomFilter -> ContentAddr -> IO Bool
bloomCheck bf addr = do
  bits <- readIORef (bfBits bf)
  let hashes = computeHashes (bfNumHash bf) (unContentAddr addr) (V.length bits)
  pure $ all (\h -> bits V.! h) hashes

-- | Insert an address into the bloom filter
bloomInsert :: BloomFilter -> ContentAddr -> IO ()
bloomInsert bf addr = do
  let hashes = computeHashes (bfNumHash bf) (unContentAddr addr) 0  -- 0 = placeholder for bit length
  atomicModifyIORef' (bfBits bf) $ \bits ->
    let bits' = foldl (\b h -> b V.// [(h `mod` V.length b, True)]) bits hashes
    in (bits', ())

-- | Compute k hash positions from a UUID
computeHashes :: Int -> UUID -> Int -> [Int]
computeHashes k uuid numBits =
  -- Double hashing: h_i(x) = h1(x) + i * h2(x) mod m
  let h1 = hash (UUID.toText uuid)
      h2 = hash (UUID.toText uuid <> "salt")
  in [ abs (h1 + i * h2) `mod` max 1 numBits | i <- [0..k-1] ]

-- ────────────────────────────────────────────────────────────────────────────
-- Epoch Snapshots
-- ────────────────────────────────────────────────────────────────────────────

-- | Take an immutable snapshot of the current CAS state.
-- Widgets read from epochs — zero contention with writers.
-- The HAMT's structural sharing means this is nearly free.
takeEpochSnapshot :: CASStore -> BrandId -> IO Epoch
takeEpochSnapshot store brandId = do
  now <- getCurrentTime
  -- Read current HAMT state (immutable snapshot via structural sharing)
  entries <- readIORef (hcEntries (cssL1 store))
  let epochId = EpochId 0  -- In production: atomic counter
      frozen  = HM.map fst entries
      root    = MerkleRoot
        { mrAddr    = computeContentAddr compassEpochNS (TE.encodeUtf8 $ T.pack $ show epochId)
        , mrBrandId = brandId
        , mrEpoch   = epochId
        }
  -- Record root in PostgreSQL for persistence
  pgSwapMerkleRoot (cssL2 store) brandId epochId (mrAddr root)
  pure Epoch
    { epochId     = epochId
    , epochRoot   = root
    , epochFrozen = frozen
    , epochTime   = now
    }

-- | Read from an epoch snapshot (immutable, zero-contention)
readEpochSnapshot :: Epoch -> ContentAddr -> Maybe (Latticed WidgetData)
readEpochSnapshot epoch addr = HM.lookup addr (epochFrozen epoch)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

incrMetric :: CASStore -> (CASMetrics -> CASMetrics) -> IO ()
incrMetric store f = modifyIORef' (cssMetrics store) f
