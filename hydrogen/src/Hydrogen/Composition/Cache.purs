-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                            // hydrogen // composition // cache
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Composition Cache — Event-driven stable state caching.
-- |
-- | ## Design Philosophy
-- |
-- | The composition layer is **event-driven, not frame-driven**. UI is stable
-- | until an event occurs. This means:
-- |
-- | 1. **Stable states don't recalculate** — Cache composition results until
-- |    a trigger fires
-- | 2. **Content-addressed** — Same Node tree = same cache key (UUID5)
-- | 3. **Generation-aware** — Track when compositions change
-- | 4. **Tiered** — Hot path (L0) vs composition results (L1) vs computed (L2)
-- |
-- | ## Cache Tiers
-- |
-- | - **L0 (Stable State)**: Hot path, <1ms, short TTL
-- |   Currently visible compositions, immediate access
-- |   
-- | - **L1 (Composition)**: Rendered compositions, <5ms, medium TTL
-- |   Fully composed nodes ready for GPU submission
-- |   
-- | - **L2 (Computed)**: Derived properties, <10ms, longer TTL
-- |   Layout calculations, bounding boxes, hit testing data
-- |
-- | ## Invalidation Strategies
-- |
-- | 1. **Generation-based**: Entity updated → generation bumped → cache miss
-- | 2. **TTL-based**: Entries expire after configured duration
-- | 3. **Tag-based**: Invalidate related entries (e.g., brand change)
-- | 4. **Memory pressure**: Evict LRU when at capacity
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Content-addressed caching is critical:
-- | - Same composition across agents → same cache key → shared computation
-- | - Diff by ID, not content → O(1) change detection
-- | - Hierarchical grouping → 1000 agents moving = 1 invalidation

module Hydrogen.Composition.Cache
  ( -- * Cache Types
    CompositionCache
  , CacheTier(..)
  , CacheConfig
  , TierConfig
  
  -- * Cache Entry
  , CacheEntry
  , EntryMetadata
  , CacheTag(..)
  
  -- * LRU Tracker
  , LRUTracker
  , emptyLRU
  , lruAdd
  , lruTouch
  , lruRemove
  , lruOldest
  , lruSize
  
  -- * Cache Operations
  , emptyCache
  , cacheGet
  , cachePut
  , cacheInvalidate
  , cacheInvalidateByTag
  , cacheEvictLRU
  , cacheStats
  
  -- * Configuration
  , defaultConfig
  , defaultTierConfig
  , tierConfigL0
  , tierConfigL1
  , tierConfigL2
  
  -- * Statistics
  , CacheStats
  , hitRate
  , missRate
  , evictionRate
  
  -- * Query Operations
  , cacheContains
  , cacheSize
  , cacheSizeBytes
  , cacheGetByTier
  , cachePruneExpired
  , cacheGetTop
  
  -- * Content-Addressed Integration
  , cacheGetIdentified
  , cachePutIdentified
  
  -- * Generation Utilities
  , initialEntryGeneration
  , bumpEntryGeneration
  
  -- * Debugging
  , showCacheEntry
  , showCacheStats
  , cacheLength
  , cacheNeedsEviction
  , compareByGeneration
  , sameEntryContent
  , filterEntries
  , memoryUtilization
  , makeCacheKeyPair
  , entryScore
  , identifiedToCacheKey
  ) where

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                      // imports
-- ═══════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , map
  , negate
  , ($)
  , (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (>=)
  , (<=)
  , (==)
  , (/=)
  , (<>)
  , (&&)
  , (||)
  , not
  , otherwise
  , compare
  , Ordering(LT, GT, EQ)
  )

import Data.Array (filter, length, sortBy, take, head) as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)
import Data.Map (Map)
import Data.Map as Map
import Data.Set (Set)
import Data.Set (empty, insert, delete, toUnfoldable) as Set
import Data.Foldable (foldl)
import Data.Tuple (Tuple(Tuple), fst, snd)

import Hydrogen.Schema.Identity.Temporal 
  ( CacheKey
  , Generation
  , Identified
  , toCacheKey
  , cacheKeyString
  , initialGeneration
  , nextGeneration
  , unwrapGeneration
  )

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // cache tiers
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cache tier — determines eviction policy and TTL.
data CacheTier
  = TierL0  -- Stable state: hot path, shortest TTL
  | TierL1  -- Composition: rendered results, medium TTL
  | TierL2  -- Computed: derived data, longer TTL

derive instance eqCacheTier :: Eq CacheTier
derive instance ordCacheTier :: Ord CacheTier

instance showCacheTier :: Show CacheTier where
  show TierL0 = "L0:StableState"
  show TierL1 = "L1:Composition"
  show TierL2 = "L2:Computed"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // cache tags
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Tags for bulk invalidation.
-- |
-- | When a brand changes, invalidate all entries tagged with that brand.
-- | When a composition changes, invalidate its dependents.
data CacheTag
  = TagBrand String        -- Brand identifier
  | TagComposition String  -- Composition identifier
  | TagNode String         -- Node identifier
  | TagTrigger String      -- Trigger identifier
  | TagCustom String       -- Custom tag

derive instance eqCacheTag :: Eq CacheTag
derive instance ordCacheTag :: Ord CacheTag

instance showCacheTag :: Show CacheTag where
  show (TagBrand b) = "brand:" <> b
  show (TagComposition c) = "comp:" <> c
  show (TagNode n) = "node:" <> n
  show (TagTrigger t) = "trigger:" <> t
  show (TagCustom c) = "custom:" <> c

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                               // entry metadata
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Metadata for a cache entry.
type EntryMetadata =
  { tier :: CacheTier
  , generation :: Generation
  , createdAt :: Number      -- Timestamp (ms since epoch)
  , expiresAt :: Maybe Number -- TTL expiration
  , lastAccessed :: Number   -- For LRU tracking
  , hitCount :: Int          -- Access statistics
  , sizeBytes :: Int         -- Memory footprint estimate
  , tags :: Set CacheTag     -- For bulk invalidation
  }

-- | A cache entry with value and metadata.
type CacheEntry a =
  { value :: a
  , metadata :: EntryMetadata
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                 // lru tracker
-- ═══════════════════════════════════════════════════════════════════════════════

-- | LRU node for doubly-linked list simulation.
-- |
-- | In pure PureScript, we simulate O(1) LRU with sorted access times.
-- | For true O(1), this would use foreign code with mutable structures.
type LRUNode =
  { key :: String
  , accessTime :: Number
  }

-- | LRU tracker using access time ordering.
-- |
-- | Operations:
-- | - add: O(1) - insert with current time
-- | - touch: O(n) - update access time (requires rebuild)
-- | - oldest: O(n) - find minimum access time
-- | - remove: O(n) - filter out key
-- |
-- | For billion-agent scale, this should be replaced with foreign O(1) impl.
type LRUTracker =
  { entries :: Map String Number  -- key -> accessTime
  , currentTime :: Number         -- monotonic counter
  }

-- | Empty LRU tracker.
emptyLRU :: LRUTracker
emptyLRU = { entries: Map.empty, currentTime: 0.0 }

-- | Add a key to LRU (or update if exists).
lruAdd :: String -> LRUTracker -> LRUTracker
lruAdd key tracker =
  { entries: Map.insert key tracker.currentTime tracker.entries
  , currentTime: tracker.currentTime + 1.0
  }

-- | Touch a key (update access time).
lruTouch :: String -> LRUTracker -> LRUTracker
lruTouch key tracker =
  case Map.lookup key tracker.entries of
    Nothing -> tracker
    Just _ -> 
      { entries: Map.insert key tracker.currentTime tracker.entries
      , currentTime: tracker.currentTime + 1.0
      }

-- | Remove a key from LRU.
lruRemove :: String -> LRUTracker -> LRUTracker
lruRemove key tracker =
  { entries: Map.delete key tracker.entries
  , currentTime: tracker.currentTime
  }

-- | Get the oldest key (lowest access time).
lruOldest :: LRUTracker -> Maybe String
lruOldest tracker =
  let pairs = Map.toUnfoldable tracker.entries :: Array (Tuple String Number)
      sorted = Array.sortBy (\a b -> compare (snd a) (snd b)) pairs
  in map fst (Array.head sorted)

-- | Get LRU size.
lruSize :: LRUTracker -> Int
lruSize tracker = Map.size tracker.entries

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                            // tier configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Configuration for a single cache tier.
type TierConfig =
  { maxEntries :: Int        -- Maximum entries in this tier
  , maxSizeBytes :: Int      -- Maximum memory for this tier
  , ttlMs :: Number          -- Time-to-live in milliseconds
  , targetLatencyMs :: Number -- Target access latency
  }

-- | Default tier configuration.
defaultTierConfig :: TierConfig
defaultTierConfig =
  { maxEntries: 100
  , maxSizeBytes: 10000000   -- 10MB
  , ttlMs: 60000.0           -- 1 minute
  , targetLatencyMs: 5.0
  }

-- | L0 tier: Stable state (hot path).
tierConfigL0 :: TierConfig
tierConfigL0 =
  { maxEntries: 1000
  , maxSizeBytes: 50000000   -- 50MB
  , ttlMs: 60000.0           -- 1 minute
  , targetLatencyMs: 0.1     -- <0.1ms
  }

-- | L1 tier: Composition results.
tierConfigL1 :: TierConfig
tierConfigL1 =
  { maxEntries: 500
  , maxSizeBytes: 100000000  -- 100MB
  , ttlMs: 300000.0          -- 5 minutes
  , targetLatencyMs: 1.0     -- <1ms
  }

-- | L2 tier: Computed/derived data.
tierConfigL2 :: TierConfig
tierConfigL2 =
  { maxEntries: 200
  , maxSizeBytes: 50000000   -- 50MB
  , ttlMs: 600000.0          -- 10 minutes
  , targetLatencyMs: 5.0     -- <5ms
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                           // cache configuration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Full cache configuration.
type CacheConfig =
  { l0 :: TierConfig
  , l1 :: TierConfig
  , l2 :: TierConfig
  , evictionRatio :: Number  -- Fraction to evict when at capacity (0.1 = 10%)
  }

-- | Default cache configuration.
defaultConfig :: CacheConfig
defaultConfig =
  { l0: tierConfigL0
  , l1: tierConfigL1
  , l2: tierConfigL2
  , evictionRatio: 0.1
  }

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                // cache stats
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Cache statistics.
type CacheStats =
  { entryCount :: Int
  , totalSizeBytes :: Int
  , hits :: Int
  , misses :: Int
  , evictions :: Int
  , l0Count :: Int
  , l1Count :: Int
  , l2Count :: Int
  }

-- | Calculate hit rate (0.0 to 1.0).
hitRate :: CacheStats -> Number
hitRate stats =
  let total = stats.hits + stats.misses
  in if total == 0 
     then 0.0 
     else toNumber stats.hits / toNumber total
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

foreign import toNumberImpl :: Int -> Number

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // composition cache
-- ═══════════════════════════════════════════════════════════════════════════════

-- | The composition cache — tiered, content-addressed, LRU-evicting.
-- |
-- | This is the main cache structure. It stores composition results
-- | indexed by content-addressed keys (UUID5 + generation).
type CompositionCache a =
  { entries :: Map String (CacheEntry a)  -- CacheKey string -> entry
  , lru :: LRUTracker                     -- Access ordering
  , tagIndex :: Map CacheTag (Set String) -- Tag -> keys
  , config :: CacheConfig
  , stats :: CacheStats
  }

-- | Create an empty cache.
emptyCache :: forall a. CacheConfig -> CompositionCache a
emptyCache config =
  { entries: Map.empty
  , lru: emptyLRU
  , tagIndex: Map.empty
  , config: config
  , stats: emptyStats
  }
  where
    emptyStats :: CacheStats
    emptyStats =
      { entryCount: 0
      , totalSizeBytes: 0
      , hits: 0
      , misses: 0
      , evictions: 0
      , l0Count: 0
      , l1Count: 0
      , l2Count: 0
      }

-- | Get an entry from the cache.
-- |
-- | Returns Just entry if found and not expired, Nothing otherwise.
-- | Updates LRU on hit.
cacheGet :: forall a. String -> Number -> CompositionCache a -> { result :: Maybe a, cache :: CompositionCache a }
cacheGet key now cache =
  case Map.lookup key cache.entries of
    Nothing -> 
      -- Cache miss
      { result: Nothing
      , cache: cache { stats = cache.stats { misses = cache.stats.misses + 1 } }
      }
    Just entry ->
      -- Check expiration
      if isExpired entry.metadata now
      then 
        -- Expired: remove and return miss
        let newEntries = Map.delete key cache.entries
            newLRU = lruRemove key cache.lru
        in { result: Nothing
           , cache: cache 
               { entries = newEntries
               , lru = newLRU
               , stats = cache.stats { misses = cache.stats.misses + 1, entryCount = cache.stats.entryCount - 1 }
               }
           }
      else
        -- Hit: update LRU and stats
        let newLRU = lruTouch key cache.lru
            newEntry = entry { metadata = entry.metadata { hitCount = entry.metadata.hitCount + 1, lastAccessed = now } }
            newEntries = Map.insert key newEntry cache.entries
        in { result: Just entry.value
           , cache: cache 
               { entries = newEntries
               , lru = newLRU
               , stats = cache.stats { hits = cache.stats.hits + 1 }
               }
           }
  where
    isExpired :: EntryMetadata -> Number -> Boolean
    isExpired meta timestamp = 
      case meta.expiresAt of
        Nothing -> false
        Just exp -> timestamp >= exp

-- | Put an entry into the cache.
-- |
-- | Evicts LRU entries if at capacity.
cachePut :: forall a. String -> a -> EntryMetadata -> CompositionCache a -> CompositionCache a
cachePut key value metadata cache =
  let 
    -- Create entry
    entry :: CacheEntry a
    entry = { value: value, metadata: metadata }
    
    -- Add to entries and LRU
    newEntries = Map.insert key entry cache.entries
    newLRU = lruAdd key cache.lru
    
    -- Update tag index
    newTagIndex = addToTagIndex key metadata.tags cache.tagIndex
    
    -- Update tier counts
    newStats = updateTierCount metadata.tier 1 cache.stats
    
  in cache
    { entries = newEntries
    , lru = newLRU
    , tagIndex = newTagIndex
    , stats = newStats { entryCount = newStats.entryCount + 1, totalSizeBytes = newStats.totalSizeBytes + metadata.sizeBytes }
    }
  where
    addToTagIndex :: String -> Set CacheTag -> Map CacheTag (Set String) -> Map CacheTag (Set String)
    addToTagIndex k tags idx =
      let tagArray :: Array CacheTag
          tagArray = Set.toUnfoldable tags
      in foldl (\acc tag -> 
           let existing = fromMaybe Set.empty (Map.lookup tag acc)
           in Map.insert tag (Set.insert k existing) acc
         ) idx tagArray

    updateTierCount :: CacheTier -> Int -> CacheStats -> CacheStats
    updateTierCount TierL0 delta stats = stats { l0Count = stats.l0Count + delta }
    updateTierCount TierL1 delta stats = stats { l1Count = stats.l1Count + delta }
    updateTierCount TierL2 delta stats = stats { l2Count = stats.l2Count + delta }

-- | Invalidate a specific cache entry.
cacheInvalidate :: forall a. String -> CompositionCache a -> CompositionCache a
cacheInvalidate key cache =
  case Map.lookup key cache.entries of
    Nothing -> cache
    Just entry ->
      let 
        newEntries = Map.delete key cache.entries
        newLRU = lruRemove key cache.lru
        newTagIndex = removeFromTagIndex key entry.metadata.tags cache.tagIndex
        newStats = updateTierCount entry.metadata.tier (-1) cache.stats
      in cache
        { entries = newEntries
        , lru = newLRU
        , tagIndex = newTagIndex
        , stats = newStats { entryCount = newStats.entryCount - 1, totalSizeBytes = newStats.totalSizeBytes - entry.metadata.sizeBytes }
        }
  where
    removeFromTagIndex :: String -> Set CacheTag -> Map CacheTag (Set String) -> Map CacheTag (Set String)
    removeFromTagIndex k tags idx =
      let tagArray :: Array CacheTag
          tagArray = Set.toUnfoldable tags
      in foldl (\acc tag ->
           case Map.lookup tag acc of
             Nothing -> acc
             Just keys -> Map.insert tag (Set.delete k keys) acc
         ) idx tagArray

    updateTierCount :: CacheTier -> Int -> CacheStats -> CacheStats
    updateTierCount TierL0 delta stats = stats { l0Count = stats.l0Count + delta }
    updateTierCount TierL1 delta stats = stats { l1Count = stats.l1Count + delta }
    updateTierCount TierL2 delta stats = stats { l2Count = stats.l2Count + delta }

-- | Invalidate all entries with a specific tag.
cacheInvalidateByTag :: forall a. CacheTag -> CompositionCache a -> CompositionCache a
cacheInvalidateByTag tag cache =
  case Map.lookup tag cache.tagIndex of
    Nothing -> cache
    Just keys -> 
      let keyArray :: Array String
          keyArray = Set.toUnfoldable keys
      in foldl (\acc k -> cacheInvalidate k acc) cache keyArray

-- | Evict LRU entries until under capacity.
cacheEvictLRU :: forall a. Int -> CompositionCache a -> CompositionCache a
cacheEvictLRU targetCount cache =
  if cache.stats.entryCount <= targetCount
  then cache
  else case lruOldest cache.lru of
    Nothing -> cache
    Just oldestKey ->
      let newCache = cacheInvalidate oldestKey cache
          updatedCache = newCache { stats = newCache.stats { evictions = newCache.stats.evictions + 1 } }
      in cacheEvictLRU targetCount updatedCache

-- | Get cache statistics.
cacheStats :: forall a. CompositionCache a -> CacheStats
cacheStats cache = cache.stats

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                          // additional stats
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Calculate miss rate (0.0 to 1.0).
missRate :: CacheStats -> Number
missRate stats =
  let total = stats.hits + stats.misses
  in if total == 0 
     then 0.0 
     else toNumber stats.misses / toNumber total
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- | Calculate eviction rate (evictions per access).
evictionRate :: CacheStats -> Number
evictionRate stats =
  let total = stats.hits + stats.misses
  in if total == 0 
     then 0.0 
     else toNumber stats.evictions / toNumber total
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                         // query operations
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if a key exists in the cache (without updating LRU).
cacheContains :: forall a. String -> CompositionCache a -> Boolean
cacheContains key cache = isJust $ Map.lookup key cache.entries

-- | Get the number of entries in the cache.
cacheSize :: forall a. CompositionCache a -> Int
cacheSize cache = cache.stats.entryCount

-- | Get the total size in bytes.
cacheSizeBytes :: forall a. CompositionCache a -> Int
cacheSizeBytes cache = cache.stats.totalSizeBytes

-- | Get entries filtered by tier.
cacheGetByTier :: forall a. CacheTier -> CompositionCache a -> Array (Tuple String (CacheEntry a))
cacheGetByTier tier cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
  in Array.filter (\entry -> (snd entry).metadata.tier == tier) allEntries

-- | Prune all expired entries.
cachePruneExpired :: forall a. Number -> CompositionCache a -> CompositionCache a
cachePruneExpired now cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
      expiredKeys = Array.filter (\entry -> isExpiredEntry (snd entry) now) allEntries
  in foldl (\acc entry -> cacheInvalidate (fst entry) acc) cache expiredKeys
  where
    isExpiredEntry :: CacheEntry a -> Number -> Boolean
    isExpiredEntry entry timestamp = 
      case entry.metadata.expiresAt of
        Nothing -> false
        Just exp -> timestamp >= exp

-- | Get top N most recently accessed entries.
cacheGetTop :: forall a. Int -> CompositionCache a -> Array (Tuple String (CacheEntry a))
cacheGetTop n cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
      sorted = Array.sortBy (\a b -> compareLastAccessed (snd a) (snd b)) allEntries
  in Array.take n sorted
  where
    compareLastAccessed :: CacheEntry a -> CacheEntry a -> Ordering
    compareLastAccessed a b = 
      if a.metadata.lastAccessed > b.metadata.lastAccessed
      then LT  -- Higher access time = more recent = should come first
      else if a.metadata.lastAccessed < b.metadata.lastAccessed
      then GT
      else EQ

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                  // content-addressed integration
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Get an entry using an Identified value's cache key.
cacheGetIdentified :: forall a b. Identified b -> Number -> CompositionCache a -> { result :: Maybe a, cache :: CompositionCache a }
cacheGetIdentified identified now cache =
  let key = cacheKeyString $ toCacheKey identified
  in cacheGet key now cache

-- | Put an entry using an Identified value's cache key.
cachePutIdentified :: forall a b. Identified b -> a -> EntryMetadata -> CompositionCache a -> CompositionCache a
cachePutIdentified identified value metadata cache =
  let key = cacheKeyString $ toCacheKey identified
      -- Update metadata generation from the identified value
      updatedMetadata = metadata { generation = getGeneration identified }
  in cachePut key value updatedMetadata cache
  where
    getGeneration :: Identified b -> Generation
    getGeneration id = id.generation

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                       // generation utilities
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Create initial generation for new entries.
initialEntryGeneration :: Generation
initialEntryGeneration = initialGeneration

-- | Bump generation for cache invalidation tracking.
bumpEntryGeneration :: Generation -> Generation
bumpEntryGeneration = nextGeneration

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                   // debugging
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Show a cache entry for debugging.
showCacheEntry :: forall a. CacheEntry a -> String
showCacheEntry entry = 
  "CacheEntry { tier: " <> show entry.metadata.tier 
  <> ", gen: " <> show (unwrapGeneration entry.metadata.generation)
  <> ", hits: " <> show entry.metadata.hitCount
  <> ", size: " <> show entry.metadata.sizeBytes <> "b }"

-- | Show cache statistics for debugging.
showCacheStats :: CacheStats -> String
showCacheStats stats =
  "CacheStats { entries: " <> show stats.entryCount
  <> ", size: " <> show stats.totalSizeBytes <> "b"
  <> ", hits: " <> show stats.hits
  <> ", misses: " <> show stats.misses
  <> ", evictions: " <> show stats.evictions
  <> ", L0: " <> show stats.l0Count
  <> ", L1: " <> show stats.l1Count
  <> ", L2: " <> show stats.l2Count <> " }"

-- | Get the total number of entries (alias for stats access).
cacheLength :: forall a. CompositionCache a -> Int
cacheLength cache = Array.length allEntries
  where
    allEntries :: Array (Tuple String (CacheEntry a))
    allEntries = Map.toUnfoldable cache.entries

-- | Check if cache needs eviction based on config.
cacheNeedsEviction :: forall a. CacheTier -> CompositionCache a -> Boolean
cacheNeedsEviction tier cache =
  let tierConfig = getTierConfig tier cache.config
      tierCount = getTierCount tier cache.stats
  in tierCount >= tierConfig.maxEntries || otherwise
  where
    getTierConfig :: CacheTier -> CacheConfig -> TierConfig
    getTierConfig TierL0 cfg = cfg.l0
    getTierConfig TierL1 cfg = cfg.l1
    getTierConfig TierL2 cfg = cfg.l2
    
    getTierCount :: CacheTier -> CacheStats -> Int
    getTierCount TierL0 s = s.l0Count
    getTierCount TierL1 s = s.l1Count
    getTierCount TierL2 s = s.l2Count

-- | Compare two cache entries by generation.
compareByGeneration :: forall a. CacheEntry a -> CacheEntry a -> Boolean
compareByGeneration a b = 
  unwrapGeneration a.metadata.generation /= unwrapGeneration b.metadata.generation

-- | Check if two entries have same content (same generation).
sameEntryContent :: forall a. CacheEntry a -> CacheEntry a -> Boolean
sameEntryContent a b = 
  not (compareByGeneration a b) && a.metadata.tier == b.metadata.tier

-- | Filter entries by multiple conditions.
filterEntries :: forall a. 
  (CacheEntry a -> Boolean) -> 
  (CacheEntry a -> Boolean) -> 
  CompositionCache a -> 
  Array (Tuple String (CacheEntry a))
filterEntries pred1 pred2 cache =
  let allEntries :: Array (Tuple String (CacheEntry a))
      allEntries = Map.toUnfoldable cache.entries
      filtered1 = Array.filter (\e -> pred1 (snd e)) allEntries
  in Array.filter (\e -> pred2 (snd e)) filtered1

-- | Calculate memory utilization ratio.
memoryUtilization :: forall a. CompositionCache a -> Number
memoryUtilization cache =
  let maxBytes = cache.config.l0.maxSizeBytes 
               + cache.config.l1.maxSizeBytes 
               + cache.config.l2.maxSizeBytes
      currentBytes = cache.stats.totalSizeBytes
  in toNumber currentBytes / toNumber maxBytes
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- | Tuple constructor wrapper for explicit usage.
makeCacheKeyPair :: forall a. String -> CacheEntry a -> Tuple String (CacheEntry a)
makeCacheKeyPair key entry = Tuple key entry

-- | Calculate weighted score for cache entry (for smart eviction).
-- | Score = hitCount * recencyWeight - ageWeight
entryScore :: forall a. CacheEntry a -> Number -> Number
entryScore entry now =
  let hits = toNumber entry.metadata.hitCount
      age = now - entry.metadata.lastAccessed
      recencyWeight = 10.0
      ageWeight = 0.001
  in hits * recencyWeight - age * ageWeight
  where
    toNumber :: Int -> Number
    toNumber n = toNumberImpl n

-- | Get the cache key for an identified value.
-- | Useful for pre-computing keys before cache operations.
identifiedToCacheKey :: forall a. Identified a -> CacheKey
identifiedToCacheKey = toCacheKey
