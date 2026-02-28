-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // hydrogen // gpu // resource
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GPU Resource Management — Caching, Pooling, and Lifecycle
-- |
-- | ## Purpose
-- |
-- | This module provides the resource management layer between pure kernel
-- | descriptions and actual WebGPU execution. It handles:
-- |
-- | - **Pipeline caching**: Compiled shaders are expensive; cache by content hash
-- | - **Buffer pooling**: Reuse buffers across frames to avoid allocation
-- | - **Texture pooling**: Reuse textures by format/size
-- | - **Resource lifecycle**: Track generation for cache invalidation
-- |
-- | ## Architecture
-- |
-- | ```
-- | ComputeKernel (pure data)
-- |       ↓
-- | Resource.purs (this module)
-- |       ↓ manages
-- | ┌─────────────────────────────────────┐
-- | │ PipelineCache                       │
-- | │   - UUID5-keyed compiled pipelines  │
-- | │   - LRU eviction                    │
-- | ├─────────────────────────────────────┤
-- | │ BufferPool                          │
-- | │   - Size-bucketed buffer pools      │
-- | │   - Free list management            │
-- | ├─────────────────────────────────────┤
-- | │ TexturePool                         │
-- | │   - Format×Size×Usage keyed         │
-- | │   - Mipmap chain handling           │
-- | └─────────────────────────────────────┘
-- |       ↓
-- | Interpreter.purs (executes against WebGPU)
-- | ```
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Resource identity is content-addressed:
-- | - Same kernel definition → same pipeline UUID5
-- | - Multiple agents can share compiled pipelines
-- | - Buffer pools reduce per-frame allocation to near-zero
-- | - Textures are reused across viewport regions
-- |
-- | ## Council Decision (2026-02-25)
-- |
-- | This module implements P2 from the Council Review:
-- | "TextureDescriptor, BufferDescriptor, PipelineCache"

module Hydrogen.GPU.Resource
  ( -- * Resource Handles
    ResourceHandle
      ( ResourceHandle )
  , handleId
  , handleGeneration
  , mkResourceHandle
  , incrementGeneration
  
  -- * Resource Identity
  , ResourceId
      ( ResourceId )
  , mkResourceId
  , resourceIdToString
  
  -- * Pipeline Cache
  , PipelineCache
  , mkPipelineCache
  , PipelineKey
  , mkPipelineKey
  , PipelineEntry
  , pipelineLookup
  , pipelineInsert
  , pipelineEvictLRU
  , pipelineCacheSize
  , pipelineCacheStats
  , CacheStats
  
  -- * Buffer Pool
  , BufferPool
  , mkBufferPool
  , BufferHandle
  , BufferSpec
  , mkBufferSpec
  , bufferAcquire
  , bufferRelease
  , bufferPoolStats
  , PoolStats
  
  -- * Texture Pool
  , TexturePool
  , mkTexturePool
  , TextureHandle
  , TextureSpec
  , mkTextureSpec
  , textureAcquire
  , textureRelease
  , texturePoolStats
  
  -- * Resource Registry
  , ResourceRegistry
  , mkResourceRegistry
  , registryPipelines
  , registryBuffers
  , registryTextures
  , registryFrame
  , advanceFrame
  , collectGarbage
  
  -- * Buffer Size Buckets
  , BufferBucket
      ( Bucket1KB
      , Bucket4KB
      , Bucket16KB
      , Bucket64KB
      , Bucket256KB
      , Bucket1MB
      , Bucket4MB
      , Bucket16MB
      , BucketCustom
      )
  , bucketSize
  , bucketForSize
  
  -- * Texture Dimensions
  , TextureDimension
      ( Dim2D
      , Dim3D
      , DimCube
      )
  
  -- * Presets
  , defaultPipelineCache
  , defaultBufferPool
  , defaultTexturePool
  , defaultResourceRegistry
  
  -- * Memory Estimation
  , estimateBufferMemory
  , estimateTextureMemory
  , bufferPoolMemoryUsed
  , texturePoolMemoryUsed
  
  -- * Resource Transforms
  , mapFreeBuffers
  , mapFreeTextures
  , pipelineKeys
  , allFreeBuffers
  , bufferCountByBucket
  
  -- * Resource Filtering
  , recentPipelines
  , expensivePipelines
  , largeBuffers
  , largeTextures
  
  -- * Registry Operations
  , withPipelines
  , withBuffers
  , withTextures
  , registryMemoryEstimate
  , RegistryStats
  , registryStats
  
  -- * Capacity Management
  , pipelineHasCapacity
  , bufferPoolUnderThreshold
  , texturePoolUnderThreshold
  , registryUnderBudget
  , findSmallestFittingBuffer
  , findSmallestFittingTexture
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , compare
  , map
  , otherwise
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
  , (>>=)
  )

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Int as Int
import Data.Map as Map
import Data.Maybe (Maybe(Just, Nothing))
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))

-- WebGPU types
import Hydrogen.GPU.WebGPU.Types
  ( GPUTextureFormat
  , GPUTextureUsage
  , GPUBufferUsage
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // resource handles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a GPU resource.
-- |
-- | Uses content-based addressing for determinism:
-- | - Same resource specification → same ResourceId
-- | - Enables cross-agent resource sharing
-- | - Supports cache invalidation via generation
newtype ResourceId = ResourceId String

derive instance eqResourceId :: Eq ResourceId
derive instance ordResourceId :: Ord ResourceId

instance showResourceId :: Show ResourceId where
  show (ResourceId s) = "(ResourceId " <> show s <> ")"

-- | Create a resource ID from a content string.
-- |
-- | In a full implementation, this would compute UUID5.
-- | For now, we use the content directly as a deterministic ID.
mkResourceId :: String -> ResourceId
mkResourceId = ResourceId

-- | Convert resource ID to string.
resourceIdToString :: ResourceId -> String
resourceIdToString (ResourceId s) = s

-- | Handle to a GPU resource with generation tracking.
-- |
-- | ## Generation Semantics
-- |
-- | Generation increments when resource content changes:
-- | - gen 0: Initial creation
-- | - gen 1: First modification
-- | - gen N: Nth modification
-- |
-- | Cache entries are invalidated when generation mismatches.
newtype ResourceHandle = ResourceHandle
  { id :: ResourceId
  , generation :: Int
  }

derive instance eqResourceHandle :: Eq ResourceHandle

instance ordResourceHandle :: Ord ResourceHandle where
  compare (ResourceHandle a) (ResourceHandle b) =
    compare (Tuple a.id a.generation) (Tuple b.id b.generation)

instance showResourceHandle :: Show ResourceHandle where
  show (ResourceHandle h) = 
    "(ResourceHandle " <> show h.id <> " gen:" <> show h.generation <> ")"

-- | Get resource ID from handle.
handleId :: ResourceHandle -> ResourceId
handleId (ResourceHandle h) = h.id

-- | Get generation from handle.
handleGeneration :: ResourceHandle -> Int
handleGeneration (ResourceHandle h) = h.generation

-- | Create a new resource handle.
mkResourceHandle :: String -> ResourceHandle
mkResourceHandle contentKey = ResourceHandle
  { id: mkResourceId contentKey
  , generation: 0
  }

-- | Increment handle generation (for modifications).
incrementGeneration :: ResourceHandle -> ResourceHandle
incrementGeneration (ResourceHandle h) = ResourceHandle
  { id: h.id
  , generation: h.generation + 1
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // pipeline cache
-- ═════════════════════════════════════════════════════════════════════════════

-- | Key for pipeline lookup.
-- |
-- | Derived from kernel specification content hash.
newtype PipelineKey = PipelineKey String

derive instance eqPipelineKey :: Eq PipelineKey
derive instance ordPipelineKey :: Ord PipelineKey

instance showPipelineKey :: Show PipelineKey where
  show (PipelineKey s) = "(PipelineKey " <> s <> ")"

-- | Create pipeline key from content description.
mkPipelineKey :: String -> PipelineKey
mkPipelineKey = PipelineKey

-- | Cached pipeline entry.
-- |
-- | ## Fields
-- |
-- | - `handle`: Resource handle for this pipeline
-- | - `lastUsedFrame`: Frame number when last accessed (for LRU)
-- | - `compilationTime`: How long compilation took (for metrics)
-- | - `shaderSource`: WGSL source (for debugging/recompilation)
type PipelineEntry =
  { handle :: ResourceHandle
  , lastUsedFrame :: Int
  , compilationTime :: Number    -- milliseconds
  , shaderSource :: String
  }

-- | Pipeline cache with LRU eviction.
-- |
-- | ## Capacity Management
-- |
-- | - `maxEntries`: Hard limit on cached pipelines
-- | - Eviction uses LRU (least recently used frame)
-- | - Evicted pipelines can be recompiled on next use
newtype PipelineCache = PipelineCache
  { entries :: Map.Map PipelineKey PipelineEntry
  , maxEntries :: Int
  , currentFrame :: Int
  , hits :: Int
  , misses :: Int
  }

derive instance eqPipelineCache :: Eq PipelineCache

instance showPipelineCache :: Show PipelineCache where
  show (PipelineCache c) = 
    "(PipelineCache entries:" <> show (Map.size c.entries) <> 
    "/" <> show c.maxEntries <> ")"

-- | Create a new pipeline cache.
mkPipelineCache :: Int -> PipelineCache
mkPipelineCache maxEntries = PipelineCache
  { entries: Map.empty
  , maxEntries
  , currentFrame: 0
  , hits: 0
  , misses: 0
  }

-- | Default pipeline cache (256 entries).
defaultPipelineCache :: PipelineCache
defaultPipelineCache = mkPipelineCache 256

-- | Look up a pipeline in the cache.
-- |
-- | Returns the entry and an updated cache (with LRU timestamp).
pipelineLookup :: PipelineKey -> PipelineCache -> { entry :: Maybe PipelineEntry, cache :: PipelineCache }
pipelineLookup key (PipelineCache c) =
  case Map.lookup key c.entries of
    Nothing -> 
      { entry: Nothing
      , cache: PipelineCache (c { misses = c.misses + 1 })
      }
    Just entry ->
      let updatedEntry = entry { lastUsedFrame = c.currentFrame }
          updatedEntries = Map.insert key updatedEntry c.entries
      in
        { entry: Just updatedEntry
        , cache: PipelineCache (c { entries = updatedEntries, hits = c.hits + 1 })
        }

-- | Insert a pipeline into the cache.
-- |
-- | If at capacity, evicts LRU entry first.
pipelineInsert :: PipelineKey -> PipelineEntry -> PipelineCache -> PipelineCache
pipelineInsert key entry cache@(PipelineCache c) =
  let 
    -- Evict if at capacity
    cache' = if Map.size c.entries >= c.maxEntries
             then pipelineEvictLRU cache
             else cache
    (PipelineCache c') = cache'
    updatedEntry = entry { lastUsedFrame = c'.currentFrame }
  in
    PipelineCache (c' { entries = Map.insert key updatedEntry c'.entries })

-- | Evict the least recently used pipeline.
pipelineEvictLRU :: PipelineCache -> PipelineCache
pipelineEvictLRU (PipelineCache c) =
  case findLRU c.entries of
    Nothing -> PipelineCache c
    Just lruKey -> 
      PipelineCache (c { entries = Map.delete lruKey c.entries })
  where
    findLRU :: Map.Map PipelineKey PipelineEntry -> Maybe PipelineKey
    findLRU entries =
      let pairs = Map.toUnfoldable entries :: Array (Tuple PipelineKey PipelineEntry)
          sorted = Array.sortBy (\(Tuple _ a) (Tuple _ b) -> 
                     compare a.lastUsedFrame b.lastUsedFrame) pairs
      in case Array.head sorted of
           Nothing -> Nothing
           Just (Tuple k _) -> Just k

-- | Get cache size.
pipelineCacheSize :: PipelineCache -> Int
pipelineCacheSize (PipelineCache c) = Map.size c.entries

-- | Cache statistics.
type CacheStats =
  { entries :: Int
  , maxEntries :: Int
  , hits :: Int
  , misses :: Int
  , hitRate :: Number
  }

-- | Get cache statistics.
pipelineCacheStats :: PipelineCache -> CacheStats
pipelineCacheStats (PipelineCache c) =
  let total = c.hits + c.misses
      hitRate = if total > 0 
                then Int.toNumber c.hits / Int.toNumber total
                else 0.0
  in
    { entries: Map.size c.entries
    , maxEntries: c.maxEntries
    , hits: c.hits
    , misses: c.misses
    , hitRate
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // buffer pools
-- ═════════════════════════════════════════════════════════════════════════════

-- | Buffer size buckets for pooling.
-- |
-- | ## Bucket Strategy
-- |
-- | Buffers are allocated in power-of-4 sizes:
-- | - Reduces fragmentation
-- | - Enables fast bucket lookup
-- | - Supports custom sizes for large allocations
data BufferBucket
  = Bucket1KB       -- 1,024 bytes
  | Bucket4KB       -- 4,096 bytes
  | Bucket16KB      -- 16,384 bytes
  | Bucket64KB      -- 65,536 bytes
  | Bucket256KB     -- 262,144 bytes
  | Bucket1MB       -- 1,048,576 bytes
  | Bucket4MB       -- 4,194,304 bytes
  | Bucket16MB      -- 16,777,216 bytes
  | BucketCustom Int  -- Custom size

derive instance eqBufferBucket :: Eq BufferBucket

instance ordBufferBucket :: Ord BufferBucket where
  compare a b = compare (bucketSize a) (bucketSize b)

instance showBufferBucket :: Show BufferBucket where
  show Bucket1KB = "Bucket1KB"
  show Bucket4KB = "Bucket4KB"
  show Bucket16KB = "Bucket16KB"
  show Bucket64KB = "Bucket64KB"
  show Bucket256KB = "Bucket256KB"
  show Bucket1MB = "Bucket1MB"
  show Bucket4MB = "Bucket4MB"
  show Bucket16MB = "Bucket16MB"
  show (BucketCustom n) = "(BucketCustom " <> show n <> ")"

-- | Get bucket size in bytes.
bucketSize :: BufferBucket -> Int
bucketSize Bucket1KB = 1024
bucketSize Bucket4KB = 4096
bucketSize Bucket16KB = 16384
bucketSize Bucket64KB = 65536
bucketSize Bucket256KB = 262144
bucketSize Bucket1MB = 1048576
bucketSize Bucket4MB = 4194304
bucketSize Bucket16MB = 16777216
bucketSize (BucketCustom n) = n

-- | Find smallest bucket that fits requested size.
bucketForSize :: Int -> BufferBucket
bucketForSize size
  | size <= 1024 = Bucket1KB
  | size <= 4096 = Bucket4KB
  | size <= 16384 = Bucket16KB
  | size <= 65536 = Bucket64KB
  | size <= 262144 = Bucket256KB
  | size <= 1048576 = Bucket1MB
  | size <= 4194304 = Bucket4MB
  | size <= 16777216 = Bucket16MB
  | otherwise = BucketCustom size

-- | Buffer specification for allocation.
type BufferSpec =
  { size :: Int
  , usage :: Array GPUBufferUsage
  , label :: String
  }

-- | Create a buffer specification.
mkBufferSpec :: Int -> Array GPUBufferUsage -> String -> BufferSpec
mkBufferSpec size usage label = { size, usage, label }

-- | Handle to a pooled buffer.
newtype BufferHandle = BufferHandle
  { handle :: ResourceHandle
  , bucket :: BufferBucket
  , actualSize :: Int
  }

derive instance eqBufferHandle :: Eq BufferHandle

instance showBufferHandle :: Show BufferHandle where
  show (BufferHandle h) = 
    "(BufferHandle " <> show h.bucket <> " size:" <> show h.actualSize <> ")"

-- | Buffer pool for efficient reuse.
-- |
-- | ## Pool Structure
-- |
-- | - Separate free list per bucket
-- | - Acquired buffers tracked for release
-- | - Statistics for monitoring
newtype BufferPool = BufferPool
  { freeLists :: Map.Map BufferBucket (Array BufferHandle)
  , acquired :: Set.Set ResourceId
  , totalAllocated :: Int
  , totalAcquired :: Int
  , totalReleased :: Int
  }

derive instance eqBufferPool :: Eq BufferPool

instance showBufferPool :: Show BufferPool where
  show (BufferPool p) = 
    "(BufferPool allocated:" <> show p.totalAllocated <> 
    " acquired:" <> show (Set.size p.acquired) <> ")"

-- | Create a new buffer pool.
mkBufferPool :: BufferPool
mkBufferPool = BufferPool
  { freeLists: Map.empty
  , acquired: Set.empty
  , totalAllocated: 0
  , totalAcquired: 0
  , totalReleased: 0
  }

-- | Default buffer pool.
defaultBufferPool :: BufferPool
defaultBufferPool = mkBufferPool

-- | Pool statistics.
type PoolStats =
  { freeCount :: Int
  , acquiredCount :: Int
  , totalAllocated :: Int
  , reuseRate :: Number
  }

-- | Acquire a buffer from the pool.
-- |
-- | Returns a buffer handle and updated pool.
-- | If no suitable buffer is free, creates a new one.
bufferAcquire :: BufferSpec -> BufferPool -> { handle :: BufferHandle, pool :: BufferPool }
bufferAcquire spec (BufferPool p) =
  let bucket = bucketForSize spec.size
      freeList = Map.lookup bucket p.freeLists
  in case freeList >>= Array.head of
       Just existingHandle ->
         -- Reuse existing buffer
         let newFreeList = case freeList of
               Nothing -> []
               Just arr -> Array.drop 1 arr
             newFreeLists = Map.insert bucket newFreeList p.freeLists
             newAcquired = Set.insert (handleId (unwrapBufferHandle existingHandle)) p.acquired
         in
           { handle: existingHandle
           , pool: BufferPool (p 
               { freeLists = newFreeLists
               , acquired = newAcquired
               , totalAcquired = p.totalAcquired + 1
               })
           }
       Nothing ->
         -- Allocate new buffer
         let contentKey = spec.label <> "-" <> show spec.size <> "-" <> show p.totalAllocated
             newHandle = BufferHandle
               { handle: mkResourceHandle contentKey
               , bucket
               , actualSize: bucketSize bucket
               }
             newAcquired = Set.insert (handleId (unwrapBufferHandle newHandle)) p.acquired
         in
           { handle: newHandle
           , pool: BufferPool (p 
               { acquired = newAcquired
               , totalAllocated = p.totalAllocated + 1
               , totalAcquired = p.totalAcquired + 1
               })
           }
  where
    unwrapBufferHandle :: BufferHandle -> ResourceHandle
    unwrapBufferHandle (BufferHandle h) = h.handle

-- | Release a buffer back to the pool.
bufferRelease :: BufferHandle -> BufferPool -> BufferPool
bufferRelease bufHandle@(BufferHandle h) (BufferPool p) =
  let resourceId = handleId h.handle
      newAcquired = Set.delete resourceId p.acquired
      currentList = case Map.lookup h.bucket p.freeLists of
                      Nothing -> []
                      Just arr -> arr
      newFreeList = Array.cons bufHandle currentList
      newFreeLists = Map.insert h.bucket newFreeList p.freeLists
  in
    BufferPool (p 
      { freeLists = newFreeLists
      , acquired = newAcquired
      , totalReleased = p.totalReleased + 1
      })

-- | Get pool statistics.
bufferPoolStats :: BufferPool -> PoolStats
bufferPoolStats (BufferPool p) =
  let freeCount = foldl (\acc arr -> acc + Array.length arr) 0 
                        (Map.values p.freeLists)
      acquiredCount = Set.size p.acquired
      totalReused = p.totalAcquired - p.totalAllocated
      reuseRate = if p.totalAcquired > 0
                  then Int.toNumber totalReused / Int.toNumber p.totalAcquired
                  else 0.0
  in
    { freeCount
    , acquiredCount
    , totalAllocated: p.totalAllocated
    , reuseRate
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // texture pools
-- ═════════════════════════════════════════════════════════════════════════════

-- | Texture dimension type.
data TextureDimension
  = Dim2D
  | Dim3D
  | DimCube

derive instance eqTextureDimension :: Eq TextureDimension
derive instance ordTextureDimension :: Ord TextureDimension

instance showTextureDimension :: Show TextureDimension where
  show Dim2D = "2D"
  show Dim3D = "3D"
  show DimCube = "Cube"

-- | Texture specification for allocation.
type TextureSpec =
  { width :: Int
  , height :: Int
  , depth :: Int
  , format :: GPUTextureFormat
  , usage :: Array GPUTextureUsage
  , mipLevels :: Int
  , dimension :: TextureDimension
  , label :: String
  }

-- | Create a texture specification.
mkTextureSpec 
  :: Int 
  -> Int 
  -> GPUTextureFormat 
  -> Array GPUTextureUsage 
  -> String 
  -> TextureSpec
mkTextureSpec width height format usage label =
  { width
  , height
  , depth: 1
  , format
  , usage
  , mipLevels: 1
  , dimension: Dim2D
  , label
  }

-- | Handle to a pooled texture.
newtype TextureHandle = TextureHandle
  { handle :: ResourceHandle
  , spec :: TextureSpec
  }

derive instance eqTextureHandle :: Eq TextureHandle

instance showTextureHandle :: Show TextureHandle where
  show (TextureHandle h) = 
    "(TextureHandle " <> show h.spec.width <> "x" <> show h.spec.height <> ")"

-- | Texture pool key (format + size + usage).
type TexturePoolKey =
  { width :: Int
  , height :: Int
  , depth :: Int
  , format :: GPUTextureFormat
  , mipLevels :: Int
  }

-- | Texture pool for efficient reuse.
newtype TexturePool = TexturePool
  { freeTextures :: Array TextureHandle
  , acquired :: Set.Set ResourceId
  , totalAllocated :: Int
  , totalAcquired :: Int
  , totalReleased :: Int
  }

derive instance eqTexturePool :: Eq TexturePool

instance showTexturePool :: Show TexturePool where
  show (TexturePool p) = 
    "(TexturePool allocated:" <> show p.totalAllocated <> 
    " acquired:" <> show (Set.size p.acquired) <> ")"

-- | Create a new texture pool.
mkTexturePool :: TexturePool
mkTexturePool = TexturePool
  { freeTextures: []
  , acquired: Set.empty
  , totalAllocated: 0
  , totalAcquired: 0
  , totalReleased: 0
  }

-- | Default texture pool.
defaultTexturePool :: TexturePool
defaultTexturePool = mkTexturePool

-- | Acquire a texture from the pool.
textureAcquire :: TextureSpec -> TexturePool -> { handle :: TextureHandle, pool :: TexturePool }
textureAcquire spec (TexturePool p) =
  let matchingTexture = Array.find (textureMatches spec) p.freeTextures
  in case matchingTexture of
       Just existingHandle ->
         -- Reuse existing texture
         let newFreeTextures = Array.filter 
               (\h -> h /= existingHandle) p.freeTextures
             newAcquired = Set.insert 
               (handleId (unwrapTextureHandle existingHandle)) p.acquired
         in
           { handle: existingHandle
           , pool: TexturePool (p 
               { freeTextures = newFreeTextures
               , acquired = newAcquired
               , totalAcquired = p.totalAcquired + 1
               })
           }
       Nothing ->
         -- Allocate new texture
         let contentKey = spec.label <> "-" <> show spec.width <> "x" <> 
                         show spec.height <> "-" <> show p.totalAllocated
             newHandle = TextureHandle
               { handle: mkResourceHandle contentKey
               , spec
               }
             newAcquired = Set.insert 
               (handleId (unwrapTextureHandle newHandle)) p.acquired
         in
           { handle: newHandle
           , pool: TexturePool (p 
               { acquired = newAcquired
               , totalAllocated = p.totalAllocated + 1
               , totalAcquired = p.totalAcquired + 1
               })
           }
  where
    unwrapTextureHandle :: TextureHandle -> ResourceHandle
    unwrapTextureHandle (TextureHandle h) = h.handle

-- | Check if texture matches specification.
textureMatches :: TextureSpec -> TextureHandle -> Boolean
textureMatches spec (TextureHandle h) =
  h.spec.width == spec.width &&
  h.spec.height == spec.height &&
  h.spec.depth == spec.depth &&
  h.spec.format == spec.format &&
  h.spec.mipLevels >= spec.mipLevels

-- | Release a texture back to the pool.
textureRelease :: TextureHandle -> TexturePool -> TexturePool
textureRelease texHandle@(TextureHandle h) (TexturePool p) =
  let resourceId = handleId h.handle
      newAcquired = Set.delete resourceId p.acquired
      newFreeTextures = Array.cons texHandle p.freeTextures
  in
    TexturePool (p 
      { freeTextures = newFreeTextures
      , acquired = newAcquired
      , totalReleased = p.totalReleased + 1
      })

-- | Get texture pool statistics.
texturePoolStats :: TexturePool -> PoolStats
texturePoolStats (TexturePool p) =
  let freeCount = Array.length p.freeTextures
      acquiredCount = Set.size p.acquired
      totalReused = p.totalAcquired - p.totalAllocated
      reuseRate = if p.totalAcquired > 0
                  then Int.toNumber totalReused / Int.toNumber p.totalAcquired
                  else 0.0
  in
    { freeCount
    , acquiredCount
    , totalAllocated: p.totalAllocated
    , reuseRate
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // resource registry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Central registry for all GPU resources.
-- |
-- | ## Lifecycle Management
-- |
-- | - Tracks frame number for LRU eviction
-- | - Garbage collection removes unused resources
-- | - Single source of truth for resource state
newtype ResourceRegistry = ResourceRegistry
  { pipelines :: PipelineCache
  , buffers :: BufferPool
  , textures :: TexturePool
  , currentFrame :: Int
  , gcThreshold :: Int        -- Frames before GC eligible
  }

derive instance eqResourceRegistry :: Eq ResourceRegistry

instance showResourceRegistry :: Show ResourceRegistry where
  show (ResourceRegistry r) = 
    "(ResourceRegistry frame:" <> show r.currentFrame <> ")"

-- | Create a new resource registry.
mkResourceRegistry :: ResourceRegistry
mkResourceRegistry = ResourceRegistry
  { pipelines: defaultPipelineCache
  , buffers: defaultBufferPool
  , textures: defaultTexturePool
  , currentFrame: 0
  , gcThreshold: 60           -- 60 frames (~1 second at 60fps)
  }

-- | Default resource registry.
defaultResourceRegistry :: ResourceRegistry
defaultResourceRegistry = mkResourceRegistry

-- | Get pipeline cache from registry.
registryPipelines :: ResourceRegistry -> PipelineCache
registryPipelines (ResourceRegistry r) = r.pipelines

-- | Get buffer pool from registry.
registryBuffers :: ResourceRegistry -> BufferPool
registryBuffers (ResourceRegistry r) = r.buffers

-- | Get texture pool from registry.
registryTextures :: ResourceRegistry -> TexturePool
registryTextures (ResourceRegistry r) = r.textures

-- | Get current frame number.
registryFrame :: ResourceRegistry -> Int
registryFrame (ResourceRegistry r) = r.currentFrame

-- | Advance to next frame.
advanceFrame :: ResourceRegistry -> ResourceRegistry
advanceFrame (ResourceRegistry r) =
  let (PipelineCache pc) = r.pipelines
      newPipelines = PipelineCache (pc { currentFrame = r.currentFrame + 1 })
  in
    ResourceRegistry (r 
      { currentFrame = r.currentFrame + 1
      , pipelines = newPipelines
      })

-- | Run garbage collection on stale resources.
-- |
-- | Evicts pipelines not used within gcThreshold frames.
collectGarbage :: ResourceRegistry -> ResourceRegistry
collectGarbage (ResourceRegistry r) =
  let (PipelineCache pc) = r.pipelines
      threshold = r.currentFrame - r.gcThreshold
      -- Filter out stale pipelines
      freshEntries = Map.filter 
        (\entry -> entry.lastUsedFrame >= threshold) pc.entries
      newPipelines = PipelineCache (pc { entries = freshEntries })
  in
    ResourceRegistry (r { pipelines = newPipelines })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // memory estimation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Estimate memory usage of a buffer specification in bytes.
-- |
-- | Uses bucket size (actual allocation) not requested size.
estimateBufferMemory :: BufferSpec -> Int
estimateBufferMemory spec = bucketSize $ bucketForSize spec.size

-- | Estimate memory usage of a texture specification in bytes.
-- |
-- | Calculation: width × height × depth × bytesPerPixel × mipFactor
-- | where mipFactor ≈ 1.33 for full mip chain (1 + 1/4 + 1/16 + ...)
estimateTextureMemory :: TextureSpec -> Int
estimateTextureMemory spec =
  let baseSize = spec.width * spec.height * spec.depth * bytesPerPixel spec.format
      -- Mip chain adds ~33% for full chain
      mipFactor :: Number
      mipFactor = if spec.mipLevels > 1 then 4.0 / 3.0 else 1.0
      -- Convert to Int (floor)
      mipMultiplied = Int.toNumber baseSize * mipFactor
  in
    Int.floor mipMultiplied
  where
    -- Approximate bytes per pixel for common formats
    bytesPerPixel :: GPUTextureFormat -> Int
    bytesPerPixel _ = 4  -- Default to RGBA8 (4 bytes)
                         -- Full implementation would pattern match on format

-- | Total estimated memory for all acquired buffers.
bufferPoolMemoryUsed :: BufferPool -> Int
bufferPoolMemoryUsed (BufferPool p) =
  -- Each acquired buffer uses its bucket size
  -- We don't track individual sizes, so estimate from total allocated
  p.totalAllocated * averageBucketSize
  where
    averageBucketSize = bucketSize Bucket64KB  -- Conservative estimate

-- | Total estimated memory for all acquired textures.
texturePoolMemoryUsed :: TexturePool -> Int
texturePoolMemoryUsed (TexturePool p) =
  foldl (\acc (TextureHandle h) -> acc + estimateTextureMemory h.spec) 0 p.freeTextures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // resource transforms
-- ═════════════════════════════════════════════════════════════════════════════

-- | Map a function over all free buffer handles.
-- |
-- | Useful for batch operations like resetting state or logging.
mapFreeBuffers :: (BufferHandle -> BufferHandle) -> BufferPool -> BufferPool
mapFreeBuffers f (BufferPool p) =
  let newFreeLists = map (map f) p.freeLists
  in BufferPool (p { freeLists = newFreeLists })

-- | Map a function over all free texture handles.
mapFreeTextures :: (TextureHandle -> TextureHandle) -> TexturePool -> TexturePool
mapFreeTextures f (TexturePool p) =
  let newFreeTextures = map f p.freeTextures
  in TexturePool (p { freeTextures = newFreeTextures })

-- | Get all pipeline keys in the cache.
pipelineKeys :: PipelineCache -> Array PipelineKey
pipelineKeys (PipelineCache c) =
  map (\(Tuple k _) -> k) $ Map.toUnfoldable c.entries

-- | Get all free buffer handles across all buckets.
allFreeBuffers :: BufferPool -> Array BufferHandle
allFreeBuffers (BufferPool p) =
  foldl (\acc arr -> acc <> arr) [] (Map.values p.freeLists)

-- | Count buffers by bucket.
bufferCountByBucket :: BufferPool -> Array { bucket :: BufferBucket, count :: Int }
bufferCountByBucket (BufferPool p) =
  map (\(Tuple bucket handles) -> { bucket, count: Array.length handles }) $
    Map.toUnfoldable p.freeLists

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // resource filtering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Filter pipelines by last used frame.
-- |
-- | Returns pipelines used within the last N frames.
recentPipelines :: Int -> PipelineCache -> Array PipelineEntry
recentPipelines withinFrames (PipelineCache c) =
  let threshold = c.currentFrame - withinFrames
      allEntries = map (\(Tuple _ e) -> e) $ Map.toUnfoldable c.entries
  in Array.filter (\e -> e.lastUsedFrame >= threshold) allEntries

-- | Filter pipelines by compilation time.
-- |
-- | Returns pipelines that took longer than threshold to compile.
-- | Useful for identifying expensive shaders.
expensivePipelines :: Number -> PipelineCache -> Array PipelineEntry
expensivePipelines thresholdMs (PipelineCache c) =
  let allEntries = map (\(Tuple _ e) -> e) $ Map.toUnfoldable c.entries
  in Array.filter (\e -> e.compilationTime > thresholdMs) allEntries

-- | Get buffers larger than a threshold.
largeBuffers :: Int -> BufferPool -> Array BufferHandle
largeBuffers thresholdBytes pool =
  Array.filter (\(BufferHandle h) -> h.actualSize > thresholdBytes) $
    allFreeBuffers pool

-- | Get textures larger than dimensions.
largeTextures :: Int -> Int -> TexturePool -> Array TextureHandle
largeTextures minWidth minHeight (TexturePool p) =
  Array.filter (\(TextureHandle h) -> 
    h.spec.width > minWidth && h.spec.height > minHeight) p.freeTextures

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // registry operations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Update pipelines in registry.
withPipelines :: (PipelineCache -> PipelineCache) -> ResourceRegistry -> ResourceRegistry
withPipelines f (ResourceRegistry r) =
  ResourceRegistry (r { pipelines = f r.pipelines })

-- | Update buffers in registry.
withBuffers :: (BufferPool -> BufferPool) -> ResourceRegistry -> ResourceRegistry
withBuffers f (ResourceRegistry r) =
  ResourceRegistry (r { buffers = f r.buffers })

-- | Update textures in registry.
withTextures :: (TexturePool -> TexturePool) -> ResourceRegistry -> ResourceRegistry
withTextures f (ResourceRegistry r) =
  ResourceRegistry (r { textures = f r.textures })

-- | Total memory estimate across all resource types.
registryMemoryEstimate :: ResourceRegistry -> Int
registryMemoryEstimate (ResourceRegistry r) =
  bufferPoolMemoryUsed r.buffers + texturePoolMemoryUsed r.textures

-- | Combined statistics for all resource pools.
type RegistryStats =
  { pipelineStats :: CacheStats
  , bufferStats :: PoolStats
  , textureStats :: PoolStats
  , totalMemoryBytes :: Int
  , currentFrame :: Int
  }

-- | Get combined registry statistics.
registryStats :: ResourceRegistry -> RegistryStats
registryStats reg@(ResourceRegistry r) =
  { pipelineStats: pipelineCacheStats r.pipelines
  , bufferStats: bufferPoolStats r.buffers
  , textureStats: texturePoolStats r.textures
  , totalMemoryBytes: registryMemoryEstimate reg
  , currentFrame: r.currentFrame
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // capacity management
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if pipeline cache has room for more entries.
pipelineHasCapacity :: PipelineCache -> Boolean
pipelineHasCapacity (PipelineCache c) =
  Map.size c.entries < c.maxEntries

-- | Check if buffer pool is below a memory threshold.
-- |
-- | Returns true if estimated memory usage is below threshold bytes.
bufferPoolUnderThreshold :: Int -> BufferPool -> Boolean
bufferPoolUnderThreshold thresholdBytes pool =
  bufferPoolMemoryUsed pool < thresholdBytes

-- | Check if texture pool is below a memory threshold.
texturePoolUnderThreshold :: Int -> TexturePool -> Boolean
texturePoolUnderThreshold thresholdBytes pool =
  texturePoolMemoryUsed pool < thresholdBytes

-- | Check if registry total memory is under budget.
registryUnderBudget :: Int -> ResourceRegistry -> Boolean
registryUnderBudget budgetBytes reg =
  registryMemoryEstimate reg < budgetBytes

-- | Find smallest buffer that fits the requested size.
-- |
-- | Returns the first free buffer with actual size >= requested,
-- | sorted by size ascending to minimize waste.
findSmallestFittingBuffer :: Int -> BufferPool -> Maybe BufferHandle
findSmallestFittingBuffer requestedSize pool =
  let allFree = allFreeBuffers pool
      fitting = Array.filter (\(BufferHandle h) -> h.actualSize >= requestedSize) allFree
      sorted = Array.sortBy (\(BufferHandle a) (BufferHandle b) -> 
                 compare a.actualSize b.actualSize) fitting
  in Array.head sorted

-- | Find smallest texture that fits the requested dimensions.
findSmallestFittingTexture :: Int -> Int -> TexturePool -> Maybe TextureHandle
findSmallestFittingTexture width height (TexturePool p) =
  let fitting = Array.filter (\(TextureHandle h) -> 
                  h.spec.width >= width && h.spec.height >= height) p.freeTextures
      sorted = Array.sortBy (\(TextureHandle a) (TextureHandle b) ->
                 compare (a.spec.width * a.spec.height) (b.spec.width * b.spec.height)) fitting
  in Array.head sorted
