-- | Lattice.Utils.ResourcePool - Generic resource pooling
-- |
-- | Abstract resource pool that can be used for any pooled resource type.
-- | The TypeScript version uses HTMLCanvasElement; this version is generic.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/ResourcePool.lean

module Lattice.Utils.ResourcePool
  ( -- Types
    PoolConfig
  , defaultPoolConfig
  , PoolEntry
  , ResourcePool
  , AcquireResult(..)
  , PoolStats
    -- Pool Operations
  , emptyPool
  , poolWithConfig
  , findAvailable
  , acquire
  , release
  , cleanup
  , clearPool
  , getStats
  ) where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Configuration for pool behavior
type PoolConfig =
  { maxSize :: Int     -- ^ Maximum pooled resources (default: 20)
  , maxAgeMs :: Int    -- ^ TTL for unused resources in ms (default: 60000)
  }

-- | Default pool configuration
defaultPoolConfig :: PoolConfig
defaultPoolConfig =
  { maxSize: 20
  , maxAgeMs: 60000
  }

-- | A pooled resource entry
type PoolEntry a =
  { resource :: a
  , width :: Int
  , height :: Int
  , inUse :: Boolean
  , lastUsed :: Int  -- ^ Timestamp in milliseconds
  }

-- | Resource pool state
type ResourcePool a =
  { entries :: Array (PoolEntry a)
  , config :: PoolConfig
  }

-- | Result of acquiring a resource
data AcquireResult a
  = AcquireFound a        -- ^ Reused from pool
  | AcquireCreated a      -- ^ Newly created and added to pool
  | AcquirePoolFull a     -- ^ Created but pool at capacity

derive instance Generic (AcquireResult a) _

instance Show a => Show (AcquireResult a) where
  show = genericShow

-- | Pool statistics
type PoolStats =
  { total :: Int
  , inUse :: Int
  , available :: Int
  }

--------------------------------------------------------------------------------
-- Pool Operations
--------------------------------------------------------------------------------

-- | Create an empty pool with default config
emptyPool :: forall a. ResourcePool a
emptyPool =
  { entries: []
  , config: defaultPoolConfig
  }

-- | Create an empty pool with custom config
poolWithConfig :: forall a. PoolConfig -> ResourcePool a
poolWithConfig config =
  { entries: []
  , config: config
  }

-- | Find a matching unused entry in the pool
findAvailable :: forall a. ResourcePool a -> Int -> Int -> Maybe (PoolEntry a)
findAvailable pool width height =
  Array.find matchEntry pool.entries
  where
    matchEntry entry =
      not entry.inUse &&
      entry.width == width &&
      entry.height == height

-- | Mark an entry as in use
markInUse :: forall a. Eq a => ResourcePool a -> a -> Int -> ResourcePool a
markInUse pool resource now =
  pool { entries = map updateEntry pool.entries }
  where
    updateEntry entry
      | entry.resource == resource =
          entry { inUse = true, lastUsed = now }
      | otherwise = entry

-- | Acquire a resource from the pool
-- |
-- | Returns { pool, result } where result indicates if reused or created.
-- | The caller must provide a function to create new resources.
acquire :: forall a. Eq a
        => ResourcePool a
        -> Int              -- ^ Width
        -> Int              -- ^ Height
        -> Int              -- ^ Current timestamp
        -> (Int -> Int -> a) -- ^ Resource creator
        -> { pool :: ResourcePool a, result :: AcquireResult a }
acquire pool width height now createResource =
  case findAvailable pool width height of
    Just entry ->
      let updatedPool = markInUse pool entry.resource now
      in { pool: updatedPool, result: AcquireFound entry.resource }
    Nothing ->
      let newResource = createResource width height
          currentSize = Array.length pool.entries
      in if currentSize < pool.config.maxSize
         then
           let newEntry =
                 { resource: newResource
                 , width: width
                 , height: height
                 , inUse: true
                 , lastUsed: now
                 }
               updatedPool = pool { entries = Array.snoc pool.entries newEntry }
           in { pool: updatedPool, result: AcquireCreated newResource }
         else
           { pool: pool, result: AcquirePoolFull newResource }

-- | Release a resource back to the pool
release :: forall a. Eq a => ResourcePool a -> a -> Int -> ResourcePool a
release pool resource now =
  pool { entries = map updateEntry pool.entries }
  where
    updateEntry entry
      | entry.resource == resource =
          entry { inUse = false, lastUsed = now }
      | otherwise = entry

-- | Remove old unused resources from the pool
cleanup :: forall a. ResourcePool a -> Int -> ResourcePool a
cleanup pool now =
  pool { entries = Array.filter keepEntry pool.entries }
  where
    keepEntry entry =
      entry.inUse || (now - entry.lastUsed) <= pool.config.maxAgeMs

-- | Clear all resources from the pool
clearPool :: forall a. ResourcePool a -> ResourcePool a
clearPool pool = pool { entries = [] }

-- | Get pool statistics
getStats :: forall a. ResourcePool a -> PoolStats
getStats pool =
  let entries = pool.entries
      inUseCount = Array.length (Array.filter _.inUse entries)
  in { total: Array.length entries
     , inUse: inUseCount
     , available: Array.length entries - inUseCount
     }
