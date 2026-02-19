{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Utils.ResourcePool
Description : Generic resource pooling
Copyright   : (c) Lattice, 2026
License     : MIT

Abstract resource pool that can be used for any pooled resource type.
The TypeScript version uses HTMLCanvasElement; this version is generic.

Source: lattice-core/lean/Lattice/Utils/ResourcePool.lean
-}

module Lattice.Utils.ResourcePool
  ( -- * Types
    PoolConfig(..)
  , defaultPoolConfig
  , PoolEntry(..)
  , ResourcePool(..)
  , AcquireResult(..)
  , PoolStats(..)
    -- * Pool Operations
  , emptyPool
  , poolWithConfig
  , findAvailable
  , acquire
  , release
  , cleanup
  , clearPool
  , getStats
  ) where

import GHC.Generics (Generic)
import Data.List (find)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Configuration for pool behavior
data PoolConfig = PoolConfig
  { poolMaxSize  :: !Int   -- ^ Maximum pooled resources (default: 20)
  , poolMaxAgeMs :: !Int   -- ^ TTL for unused resources in ms (default: 60000)
  }
  deriving stock (Eq, Show, Generic)

-- | Default pool configuration
defaultPoolConfig :: PoolConfig
defaultPoolConfig = PoolConfig
  { poolMaxSize = 20
  , poolMaxAgeMs = 60000
  }

-- | A pooled resource entry
data PoolEntry a = PoolEntry
  { entryResource :: a
  , entryWidth    :: !Int
  , entryHeight   :: !Int
  , entryInUse    :: !Bool
  , entryLastUsed :: !Int  -- ^ Timestamp in milliseconds
  }
  deriving stock (Eq, Show, Generic)

-- | Resource pool state
data ResourcePool a = ResourcePool
  { poolEntries :: [PoolEntry a]
  , poolConfig  :: PoolConfig
  }
  deriving stock (Eq, Show, Generic)

-- | Result of acquiring a resource
data AcquireResult a
  = AcquireFound a        -- ^ Reused from pool
  | AcquireCreated a      -- ^ Newly created and added to pool
  | AcquirePoolFull a     -- ^ Created but pool at capacity
  deriving stock (Eq, Show, Generic)

-- | Pool statistics
data PoolStats = PoolStats
  { statsTotal     :: !Int
  , statsInUse     :: !Int
  , statsAvailable :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Pool Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Create an empty pool with default config
emptyPool :: ResourcePool a
emptyPool = ResourcePool
  { poolEntries = []
  , poolConfig = defaultPoolConfig
  }

-- | Create an empty pool with custom config
poolWithConfig :: PoolConfig -> ResourcePool a
poolWithConfig config = ResourcePool
  { poolEntries = []
  , poolConfig = config
  }

-- | Find a matching unused entry in the pool
findAvailable :: Eq a => ResourcePool a -> Int -> Int -> Maybe (PoolEntry a)
findAvailable pool width height =
  find matchEntry (poolEntries pool)
  where
    matchEntry entry =
      not (entryInUse entry) &&
      entryWidth entry == width &&
      entryHeight entry == height

-- | Mark an entry as in use
markInUse :: Eq a => ResourcePool a -> a -> Int -> ResourcePool a
markInUse pool resource now =
  pool { poolEntries = map updateEntry (poolEntries pool) }
  where
    updateEntry entry
      | entryResource entry == resource =
          entry { entryInUse = True, entryLastUsed = now }
      | otherwise = entry

-- | Acquire a resource from the pool
--
-- Returns (updated pool, acquire result).
-- The caller must provide a function to create new resources.
acquire :: Eq a
        => ResourcePool a
        -> Int              -- ^ Width
        -> Int              -- ^ Height
        -> Int              -- ^ Current timestamp
        -> (Int -> Int -> a) -- ^ Resource creator
        -> (ResourcePool a, AcquireResult a)
acquire pool width height now createResource =
  case findAvailable pool width height of
    Just entry ->
      let updatedPool = markInUse pool (entryResource entry) now
      in (updatedPool, AcquireFound (entryResource entry))
    Nothing ->
      let newResource = createResource width height
          currentSize = length (poolEntries pool)
          maxSize = poolMaxSize (poolConfig pool)
      in if currentSize < maxSize
         then
           let newEntry = PoolEntry
                 { entryResource = newResource
                 , entryWidth = width
                 , entryHeight = height
                 , entryInUse = True
                 , entryLastUsed = now
                 }
               updatedPool = pool { poolEntries = poolEntries pool ++ [newEntry] }
           in (updatedPool, AcquireCreated newResource)
         else
           (pool, AcquirePoolFull newResource)

-- | Release a resource back to the pool
release :: Eq a => ResourcePool a -> a -> Int -> ResourcePool a
release pool resource now =
  pool { poolEntries = map updateEntry (poolEntries pool) }
  where
    updateEntry entry
      | entryResource entry == resource =
          entry { entryInUse = False, entryLastUsed = now }
      | otherwise = entry

-- | Remove old unused resources from the pool
cleanup :: ResourcePool a -> Int -> ResourcePool a
cleanup pool now =
  pool { poolEntries = filter keepEntry (poolEntries pool) }
  where
    maxAge = poolMaxAgeMs (poolConfig pool)
    keepEntry entry =
      entryInUse entry || (now - entryLastUsed entry) <= maxAge

-- | Clear all resources from the pool
clearPool :: ResourcePool a -> ResourcePool a
clearPool pool = pool { poolEntries = [] }

-- | Get pool statistics
getStats :: ResourcePool a -> PoolStats
getStats pool =
  let entries = poolEntries pool
      inUseCount = length (filter entryInUse entries)
  in PoolStats
    { statsTotal = length entries
    , statsInUse = inUseCount
    , statsAvailable = length entries - inUseCount
    }
