-- | Lattice.Utils.TypeUtils - Type utility functions
-- |
-- | Reusable type-safe utility functions for object manipulation.
-- |
-- | Source: lattice-core/lean/Lattice/Utils/TypeUtils.lean

module Lattice.Utils.TypeUtils
  ( omitKeys
  , pickKeys
  , mergeKVs
  , getByKey
  , setByKey
  , hasKey
  , keys
  , values
  ) where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)

-- ────────────────────────────────────────────────────────────────────────────
-- Key Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Type-safe key omission from a list of key-value pairs
-- | Filters out specified keys
omitKeys :: forall a b. Eq a => Array (Tuple a b) -> Array a -> Array (Tuple a b)
omitKeys kvs keysToOmit = Array.filter (\(Tuple k _) -> not (k `Array.elem` keysToOmit)) kvs

-- | Pick only specified keys from a list of key-value pairs
pickKeys :: forall a b. Eq a => Array (Tuple a b) -> Array a -> Array (Tuple a b)
pickKeys kvs keysToPick = Array.filter (\(Tuple k _) -> k `Array.elem` keysToPick) kvs

-- | Merge two lists of key-value pairs (second overrides first)
mergeKVs :: forall a b. Eq a => Array (Tuple a b) -> Array (Tuple a b) -> Array (Tuple a b)
mergeKVs first second =
  let secondKeys = map fst second
      filteredFirst = Array.filter (\(Tuple k _) -> not (k `Array.elem` secondKeys)) first
  in filteredFirst <> second

-- | Get value by key from a list of key-value pairs
getByKey :: forall a b. Eq a => Array (Tuple a b) -> a -> Maybe b
getByKey kvs key = snd <$> Array.find (\(Tuple k _) -> k == key) kvs

-- | Set or update a key-value pair
setByKey :: forall a b. Eq a => Array (Tuple a b) -> a -> b -> Array (Tuple a b)
setByKey kvs key value =
  let filtered = Array.filter (\(Tuple k _) -> k /= key) kvs
  in filtered <> [Tuple key value]

-- | Check if key exists in list
hasKey :: forall a b. Eq a => Array (Tuple a b) -> a -> Boolean
hasKey kvs key = Array.any (\(Tuple k _) -> k == key) kvs

-- | Get all keys from a list of key-value pairs
keys :: forall a b. Array (Tuple a b) -> Array a
keys = map fst

-- | Get all values from a list of key-value pairs
values :: forall a b. Array (Tuple a b) -> Array b
values = map snd
