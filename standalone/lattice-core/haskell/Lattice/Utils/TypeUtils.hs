{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Utils.TypeUtils
Description : Type utility functions
Copyright   : (c) Lattice, 2026
License     : MIT

Reusable type-safe utility functions for object manipulation.

Source: lattice-core/lean/Lattice/Utils/TypeUtils.lean
-}

module Lattice.Utils.TypeUtils
  ( -- * Key Operations
    omitKeys
  , pickKeys
  , mergeKVs
  , getByKey
  , setByKey
  , hasKey
  , keys
  , values
  ) where

import Data.List (find)

-- ────────────────────────────────────────────────────────────────────────────
-- Key Operations
-- ────────────────────────────────────────────────────────────────────────────

-- | Type-safe key omission from a list of key-value pairs
-- Filters out specified keys
omitKeys :: Eq a => [(a, b)] -> [a] -> [(a, b)]
omitKeys kvs keysToOmit = filter (\(k, _) -> k `notElem` keysToOmit) kvs

-- | Pick only specified keys from a list of key-value pairs
pickKeys :: Eq a => [(a, b)] -> [a] -> [(a, b)]
pickKeys kvs keysToPick = filter (\(k, _) -> k `elem` keysToPick) kvs

-- | Merge two lists of key-value pairs (second overrides first)
mergeKVs :: Eq a => [(a, b)] -> [(a, b)] -> [(a, b)]
mergeKVs first second =
  let secondKeys = map fst second
      filteredFirst = filter (\(k, _) -> k `notElem` secondKeys) first
  in filteredFirst ++ second

-- | Get value by key from a list of key-value pairs
getByKey :: Eq a => [(a, b)] -> a -> Maybe b
getByKey kvs key = snd <$> find (\(k, _) -> k == key) kvs

-- | Set or update a key-value pair
setByKey :: Eq a => [(a, b)] -> a -> b -> [(a, b)]
setByKey kvs key value =
  let filtered = filter (\(k, _) -> k /= key) kvs
  in filtered ++ [(key, value)]

-- | Check if key exists in list
hasKey :: Eq a => [(a, b)] -> a -> Bool
hasKey kvs key = any (\(k, _) -> k == key) kvs

-- | Get all keys from a list of key-value pairs
keys :: [(a, b)] -> [a]
keys = map fst

-- | Get all values from a list of key-value pairs
values :: [(a, b)] -> [b]
values = map snd
