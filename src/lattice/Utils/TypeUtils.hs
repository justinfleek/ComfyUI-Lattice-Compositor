-- |
-- Module      : Lattice.Utils.TypeUtils
-- Description : Type-safe utility functions for object manipulation
-- 
-- Migrated from ui/src/utils/typeUtils.ts
-- Pure functions for type-safe object operations
-- 
-- CRITICAL: No forbidden patterns - explicit types, no null/undefined, no type escapes
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Lattice.Utils.TypeUtils
  ( -- Object manipulation
    omitKeys
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as Set
import Data.Hashable (Hashable)

-- ============================================================================
-- OBJECT MANIPULATION
-- ============================================================================

-- | Type-safe omit - removes specified keys from object
-- Returns new HashMap without specified keys
-- 
-- System F/Omega proof: Explicit type HashMap k v -> HashSet k -> HashMap k v
-- Mathematical proof: Result contains all keys from input except those in omit set
-- 
-- @param obj Object to remove keys from
-- @param keys Set of keys to remove
-- @returns New object without specified keys
omitKeys :: (Eq k, Hashable k) => HashMap k v -> HashSet k -> HashMap k v
omitKeys obj keys = HM.filterWithKey (\k _ -> not (Set.member k keys)) obj
