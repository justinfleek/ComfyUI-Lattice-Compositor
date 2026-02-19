-- |
-- Module      : Lattice.State.Depthflow
-- Description : Pure state management functions for depthflow store
-- 
-- Migrated from ui/src/stores/depthflowStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Depthflow
  ( -- Helper functions
    sanitizeNumber
  ) where

import Data.Aeson (Value(..))
import Lattice.Utils.NumericSafety (ensureFinite)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                       // helper // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Sanitize numeric config value, returning default if invalid
-- Pure function: takes value and default, returns sanitized number
-- Prevents NaN/Infinity corruption in layer data
sanitizeNumber :: Value -> Double -> Double
sanitizeNumber value defaultValue =
  case value of
    Number n ->
      let
        numValue = realToFrac n
      in
        ensureFinite numValue defaultValue
    _ -> defaultValue
