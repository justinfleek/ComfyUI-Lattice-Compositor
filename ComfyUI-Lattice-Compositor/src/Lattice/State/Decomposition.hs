-- |
-- Module      : Lattice.State.Decomposition
-- Description : Pure state management functions for decomposition store
-- 
-- Migrated from ui/src/stores/decompositionStore.ts
-- Pure functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Decomposition
  ( -- Helper functions
    sortLayersByDepth
  ) where

import Data.List (sortBy)
import Data.Ord (comparing)
import Lattice.Utils.NumericSafety (ensureFiniteD)

-- ============================================================================
-- TYPES (Minimal types for pure sorting)
-- ============================================================================

-- | Decomposed layer with depth information
-- Minimal type sufficient for pure sorting function
data LayerWithDepth a = LayerWithDepth
  { layerWithDepthLayer :: a
  , layerWithDepthEstimatedDepth :: Double
  }
  deriving (Eq, Show)

-- ============================================================================
-- HELPER FUNCTIONS
-- ============================================================================

-- | Sort decomposed layers by depth (farthest first)
-- Pure function: takes list of layers with depths, returns sorted list
-- Sorts by estimatedDepth in descending order (depthB - depthA)
sortLayersByDepth :: [(a, Maybe Double)] -> [(a, Maybe Double)]
sortLayersByDepth layers =
  let withDepths = map (\(layer, mDepth) -> LayerWithDepth layer (maybe 0.0 (\d -> ensureFiniteD d 0.0) mDepth)) layers
      sorted = sortBy (flip (comparing layerWithDepthEstimatedDepth)) withDepths
  in map (\lwd -> (layerWithDepthLayer lwd, Just (layerWithDepthEstimatedDepth lwd))) sorted
