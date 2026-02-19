-- |
-- Module      : Lattice.State.Layer.Toggle
-- Description : Toggle operations for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for toggling layer properties (lock, visibility, isolate)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Toggle
  ( toggleLayerLock
  , toggleLayerVisibility
  , toggleLayerIsolate
  ) where

import Data.Text (Text)
import Lattice.Types.Layer (Layer(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // toggle // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Toggle locked state for specified layers
-- Pure function: takes list of layer IDs and layers list, returns new layers list with toggled locked state
toggleLayerLock :: [Text] -> [Layer] -> [Layer]
toggleLayerLock layerIds layers =
  map (\layer ->
    if layerId layer `elem` layerIds
      then layer {layerLocked = not (layerLocked layer)}
      else layer
  ) layers

-- | Toggle visibility for specified layers
-- Pure function: takes list of layer IDs and layers list, returns new layers list with toggled visibility
toggleLayerVisibility :: [Text] -> [Layer] -> [Layer]
toggleLayerVisibility layerIds layers =
  map (\layer ->
    if layerId layer `elem` layerIds
      then layer {layerVisible = not (layerVisible layer)}
      else layer
  ) layers

-- | Toggle isolate (solo) state for specified layers
-- Pure function: takes list of layer IDs and layers list, returns new layers list with toggled isolate state
toggleLayerIsolate :: [Text] -> [Layer] -> [Layer]
toggleLayerIsolate layerIds layers =
  map (\layer ->
    if layerId layer `elem` layerIds
      then layer {layerIsolate = not (layerIsolate layer)}
      else layer
  ) layers
