-- |
-- Module      : Lattice.State.Layer.Ordering
-- Description : Layer ordering operations
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for reordering layers in the timeline
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Ordering
  ( bringToFront
  , sendToBack
  , bringForward
  , sendBackward
  ) where

import Data.List (findIndex, sort, splitAt, partition, foldl)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import Lattice.Types.Layer (Layer(..))

-- ============================================================================
-- ORDERING OPERATIONS
-- ============================================================================

-- | Move specified layers to the front (index 0)
-- Pure function: takes list of layer IDs and layers list, returns reordered layers
bringToFront :: [Text] -> [Layer] -> [Layer]
bringToFront layerIds layers =
  let
    (targetLayers, otherLayers) = partition (\l -> layerId l `elem` layerIds) layers
  in
    targetLayers ++ otherLayers

-- | Move specified layers to the back (end of list)
-- Pure function: takes list of layer IDs and layers list, returns reordered layers
sendToBack :: [Text] -> [Layer] -> [Layer]
sendToBack layerIds layers =
  let
    (targetLayers, otherLayers) = partition (\l -> layerId l `elem` layerIds) layers
  in
    otherLayers ++ targetLayers

-- | Move specified layers forward one position (toward index 0)
-- Pure function: takes list of layer IDs and layers list, returns reordered layers list
bringForward :: [Text] -> [Layer] -> [Layer]
bringForward layerIds layers =
  let
    -- Find indices of target layers
    targetIndices = mapMaybe (\lid -> findIndex (\l -> layerId l == lid) layers) layerIds
    
    -- Sort indices in descending order to process from back to front
    sortedIndices = reverse (sort targetIndices)
    
    -- Move each layer forward one position
    moveForwardOne idx ls =
      if idx > 0
        then
          let
            (before, rest) = splitAt (idx - 1) ls
            (layerToMove, after) = splitAt 1 rest
            (layerBefore, beforeRest) = splitAt 1 before
          in
            beforeRest ++ layerToMove ++ layerBefore ++ after
        else ls
  in
    foldl (\ls idx -> moveForwardOne idx ls) layers sortedIndices

-- | Move specified layers backward one position (toward end of list)
-- Pure function: takes list of layer IDs and layers list, returns reordered layers list
sendBackward :: [Text] -> [Layer] -> [Layer]
sendBackward layerIds layers =
  let
    -- Find indices of target layers
    targetIndices = mapMaybe (\lid -> findIndex (\l -> layerId l == lid) layers) layerIds
    
    -- Sort indices in ascending order to process from front to back
    sortedIndices = sort targetIndices
    
    -- Move each layer backward one position
    moveBackwardOne idx ls =
      if idx < length ls - 1
        then
          let
            (before, rest) = splitAt idx ls
            (layerToMove, after) = splitAt 1 rest
            (layerAfter, afterRest) = splitAt 1 after
          in
            before ++ layerAfter ++ layerToMove ++ afterRest
        else ls
  in
    foldl (\ls idx -> moveBackwardOne idx ls) layers sortedIndices
