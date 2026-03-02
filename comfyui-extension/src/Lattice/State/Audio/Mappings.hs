-- |
-- Module      : Lattice.State.Audio.Mappings
-- Description : Pure mapping query functions for audio store
-- 
-- Migrated from ui/src/stores/audioStore.ts
-- Pure query functions for audio reactive mappings and legacy mappings
-- No state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Audio.Mappings
  ( -- Pure mapping queries
    getMappings
  , getActiveMappingsForLayer
  , getLegacyMappings
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.List (filter)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Services.PropertyEvaluator (AudioMapping(..))
import Lattice.State.Audio.Types (AudioState(..))
import Lattice.Types.LayerDataParticles (AudioParticleMapping(..))

-- ============================================================================
-- PURE MAPPING QUERIES
-- ============================================================================

-- | Get all audio reactive mappings
-- Pure function: takes audio state, returns all mappings
getMappings ::
  AudioState ->
  [AudioMapping]
getMappings state = audioStateReactiveMappings state

-- | Get active mappings for a specific layer
-- Pure function: takes audio state, layer ID, returns filtered mappings
-- Filters by enabled state and targetLayerId (or empty string for global mappings)
-- Uses explicit Text values with defaults - no Maybe/Nothing
getActiveMappingsForLayer ::
  AudioState ->
  Text ->
  [AudioMapping]
getActiveMappingsForLayer state layerId =
  filter (\m ->
    mappingEnabled m &&
    (mappingTargetLayerId m == Just layerId || mappingTargetLayerId m == Nothing || mappingTargetLayerId m == Just (T.pack ""))
  ) (audioStateReactiveMappings state)

-- | Get legacy audio-particle mappings for a layer
-- Pure function: takes audio state, layer ID, returns legacy mappings
-- Returns empty list if no mappings found (explicit default, no Maybe/Nothing)
getLegacyMappings ::
  AudioState ->
  Text ->
  [AudioParticleMapping]
getLegacyMappings state layerId =
  case HM.lookup layerId (audioStateLegacyMappings state) of
    Just mappings -> mappings
    Nothing -> []  -- Explicit default: empty list
