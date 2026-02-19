-- |
-- Module      : Lattice.State.Audio
-- Description : Pure state management functions for audio store
-- 
-- Migrated from ui/src/stores/audioStore.ts
-- Pure query and calculation functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Audio
  ( -- Pure queries (getters)
    isLoaded
  , isLoading
  , hasError
  , duration
  , bpm
  , frameCount
  , hasAudioBuffer
  , getBPM
  , availableStems
  , hasStems
  , getActiveStemName
  , activeAnalysis
  , activeBuffer
  -- Pure feature queries
  , getFeatureAtFrame
  , isBeatAtFrame
  -- Types (re-exported from Types)
  , AudioState(..)
  , LoadingState(..)
  , StemData(..)
  -- Re-export AudioAnalysis and FrequencyBands from AudioFeatures
  , module Lattice.Services.AudioFeatures
  -- Re-export mapping, stem, and beat modules
  , module Lattice.State.Audio.Mappings
  , module Lattice.State.Audio.Stems
  , module Lattice.State.Audio.Beats
  , module Lattice.State.Audio.Types
  , module Lattice.State.Audio.Queries
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import qualified Lattice.Services.AudioFeatures as AudioFeatures
import Lattice.Services.AudioFeatures
  ( AudioAnalysis(..)
  , AudioFeatureType(..)
  , FrequencyBands(..)
  )
import Lattice.State.Audio.Beats
import Lattice.State.Audio.Mappings
import Lattice.State.Audio.Queries (activeAnalysis)
import Lattice.State.Audio.Stems
import Lattice.State.Audio.Types
  ( AudioState(..)
  , AudioBuffer(..)
  , LoadingState(..)
  , StemData(..)
  )
import Lattice.Utils.NumericSafety (ensureFiniteD)

-- ============================================================================
-- PURE QUERIES (GETTERS)
-- ============================================================================

-- | Check if audio is loaded
-- Pure function: takes audio state, returns boolean
-- Uses explicit loaded flag - no Maybe/Nothing
isLoaded ::
  AudioState ->
  Bool
isLoaded state = audioStateAudioAnalysisLoaded state

-- | Check if audio is loading
-- Pure function: takes audio state, returns boolean
isLoading ::
  AudioState ->
  Bool
isLoading state =
  case audioStateLoadingState state of
    LoadingStateDecoding -> True
    LoadingStateAnalyzing -> True
    _ -> False

-- | Check if there's an error
-- Pure function: takes audio state, returns boolean
hasError ::
  AudioState ->
  Bool
hasError state =
  case audioStateLoadingState state of
    LoadingStateError -> True
    _ -> False

-- | Get audio duration (from audioBuffer)
-- Pure function: takes audio state, returns duration
-- Uses explicit buffer value with default - no Maybe/Nothing
duration ::
  AudioState ->
  Double
duration state =
  if audioStateAudioBufferLoaded state
  then
    let dur = audioBufferDuration (audioStateAudioBuffer state)
        finiteDur = ensureFiniteD dur 0.0
    in if finiteDur >= 0 then finiteDur else 0.0
  else 0.0

-- | Get BPM (from audioAnalysis)
-- Pure function: takes audio state, returns BPM
-- Uses explicit analysis value with default - no Maybe/Nothing
bpm ::
  AudioState ->
  Double
bpm state =
  if audioStateAudioAnalysisLoaded state
  then
    let bpmVal = audioAnalysisBpm (audioStateAudioAnalysis state)
        finiteBpm = ensureFiniteD bpmVal 0.0
    in if finiteBpm > 0 then finiteBpm else 0.0
  else 0.0

-- | Get frame count (from audioAnalysis)
-- Pure function: takes audio state, returns frame count
-- Uses explicit analysis value with default - no Maybe/Nothing
frameCount ::
  AudioState ->
  Int
frameCount state =
  if audioStateAudioAnalysisLoaded state
  then
    let fc = audioAnalysisFrameCount (audioStateAudioAnalysis state)
    in if fc >= 0 then fc else 0
  else 0

-- | Check if audio buffer is loaded
-- Pure function: takes audio state, returns boolean
-- Uses explicit loaded flag - no Maybe/Nothing
hasAudioBuffer ::
  AudioState ->
  Bool
hasAudioBuffer state = audioStateAudioBufferLoaded state

-- | Get BPM (from audioAnalysis, returns 0.0 if not loaded)
-- Pure function: takes audio state, returns BPM (default: 0.0)
-- Uses explicit analysis value with default - no Maybe/Nothing
getBPM ::
  AudioState ->
  Double
getBPM state = bpm state  -- Same as bpm getter - returns 0.0 if not loaded

-- | Get available stem names
-- Pure function: takes audio state, returns list of stem names
availableStems ::
  AudioState ->
  [Text]
availableStems state = HM.keys (audioStateStemBuffers state)

-- | Check if any stems are loaded
-- Pure function: takes audio state, returns boolean
hasStems ::
  AudioState ->
  Bool
hasStems state = not (HM.null (audioStateStemBuffers state))

-- | Get active stem name
-- Pure function: takes audio state, returns stem name (default: "" = use main audio)
-- Uses explicit text value with default - no Maybe/Nothing
getActiveStemName ::
  AudioState ->
  Text
getActiveStemName state = audioStateActiveStemName state

-- | Get active buffer (stem or main)
-- Note: This is simplified - actual implementation would need full AudioBuffer
-- For pure queries, we only need duration, which is already handled by duration()
-- Pure function: takes audio state, returns buffer (with defaults if not loaded)
-- Uses explicit values with defaults - no Maybe/Nothing
activeBuffer ::
  AudioState ->
  AudioBuffer
activeBuffer state =
  if not (T.null (audioStateActiveStemName state))
  then
    -- For stems, we'd need to store buffers separately
    -- For now, return main buffer (stems use same buffer structure)
    audioStateAudioBuffer state
  else audioStateAudioBuffer state

-- ============================================================================
-- PURE FEATURE QUERIES
-- ============================================================================

-- | Get audio feature value at frame (wrapper for AudioFeatures service)
-- Pure function: takes audio state, feature name, frame, returns feature value
-- Uses active analysis (stem or main) - returns 0.0 if not loaded
-- AudioAnalysis type is from AudioFeatures service for compatibility
-- Uses explicit analysis value with defaults - no Maybe/Nothing
getFeatureAtFrame ::
  AudioState ->
  AudioFeatureType ->
  Int ->
  Double
getFeatureAtFrame state feature frame =
  if audioStateAudioAnalysisLoaded state
  then AudioFeatures.getFeatureAtFrame (Just (activeAnalysis state)) feature frame
  else 0.0

-- | Check if frame is on a beat
-- Pure function: takes audio state, frame, returns boolean
-- Uses active analysis (stem or main) - returns False if not loaded
-- AudioAnalysis type is from AudioFeatures service for compatibility
-- Uses explicit analysis value with defaults - no Maybe/Nothing
isBeatAtFrame ::
  AudioState ->
  Int ->
  Bool
isBeatAtFrame state frame =
  if audioStateAudioAnalysisLoaded state
  then AudioFeatures.isBeatAtFrame (Just (activeAnalysis state)) frame
  else False
