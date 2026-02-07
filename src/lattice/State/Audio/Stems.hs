-- |
-- Module      : Lattice.State.Audio.Stems
-- Description : Pure stem query functions for audio store
-- 
-- Migrated from ui/src/stores/audioStore.ts
-- Pure query functions for audio stem operations
-- No state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Audio.Stems
  ( -- Pure stem queries
    getStemAnalysis
  , getStemBuffer
  , hasStem
  , getStemInfo
  , StemInfo(..)
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import GHC.Generics (Generic)
import Lattice.Services.AudioFeatures (AudioAnalysis(..))
import Lattice.State.Audio.Types (AudioState(..), AudioBuffer(..), StemData(..))

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Stem information (name, duration, BPM)
data StemInfo = StemInfo
  { stemInfoName :: Text
  , stemInfoDuration :: Double
  , stemInfoBpm :: Double
  }
  deriving (Eq, Show, Generic)

-- ============================================================================
-- PURE STEM QUERIES
-- ============================================================================

-- | Get stem analysis by name
-- Pure function: takes audio state, stem name, returns analysis (with defaults if not found)
-- Returns default analysis if stem not found (explicit default, no Maybe/Nothing)
getStemAnalysis ::
  AudioState ->
  Text ->
  AudioAnalysis
getStemAnalysis state stemName =
  case HM.lookup stemName (audioStateStemBuffers state) of
    Just stemData -> stemDataAnalysis stemData
    Nothing -> audioStateAudioAnalysis state  -- Explicit default: use main analysis

-- | Get stem buffer by name
-- Pure function: takes audio state, stem name, returns buffer (with defaults if not found)
-- Returns default buffer if stem not found (explicit default, no Maybe/Nothing)
getStemBuffer ::
  AudioState ->
  Text ->
  AudioBuffer
getStemBuffer state stemName =
  case HM.lookup stemName (audioStateStemBuffers state) of
    Just stemData -> stemDataBuffer stemData
    Nothing -> audioStateAudioBuffer state  -- Explicit default: use main buffer

-- | Check if a stem is loaded
-- Pure function: takes audio state, stem name, returns boolean
hasStem ::
  AudioState ->
  Text ->
  Bool
hasStem state stemName = HM.member stemName (audioStateStemBuffers state)

-- | Get all stem names and their durations/BPM
-- Pure function: takes audio state, returns list of stem info
getStemInfo ::
  AudioState ->
  [StemInfo]
getStemInfo state =
  let stemEntries = HM.toList (audioStateStemBuffers state)
      createStemInfo (name, stemData) =
        StemInfo
          { stemInfoName = name
          , stemInfoDuration = audioBufferDuration (stemDataBuffer stemData)
          , stemInfoBpm = audioAnalysisBpm (stemDataAnalysis stemData)
          }
  in map createStemInfo stemEntries
