-- |
-- Module      : Lattice.State.Audio.Beats
-- Description : Pure beat calculation functions for audio store
-- 
-- Migrated from ui/src/stores/audioStore.ts getBeats getter
-- Pure calculation function for extracting beat timestamps
-- No state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Audio.Beats
  ( -- Pure beat calculations
    getBeats
  ) where

import Data.Maybe (mapMaybe)
import Lattice.Services.AudioFeatures
  ( AudioAnalysis(..)
  , isBeatAtFrame
  )
import Lattice.State.Audio.Queries (activeAnalysis)
import Lattice.State.Audio.Types (AudioState(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                              // pure // beat // calculations
-- ════════════════════════════════════════════════════════════════════════════

-- | Get beat timestamps in seconds
-- Pure function: takes audio state, returns list of beat timestamps
-- Uses active analysis (stem or main) and calculates fps from frameCount/duration
-- Returns empty list if analysis not loaded or no beats found
-- Migrated from audioStore.ts getBeats getter (lines 136-152)
-- Uses explicit analysis value with defaults - no Maybe/Nothing
getBeats ::
  AudioState ->
  [Double]
getBeats state =
  if audioStateAudioAnalysisLoaded state
  then
    let analysis = activeAnalysis state
        -- Calculate fps from analysis data: fps = frameCount / duration
        -- This ensures we use the same fps that was used during analysis
        frameCountVal = fromIntegral (audioAnalysisFrameCount analysis)
        durationVal = audioAnalysisDuration analysis
        fps = if durationVal > 0 && frameCountVal > 0
          then frameCountVal / durationVal
          else 30.0  -- Default fps if calculation fails
        
        -- Check each frame for beats and convert to seconds
        checkFrame frame =
          if isBeatAtFrame (Just analysis) frame
          then Just (fromIntegral frame / fps)
          else Nothing
        
        -- Check all frames
        beats = mapMaybe checkFrame [0 .. audioAnalysisFrameCount analysis - 1]
    in beats
  else []  -- Explicit default: empty list if not loaded
