-- |
-- Module      : Lattice.State.Audio.Defaults
-- Description : Default values for audio state
-- 
-- Every value must have explicit defaults - no Maybe/Nothing
-- All values are deterministic with min/max bounds
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Audio.Defaults
  ( defaultAudioBuffer
  , defaultAudioAnalysis
  , defaultFrequencyBands
  , defaultAudioState
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import Lattice.Services.AudioFeatures
  ( AudioAnalysis(..)
  , FrequencyBands(..)
  )
import Lattice.State.Audio
  ( AudioBuffer(..)
  , AudioState(..)
  , LoadingState(..)
  , StemData(..)
  )

-- ============================================================================
-- DEFAULT VALUES
-- ============================================================================

-- | Default audio buffer (unloaded state)
-- Default: duration = 0.0 (min: 0.0, max: no upper bound)
defaultAudioBuffer :: AudioBuffer
defaultAudioBuffer = AudioBuffer
  { audioBufferDuration = 0.0  -- Default: not loaded
  }

-- | Default frequency bands (empty arrays)
defaultFrequencyBands :: FrequencyBands
defaultFrequencyBands = FrequencyBands
  { frequencyBandsSub = []
  , frequencyBandsBass = []
  , frequencyBandsLowMid = []
  , frequencyBandsMid = []
  , frequencyBandsHighMid = []
  , frequencyBandsHigh = []
  }

-- | Default audio analysis (unloaded state)
-- All fields have explicit defaults
defaultAudioAnalysis :: AudioAnalysis
defaultAudioAnalysis = AudioAnalysis
  { audioAnalysisSampleRate = 0.0  -- Default: not loaded (min: 0.0, max: 192000.0)
  , audioAnalysisDuration = 0.0  -- Default: not loaded (min: 0.0, max: no upper bound)
  , audioAnalysisFrameCount = 0  -- Default: not loaded (min: 0, max: no upper bound)
  , audioAnalysisBpm = 0.0  -- Default: not loaded (min: 0.0, max: 300.0)
  , audioAnalysisAmplitudeEnvelope = []  -- Default: empty array
  , audioAnalysisRmsEnergy = []  -- Default: empty array
  , audioAnalysisSpectralCentroid = []  -- Default: empty array
  , audioAnalysisFrequencyBands = defaultFrequencyBands  -- Default: empty bands
  , audioAnalysisOnsets = []  -- Default: empty array
  , audioAnalysisSpectralFlux = []  -- Default: empty array
  , audioAnalysisZeroCrossingRate = []  -- Default: empty array
  , audioAnalysisSpectralRolloff = []  -- Default: empty array
  , audioAnalysisSpectralFlatness = []  -- Default: empty array
  , audioAnalysisChromaFeatures = Nothing  -- TODO: Replace with default ChromaFeatures
  , audioAnalysisHarmonicEnergy = Nothing  -- TODO: Replace with default [Double]
  , audioAnalysisPercussiveEnergy = Nothing  -- TODO: Replace with default [Double]
  , audioAnalysisHpRatio = Nothing  -- TODO: Replace with default [Double]
  , audioAnalysisMfcc = Nothing  -- TODO: Replace with default [[Double]]
  , audioAnalysisMfccStats = Nothing  -- TODO: Replace with default MfccStats
  }

-- | Default audio state (unloaded, idle)
-- Every field has explicit default - no Maybe/Nothing
defaultAudioState :: AudioState
defaultAudioState = AudioState
  { audioStateAudioBuffer = defaultAudioBuffer  -- Default: duration = 0.0
  , audioStateAudioBufferLoaded = False  -- Explicit flag: buffer not loaded
  , audioStateAudioAnalysis = defaultAudioAnalysis  -- Default: all fields = 0/empty
  , audioStateAudioAnalysisLoaded = False  -- Explicit flag: analysis not loaded
  , audioStateLoadingState = LoadingStateIdle  -- Default: idle
  , audioStateLoadingProgress = 0.0  -- Default: 0.0 (min: 0.0, max: 1.0)
  , audioStateLoadingPhase = ""  -- Default: empty string
  , audioStateLoadingError = ""  -- Default: empty string (no error)
  , audioStateStemBuffers = HM.empty  -- Default: empty map
  , audioStateActiveStemName = ""  -- Default: empty string = use main audio
  , audioStateVolume = 100.0  -- Default: 100% (min: 0.0, max: 100.0)
  , audioStateMuted = False  -- Default: not muted
  , audioStateReactiveMappings = []  -- Default: empty list
  , audioStateLegacyMappings = HM.empty  -- Default: empty map
  }
