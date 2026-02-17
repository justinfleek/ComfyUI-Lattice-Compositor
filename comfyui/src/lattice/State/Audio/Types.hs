-- |
-- Module      : Lattice.State.Audio.Types
-- Description : Audio state types (breaks cycle between Audio and Audio.Stems)
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Audio.Types
  ( LoadingState(..)
  , AudioBuffer(..)
  , StemData(..)
  , AudioState(..)
  , defaultAudioBuffer
  , defaultAudioAnalysis
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Aeson.Types ((.!=))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Services.AudioFeatures
  ( AudioAnalysis(..)
  , FrequencyBands(..)
  )
import Lattice.Services.PropertyEvaluator (AudioMapping(..))
import Lattice.Types.LayerDataParticles (AudioParticleMapping(..))

-- ============================================================================
-- TYPES
-- ============================================================================

data LoadingState
  = LoadingStateIdle
  | LoadingStateDecoding
  | LoadingStateAnalyzing
  | LoadingStateComplete
  | LoadingStateError
  deriving (Eq, Show, Generic)

instance ToJSON LoadingState where
  toJSON LoadingStateIdle = "idle"
  toJSON LoadingStateDecoding = "decoding"
  toJSON LoadingStateAnalyzing = "analyzing"
  toJSON LoadingStateComplete = "complete"
  toJSON LoadingStateError = "error"

instance FromJSON LoadingState where
  parseJSON = withText "LoadingState" $ \s ->
    case s of
      "idle" -> return LoadingStateIdle
      "decoding" -> return LoadingStateDecoding
      "analyzing" -> return LoadingStateAnalyzing
      "complete" -> return LoadingStateComplete
      "error" -> return LoadingStateError
      _ -> fail "Invalid LoadingState"

data AudioBuffer = AudioBuffer
  { audioBufferDuration :: Double
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioBuffer where
  toJSON (AudioBuffer dur) = object ["duration" .= dur]

instance FromJSON AudioBuffer where
  parseJSON = withObject "AudioBuffer" $ \o -> AudioBuffer <$> o .: "duration"

defaultAudioBuffer :: AudioBuffer
defaultAudioBuffer = AudioBuffer {audioBufferDuration = 0.0}

defaultAudioAnalysis :: AudioAnalysis
defaultAudioAnalysis = AudioAnalysis
  { audioAnalysisSampleRate = 0.0
  , audioAnalysisDuration = 0.0
  , audioAnalysisFrameCount = 0
  , audioAnalysisBpm = 0.0
  , audioAnalysisAmplitudeEnvelope = []
  , audioAnalysisRmsEnergy = []
  , audioAnalysisSpectralCentroid = []
  , audioAnalysisFrequencyBands = FrequencyBands [] [] [] [] [] []
  , audioAnalysisOnsets = []
  , audioAnalysisSpectralFlux = []
  , audioAnalysisZeroCrossingRate = []
  , audioAnalysisSpectralRolloff = []
  , audioAnalysisSpectralFlatness = []
  , audioAnalysisChromaFeatures = Nothing
  , audioAnalysisHarmonicEnergy = Nothing
  , audioAnalysisPercussiveEnergy = Nothing
  , audioAnalysisHpRatio = Nothing
  , audioAnalysisMfcc = Nothing
  , audioAnalysisMfccStats = Nothing
  }

data StemData = StemData
  { stemDataAnalysis :: AudioAnalysis
  , stemDataBuffer :: AudioBuffer
  }
  deriving (Eq, Show, Generic)

instance ToJSON StemData where
  toJSON (StemData analysis buffer) =
    object ["analysis" .= analysis, "buffer" .= buffer]

instance FromJSON StemData where
  parseJSON = withObject "StemData" $ \o ->
    StemData <$> o .: "analysis" <*> o .: "buffer"

data AudioState = AudioState
  { audioStateAudioBuffer :: AudioBuffer
  , audioStateAudioBufferLoaded :: Bool
  , audioStateAudioAnalysis :: AudioAnalysis
  , audioStateAudioAnalysisLoaded :: Bool
  , audioStateLoadingState :: LoadingState
  , audioStateLoadingProgress :: Double
  , audioStateLoadingPhase :: Text
  , audioStateLoadingError :: Text
  , audioStateStemBuffers :: HashMap Text StemData
  , audioStateActiveStemName :: Text
  , audioStateVolume :: Double
  , audioStateMuted :: Bool
  , audioStateReactiveMappings :: [AudioMapping]
  , audioStateLegacyMappings :: HashMap Text [AudioParticleMapping]
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioState where
  toJSON (AudioState buf bufLoaded analysis analysisLoaded loading progress phase err stems activeStem volume muted reactiveMappings legacyMappings) =
    let baseFields = ["audioBufferLoaded" .= bufLoaded, "audioAnalysisLoaded" .= analysisLoaded, "loadingState" .= loading, "loadingProgress" .= progress, "loadingPhase" .= phase, "stemBuffers" .= stems, "volume" .= volume, "muted" .= muted, "reactiveMappings" .= reactiveMappings, "legacyMappings" .= legacyMappings]
        withBuf = if bufLoaded then ("audioBuffer" .= buf) : baseFields else baseFields
        withAnalysis = if analysisLoaded then ("audioAnalysis" .= analysis) : withBuf else withBuf
        withError = if T.null err then withAnalysis else ("loadingError" .= err) : withAnalysis
        withActiveStem = if T.null activeStem then withError else ("activeStemName" .= activeStem) : withError
    in object withActiveStem

instance FromJSON AudioState where
  parseJSON = withObject "AudioState" $ \o ->
    AudioState
      <$> o .:? "audioBuffer" .!= defaultAudioBuffer
      <*> o .:? "audioBufferLoaded" .!= False
      <*> o .:? "audioAnalysis" .!= defaultAudioAnalysis
      <*> o .:? "audioAnalysisLoaded" .!= False
      <*> o .:? "loadingState" .!= LoadingStateIdle
      <*> o .:? "loadingProgress" .!= 0.0
      <*> o .:? "loadingPhase" .!= ""
      <*> o .:? "loadingError" .!= ""
      <*> o .:? "stemBuffers" .!= HM.empty
      <*> o .:? "activeStemName" .!= ""
      <*> o .:? "volume" .!= 100.0
      <*> o .:? "muted" .!= False
      <*> o .:? "reactiveMappings" .!= []
      <*> o .:? "legacyMappings" .!= HM.empty
