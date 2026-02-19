-- |
-- Module      : Lattice.Services.AudioFeatures
-- Description : Pure audio feature lookup functions
-- 
-- Migrated from ui/src/services/audioFeatures.ts
-- Pure lookup functions for deterministic audio-reactive evaluation
-- These functions are PURE: same inputs → same outputs
-- Analysis data is computed once at load time, then only read
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.AudioFeatures
  ( -- Types
    AudioAnalysis(..)
  , FrequencyBands(..)
  , ChromaFeatures(..)
  , MfccStats(..)
  , AudioFeatureType(..)
  , CurveType(..)
  -- Pure lookup functions
  , getFeatureAtFrame
  , isBeatAtFrame
  , isPeakAtFrame
  -- Pure calculation functions
  , getBPM
  , getSmoothedFeature
  , normalizeFeature
  , applyFeatureCurve
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.List (sortBy)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Utils.NumericSafety (isFinite)
import Lattice.Utils.ArrayUtils (safeArrayGet)
import Lattice.Utils.NumericSafety
  ( clamp01
  , safeLerp
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Audio analysis data structure
-- Analysis is computed once at load time, then only read
data AudioAnalysis = AudioAnalysis
  { audioAnalysisSampleRate :: Double
  , audioAnalysisDuration :: Double
  , audioAnalysisFrameCount :: Int
  , audioAnalysisAmplitudeEnvelope :: [Double]
  , audioAnalysisRmsEnergy :: [Double]
  , audioAnalysisSpectralCentroid :: [Double]
  , audioAnalysisFrequencyBands :: FrequencyBands
  , audioAnalysisOnsets :: [Double]
  , audioAnalysisBpm :: Double
  , audioAnalysisSpectralFlux :: [Double]
  , audioAnalysisZeroCrossingRate :: [Double]
  , audioAnalysisSpectralRolloff :: [Double]
  , audioAnalysisSpectralFlatness :: [Double]
  , audioAnalysisChromaFeatures :: Maybe ChromaFeatures
  , audioAnalysisHarmonicEnergy :: Maybe [Double]
  , audioAnalysisPercussiveEnergy :: Maybe [Double]
  , audioAnalysisHpRatio :: Maybe [Double]
  , audioAnalysisMfcc :: Maybe [[Double]]
  , audioAnalysisMfccStats :: Maybe MfccStats
  } deriving (Eq, Show, Generic)

instance ToJSON AudioAnalysis
instance FromJSON AudioAnalysis

-- | Frequency bands structure
data FrequencyBands = FrequencyBands
  { frequencyBandsSub :: [Double]
  , frequencyBandsBass :: [Double]
  , frequencyBandsLowMid :: [Double]
  , frequencyBandsMid :: [Double]
  , frequencyBandsHighMid :: [Double]
  , frequencyBandsHigh :: [Double]
  } deriving (Eq, Show, Generic)

instance ToJSON FrequencyBands
instance FromJSON FrequencyBands

-- | Chroma features for key/chord detection
data ChromaFeatures = ChromaFeatures
  { chromaFeaturesChroma :: [[Double]]  -- [frameIndex][pitchClass] 12 values per frame
  , chromaFeaturesChromaEnergy :: [Double]
  , chromaFeaturesEstimatedKey :: Text
  , chromaFeaturesKeyConfidence :: Double
  } deriving (Eq, Show, Generic)

instance ToJSON ChromaFeatures
instance FromJSON ChromaFeatures

-- | MFCC statistics for normalization
data MfccStats = MfccStats
  { mfccStatsMin :: [Double]  -- Min value per coefficient [13]
  , mfccStatsMax :: [Double]  -- Max value per coefficient [13]
  } deriving (Eq, Show, Generic)

instance ToJSON MfccStats
instance FromJSON MfccStats

-- | Audio feature types
data AudioFeatureType
  = FeatureAmplitude
  | FeatureRms
  | FeatureSpectralCentroid
  | FeatureSub
  | FeatureBass
  | FeatureLowMid
  | FeatureMid
  | FeatureHighMid
  | FeatureHigh
  | FeatureOnsets
  | FeaturePeaks
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                               // pure // lookup // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Get audio feature value at a specific frame
-- Pure function: same inputs → same outputs
-- Analysis data is read-only (computed once at load time)
-- Returns 0 for missing or invalid analysis data
getFeatureAtFrame :: Maybe AudioAnalysis -> AudioFeatureType -> Int -> Double
getFeatureAtFrame Nothing _ _ = 0.0
getFeatureAtFrame (Just analysis) feature frame
  | frame < 0 || frame >= audioAnalysisFrameCount analysis = 0.0
  | otherwise =
      let clampedFrame = frame
          getArrayValue arr idx =
            let val = safeArrayGet arr idx 0.0
            in if isFinite val && val >= 0 then val else 0.0
      in case feature of
    FeatureAmplitude -> getArrayValue (audioAnalysisAmplitudeEnvelope analysis) clampedFrame
    FeatureRms -> getArrayValue (audioAnalysisRmsEnergy analysis) clampedFrame
    FeatureSpectralCentroid -> getArrayValue (audioAnalysisSpectralCentroid analysis) clampedFrame
    FeatureSub -> getArrayValue (frequencyBandsSub (audioAnalysisFrequencyBands analysis)) clampedFrame
    FeatureBass -> getArrayValue (frequencyBandsBass (audioAnalysisFrequencyBands analysis)) clampedFrame
    FeatureLowMid -> getArrayValue (frequencyBandsLowMid (audioAnalysisFrequencyBands analysis)) clampedFrame
    FeatureMid -> getArrayValue (frequencyBandsMid (audioAnalysisFrequencyBands analysis)) clampedFrame
    FeatureHighMid -> getArrayValue (frequencyBandsHighMid (audioAnalysisFrequencyBands analysis)) clampedFrame
    FeatureHigh -> getArrayValue (frequencyBandsHigh (audioAnalysisFrequencyBands analysis)) clampedFrame
    FeatureOnsets ->
      let onsets = audioAnalysisOnsets analysis
          onsetVal = safeArrayGet onsets clampedFrame 0
      in if onsetVal > 0 then 1.0 else 0.0
    FeaturePeaks -> 0.0  -- Peaks require separate PeakData structure

-- | Check if a frame is a beat
-- Pure function: same inputs → same outputs
isBeatAtFrame :: Maybe AudioAnalysis -> Int -> Bool
isBeatAtFrame Nothing _ = False
isBeatAtFrame (Just analysis) frame =
  let clampedFrame = max 0 (min frame (audioAnalysisFrameCount analysis - 1))
      onsets = audioAnalysisOnsets analysis
      onsetVal = safeArrayGet onsets clampedFrame 0
  in onsetVal > 0

-- | Check if a frame is a peak
-- Pure function: same inputs → same outputs
-- Requires PeakData structure (to be migrated separately)
isPeakAtFrame :: [Int] -> Int -> Bool  -- Simplified: peaks as list of frame indices
isPeakAtFrame peaks frame = frame `elem` peaks

-- ════════════════════════════════════════════════════════════════════════════
--                                          // pure // calculation // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Get BPM from analysis
-- Pure getter function
getBPM :: AudioAnalysis -> Double
getBPM = audioAnalysisBpm

-- | Get smoothed feature value using moving average
-- Pure calculation function
getSmoothedFeature :: Maybe AudioAnalysis -> AudioFeatureType -> Int -> Int -> Double
getSmoothedFeature analysis feature frame smoothingWindow =
  case analysis of
    Nothing -> 0.0
    Just a ->
      let startFrame = max 0 (frame - smoothingWindow)
          endFrame = min (audioAnalysisFrameCount a - 1) (frame + smoothingWindow)
          frames = [startFrame .. endFrame]
          values = map (\f -> getFeatureAtFrame analysis feature f) frames
          sumValues = sum values
          count = fromIntegral (length values)
      in if count > 0 then sumValues / count else 0.0

-- | Normalize a feature array to a specific range
-- Pure calculation function
normalizeFeature :: [Double] -> Double -> Double -> [Double]
normalizeFeature values minVal maxVal =
  let minV = if null values then 0.0 else minimum values
      maxV = if null values then 1.0 else maximum values
      range = if maxV > minV then maxV - minV else 1.0
  in map (\v -> minVal + ((v - minV) / range) * (maxVal - minVal)) values

-- | Apply a curve transformation to a feature value
-- Pure calculation function
-- Curve types: linear, exponential, logarithmic, smoothstep
data CurveType = CurveLinear | CurveExponential | CurveLogarithmic | CurveSmoothstep
  deriving (Eq, Show)

applyFeatureCurve :: Double -> CurveType -> Double
applyFeatureCurve value curveType =
  let clamped = clamp01 value
  in case curveType of
    CurveLinear -> clamped
    CurveExponential -> clamped * clamped
    CurveLogarithmic -> sqrt clamped
    CurveSmoothstep -> clamped * clamped * (3 - 2 * clamped)
