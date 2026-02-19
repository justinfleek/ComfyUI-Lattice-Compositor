-- |
-- Module      : Lattice.Services.PropertyEvaluator
-- Description : Pure property evaluation functions
-- 
-- Migrated from ui/src/services/propertyEvaluator.ts
-- Pure functions for property evaluation coordination
-- Note: Main orchestrator functions deferred until interpolation service is complete
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Services.PropertyEvaluator
  ( -- Types
    PropertyValueSource(..)
  , AudioAnalysisData(..)
  , FrequencyBands(..)
  , AudioMapping(..)
  -- Pure predicates
  , propertyHasKeyframes
  , propertyHasExpression
  , getPropertyValueSource
  -- Audio mapping
  , applyAudioMapping
  ) where

import Data.Aeson (FromJSON, ToJSON)
import Data.Text (Text)
import GHC.Generics (Generic)
import qualified Data.Text as T
import Lattice.Utils.NumericSafety (isFinite)
import Data.Either (Either(..))
import Lattice.Types.Animation (AnimatableProperty(..), PropertyExpression(..))
import Lattice.Utils.NumericSafety (ensureFinite, clamp)
import Lattice.Utils.ArrayUtils (safeArrayGet)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Property value source type
data PropertyValueSource
  = Static
  | Keyframes
  | Expression
  deriving (Eq, Show)

-- | Audio analysis data structure (simplified for property evaluator)
data AudioAnalysisData = AudioAnalysisData
  { amplitudeEnvelope :: Maybe [Double]
  , frequencyBands :: Maybe FrequencyBands
  , beats :: Maybe [Int]
  , bpm :: Maybe Double
  }
  deriving (Eq, Show)

-- | Frequency bands structure
data FrequencyBands = FrequencyBands
  { bass :: Maybe [Double]
  , mid :: Maybe [Double]
  , high :: Maybe [Double]
  }
  deriving (Eq, Show)

-- | Audio mapping configuration
data AudioMapping = AudioMapping
  { mappingId :: Text
  , mappingFeature :: Text  -- "amplitude" | "bass" | "mid" | "high" | "spectralFlux" | "onsets" | "peaks"
  , mappingTargetLayerId :: Maybe Text
  , mappingSensitivity :: Double
  , mappingOffset :: Double
  , mappingMin :: Double
  , mappingMax :: Double
  , mappingThreshold :: Double
  , mappingAmplitudeCurve :: Double
  , mappingInvert :: Bool
  , mappingEnabled :: Bool
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- ============================================================================
-- PURE PREDICATES
-- ============================================================================

-- | Check if a property has keyframes
-- Pure function: same inputs → same outputs
propertyHasKeyframes :: AnimatableProperty a -> Bool
propertyHasKeyframes prop = not (null (animatablePropertyKeyframes prop))

-- | Check if a property has an enabled expression
-- Pure function: same inputs → same outputs
propertyHasExpression :: AnimatableProperty a -> Bool
propertyHasExpression prop =
  case animatablePropertyExpression prop of
    Just expr -> propertyExpressionEnabled expr
    Nothing -> False

-- | Get the effective value source for a property
-- Pure function: same inputs → same outputs
getPropertyValueSource :: AnimatableProperty a -> PropertyValueSource
getPropertyValueSource prop
  | propertyHasExpression prop = Expression
  | propertyHasKeyframes prop = Keyframes
  | otherwise = Static

-- ============================================================================
-- AUDIO REACTIVE MAPPING
-- ============================================================================

-- | Apply audio reactive mapping to a property value
-- Pure function: same inputs → same outputs
-- Returns Left error message or Right property value
applyAudioMapping ::
  Either [Double] Double ->
  Text ->
  Int ->
  [AudioMapping] ->
  Maybe AudioAnalysisData ->
  Either Text (Either [Double] Double)
applyAudioMapping baseValue layerId frame mappings mAudioAnalysis =
  case mAudioAnalysis of
    Nothing -> Right baseValue
    Just audioAnalysis ->
      case findMappingForLayer layerId mappings of
        Nothing -> Right baseValue
        Just mapping ->
          if not (mappingEnabled mapping)
          then Right baseValue
          else
            case getAudioValueForFrame frame (mappingFeature mapping) audioAnalysis of
              Left err -> Left err
              Right audioValue ->
                let processedValue = processAudioValue audioValue mapping
                in Right (applyToBaseValue baseValue processedValue)

-- | Find mapping for a specific layer
findMappingForLayer :: Text -> [AudioMapping] -> Maybe AudioMapping
findMappingForLayer layerId mappings =
  case filter (\m -> mappingTargetLayerId m == Just layerId && mappingEnabled m) mappings of
    [] -> Nothing
    (m:_) -> Just m

-- | Get audio value for a specific frame and feature type
getAudioValueForFrame :: Int -> Text -> AudioAnalysisData -> Either Text Double
getAudioValueForFrame frameIndex feature audioAnalysis =
  let frame = fromIntegral frameIndex
  in case feature of
    "amplitude" -> getAmplitudeValue frame audioAnalysis
    "bass" -> getFrequencyBandValue frame "bass" audioAnalysis
    "mid" -> getFrequencyBandValue frame "mid" audioAnalysis
    "high" -> getFrequencyBandValue frame "high" audioAnalysis
    "spectralFlux" -> getBeatValue frame audioAnalysis
    "onsets" -> getBeatValue frame audioAnalysis
    "peaks" -> getBeatValue frame audioAnalysis
    _ -> getAmplitudeValue frame audioAnalysis  -- Default to amplitude

-- | Get amplitude value at frame
getAmplitudeValue :: Double -> AudioAnalysisData -> Either Text Double
getAmplitudeValue frameIndex audioAnalysis =
  case amplitudeEnvelope audioAnalysis of
    Nothing -> Right 0.0
    Just envelope ->
      let idx = floor frameIndex
          value = safeArrayGet envelope idx 0.0
      in Right (if isFinite value then value else 0.0)

-- | Get frequency band value at frame
getFrequencyBandValue :: Double -> Text -> AudioAnalysisData -> Either Text Double
getFrequencyBandValue frameIndex bandName audioAnalysis =
  case frequencyBands audioAnalysis of
    Nothing -> Right 0.0
    Just bands ->
      let idx = floor frameIndex
          bandArray = case bandName of
            "bass" -> bass bands
            "mid" -> mid bands
            "high" -> high bands
            _ -> Nothing
      in case bandArray of
        Nothing -> Right 0.0
        Just arr ->
          let value = safeArrayGet arr idx 0.0
          in Right (if isFinite value then value else 0.0)

-- | Get beat value at frame (1 if beat, 0 otherwise)
getBeatValue :: Double -> AudioAnalysisData -> Either Text Double
getBeatValue frameIndex audioAnalysis =
  case beats audioAnalysis of
    Nothing -> Right 0.0
    Just beatFrames ->
      let idx = floor frameIndex
          hasBeat = idx `elem` beatFrames
      in Right (if hasBeat then 1.0 else 0.0)

-- | Process audio value with mapping parameters
processAudioValue :: Double -> AudioMapping -> Double
processAudioValue audioValue mapping =
  let -- Apply threshold (noise gate)
      afterThreshold = if audioValue < mappingThreshold mapping
                       then 0.0
                       else audioValue
      
      -- Apply curve shaping
      afterCurve = if mappingAmplitudeCurve mapping /= 1.0
                   then let curve = ensureFinite (mappingAmplitudeCurve mapping) 1.0
                            result = afterThreshold ** curve
                        in ensureFinite result 0.0
                   else afterThreshold
      
      -- Apply sensitivity and offset
      afterSensitivity = afterCurve * (mappingSensitivity mapping) + (mappingOffset mapping)
      
      -- Apply inversion if needed
      afterInvert = if mappingInvert mapping
                    then 1.0 - afterSensitivity
                    else afterSensitivity
      
      -- Clamp to min/max range
      clamped = clamp afterInvert (mappingMin mapping) (mappingMax mapping)
  in ensureFinite clamped 0.0

-- | Apply processed audio value to base value
applyToBaseValue :: Either [Double] Double -> Double -> Either [Double] Double
applyToBaseValue (Right scalar) audioValue = Right (scalar + audioValue)
applyToBaseValue (Left array) audioValue = Left (map (+ audioValue) array)
