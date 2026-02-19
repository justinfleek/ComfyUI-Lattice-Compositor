-- |
-- Module      : Lattice.Services.AudioStemSeparation
-- Description : Pure audio stem separation configuration and validation functions
-- 
-- Migrated from src/lattice/nodes/lattice_stem_separation.py
-- Pure functions for model configuration, attribution info, and parameter validation
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.AudioStemSeparation
  ( -- Model configuration
    DemucsModel(..)
  , getModelConfig
  , getAvailableModels
  -- Attribution
  , Attribution(..)
  , getAttributionInfo
  -- Parameter validation
  , StemSeparationParams(..)
  , validateStemSeparationParams
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.Utils.NumericSafety
  ( validateFinite
  )

-- ============================================================================
-- MODEL CONFIGURATION
-- ============================================================================

-- | Demucs model configuration
data DemucsModel = DemucsModel
  { modelId :: Text  -- e.g., "htdemucs"
  , modelDisplayName :: Text  -- e.g., "HT-Demucs"
  , modelDescription :: Text  -- e.g., "Hybrid Transformer Demucs - Best quality, slower"
  , modelStems :: [Text]  -- e.g., ["drums", "bass", "other", "vocals"]
  , modelSampleRate :: Int  -- e.g., 44100
  , modelRecommended :: Bool  -- Whether this is the recommended model
  } deriving (Eq, Show)

-- | All available Demucs models
demucsModels :: Map Text DemucsModel
demucsModels = Map.fromList
  [ ("htdemucs", DemucsModel
      "htdemucs"
      "HT-Demucs"
      "Hybrid Transformer Demucs - Best quality, slower"
      ["drums", "bass", "other", "vocals"]
      44100
      True)
  , ("htdemucs_ft", DemucsModel
      "htdemucs_ft"
      "HT-Demucs Fine-tuned"
      "Fine-tuned on MusDB-HQ - Highest quality"
      ["drums", "bass", "other", "vocals"]
      44100
      False)
  , ("htdemucs_6s", DemucsModel
      "htdemucs_6s"
      "HT-Demucs 6 Stems"
      "6 stem separation (includes piano, guitar)"
      ["drums", "bass", "other", "vocals", "guitar", "piano"]
      44100
      False)
  , ("mdx_extra", DemucsModel
      "mdx_extra"
      "MDX Extra"
      "Fast and accurate - Good balance"
      ["drums", "bass", "other", "vocals"]
      44100
      False)
  ]

-- | Get model configuration by name
-- Pure function: deterministic lookup
-- @param name - Model identifier (e.g., "htdemucs")
-- @returns Just model config if found, Nothing otherwise
getModelConfig :: Text -> Maybe DemucsModel
getModelConfig name = Map.lookup name demucsModels

-- | Get all available models
-- Pure function: returns all model configurations
-- @returns List of all available models
getAvailableModels :: [DemucsModel]
getAvailableModels = Map.elems demucsModels

-- ============================================================================
-- ATTRIBUTION
-- ============================================================================

-- | Attribution information for open source dependencies
data Attribution = Attribution
  { attributionId :: Text  -- e.g., "fill_nodes"
  , attributionName :: Text  -- e.g., "ComfyUI_Fill-Nodes"
  , attributionRepo :: Text  -- e.g., "https://github.com/filliptm/ComfyUI_Fill-Nodes"
  , attributionAuthor :: Text  -- e.g., "filliptm"
  , attributionLicense :: Text  -- e.g., "MIT"
  , attributionNote :: Text  -- e.g., "Concept and workflow inspiration"
  } deriving (Eq, Show)

-- | Attribution information for all sources
sourceAttribution :: Map Text Attribution
sourceAttribution = Map.fromList
  [ ("fill_nodes", Attribution
      "fill_nodes"
      "ComfyUI_Fill-Nodes"
      "https://github.com/filliptm/ComfyUI_Fill-Nodes"
      "filliptm"
      "MIT"
      "Concept and workflow inspiration")
  , ("demucs", Attribution
      "demucs"
      "Demucs"
      "https://github.com/facebookresearch/demucs"
      "Facebook Research"
      "MIT"
      "Core separation model")
  ]

-- | Get attribution information
-- Pure function: returns all attribution data
-- @returns Map of attribution ID to attribution info
getAttributionInfo :: Map Text Attribution
getAttributionInfo = sourceAttribution

-- ============================================================================
-- PARAMETER VALIDATION
-- ============================================================================

-- | Validated stem separation parameters
data StemSeparationParams = StemSeparationParams
  { paramsModelName :: Text  -- Model identifier (validated)
  , paramsSegmentLength :: Double  -- > 0
  , paramsOverlap :: Double  -- 0-0.5
  , paramsStemsToReturn :: Maybe [Text]  -- Optional list of stems (validated against model)
  } deriving (Eq, Show)

-- | Validate stem separation parameters
-- Pure function: deterministic validation
-- @param modelName - Model identifier
-- @param segmentLength - Length of audio chunks in seconds (> 0)
-- @param overlap - Overlap ratio between chunks (0-0.5)
-- @param mStems - Optional list of stem names to return
-- @returns Either error message or validated parameters
validateStemSeparationParams
  :: Text
  -> Double
  -> Double
  -> Maybe [Text]
  -> Either Text StemSeparationParams
validateStemSeparationParams modelName segmentLength overlap mStems =
  case getModelConfig modelName of
    Nothing -> Left $ "Unknown model: " <> modelName
    Just modelConfig ->
      if not (validateFinite segmentLength) || segmentLength <= 0
        then Left "segment_length must be positive and finite"
      else if not (validateFinite overlap) || overlap < 0 || overlap > 0.5
        then Left "overlap must be between 0 and 0.5 and finite"
      else if maybe False (any (`notElem` modelStems modelConfig)) mStems
        then Left $ "Invalid stem names. Available stems: " <> T.intercalate ", " (modelStems modelConfig)
      else Right $ StemSeparationParams modelName segmentLength overlap mStems
