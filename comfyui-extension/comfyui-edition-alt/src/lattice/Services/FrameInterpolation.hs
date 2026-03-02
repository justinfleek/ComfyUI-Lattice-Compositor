-- |
-- Module      : Lattice.Services.FrameInterpolation
-- Description : Pure frame interpolation configuration and validation functions
-- 
-- Migrated from src/lattice/nodes/lattice_frame_interpolation.py
-- Pure functions for model configuration, attribution info, parameter validation, and slowdown mapping
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.FrameInterpolation
  ( -- Model configuration
    RIFEModel(..)
  , getRIFEModelConfig
  , getAvailableRIFEModels
  -- Attribution
  , Attribution(..)
  , getRIFEAttributionInfo
  -- Parameter validation
  , FrameInterpolationParams(..)
  , validateInterpolationParams
  -- Slowdown mapping
  , slowdownToFactor
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.Utils.NumericSafety
  ( validateFinite
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // model // configuration
-- ════════════════════════════════════════════════════════════════════════════

-- | RIFE model configuration
data RIFEModel = RIFEModel
  { rifeModelId :: Text  -- e.g., "rife-v4.6"
  , rifeModelDisplayName :: Text  -- e.g., "RIFE v4.6"
  , rifeModelDescription :: Text  -- e.g., "Latest RIFE - Best quality and speed balance"
  , rifeModelSupportsEnsemble :: Bool  -- Whether ensemble mode is supported
  , rifeModelRecommended :: Bool  -- Whether this is the recommended model
  } deriving (Eq, Show)

-- | All available RIFE models
rifeModels :: Map Text RIFEModel
rifeModels = Map.fromList
  [ ("rife-v4.6", RIFEModel
      "rife-v4.6"
      "RIFE v4.6"
      "Latest RIFE - Best quality and speed balance"
      True
      True)
  , ("rife-v4.0", RIFEModel
      "rife-v4.0"
      "RIFE v4.0"
      "Stable RIFE v4 - Good all-around performance"
      True
      False)
  , ("rife-v3.9", RIFEModel
      "rife-v3.9"
      "RIFE v3.9"
      "Older RIFE - Faster but lower quality"
      False
      False)
  , ("film", RIFEModel
      "film"
      "FILM"
      "Frame Interpolation for Large Motion - Google Research"
      False
      False)
  ]

-- | Get model configuration by name
-- Pure function: deterministic lookup
-- @param name - Model identifier (e.g., "rife-v4.6")
-- @returns Just model config if found, Nothing otherwise
getRIFEModelConfig :: Text -> Maybe RIFEModel
getRIFEModelConfig name = Map.lookup name rifeModels

-- | Get all available models
-- Pure function: returns all model configurations
-- @returns List of all available models
getAvailableRIFEModels :: [RIFEModel]
getAvailableRIFEModels = Map.elems rifeModels

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // attribution
-- ════════════════════════════════════════════════════════════════════════════

-- | Attribution information for open source dependencies
data Attribution = Attribution
  { attributionId :: Text  -- e.g., "fill_nodes"
  , attributionName :: Text  -- e.g., "ComfyUI_Fill-Nodes"
  , attributionRepo :: Text  -- e.g., "https://github.com/filliptm/ComfyUI_Fill-Nodes"
  , attributionAuthor :: Text  -- e.g., "filliptm"
  , attributionLicense :: Text  -- e.g., "MIT"
  , attributionNote :: Text  -- e.g., "FL_RIFE_Interpolation workflow inspiration"
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
      "FL_RIFE_Interpolation workflow inspiration")
  , ("rife", Attribution
      "rife"
      "RIFE (Real-time Intermediate Flow Estimation)"
      "https://github.com/megvii-research/ECCV2022-RIFE"
      "Megvii Research"
      "Apache 2.0"
      "Core interpolation model")
  , ("practical_rife", Attribution
      "practical_rife"
      "Practical-RIFE"
      "https://github.com/hzwer/Practical-RIFE"
      "hzwer"
      "Apache 2.0"
      "Production implementation")
  ]

-- | Get attribution information
-- Pure function: returns all attribution data
-- @returns Map of attribution ID to attribution info
getRIFEAttributionInfo :: Map Text Attribution
getRIFEAttributionInfo = sourceAttribution

-- ════════════════════════════════════════════════════════════════════════════
--                                                   // parameter // validation
-- ════════════════════════════════════════════════════════════════════════════

-- | Validated frame interpolation parameters
data FrameInterpolationParams = FrameInterpolationParams
  { paramsModelName :: Text  -- Model identifier (validated)
  , paramsFactor :: Int  -- 2, 4, or 8
  , paramsEnsemble :: Bool  -- Whether to use ensemble mode
  , paramsSlowdown :: Maybe Double  -- Optional slowdown factor (0-8)
  } deriving (Eq, Show)

-- | Validate frame interpolation parameters
-- Pure function: deterministic validation
-- @param modelName - Model identifier
-- @param factor - Interpolation factor (2, 4, or 8)
-- @param ensemble - Whether to use ensemble mode
-- @param mSlowdown - Optional slowdown factor (0-8)
-- @returns Either error message or validated parameters
validateInterpolationParams
  :: Text
  -> Int
  -> Bool
  -> Maybe Double
  -> Either Text FrameInterpolationParams
validateInterpolationParams modelName factor ensemble mSlowdown =
  case getRIFEModelConfig modelName of
    Nothing -> Left $ "Unknown model: " <> modelName
    Just modelConfig ->
      if factor `notElem` [2, 4, 8]
        then Left "factor must be 2, 4, or 8"
      else if ensemble && not (rifeModelSupportsEnsemble modelConfig)
        then Left $ "Model " <> modelName <> " does not support ensemble mode"
      else if maybe False (\s -> not (validateFinite s) || s <= 0 || s > 8) mSlowdown
        then Left "slowdown must be between 0 and 8 and finite"
      else Right $ FrameInterpolationParams modelName factor ensemble mSlowdown

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // slowdown // mapping
-- ════════════════════════════════════════════════════════════════════════════

-- | Map slowdown factor to interpolation factor
-- Pure function: deterministic mapping
-- @param slowdown - Slowdown factor (e.g., 2.0 = half speed)
-- @returns Interpolation factor (2, 4, or 8)
-- Note: slowdown <= 2.0 → factor 2, <= 4.0 → factor 4, otherwise → factor 8
slowdownToFactor :: Double -> Int
slowdownToFactor slowdown
  | slowdown <= 2.0 = 2
  | slowdown <= 4.0 = 4
  | otherwise = 8
