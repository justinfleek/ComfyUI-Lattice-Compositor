{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.TTMSchema
Description : TTM export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

TTM (Time-to-Move) export format enums and types.

Source: ui/src/schemas/exports/ttm-schema.ts
-}

module Lattice.Schemas.Exports.TTMSchema
  ( -- * TTM Model
    TTMModel(..)
  , ttmModelFromText
  , ttmModelToText
    -- * Constants
  , maxFrames
  , maxDimension
  , maxLayers
  , maxTweakIndex
  , maxInferenceSteps
    -- * Structures
  , TrajectoryPoint(..)
  , TTMLayerExport(..)
  , TTMModelConfig(..)
  , TTMMetadata(..)
  , TTMExport(..)
  , LegacyTrajectoryPoint(..)
  , TTMSingleLayerExport(..)
    -- * Validation
  , isValidTrajectoryPoint
  , isValidLayerExport
  , isValidModelConfig
  , isValidMetadata
  , isValidExport
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- TTM Model
--------------------------------------------------------------------------------

-- | TTM model options
data TTMModel
  = ModelWan
  | ModelCogvideox
  | ModelSvd
  deriving stock (Eq, Show, Generic, Enum, Bounded)

ttmModelFromText :: Text -> Maybe TTMModel
ttmModelFromText "wan" = Just ModelWan
ttmModelFromText "cogvideox" = Just ModelCogvideox
ttmModelFromText "svd" = Just ModelSvd
ttmModelFromText _ = Nothing

ttmModelToText :: TTMModel -> Text
ttmModelToText ModelWan = "wan"
ttmModelToText ModelCogvideox = "cogvideox"
ttmModelToText ModelSvd = "svd"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxFrames :: Int
maxFrames = 100000

maxDimension :: Int
maxDimension = 16384

maxLayers :: Int
maxLayers = 1000

maxTweakIndex :: Double
maxTweakIndex = 100.0

maxInferenceSteps :: Int
maxInferenceSteps = 1000

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Trajectory point
data TrajectoryPoint = TrajectoryPoint
  { tpFrame :: !Int
  , tpX :: !Double
  , tpY :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | TTM layer export data
data TTMLayerExport = TTMLayerExport
  { tleLayerId :: !Text
  , tleLayerName :: !Text
  , tleMotionMask :: !Text        -- ^ Base64 PNG
  , tleTrajectory :: !(Vector TrajectoryPoint)
  , tleVisibility :: !(Vector Bool)
  }
  deriving stock (Eq, Show, Generic)

-- | TTM model configuration
data TTMModelConfig = TTMModelConfig
  { tmcModel :: !TTMModel
  , tmcTweakIndex :: !Double
  , tmcTstrongIndex :: !Double
  , tmcInferenceSteps :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | TTM export metadata
data TTMMetadata = TTMMetadata
  { tmLayerCount :: !Int
  , tmFrameCount :: !Int
  , tmWidth :: !Int
  , tmHeight :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | TTM export format (multi-layer)
data TTMExport = TTMExport
  { teReferenceImage :: !Text       -- ^ Base64 or path
  , teLastFrame :: !(Maybe Text)    -- ^ Last frame for temporal context
  , teLayers :: !(Vector TTMLayerExport)
  , teCombinedMotionMask :: !Text   -- ^ Base64 PNG
  , teModelConfig :: !TTMModelConfig
  , teMetadata :: !TTMMetadata
  }
  deriving stock (Eq, Show, Generic)

-- | Legacy single trajectory point (no frame)
data LegacyTrajectoryPoint = LegacyTrajectoryPoint
  { ltpX :: !Double
  , ltpY :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | TTM single layer export (legacy)
data TTMSingleLayerExport = TTMSingleLayerExport
  { tsleReferenceImage :: !Text
  , tsleMotionMask :: !Text
  , tsleTrajectory :: !(Vector LegacyTrajectoryPoint)
  , tsleModelConfig :: !TTMModelConfig
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if trajectory point is valid
isValidTrajectoryPoint :: TrajectoryPoint -> Bool
isValidTrajectoryPoint p =
  tpFrame p >= 0 && tpFrame p <= maxFrames &&
  tpX p >= 0 && tpX p <= fromIntegral maxDimension &&
  tpY p >= 0 && tpY p <= fromIntegral maxDimension

-- | Check if layer export is valid
isValidLayerExport :: TTMLayerExport -> Bool
isValidLayerExport l =
  V.length (tleTrajectory l) == V.length (tleVisibility l) &&
  V.length (tleTrajectory l) <= maxFrames

-- | Check if model config is valid
isValidModelConfig :: TTMModelConfig -> Bool
isValidModelConfig c =
  tmcTweakIndex c >= 0 && tmcTweakIndex c <= maxTweakIndex &&
  tmcTstrongIndex c >= 0 && tmcTstrongIndex c <= maxTweakIndex &&
  tmcInferenceSteps c > 0 && tmcInferenceSteps c <= maxInferenceSteps

-- | Check if metadata is valid
isValidMetadata :: TTMMetadata -> Bool
isValidMetadata m =
  tmLayerCount m <= maxLayers &&
  tmFrameCount m > 0 && tmFrameCount m <= maxFrames &&
  tmWidth m > 0 && tmWidth m <= maxDimension &&
  tmHeight m > 0 && tmHeight m <= maxDimension

-- | Check if TTM export is valid
isValidExport :: TTMExport -> Bool
isValidExport e =
  isValidMetadata (teMetadata e) &&
  isValidModelConfig (teModelConfig e) &&
  V.length (teLayers e) == tmLayerCount (teMetadata e)
