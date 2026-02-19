-- | Lattice.Schemas.Exports.TTMSchema - TTM export format enums and types
-- |
-- | TTM (Time-to-Move) export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/ttm-schema.ts

module Lattice.Schemas.Exports.TTMSchema
  ( -- TTM Model
    TTMModel(..)
  , ttmModelFromString
  , ttmModelToString
    -- Constants
  , maxFrames
  , maxDimension
  , maxLayers
  , maxTweakIndex
  , maxInferenceSteps
    -- Structures
  , TrajectoryPoint
  , TTMLayerExport
  , TTMModelConfig
  , TTMMetadata
  , TTMExport
  , LegacyTrajectoryPoint
  , TTMSingleLayerExport
    -- Validation
  , isValidTrajectoryPoint
  , isValidLayerExport
  , isValidModelConfig
  , isValidMetadata
  , isValidExport
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (length)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Int (toNumber)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // ttm // m
-- ────────────────────────────────────────────────────────────────────────────

-- | TTM model options
data TTMModel
  = ModelWan
  | ModelCogvideox
  | ModelSvd

derive instance Eq TTMModel
derive instance Generic TTMModel _

instance Show TTMModel where
  show = genericShow

ttmModelFromString :: String -> Maybe TTMModel
ttmModelFromString = case _ of
  "wan" -> Just ModelWan
  "cogvideox" -> Just ModelCogvideox
  "svd" -> Just ModelSvd
  _ -> Nothing

ttmModelToString :: TTMModel -> String
ttmModelToString = case _ of
  ModelWan -> "wan"
  ModelCogvideox -> "cogvideox"
  ModelSvd -> "svd"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFrames :: Int
maxFrames = 100000

maxDimension :: Int
maxDimension = 16384

maxLayers :: Int
maxLayers = 1000

maxTweakIndex :: Number
maxTweakIndex = 100.0

maxInferenceSteps :: Int
maxInferenceSteps = 1000

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Trajectory point
type TrajectoryPoint =
  { frame :: Int
  , x :: Number
  , y :: Number
  }

-- | TTM layer export data
type TTMLayerExport =
  { layerId :: String
  , layerName :: String
  , motionMask :: String        -- ^ Base64 PNG
  , trajectory :: Array TrajectoryPoint
  , visibility :: Array Boolean
  }

-- | TTM model configuration
type TTMModelConfig =
  { model :: TTMModel
  , tweakIndex :: Number
  , tstrongIndex :: Number
  , inferenceSteps :: Int
  }

-- | TTM export metadata
type TTMMetadata =
  { layerCount :: Int
  , frameCount :: Int
  , width :: Int
  , height :: Int
  }

-- | TTM export format (multi-layer)
type TTMExport =
  { referenceImage :: String       -- ^ Base64 or path
  , lastFrame :: Maybe String      -- ^ Last frame for temporal context
  , layers :: Array TTMLayerExport
  , combinedMotionMask :: String   -- ^ Base64 PNG
  , modelConfig :: TTMModelConfig
  , metadata :: TTMMetadata
  }

-- | Legacy single trajectory point (no frame)
type LegacyTrajectoryPoint =
  { x :: Number
  , y :: Number
  }

-- | TTM single layer export (legacy)
type TTMSingleLayerExport =
  { referenceImage :: String
  , motionMask :: String
  , trajectory :: Array LegacyTrajectoryPoint
  , modelConfig :: TTMModelConfig
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if trajectory point is valid
isValidTrajectoryPoint :: TrajectoryPoint -> Boolean
isValidTrajectoryPoint p =
  p.frame >= 0 && p.frame <= maxFrames &&
  p.x >= 0.0 && p.x <= toNumber maxDimension &&
  p.y >= 0.0 && p.y <= toNumber maxDimension

-- | Check if layer export is valid
isValidLayerExport :: TTMLayerExport -> Boolean
isValidLayerExport l =
  length l.trajectory == length l.visibility &&
  length l.trajectory <= maxFrames

-- | Check if model config is valid
isValidModelConfig :: TTMModelConfig -> Boolean
isValidModelConfig c =
  c.tweakIndex >= 0.0 && c.tweakIndex <= maxTweakIndex &&
  c.tstrongIndex >= 0.0 && c.tstrongIndex <= maxTweakIndex &&
  c.inferenceSteps > 0 && c.inferenceSteps <= maxInferenceSteps

-- | Check if metadata is valid
isValidMetadata :: TTMMetadata -> Boolean
isValidMetadata m =
  m.layerCount <= maxLayers &&
  m.frameCount > 0 && m.frameCount <= maxFrames &&
  m.width > 0 && m.width <= maxDimension &&
  m.height > 0 && m.height <= maxDimension

-- | Check if TTM export is valid
isValidExport :: TTMExport -> Boolean
isValidExport e =
  isValidMetadata e.metadata &&
  isValidModelConfig e.modelConfig &&
  length e.layers == e.metadata.layerCount
