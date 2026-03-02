-- |
-- Module      : Lattice.Services.TimelineSnap
-- Description : Pure timeline snapping functions
-- 
-- Migrated from ui/src/services/timelineSnap.ts
-- Pure functions extracted - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.TimelineSnap
  ( -- Query functions
    getBeatFrames
  , getPeakFrames
  , isNearBeat
  , getSnapColor
  -- Types
  , SnapType(..)
  , SnapConfig(..)
  , defaultSnapConfig
  , SnapResult(..)
  , AudioAnalysis(..)
  , PeakData(..)
  ) where

import Data.Aeson.Types ((.!=))
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
import Data.List (any)
import Data.Maybe (Maybe)
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Primitives (validateFinite, validateNonNegative)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                              // snap // type
-- ════════════════════════════════════════════════════════════════════════════

-- | Snap target types
data SnapType
  = SnapTypeFrame
  | SnapTypeKeyframe
  | SnapTypeBeat
  | SnapTypePeak
  | SnapTypeLayerIn
  | SnapTypeLayerOut
  | SnapTypePlayhead
  deriving (Eq, Show, Generic)

instance ToJSON SnapType where
  toJSON SnapTypeFrame = "frame"
  toJSON SnapTypeKeyframe = "keyframe"
  toJSON SnapTypeBeat = "beat"
  toJSON SnapTypePeak = "peak"
  toJSON SnapTypeLayerIn = "layer-in"
  toJSON SnapTypeLayerOut = "layer-out"
  toJSON SnapTypePlayhead = "playhead"

instance FromJSON SnapType where
  parseJSON = withText "SnapType" $ \t ->
    case t of
      "frame" -> return SnapTypeFrame
      "keyframe" -> return SnapTypeKeyframe
      "beat" -> return SnapTypeBeat
      "peak" -> return SnapTypePeak
      "layer-in" -> return SnapTypeLayerIn
      "layer-out" -> return SnapTypeLayerOut
      "playhead" -> return SnapTypePlayhead
      _ -> fail ("Invalid SnapType: " ++ show t)

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // audio // analysis
-- ════════════════════════════════════════════════════════════════════════════

-- | Audio analysis with minimal fields for snap queries
data AudioAnalysis = AudioAnalysis
  { audioAnalysisOnsets :: [Double]
  }
  deriving (Eq, Show, Generic)

instance ToJSON AudioAnalysis where
  toJSON (AudioAnalysis onsets) =
    object ["onsets" .= onsets]

instance FromJSON AudioAnalysis where
  parseJSON = withObject "AudioAnalysis" $ \o -> do
    onsets <- o .:? "onsets" .!= []
    return (AudioAnalysis onsets)

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // snap // configuration
-- ════════════════════════════════════════════════════════════════════════════

-- | Snap configuration for timeline snapping
data SnapConfig = SnapConfig
  { snapConfigEnabled :: Bool
  , snapConfigSnapToGrid :: Bool
  , snapConfigSnapToKeyframes :: Bool
  , snapConfigSnapToBeats :: Bool
  , snapConfigSnapToPeaks :: Bool
  , snapConfigSnapToLayerBounds :: Bool
  , snapConfigSnapToPlayhead :: Bool
  , snapConfigThreshold :: Double  -- Snap threshold in pixels (must be >= 0)
  , snapConfigGridInterval :: Double  -- Grid interval in frames (must be >= 1)
  }
  deriving (Eq, Show, Generic)

instance ToJSON SnapConfig where
  toJSON (SnapConfig enabled grid keyframes beats peaks layerBounds playhead threshold gridInterval) =
    object
      [ "enabled" .= enabled
      , "snapToGrid" .= grid
      , "snapToKeyframes" .= keyframes
      , "snapToBeats" .= beats
      , "snapToPeaks" .= peaks
      , "snapToLayerBounds" .= layerBounds
      , "snapToPlayhead" .= playhead
      , "threshold" .= threshold
      , "gridInterval" .= gridInterval
      ]

instance FromJSON SnapConfig where
  parseJSON = withObject "SnapConfig" $ \o -> do
    enabled <- o .: "enabled"
    grid <- o .: "snapToGrid"
    keyframes <- o .: "snapToKeyframes"
    beats <- o .: "snapToBeats"
    peaks <- o .: "snapToPeaks"
    layerBounds <- o .: "snapToLayerBounds"
    playhead <- o .: "snapToPlayhead"
    threshold <- o .: "threshold"
    gridInterval <- o .: "gridInterval"
    -- Validate threshold and gridInterval are finite and non-negative
    if validateFinite threshold && validateNonNegative threshold && validateFinite gridInterval && gridInterval >= 1
      then return (SnapConfig enabled grid keyframes beats peaks layerBounds playhead threshold gridInterval)
      else fail "SnapConfig: threshold must be finite and non-negative, gridInterval must be finite and >= 1"

-- | Default snap configuration
defaultSnapConfig :: SnapConfig
defaultSnapConfig = SnapConfig
  { snapConfigEnabled = True
  , snapConfigSnapToGrid = True
  , snapConfigSnapToKeyframes = True
  , snapConfigSnapToBeats = True
  , snapConfigSnapToPeaks = True
  , snapConfigSnapToLayerBounds = True
  , snapConfigSnapToPlayhead = True
  , snapConfigThreshold = 8.0  -- 8 pixels snap threshold
  , snapConfigGridInterval = 5.0  -- Snap to every 5 frames by default
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // snap // result
-- ════════════════════════════════════════════════════════════════════════════

-- | Result of finding nearest snap point
data SnapResult = SnapResult
  { snapResultFrame :: Double  -- Snapped frame number
  , snapResultType :: SnapType  -- Type of snap target
  , snapResultDistance :: Double  -- Distance from original frame in pixels (must be >= 0)
  }
  deriving (Eq, Show, Generic)

instance ToJSON SnapResult where
  toJSON (SnapResult frame typ distance) =
    object
      [ "frame" .= frame
      , "type" .= typ
      , "distance" .= distance
      ]

instance FromJSON SnapResult where
  parseJSON = withObject "SnapResult" $ \o -> do
    frame <- o .: "frame"
    typ <- o .: "type"
    distance <- o .: "distance"
    -- Validate frame and distance are finite and non-negative
    if validateFinite frame && validateNonNegative frame && validateFinite distance && validateNonNegative distance
      then return (SnapResult frame typ distance)
      else fail "SnapResult: frame and distance must be finite and non-negative"

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // peak // data
-- ════════════════════════════════════════════════════════════════════════════

-- | Peak data with minimal fields for snap queries
data PeakData = PeakData
  { peakDataIndices :: [Double]
  }
  deriving (Eq, Show, Generic)

instance ToJSON PeakData where
  toJSON (PeakData indices) =
    object ["indices" .= indices]

instance FromJSON PeakData where
  parseJSON = withObject "PeakData" $ \o -> do
    indices <- o .:? "indices" .!= []
    return (PeakData indices)

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // query // functions
-- ════════════════════════════════════════════════════════════════════════════

-- | Get all beat frames from audio analysis
-- Pure function: takes audio analysis, returns beat frames list
getBeatFrames :: Maybe AudioAnalysis -> [Double]
getBeatFrames mAnalysis =
  case mAnalysis of
    Nothing -> []
    Just analysis -> audioAnalysisOnsets analysis

-- | Get all peak frames from peak data
-- Pure function: takes peak data, returns peak frames list
getPeakFrames :: Maybe PeakData -> [Double]
getPeakFrames mPeakData =
  case mPeakData of
    Nothing -> []
    Just peakData -> peakDataIndices peakData

-- | Check if a frame is near a beat (within threshold)
-- Pure function: takes frame, audio analysis, threshold, returns Bool
isNearBeat :: Double -> Maybe AudioAnalysis -> Double -> Bool
isNearBeat frame mAnalysis thresholdFrames =
  case mAnalysis of
    Nothing -> False
    Just analysis ->
      any (\onset -> abs (frame - onset) <= thresholdFrames) (audioAnalysisOnsets analysis)

-- | Get color for snap type
-- Pure function: takes snap type, returns color hex string
getSnapColor :: SnapType -> Text
getSnapColor snapType =
  case snapType of
    SnapTypeFrame -> "#666"
    SnapTypeKeyframe -> "#7c9cff"
    SnapTypeBeat -> "#ffc107"
    SnapTypePeak -> "#ff6b6b"
    SnapTypeLayerIn -> "#4ecdc4"
    SnapTypeLayerOut -> "#4ecdc4"
    SnapTypePlayhead -> "#ff4444"
