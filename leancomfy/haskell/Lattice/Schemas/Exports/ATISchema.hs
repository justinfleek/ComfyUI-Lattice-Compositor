{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.ATISchema
Description : ATI export format types and constants
Copyright   : (c) Lattice, 2026
License     : MIT

ATI (Attention-based Temporal Interpolation) export format types and constants.
ATI format uses exactly 121 frames with pixel coordinate trajectories.

Source: ui/src/schemas/exports/ati-schema.ts
-}

module Lattice.Schemas.Exports.ATISchema
  ( -- * Constants
    atiFixedFrames
  , atiMaxDimension
  , atiMinDimension
  , maxTracks
  , maxOriginalFrames
  , maxFPS
    -- * Track Point
  , ATITrackPoint(..)
  , ATIPointTuple
    -- * Export Result
  , ATIExportResult(..)
    -- * Export Config
  , ATIExportConfig(..)
    -- * Metadata
  , ATIMetadata(..)
    -- * ATI Data
  , ATIData(..)
    -- * Validation
  , isValidExportResult
  , isValidExportConfig
  , isValidMetadata
  , isValidATIData
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | ATI format requires exactly 121 frames
atiFixedFrames :: Int
atiFixedFrames = 121

-- | Maximum supported resolution
atiMaxDimension :: Int
atiMaxDimension = 8192

-- | Minimum supported resolution
atiMinDimension :: Int
atiMinDimension = 1

-- | Maximum number of tracks
maxTracks :: Int
maxTracks = 10000

-- | Maximum original frame count before resampling
maxOriginalFrames :: Int
maxOriginalFrames = 100000

-- | Maximum FPS
maxFPS :: Double
maxFPS = 120.0

--------------------------------------------------------------------------------
-- Track Point
--------------------------------------------------------------------------------

-- | A single 2D point in pixel coordinates for ATI tracking
data ATITrackPoint = ATITrackPoint
  { atpX :: !Double
  , atpY :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | A single 2D point tuple
type ATIPointTuple = (Double, Double)

--------------------------------------------------------------------------------
-- Export Result
--------------------------------------------------------------------------------

-- | Result of an ATI export operation
data ATIExportResult = ATIExportResult
  { aerTracks :: !Text          -- ^ JSON-serialized track data
  , aerWidth :: !Int            -- ^ Width of the composition in pixels
  , aerHeight :: !Int           -- ^ Height of the composition in pixels
  , aerNumTracks :: !Int        -- ^ Number of tracks exported
  , aerOriginalFrames :: !Int   -- ^ Original frame count before resampling to 121
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Export Config
--------------------------------------------------------------------------------

-- | Configuration options for ATI export
data ATIExportConfig = ATIExportConfig
  { aecCompositionId :: !Text       -- ^ Composition ID to export
  , aecIncludeVisibility :: !Bool   -- ^ Whether to include visibility data
  , aecStartFrame :: !(Maybe Int)   -- ^ Frame range start
  , aecEndFrame :: !(Maybe Int)     -- ^ Frame range end
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Metadata
--------------------------------------------------------------------------------

-- | ATI metadata
data ATIMetadata = ATIMetadata
  { amVersion :: !Text
  , amWidth :: !Int
  , amHeight :: !Int
  , amFps :: !Double
  , amFrameCount :: !Int
  , amNumTracks :: !Int
  , amExportedAt :: !(Maybe Text)
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- ATI Data
--------------------------------------------------------------------------------

-- | Full ATI data structure for import/export operations
data ATIData = ATIData
  { adTracks :: !(Vector (Vector ATIPointTuple))  -- ^ Track coordinate data
  , adVisibility :: !(Maybe (Vector (Vector Bool)))  -- ^ Optional visibility data
  , adMetadata :: !ATIMetadata  -- ^ Metadata
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if export result dimensions are valid
isValidExportResult :: ATIExportResult -> Bool
isValidExportResult r =
  aerWidth r >= atiMinDimension && aerWidth r <= atiMaxDimension &&
  aerHeight r >= atiMinDimension && aerHeight r <= atiMaxDimension &&
  aerNumTracks r <= maxTracks &&
  aerOriginalFrames r <= maxOriginalFrames

-- | Check if config has valid frame range
isValidExportConfig :: ATIExportConfig -> Bool
isValidExportConfig c =
  case (aecStartFrame c, aecEndFrame c) of
    (Just start, Just end) -> end >= start && end <= maxOriginalFrames
    (Just start, Nothing) -> start <= maxOriginalFrames
    (Nothing, Just end) -> end <= maxOriginalFrames
    (Nothing, Nothing) -> True

-- | Check if metadata is valid
isValidMetadata :: ATIMetadata -> Bool
isValidMetadata m =
  amWidth m >= atiMinDimension && amWidth m <= atiMaxDimension &&
  amHeight m >= atiMinDimension && amHeight m <= atiMaxDimension &&
  amFps m > 0 && amFps m <= maxFPS &&
  amFrameCount m == atiFixedFrames &&
  amNumTracks m <= maxTracks

-- | Check if ATI data is valid
isValidATIData :: ATIData -> Bool
isValidATIData d =
  isValidMetadata (adMetadata d) &&
  V.length (adTracks d) == amNumTracks (adMetadata d) &&
  V.all (\track -> V.length track == atiFixedFrames) (adTracks d) &&
  case adVisibility d of
    Just vis ->
      V.length vis == V.length (adTracks d) &&
      V.all (\v -> V.length v == atiFixedFrames) vis
    Nothing -> True
