-- | Lattice.Schemas.Exports.ATISchema - ATI export format types and constants
-- |
-- | ATI (Attention-based Temporal Interpolation) export format types and constants.
-- | ATI format uses exactly 121 frames with pixel coordinate trajectories.
-- |
-- | Source: ui/src/schemas/exports/ati-schema.ts

module Lattice.Schemas.Exports.ATISchema
  ( -- Constants
    atiFixedFrames
  , atiMaxDimension
  , atiMinDimension
  , maxTracks
  , maxOriginalFrames
  , maxFPS
    -- Track Point
  , ATITrackPoint
  , ATIPointTuple
    -- Export Result
  , ATIExportResult
    -- Export Config
  , ATIExportConfig
    -- Metadata
  , ATIMetadata
    -- ATI Data
  , ATIData
    -- Validation
  , isValidExportResult
  , isValidExportConfig
  , isValidMetadata
  , isValidATIData
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (length, all)
import Data.Tuple (Tuple)

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
maxFPS :: Number
maxFPS = 120.0

--------------------------------------------------------------------------------
-- Track Point
--------------------------------------------------------------------------------

-- | A single 2D point in pixel coordinates for ATI tracking
type ATITrackPoint =
  { x :: Number
  , y :: Number
  }

-- | A single 2D point tuple
type ATIPointTuple = Tuple Number Number

--------------------------------------------------------------------------------
-- Export Result
--------------------------------------------------------------------------------

-- | Result of an ATI export operation
type ATIExportResult =
  { tracks :: String          -- ^ JSON-serialized track data
  , width :: Int              -- ^ Width of the composition in pixels
  , height :: Int             -- ^ Height of the composition in pixels
  , numTracks :: Int          -- ^ Number of tracks exported
  , originalFrames :: Int     -- ^ Original frame count before resampling to 121
  }

--------------------------------------------------------------------------------
-- Export Config
--------------------------------------------------------------------------------

-- | Configuration options for ATI export
type ATIExportConfig =
  { compositionId :: String       -- ^ Composition ID to export
  , includeVisibility :: Boolean  -- ^ Whether to include visibility data
  , startFrame :: Maybe Int       -- ^ Frame range start
  , endFrame :: Maybe Int         -- ^ Frame range end
  }

--------------------------------------------------------------------------------
-- Metadata
--------------------------------------------------------------------------------

-- | ATI metadata
type ATIMetadata =
  { version :: String
  , width :: Int
  , height :: Int
  , fps :: Number
  , frameCount :: Int
  , numTracks :: Int
  , exportedAt :: Maybe String
  }

--------------------------------------------------------------------------------
-- ATI Data
--------------------------------------------------------------------------------

-- | Full ATI data structure for import/export operations
type ATIData =
  { tracks :: Array (Array ATIPointTuple)     -- ^ Track coordinate data
  , visibility :: Maybe (Array (Array Boolean))  -- ^ Optional visibility data
  , metadata :: ATIMetadata                   -- ^ Metadata
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if export result dimensions are valid
isValidExportResult :: ATIExportResult -> Boolean
isValidExportResult r =
  r.width >= atiMinDimension && r.width <= atiMaxDimension &&
  r.height >= atiMinDimension && r.height <= atiMaxDimension &&
  r.numTracks <= maxTracks &&
  r.originalFrames <= maxOriginalFrames

-- | Check if config has valid frame range
isValidExportConfig :: ATIExportConfig -> Boolean
isValidExportConfig c =
  case c.startFrame, c.endFrame of
    Just start, Just end -> end >= start && end <= maxOriginalFrames
    Just start, Nothing -> start <= maxOriginalFrames
    Nothing, Just end -> end <= maxOriginalFrames
    Nothing, Nothing -> true

-- | Check if metadata is valid
isValidMetadata :: ATIMetadata -> Boolean
isValidMetadata m =
  m.width >= atiMinDimension && m.width <= atiMaxDimension &&
  m.height >= atiMinDimension && m.height <= atiMaxDimension &&
  m.fps > 0.0 && m.fps <= maxFPS &&
  m.frameCount == atiFixedFrames &&
  m.numTracks <= maxTracks

-- | Check if ATI data is valid
isValidATIData :: ATIData -> Boolean
isValidATIData d =
  isValidMetadata d.metadata &&
  length d.tracks == d.metadata.numTracks &&
  all (\track -> length track == atiFixedFrames) d.tracks &&
  case d.visibility of
    Just vis ->
      length vis == length d.tracks &&
      all (\v -> length v == atiFixedFrames) vis
    Nothing -> true
