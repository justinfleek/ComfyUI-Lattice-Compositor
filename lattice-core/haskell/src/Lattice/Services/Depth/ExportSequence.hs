{-|
Module      : Lattice.Services.Depth.ExportSequence
Description : Depth export sequence and metadata generation
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for depth sequence export:
- Frame sequence generation
- Filename generation
- Depth metadata structure
- Export progress tracking

Source: ui/src/services/export/depthRenderer.ts (lines 1006-1115)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Depth.ExportSequence
  ( -- * Types
    DepthMapFormat(..)
  , DepthExportOptions(..)
  , DepthMetadata(..)
  , ExportProgress(..)
  , FrameExportResult(..)
    -- * Frame Calculations
  , totalFrames
  , frameFromIndex
  , frameIndices
    -- * Filename Generation
  , padNumber
  , depthFilename
  , depthOutputPath
  , allOutputPaths
    -- * Format Specification Lookup
  , formatBitDepth
  , formatNearClip
  , formatFarClip
  , formatNormalized
  , formatInverted
    -- * Metadata Generation
  , generatorName
  , createDepthMetadata
  , metadataFromOptions
    -- * Progress Tracking
  , createProgress
  , progressPercent
  , isComplete
    -- * Export Validation
  , validateOptions
  , isValidOutputDir
  ) where

import Data.List (replicate)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth map format enumeration.
data DepthMapFormat
  = FormatRaw
  | FormatMidas
  | FormatDepthAnything
  | FormatZoeDepth
  | FormatMarigold
  | FormatGrayscale8
  | FormatGrayscale16
  deriving (Show, Eq)

-- | Export options for depth sequence.
data DepthExportOptions = DepthExportOptions
  { deoStartFrame :: Int
  , deoEndFrame   :: Int
  , deoWidth      :: Int
  , deoHeight     :: Int
  , deoFormat     :: DepthMapFormat
  , deoOutputDir  :: String
  } deriving (Show, Eq)

-- | Depth metadata for export.
data DepthMetadata = DepthMetadata
  { dmFormat         :: DepthMapFormat
  , dmBitDepth       :: Int
  , dmNearClip       :: Double
  , dmFarClip        :: Double
  , dmInverted       :: Bool
  , dmNormalized     :: Bool
  , dmFrameCount     :: Int
  , dmWidth          :: Int
  , dmHeight         :: Int
  , dmActualRangeMin :: Double
  , dmActualRangeMax :: Double
  , dmGeneratedAt    :: String  -- ^ ISO 8601 timestamp
  , dmGenerator      :: String
  } deriving (Show, Eq)

-- | Export progress event.
data ExportProgress = ExportProgress
  { epCurrentFrame :: Int
  , epTotalFrames  :: Int
  } deriving (Show, Eq)

-- | Frame export result.
data FrameExportResult = FrameExportResult
  { ferFrameIndex :: Int
  , ferOutputPath :: String
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Frame Calculations
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate total frame count in sequence.
totalFrames :: Int -> Int -> Int
totalFrames startFrame endFrame
  | endFrame >= startFrame = endFrame - startFrame + 1
  | otherwise = 0

-- | Calculate frame number from index.
frameFromIndex :: Int -> Int -> Int
frameFromIndex startFrame index = startFrame + index

-- | Generate frame indices for sequence.
frameIndices :: Int -> Int -> [Int]
frameIndices startFrame endFrame = [0 .. totalFrames startFrame endFrame - 1]

-- ────────────────────────────────────────────────────────────────────────────
-- Filename Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Pad number with leading zeros.
padNumber :: Int -> Int -> String
padNumber n width =
  let s = show n
      padding = replicate (width - length s) '0'
  in padding ++ s

-- | Generate depth frame filename.
-- Format: depth_XXXXX.png (5-digit padding)
depthFilename :: Int -> String
depthFilename frameIndex = "depth_" ++ padNumber frameIndex 5 ++ ".png"

-- | Generate full output path for depth frame.
depthOutputPath :: String -> Int -> String
depthOutputPath outputDir frameIndex =
  outputDir ++ "/depth/" ++ depthFilename frameIndex

-- | Generate all output paths for sequence.
allOutputPaths :: DepthExportOptions -> [String]
allOutputPaths options =
  let total = totalFrames (deoStartFrame options) (deoEndFrame options)
  in [depthOutputPath (deoOutputDir options) i | i <- [0 .. total - 1]]

-- ────────────────────────────────────────────────────────────────────────────
-- Format Specification Lookup
-- ────────────────────────────────────────────────────────────────────────────

-- | Get bit depth for format.
formatBitDepth :: DepthMapFormat -> Int
formatBitDepth format = case format of
  FormatRaw         -> 32
  FormatGrayscale8  -> 8
  _                 -> 16

-- | Get near clip for format.
formatNearClip :: DepthMapFormat -> Double
formatNearClip format = case format of
  FormatZoeDepth -> 0.001
  _              -> 0.1

-- | Get far clip for format.
formatFarClip :: DepthMapFormat -> Double
formatFarClip format = case format of
  FormatZoeDepth -> 80.0
  _              -> 100.0

-- | Check if format uses normalization.
formatNormalized :: DepthMapFormat -> Bool
formatNormalized format = case format of
  FormatRaw      -> False
  FormatZoeDepth -> False
  _              -> True

-- | Check if format uses inversion.
formatInverted :: DepthMapFormat -> Bool
formatInverted format = case format of
  FormatMidas         -> True
  FormatDepthAnything -> True
  _                   -> False

-- ────────────────────────────────────────────────────────────────────────────
-- Metadata Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generator name constant.
generatorName :: String
generatorName = "Lattice Compositor"

-- | Create depth metadata from export results.
createDepthMetadata :: DepthMapFormat -> Int -> Int -> Int
                    -> Double -> Double -> String -> DepthMetadata
createDepthMetadata format frameCount width height minDepth maxDepth timestamp =
  DepthMetadata
    { dmFormat         = format
    , dmBitDepth       = formatBitDepth format
    , dmNearClip       = formatNearClip format
    , dmFarClip        = formatFarClip format
    , dmInverted       = formatInverted format
    , dmNormalized     = formatNormalized format
    , dmFrameCount     = frameCount
    , dmWidth          = width
    , dmHeight         = height
    , dmActualRangeMin = minDepth
    , dmActualRangeMax = maxDepth
    , dmGeneratedAt    = timestamp
    , dmGenerator      = generatorName
    }

-- | Calculate metadata from export options.
metadataFromOptions :: DepthExportOptions -> Double -> Double
                    -> String -> DepthMetadata
metadataFromOptions options minDepth maxDepth timestamp =
  createDepthMetadata
    (deoFormat options)
    (totalFrames (deoStartFrame options) (deoEndFrame options))
    (deoWidth options)
    (deoHeight options)
    minDepth
    maxDepth
    timestamp

-- ────────────────────────────────────────────────────────────────────────────
-- Progress Tracking
-- ────────────────────────────────────────────────────────────────────────────

-- | Create progress event.
createProgress :: Int -> Int -> ExportProgress
createProgress = ExportProgress

-- | Calculate progress percentage.
progressPercent :: ExportProgress -> Double
progressPercent progress
  | epTotalFrames progress == 0 = 100.0
  | otherwise =
      fromIntegral (epCurrentFrame progress) /
      fromIntegral (epTotalFrames progress) * 100.0

-- | Check if export is complete.
isComplete :: ExportProgress -> Bool
isComplete progress = epCurrentFrame progress >= epTotalFrames progress

-- ────────────────────────────────────────────────────────────────────────────
-- Export Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate export options.
validateOptions :: DepthExportOptions -> Bool
validateOptions options =
  deoWidth options > 0 &&
  deoHeight options > 0 &&
  deoEndFrame options >= deoStartFrame options

-- | Check if output directory path is valid.
isValidOutputDir :: String -> Bool
isValidOutputDir path =
  not (null path) && head path /= ' '
