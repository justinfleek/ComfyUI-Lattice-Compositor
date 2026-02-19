-- | Lattice.Services.Depth.ExportSequence - Depth Export Sequence
-- |
-- | Pure functions for depth sequence export:
-- | - Frame sequence generation
-- | - Filename generation
-- | - Depth metadata structure
-- | - Export progress tracking
-- |
-- | Source: ui/src/services/export/depthRenderer.ts (lines 1006-1115)

module Lattice.Services.Depth.ExportSequence
  ( DepthMapFormat(..)
  , DepthExportOptions
  , DepthMetadata
  , ExportProgress
  , FrameExportResult
  , totalFrames
  , frameFromIndex
  , frameIndices
  , padNumber
  , depthFilename
  , depthOutputPath
  , allOutputPaths
  , formatBitDepth
  , formatNearClip
  , formatFarClip
  , formatNormalized
  , formatInverted
  , generatorName
  , createDepthMetadata
  , metadataFromOptions
  , createProgress
  , progressPercent
  , isComplete
  , validateOptions
  , isValidOutputDir
  ) where

import Prelude

import Data.Array (range)
import Data.Int (toNumber)
import Data.String (length, take) as String
import Data.String.CodeUnits (fromCharArray, toCharArray)

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

derive instance eqDepthMapFormat :: Eq DepthMapFormat

instance showDepthMapFormat :: Show DepthMapFormat where
  show FormatRaw = "raw"
  show FormatMidas = "midas"
  show FormatDepthAnything = "depth-anything"
  show FormatZoeDepth = "zoe-depth"
  show FormatMarigold = "marigold"
  show FormatGrayscale8 = "grayscale-8"
  show FormatGrayscale16 = "grayscale-16"

-- | Export options for depth sequence.
type DepthExportOptions =
  { startFrame :: Int
  , endFrame :: Int
  , width :: Int
  , height :: Int
  , format :: DepthMapFormat
  , outputDir :: String
  }

-- | Depth metadata for export.
type DepthMetadata =
  { format :: DepthMapFormat
  , bitDepth :: Int
  , nearClip :: Number
  , farClip :: Number
  , inverted :: Boolean
  , normalized :: Boolean
  , frameCount :: Int
  , width :: Int
  , height :: Int
  , actualRangeMin :: Number
  , actualRangeMax :: Number
  , generatedAt :: String
  , generator :: String
  }

-- | Export progress event.
type ExportProgress =
  { currentFrame :: Int
  , totalFrames :: Int
  }

-- | Frame export result.
type FrameExportResult =
  { frameIndex :: Int
  , outputPath :: String
  }

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
frameIndices :: Int -> Int -> Array Int
frameIndices startFrame endFrame = range 0 (totalFrames startFrame endFrame - 1)

-- ────────────────────────────────────────────────────────────────────────────
-- Filename Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Pad number with leading zeros.
padNumber :: Int -> Int -> String
padNumber n width =
  let s = show n
      paddingLen = width - String.length s
      padding = fromCharArray (map (const '0') (range 1 paddingLen))
  in if paddingLen > 0 then padding <> s else s

-- | Generate depth frame filename.
-- | Format: depth_XXXXX.png (5-digit padding)
depthFilename :: Int -> String
depthFilename frameIndex = "depth_" <> padNumber frameIndex 5 <> ".png"

-- | Generate full output path for depth frame.
depthOutputPath :: String -> Int -> String
depthOutputPath outputDir frameIndex =
  outputDir <> "/depth/" <> depthFilename frameIndex

-- | Generate all output paths for sequence.
allOutputPaths :: DepthExportOptions -> Array String
allOutputPaths options =
  let total = totalFrames options.startFrame options.endFrame
  in map (depthOutputPath options.outputDir) (range 0 (total - 1))

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
formatNearClip :: DepthMapFormat -> Number
formatNearClip format = case format of
  FormatZoeDepth -> 0.001
  _              -> 0.1

-- | Get far clip for format.
formatFarClip :: DepthMapFormat -> Number
formatFarClip format = case format of
  FormatZoeDepth -> 80.0
  _              -> 100.0

-- | Check if format uses normalization.
formatNormalized :: DepthMapFormat -> Boolean
formatNormalized format = case format of
  FormatRaw      -> false
  FormatZoeDepth -> false
  _              -> true

-- | Check if format uses inversion.
formatInverted :: DepthMapFormat -> Boolean
formatInverted format = case format of
  FormatMidas         -> true
  FormatDepthAnything -> true
  _                   -> false

-- ────────────────────────────────────────────────────────────────────────────
-- Metadata Generation
-- ────────────────────────────────────────────────────────────────────────────

-- | Generator name constant.
generatorName :: String
generatorName = "Lattice Compositor"

-- | Create depth metadata from export results.
createDepthMetadata :: DepthMapFormat -> Int -> Int -> Int
                    -> Number -> Number -> String -> DepthMetadata
createDepthMetadata format frameCount width height minDepth maxDepth timestamp =
  { format: format
  , bitDepth: formatBitDepth format
  , nearClip: formatNearClip format
  , farClip: formatFarClip format
  , inverted: formatInverted format
  , normalized: formatNormalized format
  , frameCount: frameCount
  , width: width
  , height: height
  , actualRangeMin: minDepth
  , actualRangeMax: maxDepth
  , generatedAt: timestamp
  , generator: generatorName
  }

-- | Calculate metadata from export options.
metadataFromOptions :: DepthExportOptions -> Number -> Number
                    -> String -> DepthMetadata
metadataFromOptions options minDepth maxDepth timestamp =
  createDepthMetadata
    options.format
    (totalFrames options.startFrame options.endFrame)
    options.width
    options.height
    minDepth
    maxDepth
    timestamp

-- ────────────────────────────────────────────────────────────────────────────
-- Progress Tracking
-- ────────────────────────────────────────────────────────────────────────────

-- | Create progress event.
createProgress :: Int -> Int -> ExportProgress
createProgress currentFrame totalFrames' =
  { currentFrame: currentFrame, totalFrames: totalFrames' }

-- | Calculate progress percentage.
progressPercent :: ExportProgress -> Number
progressPercent progress
  | progress.totalFrames == 0 = 100.0
  | otherwise =
      toNumber progress.currentFrame /
      toNumber progress.totalFrames * 100.0

-- | Check if export is complete.
isComplete :: ExportProgress -> Boolean
isComplete progress = progress.currentFrame >= progress.totalFrames

-- ────────────────────────────────────────────────────────────────────────────
-- Export Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate export options.
validateOptions :: DepthExportOptions -> Boolean
validateOptions options =
  options.width > 0 &&
  options.height > 0 &&
  options.endFrame >= options.startFrame

-- | Check if output directory path is valid.
isValidOutputDir :: String -> Boolean
isValidOutputDir path =
  String.length path > 0 && String.take 1 path /= " "
