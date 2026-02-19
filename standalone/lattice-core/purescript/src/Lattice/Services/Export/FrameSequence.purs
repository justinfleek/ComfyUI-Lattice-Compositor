-- | Lattice.Services.Export.FrameSequence - Frame sequence exporter
-- |
-- | Pure request types for exporting rendered frames as image sequences.
-- | All actual rendering and export is done by the Haskell backend via Bridge.
-- |
-- | Source: ui/src/services/export/frameSequenceExporter.ts

module Lattice.Services.Export.FrameSequence
  ( -- * Types
    FrameFormat(..)
  , ColorSpace(..)
  , FrameExportOptions
  , ExportedFrame
  , FrameSequenceResult
  , FormatInfo
    -- * Request Types
  , FrameExportRequest(..)
    -- * Format Utilities
  , isBrowserFormat
  , formatFrameNumber
  , generateFilename
  , getFormatInfo
  , formatExtension
    -- * Request Builders
  , mkExportCanvasRequest
  , mkExportSequenceRequest
  , mkCreateZipRequest
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.String as String
import Data.String.Regex as Regex
import Data.String.Regex.Flags (global)
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Frame format options
data FrameFormat
  = FormatPNG      -- Lossless, 8-bit RGBA
  | FormatJPEG     -- Lossy, 8-bit RGB
  | FormatWebP     -- Modern, supports lossless
  | FormatTIFF     -- Via backend - 8/16-bit
  | FormatEXR      -- Via backend - HDR 32-bit float
  | FormatDPX      -- Via backend - 10/16-bit film format

derive instance Generic FrameFormat _
instance Show FrameFormat where show = genericShow
instance Eq FrameFormat where eq = genericEq
instance EncodeJson FrameFormat where
  encodeJson = genericEncodeJson

-- | Color space options
data ColorSpace
  = ColorSRGB
  | ColorLinear
  | ColorACEScg
  | ColorRec709

derive instance Generic ColorSpace _
instance Show ColorSpace where show = genericShow
instance Eq ColorSpace where eq = genericEq
instance EncodeJson ColorSpace where
  encodeJson = genericEncodeJson

-- | Frame export options
type FrameExportOptions =
  { format :: FrameFormat
  , quality :: Int               -- 0-100 for lossy formats
  , filenamePattern :: String    -- e.g., "frame_{frame:04d}"
  , outputDir :: String
  , startFrame :: Int
  , endFrame :: Int
  , bitDepth :: Maybe Int        -- 8, 10, 16, or 32
  , colorSpace :: Maybe ColorSpace
  }

-- | Single exported frame
type ExportedFrame =
  { frameNumber :: Int
  , filename :: String
  , outputPath :: Maybe String   -- Path on server
  , dataUrl :: Maybe String
  , size :: Int
  }

-- | Frame sequence export result
type FrameSequenceResult =
  { success :: Boolean
  , frames :: Array ExportedFrame
  , totalSize :: Int
  , errors :: Array String
  , warnings :: Array String
  }

-- | Format info for UI display
type FormatInfo =
  { name :: String
  , description :: String
  , extension :: String
  , requiresBackend :: Boolean
  , supportsAlpha :: Boolean
  , bitDepths :: Array Int
  , lossy :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Frame export request - sent to Haskell backend
data FrameExportRequest
  = ExportCanvasRequest
      { frameData :: String        -- Base64 encoded frame data
      , format :: FrameFormat
      , quality :: Int
      , filename :: String
      }
  | ExportSequenceRequest
      { framePaths :: Array String -- Paths to frame images on server
      , options :: FrameExportOptions
      }
  | CreateZipRequest
      { frames :: Array ExportedFrame
      , folderName :: String
      , compressionLevel :: Int
      }
  | DownloadRequest
      { outputPath :: String
      , filename :: String
      }

derive instance Generic FrameExportRequest _
instance Show FrameExportRequest where show = genericShow
instance EncodeJson FrameExportRequest where
  encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create canvas export request
mkExportCanvasRequest
  :: String
  -> FrameFormat
  -> Int
  -> String
  -> FrameExportRequest
mkExportCanvasRequest frameData format quality filename =
  ExportCanvasRequest { frameData, format, quality, filename }

-- | Create sequence export request
mkExportSequenceRequest
  :: Array String
  -> FrameExportOptions
  -> FrameExportRequest
mkExportSequenceRequest framePaths options =
  ExportSequenceRequest { framePaths, options }

-- | Create zip request
mkCreateZipRequest
  :: Array ExportedFrame
  -> String
  -> Int
  -> FrameExportRequest
mkCreateZipRequest frames folderName compressionLevel =
  CreateZipRequest { frames, folderName, compressionLevel }

-- ────────────────────────────────────────────────────────────────────────────
-- Format Utilities
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if format is supported natively in browser
isBrowserFormat :: FrameFormat -> Boolean
isBrowserFormat = case _ of
  FormatPNG -> true
  FormatJPEG -> true
  FormatWebP -> true
  FormatTIFF -> false
  FormatEXR -> false
  FormatDPX -> false

-- | Get format extension
formatExtension :: FrameFormat -> String
formatExtension = case _ of
  FormatPNG -> "png"
  FormatJPEG -> "jpg"
  FormatWebP -> "webp"
  FormatTIFF -> "tiff"
  FormatEXR -> "exr"
  FormatDPX -> "dpx"

-- | Format frame number with padding
-- | Handles {frame:04d} style patterns
formatFrameNumber :: String -> Int -> String
formatFrameNumber pattern frame =
  -- Replace {frame:04d} style patterns
  case Regex.regex "\\{frame:(\\d+)d\\}" global of
    Left _ -> pattern
    Right re ->
      Regex.replace' re (\match groups ->
        let
          digits = case Array.head groups of
            Just (Just d) -> parseDigits d
            _ -> 4
        in
          padStart digits '0' (show frame)
      ) pattern

-- | Parse digits from string
parseDigits :: String -> Int
parseDigits s =
  case String.toCodePointArray s of
    _ -> 4  -- Default to 4 if parsing fails

-- | Pad string to length with character
padStart :: Int -> Char -> String -> String
padStart len c s =
  let
    padding = len - String.length s
  in
    if padding > 0
    then String.fromCodePointArray (Array.replicate padding (String.codePointFromChar c)) <> s
    else s

-- | Generate filename for a frame
generateFilename :: String -> Int -> FrameFormat -> String
generateFilename pattern frame format =
  let
    base = formatFrameNumber pattern frame
  in
    base <> "." <> formatExtension format

-- | Get format info for UI display
getFormatInfo :: FrameFormat -> FormatInfo
getFormatInfo = case _ of
  FormatPNG ->
    { name: "PNG"
    , description: "Lossless compression, 8-bit RGBA"
    , extension: "png"
    , requiresBackend: false
    , supportsAlpha: true
    , bitDepths: [8]
    , lossy: false
    }
  FormatJPEG ->
    { name: "JPEG"
    , description: "Lossy compression, 8-bit RGB"
    , extension: "jpg"
    , requiresBackend: false
    , supportsAlpha: false
    , bitDepths: [8]
    , lossy: true
    }
  FormatWebP ->
    { name: "WebP"
    , description: "Modern format, lossy or lossless"
    , extension: "webp"
    , requiresBackend: false
    , supportsAlpha: true
    , bitDepths: [8]
    , lossy: true
    }
  FormatTIFF ->
    { name: "TIFF"
    , description: "Professional format, 8/16-bit"
    , extension: "tiff"
    , requiresBackend: true
    , supportsAlpha: true
    , bitDepths: [8, 16]
    , lossy: false
    }
  FormatEXR ->
    { name: "OpenEXR"
    , description: "HDR format, 16/32-bit float"
    , extension: "exr"
    , requiresBackend: true
    , supportsAlpha: true
    , bitDepths: [16, 32]
    , lossy: false
    }
  FormatDPX ->
    { name: "DPX"
    , description: "Film industry format, 10/16-bit"
    , extension: "dpx"
    , requiresBackend: true
    , supportsAlpha: false
    , bitDepths: [10, 16]
    , lossy: false
    }
