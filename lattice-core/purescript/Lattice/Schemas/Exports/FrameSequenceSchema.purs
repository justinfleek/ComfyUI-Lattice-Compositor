-- | Lattice.Schemas.Exports.FrameSequenceSchema - Frame sequence export format enums and types
-- |
-- | Frame sequence export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/framesequence-schema.ts

module Lattice.Schemas.Exports.FrameSequenceSchema
  ( -- Frame Format
    FrameFormat(..)
  , frameFormatFromString
  , frameFormatToString
    -- Color Space
  , ColorSpace(..)
  , colorSpaceFromString
  , colorSpaceToString
    -- Bit Depth
  , BitDepth(..)
  , bitDepthFromInt
  , bitDepthToInt
    -- Constants
  , maxFrames
  , maxDimension
  , maxFPS
  , maxQuality
  , maxFileSize
    -- Structures
  , FrameExportOptions
  , ExportedFrame
  , FrameSequenceResult
    -- Validation
  , isValidExportOptions
  , isValidExportedFrame
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Frame Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Frame export format options
data FrameFormat
  = FormatPNG    -- ^ Lossless, 8-bit RGBA
  | FormatJPEG   -- ^ Lossy, 8-bit RGB
  | FormatWebP   -- ^ Modern, supports lossless
  | FormatTIFF   -- ^ Via backend - 8/16-bit
  | FormatEXR    -- ^ Via backend - HDR 32-bit float
  | FormatDPX    -- ^ Via backend - 10/16-bit film format

derive instance Eq FrameFormat
derive instance Generic FrameFormat _

instance Show FrameFormat where
  show = genericShow

frameFormatFromString :: String -> Maybe FrameFormat
frameFormatFromString = case _ of
  "png" -> Just FormatPNG
  "jpeg" -> Just FormatJPEG
  "webp" -> Just FormatWebP
  "tiff" -> Just FormatTIFF
  "exr" -> Just FormatEXR
  "dpx" -> Just FormatDPX
  _ -> Nothing

frameFormatToString :: FrameFormat -> String
frameFormatToString = case _ of
  FormatPNG -> "png"
  FormatJPEG -> "jpeg"
  FormatWebP -> "webp"
  FormatTIFF -> "tiff"
  FormatEXR -> "exr"
  FormatDPX -> "dpx"

-- ────────────────────────────────────────────────────────────────────────────
-- Color Space
-- ────────────────────────────────────────────────────────────────────────────

-- | Color space options
data ColorSpace
  = ColorSRGB
  | ColorLinear
  | ColorACEScg
  | ColorRec709

derive instance Eq ColorSpace
derive instance Generic ColorSpace _

instance Show ColorSpace where
  show = genericShow

colorSpaceFromString :: String -> Maybe ColorSpace
colorSpaceFromString = case _ of
  "sRGB" -> Just ColorSRGB
  "Linear" -> Just ColorLinear
  "ACEScg" -> Just ColorACEScg
  "Rec709" -> Just ColorRec709
  _ -> Nothing

colorSpaceToString :: ColorSpace -> String
colorSpaceToString = case _ of
  ColorSRGB -> "sRGB"
  ColorLinear -> "Linear"
  ColorACEScg -> "ACEScg"
  ColorRec709 -> "Rec709"

-- ────────────────────────────────────────────────────────────────────────────
-- Bit Depth
-- ────────────────────────────────────────────────────────────────────────────

-- | Bit depth options
data BitDepth
  = Bits8
  | Bits10
  | Bits16
  | Bits32

derive instance Eq BitDepth
derive instance Generic BitDepth _

instance Show BitDepth where
  show = genericShow

bitDepthFromInt :: Int -> Maybe BitDepth
bitDepthFromInt = case _ of
  8 -> Just Bits8
  10 -> Just Bits10
  16 -> Just Bits16
  32 -> Just Bits32
  _ -> Nothing

bitDepthToInt :: BitDepth -> Int
bitDepthToInt = case _ of
  Bits8 -> 8
  Bits10 -> 10
  Bits16 -> 16
  Bits32 -> 32

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxFrames :: Int
maxFrames = 100000

maxDimension :: Int
maxDimension = 16384

maxFPS :: Number
maxFPS = 120.0

maxQuality :: Int
maxQuality = 100

maxFileSize :: Int
maxFileSize = 2147483647  -- 2GB

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Frame export options
type FrameExportOptions =
  { format :: FrameFormat
  , quality :: Int          -- ^ 0-100 for lossy formats
  , filenamePattern :: String -- ^ e.g., "frame_{frame:04d}"
  , outputDir :: String
  , startFrame :: Int
  , endFrame :: Int
  , bitDepth :: Maybe BitDepth
  , colorSpace :: Maybe ColorSpace
  }

-- | Exported frame info
type ExportedFrame =
  { frameNumber :: Int
  , filename :: String
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

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if export options are valid
isValidExportOptions :: FrameExportOptions -> Boolean
isValidExportOptions o =
  o.quality >= 0 && o.quality <= maxQuality &&
  o.startFrame >= 0 && o.startFrame <= maxFrames &&
  o.endFrame >= 0 && o.endFrame <= maxFrames &&
  o.endFrame >= o.startFrame

-- | Check if exported frame is valid
isValidExportedFrame :: ExportedFrame -> Boolean
isValidExportedFrame f =
  f.frameNumber >= 0 && f.frameNumber <= maxFrames &&
  f.size >= 0 && f.size <= maxFileSize
