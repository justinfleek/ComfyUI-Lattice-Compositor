{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.FrameSequenceSchema
Description : Frame sequence export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Frame sequence export format enums and types.

Source: ui/src/schemas/exports/framesequence-schema.ts
-}

module Lattice.Schemas.Exports.FrameSequenceSchema
  ( -- * Frame Format
    FrameFormat(..)
  , frameFormatFromText
  , frameFormatToText
    -- * Color Space
  , ColorSpace(..)
  , colorSpaceFromText
  , colorSpaceToText
    -- * Bit Depth
  , BitDepth(..)
  , bitDepthFromInt
  , bitDepthToInt
    -- * Constants
  , maxFrames
  , maxDimension
  , maxFPS
  , maxQuality
  , maxFileSize
    -- * Structures
  , FrameExportOptions(..)
  , ExportedFrame(..)
  , FrameSequenceResult(..)
    -- * Validation
  , isValidExportOptions
  , isValidExportedFrame
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)

--------------------------------------------------------------------------------
-- Frame Format
--------------------------------------------------------------------------------

-- | Frame export format options
data FrameFormat
  = FormatPNG    -- ^ Lossless, 8-bit RGBA
  | FormatJPEG   -- ^ Lossy, 8-bit RGB
  | FormatWebP   -- ^ Modern, supports lossless
  | FormatTIFF   -- ^ Via backend - 8/16-bit
  | FormatEXR    -- ^ Via backend - HDR 32-bit float
  | FormatDPX    -- ^ Via backend - 10/16-bit film format
  deriving stock (Eq, Show, Generic, Enum, Bounded)

frameFormatFromText :: Text -> Maybe FrameFormat
frameFormatFromText "png" = Just FormatPNG
frameFormatFromText "jpeg" = Just FormatJPEG
frameFormatFromText "webp" = Just FormatWebP
frameFormatFromText "tiff" = Just FormatTIFF
frameFormatFromText "exr" = Just FormatEXR
frameFormatFromText "dpx" = Just FormatDPX
frameFormatFromText _ = Nothing

frameFormatToText :: FrameFormat -> Text
frameFormatToText FormatPNG = "png"
frameFormatToText FormatJPEG = "jpeg"
frameFormatToText FormatWebP = "webp"
frameFormatToText FormatTIFF = "tiff"
frameFormatToText FormatEXR = "exr"
frameFormatToText FormatDPX = "dpx"

--------------------------------------------------------------------------------
-- Color Space
--------------------------------------------------------------------------------

-- | Color space options
data ColorSpace
  = ColorSRGB
  | ColorLinear
  | ColorACEScg
  | ColorRec709
  deriving stock (Eq, Show, Generic, Enum, Bounded)

colorSpaceFromText :: Text -> Maybe ColorSpace
colorSpaceFromText "sRGB" = Just ColorSRGB
colorSpaceFromText "Linear" = Just ColorLinear
colorSpaceFromText "ACEScg" = Just ColorACEScg
colorSpaceFromText "Rec709" = Just ColorRec709
colorSpaceFromText _ = Nothing

colorSpaceToText :: ColorSpace -> Text
colorSpaceToText ColorSRGB = "sRGB"
colorSpaceToText ColorLinear = "Linear"
colorSpaceToText ColorACEScg = "ACEScg"
colorSpaceToText ColorRec709 = "Rec709"

--------------------------------------------------------------------------------
-- Bit Depth
--------------------------------------------------------------------------------

-- | Bit depth options
data BitDepth
  = Bits8
  | Bits10
  | Bits16
  | Bits32
  deriving stock (Eq, Show, Generic, Enum, Bounded)

bitDepthFromInt :: Int -> Maybe BitDepth
bitDepthFromInt 8 = Just Bits8
bitDepthFromInt 10 = Just Bits10
bitDepthFromInt 16 = Just Bits16
bitDepthFromInt 32 = Just Bits32
bitDepthFromInt _ = Nothing

bitDepthToInt :: BitDepth -> Int
bitDepthToInt Bits8 = 8
bitDepthToInt Bits10 = 10
bitDepthToInt Bits16 = 16
bitDepthToInt Bits32 = 32

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxFrames :: Int
maxFrames = 100000

maxDimension :: Int
maxDimension = 16384

maxFPS :: Double
maxFPS = 120.0

maxQuality :: Int
maxQuality = 100

maxFileSize :: Int
maxFileSize = 2147483647  -- 2GB

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Frame export options
data FrameExportOptions = FrameExportOptions
  { feoFormat :: !FrameFormat
  , feoQuality :: !Int          -- ^ 0-100 for lossy formats
  , feoFilenamePattern :: !Text -- ^ e.g., "frame_{frame:04d}"
  , feoOutputDir :: !Text
  , feoStartFrame :: !Int
  , feoEndFrame :: !Int
  , feoBitDepth :: !(Maybe BitDepth)
  , feoColorSpace :: !(Maybe ColorSpace)
  }
  deriving stock (Eq, Show, Generic)

-- | Exported frame info
data ExportedFrame = ExportedFrame
  { efFrameNumber :: !Int
  , efFilename :: !Text
  , efSize :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Frame sequence export result
data FrameSequenceResult = FrameSequenceResult
  { fsrSuccess :: !Bool
  , fsrFrames :: !(Vector ExportedFrame)
  , fsrTotalSize :: !Int
  , fsrErrors :: !(Vector Text)
  , fsrWarnings :: !(Vector Text)
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if export options are valid
isValidExportOptions :: FrameExportOptions -> Bool
isValidExportOptions o =
  feoQuality o >= 0 && feoQuality o <= maxQuality &&
  feoStartFrame o >= 0 && feoStartFrame o <= maxFrames &&
  feoEndFrame o >= 0 && feoEndFrame o <= maxFrames &&
  feoEndFrame o >= feoStartFrame o

-- | Check if exported frame is valid
isValidExportedFrame :: ExportedFrame -> Bool
isValidExportedFrame f =
  efFrameNumber f >= 0 && efFrameNumber f <= maxFrames &&
  efSize f >= 0 && efSize f <= maxFileSize
