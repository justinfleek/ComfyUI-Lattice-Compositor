{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.MeshDeformSchema
Description : Mesh deformation export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Mesh deformation export format enums and types.

Source: ui/src/schemas/exports/meshdeform-schema.ts
-}

module Lattice.Schemas.Exports.MeshDeformSchema
  ( -- * Mesh Deform Depth Format
    MeshDeformDepthFormat(..)
  , meshDeformDepthFormatFromText
  , meshDeformDepthFormatToText
    -- * Constants
  , maxDimension
  , maxFPS
  , maxFrames
  , maxPins
  , maxDepth
    -- * Structures
  , CompositionInfo(..)
  , PinMetadata(..)
  , MeshMaskExportMetadata(..)
  , OverlapDepthExportMetadata(..)
  , MeshMaskFrame(..)
  , OverlapDepthFrame(..)
  , MeshMaskSequenceMetadata(..)
  , MeshMaskSequenceExport(..)
  , OverlapDepthSequenceMetadata(..)
  , OverlapDepthSequenceExport(..)
    -- * Validation
  , isValidCompositionInfo
  , isValidOverlapDepthMetadata
  , isValidMeshMaskSequence
  , isValidOverlapDepthSequenceMetadata
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Mesh Deform Depth Format
--------------------------------------------------------------------------------

-- | Mesh deformation depth format options
data MeshDeformDepthFormat
  = DepthUInt8
  | DepthUInt16
  | DepthFloat32
  deriving stock (Eq, Show, Generic, Enum, Bounded)

meshDeformDepthFormatFromText :: Text -> Maybe MeshDeformDepthFormat
meshDeformDepthFormatFromText "uint8" = Just DepthUInt8
meshDeformDepthFormatFromText "uint16" = Just DepthUInt16
meshDeformDepthFormatFromText "float32" = Just DepthFloat32
meshDeformDepthFormatFromText _ = Nothing

meshDeformDepthFormatToText :: MeshDeformDepthFormat -> Text
meshDeformDepthFormatToText DepthUInt8 = "uint8"
meshDeformDepthFormatToText DepthUInt16 = "uint16"
meshDeformDepthFormatToText DepthFloat32 = "float32"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDimension :: Int
maxDimension = 16384

maxFPS :: Double
maxFPS = 120.0

maxFrames :: Int
maxFrames = 100000

maxPins :: Int
maxPins = 10000

maxDepth :: Double
maxDepth = 100000.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Composition info
data CompositionInfo = CompositionInfo
  { ciWidth :: !Int
  , ciHeight :: !Int
  , ciFrameRate :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Pin metadata
data PinMetadata = PinMetadata
  { pmId :: !Text
  , pmName :: !Text
  , pmPinType :: !Text
  }
  deriving stock (Eq, Show, Generic)

-- | Mesh mask export metadata
data MeshMaskExportMetadata = MeshMaskExportMetadata
  { mmemWidth :: !Int
  , mmemHeight :: !Int
  , mmemFormat :: !Text  -- ^ "ImageData"
  }
  deriving stock (Eq, Show, Generic)

-- | Overlap depth export metadata
data OverlapDepthExportMetadata = OverlapDepthExportMetadata
  { odemWidth :: !Int
  , odemHeight :: !Int
  , odemMinDepth :: !Double
  , odemMaxDepth :: !Double
  , odemFormat :: !Text  -- ^ "ImageData"
  }
  deriving stock (Eq, Show, Generic)

-- | Single frame mask data
data MeshMaskFrame = MeshMaskFrame
  { mmfFrame :: !Int
  , mmfMask :: !Text  -- ^ Base64 PNG or filename
  }
  deriving stock (Eq, Show, Generic)

-- | Single frame depth data
data OverlapDepthFrame = OverlapDepthFrame
  { odfFrame :: !Int
  , odfDepth :: !Text  -- ^ Base64 PNG or filename
  }
  deriving stock (Eq, Show, Generic)

-- | Mesh mask sequence export metadata
data MeshMaskSequenceMetadata = MeshMaskSequenceMetadata
  { mmsmFrameCount :: !Int
  , mmsmWidth :: !Int
  , mmsmHeight :: !Int
  }
  deriving stock (Eq, Show, Generic)

-- | Mesh mask sequence export
data MeshMaskSequenceExport = MeshMaskSequenceExport
  { mmseFrames :: !(Vector MeshMaskFrame)
  , mmseMetadata :: !MeshMaskSequenceMetadata
  }
  deriving stock (Eq, Show, Generic)

-- | Overlap depth sequence export metadata
data OverlapDepthSequenceMetadata = OverlapDepthSequenceMetadata
  { odsmFrameCount :: !Int
  , odsmWidth :: !Int
  , odsmHeight :: !Int
  , odsmMinDepth :: !Double
  , odsmMaxDepth :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Overlap depth sequence export
data OverlapDepthSequenceExport = OverlapDepthSequenceExport
  { odseFrames :: !(Vector OverlapDepthFrame)
  , odseMetadata :: !OverlapDepthSequenceMetadata
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Check if composition info is valid
isValidCompositionInfo :: CompositionInfo -> Bool
isValidCompositionInfo c =
  ciWidth c > 0 && ciWidth c <= maxDimension &&
  ciHeight c > 0 && ciHeight c <= maxDimension &&
  ciFrameRate c > 0 && ciFrameRate c <= maxFPS

-- | Check if overlap depth export metadata is valid
isValidOverlapDepthMetadata :: OverlapDepthExportMetadata -> Bool
isValidOverlapDepthMetadata m =
  odemWidth m > 0 && odemWidth m <= maxDimension &&
  odemHeight m > 0 && odemHeight m <= maxDimension &&
  odemMaxDepth m > odemMinDepth m &&
  odemMaxDepth m <= maxDepth

-- | Check if mesh mask sequence export is valid
isValidMeshMaskSequence :: MeshMaskSequenceExport -> Bool
isValidMeshMaskSequence e =
  mmsmWidth (mmseMetadata e) > 0 && mmsmWidth (mmseMetadata e) <= maxDimension &&
  mmsmHeight (mmseMetadata e) > 0 && mmsmHeight (mmseMetadata e) <= maxDimension &&
  mmsmFrameCount (mmseMetadata e) <= maxFrames &&
  V.length (mmseFrames e) == mmsmFrameCount (mmseMetadata e)

-- | Check if overlap depth sequence metadata is valid
isValidOverlapDepthSequenceMetadata :: OverlapDepthSequenceMetadata -> Bool
isValidOverlapDepthSequenceMetadata m =
  odsmWidth m > 0 && odsmWidth m <= maxDimension &&
  odsmHeight m > 0 && odsmHeight m <= maxDimension &&
  odsmFrameCount m <= maxFrames &&
  odsmMaxDepth m > odsmMinDepth m &&
  odsmMaxDepth m <= maxDepth
