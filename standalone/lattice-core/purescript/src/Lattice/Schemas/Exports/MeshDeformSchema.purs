-- | Lattice.Schemas.Exports.MeshDeformSchema - Mesh deformation export format enums and types
-- |
-- | Mesh deformation export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/meshdeform-schema.ts

module Lattice.Schemas.Exports.MeshDeformSchema
  ( -- Mesh Deform Depth Format
    MeshDeformDepthFormat(..)
  , meshDeformDepthFormatFromString
  , meshDeformDepthFormatToString
    -- Constants
  , maxDimension
  , maxFPS
  , maxFrames
  , maxPins
  , maxDepth
    -- Structures
  , CompositionInfo
  , PinMetadata
  , MeshMaskExportMetadata
  , OverlapDepthExportMetadata
  , MeshMaskFrame
  , OverlapDepthFrame
  , MeshMaskSequenceMetadata
  , MeshMaskSequenceExport
  , OverlapDepthSequenceMetadata
  , OverlapDepthSequenceExport
    -- Validation
  , isValidCompositionInfo
  , isValidOverlapDepthMetadata
  , isValidMeshMaskSequence
  , isValidOverlapDepthSequenceMetadata
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (length)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

-- ────────────────────────────────────────────────────────────────────────────
-- Mesh Deform Depth Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Mesh deformation depth format options
data MeshDeformDepthFormat
  = DepthUInt8
  | DepthUInt16
  | DepthFloat32

derive instance Eq MeshDeformDepthFormat
derive instance Generic MeshDeformDepthFormat _

instance Show MeshDeformDepthFormat where
  show = genericShow

meshDeformDepthFormatFromString :: String -> Maybe MeshDeformDepthFormat
meshDeformDepthFormatFromString = case _ of
  "uint8" -> Just DepthUInt8
  "uint16" -> Just DepthUInt16
  "float32" -> Just DepthFloat32
  _ -> Nothing

meshDeformDepthFormatToString :: MeshDeformDepthFormat -> String
meshDeformDepthFormatToString = case _ of
  DepthUInt8 -> "uint8"
  DepthUInt16 -> "uint16"
  DepthFloat32 -> "float32"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxDimension :: Int
maxDimension = 16384

maxFPS :: Number
maxFPS = 120.0

maxFrames :: Int
maxFrames = 100000

maxPins :: Int
maxPins = 10000

maxDepth :: Number
maxDepth = 100000.0

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Composition info
type CompositionInfo =
  { width :: Int
  , height :: Int
  , frameRate :: Number
  }

-- | Pin metadata
type PinMetadata =
  { id :: String
  , name :: String
  , pinType :: String
  }

-- | Mesh mask export metadata
type MeshMaskExportMetadata =
  { width :: Int
  , height :: Int
  , format :: String  -- ^ "ImageData"
  }

-- | Overlap depth export metadata
type OverlapDepthExportMetadata =
  { width :: Int
  , height :: Int
  , minDepth :: Number
  , maxDepth :: Number
  , format :: String  -- ^ "ImageData"
  }

-- | Single frame mask data
type MeshMaskFrame =
  { frame :: Int
  , mask :: String  -- ^ Base64 PNG or filename
  }

-- | Single frame depth data
type OverlapDepthFrame =
  { frame :: Int
  , depth :: String  -- ^ Base64 PNG or filename
  }

-- | Mesh mask sequence export metadata
type MeshMaskSequenceMetadata =
  { frameCount :: Int
  , width :: Int
  , height :: Int
  }

-- | Mesh mask sequence export
type MeshMaskSequenceExport =
  { frames :: Array MeshMaskFrame
  , metadata :: MeshMaskSequenceMetadata
  }

-- | Overlap depth sequence export metadata
type OverlapDepthSequenceMetadata =
  { frameCount :: Int
  , width :: Int
  , height :: Int
  , minDepth :: Number
  , maxDepth :: Number
  }

-- | Overlap depth sequence export
type OverlapDepthSequenceExport =
  { frames :: Array OverlapDepthFrame
  , metadata :: OverlapDepthSequenceMetadata
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if composition info is valid
isValidCompositionInfo :: CompositionInfo -> Boolean
isValidCompositionInfo c =
  c.width > 0 && c.width <= maxDimension &&
  c.height > 0 && c.height <= maxDimension &&
  c.frameRate > 0.0 && c.frameRate <= maxFPS

-- | Check if overlap depth export metadata is valid
isValidOverlapDepthMetadata :: OverlapDepthExportMetadata -> Boolean
isValidOverlapDepthMetadata m =
  m.width > 0 && m.width <= maxDimension &&
  m.height > 0 && m.height <= maxDimension &&
  m.maxDepth > m.minDepth &&
  m.maxDepth <= maxDepth

-- | Check if mesh mask sequence export is valid
isValidMeshMaskSequence :: MeshMaskSequenceExport -> Boolean
isValidMeshMaskSequence e =
  e.metadata.width > 0 && e.metadata.width <= maxDimension &&
  e.metadata.height > 0 && e.metadata.height <= maxDimension &&
  e.metadata.frameCount <= maxFrames &&
  length e.frames == e.metadata.frameCount

-- | Check if overlap depth sequence metadata is valid
isValidOverlapDepthSequenceMetadata :: OverlapDepthSequenceMetadata -> Boolean
isValidOverlapDepthSequenceMetadata m =
  m.width > 0 && m.width <= maxDimension &&
  m.height > 0 && m.height <= maxDimension &&
  m.frameCount <= maxFrames &&
  m.maxDepth > m.minDepth &&
  m.maxDepth <= maxDepth
