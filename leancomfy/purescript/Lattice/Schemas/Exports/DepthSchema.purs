-- | Lattice.Schemas.Exports.DepthSchema - Depth export format enums and types
-- |
-- | Depth export format enums and types.
-- |
-- | Source: ui/src/schemas/exports/depth-schema.ts

module Lattice.Schemas.Exports.DepthSchema
  ( -- Depth Format
    DepthFormat(..)
  , depthFormatFromString
  , depthFormatToString
    -- Colormap
  , Colormap(..)
  , colormapFromString
  , colormapToString
    -- Structures
  , DepthRange
  , DepthStats
    -- Constants
  , maxDepthRange
  , maxFrames
  , maxDimension
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Depth Format
--------------------------------------------------------------------------------

-- | Depth output format options
data DepthFormat
  = DepthRaw           -- Float32Array direct depth values
  | DepthPNG           -- 8-bit grayscale PNG
  | DepthPNG16         -- 16-bit grayscale PNG
  | DepthEXR           -- OpenEXR floating point
  | DepthDepthAnything -- Depth-Anything model format
  | DepthMarigold      -- Marigold model format

derive instance Eq DepthFormat
derive instance Generic DepthFormat _

instance Show DepthFormat where
  show = genericShow

depthFormatFromString :: String -> Maybe DepthFormat
depthFormatFromString = case _ of
  "raw" -> Just DepthRaw
  "png" -> Just DepthPNG
  "png16" -> Just DepthPNG16
  "exr" -> Just DepthEXR
  "depth-anything" -> Just DepthDepthAnything
  "marigold" -> Just DepthMarigold
  _ -> Nothing

depthFormatToString :: DepthFormat -> String
depthFormatToString = case _ of
  DepthRaw -> "raw"
  DepthPNG -> "png"
  DepthPNG16 -> "png16"
  DepthEXR -> "exr"
  DepthDepthAnything -> "depth-anything"
  DepthMarigold -> "marigold"

--------------------------------------------------------------------------------
-- Colormap
--------------------------------------------------------------------------------

-- | Colormap options for depth visualization
data Colormap
  = ColormapGrayscale
  | ColormapViridis
  | ColormapPlasma
  | ColormapMagma
  | ColormapInferno
  | ColormapTurbo

derive instance Eq Colormap
derive instance Generic Colormap _

instance Show Colormap where
  show = genericShow

colormapFromString :: String -> Maybe Colormap
colormapFromString = case _ of
  "grayscale" -> Just ColormapGrayscale
  "viridis" -> Just ColormapViridis
  "plasma" -> Just ColormapPlasma
  "magma" -> Just ColormapMagma
  "inferno" -> Just ColormapInferno
  "turbo" -> Just ColormapTurbo
  _ -> Nothing

colormapToString :: Colormap -> String
colormapToString = case _ of
  ColormapGrayscale -> "grayscale"
  ColormapViridis -> "viridis"
  ColormapPlasma -> "plasma"
  ColormapMagma -> "magma"
  ColormapInferno -> "inferno"
  ColormapTurbo -> "turbo"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

-- | Depth range specification
type DepthRange =
  { near :: Number
  , far :: Number
  }

-- | Depth statistics
type DepthStats =
  { min :: Number
  , max :: Number
  , mean :: Maybe Number
  }

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxDepthRange :: Number
maxDepthRange = 100000.0

maxFrames :: Int
maxFrames = 100000

maxDimension :: Int
maxDimension = 16384
