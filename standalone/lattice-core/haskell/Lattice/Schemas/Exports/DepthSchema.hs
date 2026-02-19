{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Exports.DepthSchema
Description : Depth export format enums and types
Copyright   : (c) Lattice, 2026
License     : MIT

Depth export format enums and types.

Source: ui/src/schemas/exports/depth-schema.ts
-}

module Lattice.Schemas.Exports.DepthSchema
  ( -- * Depth Format
    DepthFormat(..)
  , depthFormatFromText
  , depthFormatToText
    -- * Colormap
  , Colormap(..)
  , colormapFromText
  , colormapToText
    -- * Structures
  , DepthRange(..)
  , DepthStats(..)
    -- * Constants
  , maxDepthRange
  , maxFrames
  , maxDimension
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Format
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth output format options
data DepthFormat
  = DepthRaw           -- Float32Array direct depth values
  | DepthPNG           -- 8-bit grayscale PNG
  | DepthPNG16         -- 16-bit grayscale PNG
  | DepthEXR           -- OpenEXR floating point
  | DepthDepthAnything -- Depth-Anything model format
  | DepthMarigold      -- Marigold model format
  deriving stock (Eq, Show, Generic, Enum, Bounded)

depthFormatFromText :: Text -> Maybe DepthFormat
depthFormatFromText "raw" = Just DepthRaw
depthFormatFromText "png" = Just DepthPNG
depthFormatFromText "png16" = Just DepthPNG16
depthFormatFromText "exr" = Just DepthEXR
depthFormatFromText "depth-anything" = Just DepthDepthAnything
depthFormatFromText "marigold" = Just DepthMarigold
depthFormatFromText _ = Nothing

depthFormatToText :: DepthFormat -> Text
depthFormatToText DepthRaw = "raw"
depthFormatToText DepthPNG = "png"
depthFormatToText DepthPNG16 = "png16"
depthFormatToText DepthEXR = "exr"
depthFormatToText DepthDepthAnything = "depth-anything"
depthFormatToText DepthMarigold = "marigold"

-- ────────────────────────────────────────────────────────────────────────────
-- Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Colormap options for depth visualization
data Colormap
  = ColormapGrayscale
  | ColormapViridis
  | ColormapPlasma
  | ColormapMagma
  | ColormapInferno
  | ColormapTurbo
  deriving stock (Eq, Show, Generic, Enum, Bounded)

colormapFromText :: Text -> Maybe Colormap
colormapFromText "grayscale" = Just ColormapGrayscale
colormapFromText "viridis" = Just ColormapViridis
colormapFromText "plasma" = Just ColormapPlasma
colormapFromText "magma" = Just ColormapMagma
colormapFromText "inferno" = Just ColormapInferno
colormapFromText "turbo" = Just ColormapTurbo
colormapFromText _ = Nothing

colormapToText :: Colormap -> Text
colormapToText ColormapGrayscale = "grayscale"
colormapToText ColormapViridis = "viridis"
colormapToText ColormapPlasma = "plasma"
colormapToText ColormapMagma = "magma"
colormapToText ColormapInferno = "inferno"
colormapToText ColormapTurbo = "turbo"

-- ────────────────────────────────────────────────────────────────────────────
-- Structures
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth range specification
data DepthRange = DepthRange
  { drNear :: !Double
  , drFar :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- | Depth statistics
data DepthStats = DepthStats
  { dsMin :: !Double
  , dsMax :: !Double
  , dsMean :: !(Maybe Double)
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxDepthRange :: Double
maxDepthRange = 100000.0

maxFrames :: Int
maxFrames = 100000

maxDimension :: Int
maxDimension = 16384
