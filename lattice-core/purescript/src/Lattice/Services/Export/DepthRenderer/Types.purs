-- | Lattice.Services.Export.DepthRenderer.Types - Depth rendering types
-- |
-- | Types for depth map rendering and format conversion.
-- |
-- | Source: ui/src/services/export/depthRenderer.ts

module Lattice.Services.Export.DepthRenderer.Types
  ( -- * Depth Render Types
    DepthRenderOptions
  , DepthRenderResult
  , DepthMetadata
  , Vec3
    -- * Format Types
  , DepthMapFormat(..)
  , DepthFormatSpec
  , Colormap(..)
    -- * Screen Bounds
  , ScreenBounds
    -- * Defaults
  , defaultDepthFormatSpec
  , defaultDepthMetadata
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Eq.Generic (genericEq)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

-- ────────────────────────────────────────────────────────────────────────────
-- Core Types
-- ────────────────────────────────────────────────────────────────────────────

-- | 3D vector type (shared)
type Vec3 = { x :: Number, y :: Number, z :: Number }

-- | Depth render options
type DepthRenderOptions =
  { width :: Int
  , height :: Int
  , nearClip :: Number
  , farClip :: Number
  , cameraPosition :: Vec3
  , frame :: Int
  }

-- | Depth render result
type DepthRenderResult =
  { width :: Int
  , height :: Int
  , minDepth :: Number
  , maxDepth :: Number
  }

-- | Screen bounds
type ScreenBounds =
  { x :: Number
  , y :: Number
  , width :: Number
  , height :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Format Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth map format
data DepthMapFormat
  = FormatRaw           -- Float32, metric
  | FormatMiDaS         -- 16-bit normalized, inverted
  | FormatDepthAnything -- 16-bit normalized
  | FormatZoeDepth      -- 16-bit metric
  | FormatMarigold      -- 8-bit normalized
  | FormatControlNet    -- 8-bit grayscale

derive instance Generic DepthMapFormat _
instance Show DepthMapFormat where show = genericShow
instance Eq DepthMapFormat where eq = genericEq
instance EncodeJson DepthMapFormat where encodeJson = genericEncodeJson

-- | Depth format specification
type DepthFormatSpec =
  { bitDepth :: Int       -- 8, 16, or 32
  , nearClip :: Number
  , farClip :: Number
  , invert :: Boolean     -- Near=bright vs Near=dark
  , normalize :: Boolean  -- 0-1 range vs metric
  }

-- | Colormap type
data Colormap
  = ColormapGrayscale
  | ColormapViridis
  | ColormapMagma
  | ColormapPlasma
  | ColormapInferno
  | ColormapTurbo

derive instance Generic Colormap _
instance Show Colormap where show = genericShow
instance Eq Colormap where eq = genericEq
instance EncodeJson Colormap where encodeJson = genericEncodeJson

-- ────────────────────────────────────────────────────────────────────────────
-- Metadata Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth metadata for export
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
  , actualRange :: { min :: Number, max :: Number }
  , generatedAt :: String  -- ISO 8601 timestamp
  , generator :: String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Defaults
-- ────────────────────────────────────────────────────────────────────────────

-- | Default depth format spec (ControlNet compatible)
defaultDepthFormatSpec :: DepthFormatSpec
defaultDepthFormatSpec =
  { bitDepth: 8
  , nearClip: 0.1
  , farClip: 1000.0
  , invert: true
  , normalize: true
  }

-- | Default depth metadata
defaultDepthMetadata :: DepthMetadata
defaultDepthMetadata =
  { format: FormatControlNet
  , bitDepth: 8
  , nearClip: 0.1
  , farClip: 1000.0
  , inverted: true
  , normalized: true
  , frameCount: 1
  , width: 512
  , height: 512
  , actualRange: { min: 0.0, max: 1000.0 }
  , generatedAt: ""
  , generator: "Lattice Compositor"
  }
