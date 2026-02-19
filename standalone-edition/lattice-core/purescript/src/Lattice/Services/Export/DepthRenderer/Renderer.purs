-- | Lattice.Services.Export.DepthRenderer.Renderer - Depth rendering requests
-- |
-- | Pure request types for depth map rendering.
-- | All actual rendering is done by the Haskell backend via Bridge.
-- |
-- | Source: ui/src/services/export/depthRenderer.ts

module Lattice.Services.Export.DepthRenderer.Renderer
  ( -- * Request Types
    DepthRenderRequest(..)
  , DepthConversionRequest
  , DepthExportSequenceRequest
    -- * Request Builders
  , mkRenderDepthRequest
  , mkRenderDepthFromEngineRequest
  , mkConvertDepthRequest
  , mkExportSequenceRequest
    -- * Metadata
  , generateDepthMetadata
    -- * Utilities
  , getFormatSpec
  , formatToString
  , colormapToString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut.Encode (class EncodeJson)
import Data.Argonaut.Encode.Generic (genericEncodeJson)

import Lattice.Services.Export.DepthRenderer.Types
  ( DepthRenderOptions
  , DepthRenderResult
  , DepthMetadata
  , DepthMapFormat(..)
  , DepthFormatSpec
  , Colormap(..)
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Request Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Depth rendering request - sent to Haskell backend
data DepthRenderRequest
  = RenderDepthFrame DepthRenderOptions
  | RenderDepthFromEngine
      { layerId :: String
      , frameNumber :: Int
      }
  | ConvertDepthFormat DepthConversionRequest
  | ApplyColormap
      { depthData :: String       -- Base64 encoded depth buffer
      , result :: DepthRenderResult
      , colormap :: Colormap
      }
  | ExportDepthSequence DepthExportSequenceRequest

derive instance Generic DepthRenderRequest _
instance Show DepthRenderRequest where show = genericShow
instance EncodeJson DepthRenderRequest where
  encodeJson = genericEncodeJson

-- | Depth format conversion request
type DepthConversionRequest =
  { depthData :: String         -- Base64 encoded depth buffer
  , result :: DepthRenderResult
  , targetFormat :: DepthMapFormat
  }

-- | Depth sequence export request
type DepthExportSequenceRequest =
  { startFrame :: Int
  , endFrame :: Int
  , width :: Int
  , height :: Int
  , format :: DepthMapFormat
  , outputDir :: String
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Request Builders
-- ────────────────────────────────────────────────────────────────────────────

-- | Create depth frame render request
mkRenderDepthRequest :: DepthRenderOptions -> DepthRenderRequest
mkRenderDepthRequest = RenderDepthFrame

-- | Create depth frame render request from engine layer
mkRenderDepthFromEngineRequest :: String -> Int -> DepthRenderRequest
mkRenderDepthFromEngineRequest layerId frameNumber =
  RenderDepthFromEngine { layerId, frameNumber }

-- | Create depth format conversion request
mkConvertDepthRequest
  :: String
  -> DepthRenderResult
  -> DepthMapFormat
  -> DepthRenderRequest
mkConvertDepthRequest depthData result targetFormat =
  ConvertDepthFormat { depthData, result, targetFormat }

-- | Create depth sequence export request
mkExportSequenceRequest
  :: { startFrame :: Int
     , endFrame :: Int
     , width :: Int
     , height :: Int
     , format :: DepthMapFormat
     , outputDir :: String
     }
  -> DepthRenderRequest
mkExportSequenceRequest = ExportDepthSequence

-- ────────────────────────────────────────────────────────────────────────────
-- Metadata
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate depth metadata for export
generateDepthMetadata
  :: DepthMapFormat
  -> Int  -- Frame count
  -> Int  -- Width
  -> Int  -- Height
  -> Number  -- Min depth
  -> Number  -- Max depth
  -> DepthMetadata
generateDepthMetadata format frameCount width height minDepth maxDepth =
  let
    spec = getFormatSpec format
  in
    { format
    , bitDepth: spec.bitDepth
    , nearClip: spec.nearClip
    , farClip: spec.farClip
    , inverted: spec.invert
    , normalized: spec.normalize
    , frameCount
    , width
    , height
    , actualRange: { min: minDepth, max: maxDepth }
    , generatedAt: ""  -- Set by backend
    , generator: "Lattice Compositor"
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Format Specifications
-- ────────────────────────────────────────────────────────────────────────────

-- | Get format specification
getFormatSpec :: DepthMapFormat -> DepthFormatSpec
getFormatSpec = case _ of
  FormatRaw ->
    { bitDepth: 32
    , nearClip: 0.1
    , farClip: 1000.0
    , invert: false
    , normalize: false
    }
  FormatMiDaS ->
    { bitDepth: 16
    , nearClip: 0.1
    , farClip: 1000.0
    , invert: true
    , normalize: true
    }
  FormatDepthAnything ->
    { bitDepth: 16
    , nearClip: 0.1
    , farClip: 100.0
    , invert: false
    , normalize: true
    }
  FormatZoeDepth ->
    { bitDepth: 16
    , nearClip: 0.1
    , farClip: 10.0
    , invert: false
    , normalize: false
    }
  FormatMarigold ->
    { bitDepth: 8
    , nearClip: 0.1
    , farClip: 100.0
    , invert: false
    , normalize: true
    }
  FormatControlNet ->
    { bitDepth: 8
    , nearClip: 0.1
    , farClip: 1000.0
    , invert: true
    , normalize: true
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert format to string
formatToString :: DepthMapFormat -> String
formatToString = case _ of
  FormatRaw -> "raw"
  FormatMiDaS -> "midas"
  FormatDepthAnything -> "depth-anything"
  FormatZoeDepth -> "zoe-depth"
  FormatMarigold -> "marigold"
  FormatControlNet -> "controlnet"

-- | Convert colormap to string
colormapToString :: Colormap -> String
colormapToString = case _ of
  ColormapGrayscale -> "grayscale"
  ColormapViridis -> "viridis"
  ColormapMagma -> "magma"
  ColormapPlasma -> "plasma"
  ColormapInferno -> "inferno"
  ColormapTurbo -> "turbo"
