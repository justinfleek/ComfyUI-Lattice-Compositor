-- | Lattice.Services.Export.DepthRenderer.Renderer - Depth rendering FFI
-- |
-- | FFI bindings for depth map rendering using browser APIs.
-- |
-- | Source: ui/src/services/export/depthRenderer.ts

module Lattice.Services.Export.DepthRenderer.Renderer
  ( -- * Opaque Handles
    DepthBufferHandle
  , ImageDataHandle
    -- * Rendering
  , renderDepthFrame
  , renderDepthFrameFromEngine
    -- * Format Conversion
  , convertDepthToFormat
  , depthToImageData
  , applyColormapToBuffer
    -- * Export
  , exportDepthSequence
    -- * Metadata
  , generateDepthMetadata
    -- * Utilities
  , getFormatSpec
  ) where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Maybe (Maybe(..))

import Lattice.Services.Export.DepthRenderer.Types
  ( DepthRenderOptions
  , DepthRenderResult
  , DepthMetadata
  , DepthMapFormat(..)
  , DepthFormatSpec
  , Colormap(..)
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Opaque Handles
-- ────────────────────────────────────────────────────────────────────────────

-- | Opaque handle to Float32Array depth buffer
foreign import data DepthBufferHandle :: Type

-- | Opaque handle to ImageData
foreign import data ImageDataHandle :: Type

-- ────────────────────────────────────────────────────────────────────────────
-- Rendering
-- ────────────────────────────────────────────────────────────────────────────

-- | Render depth frame from layer data
-- | Note: Actual implementation requires browser engine context
foreign import renderDepthFrameImpl
  :: DepthRenderOptions
  -> Effect { result :: DepthRenderResult, buffer :: DepthBufferHandle }

renderDepthFrame
  :: DepthRenderOptions
  -> Effect { result :: DepthRenderResult, buffer :: DepthBufferHandle }
renderDepthFrame = renderDepthFrameImpl

-- | Render depth frame using the Lattice engine
foreign import renderDepthFrameFromEngineImpl
  :: String  -- ^ Layer ID
  -> Int     -- ^ Frame number
  -> Effect { result :: DepthRenderResult, buffer :: DepthBufferHandle }

renderDepthFrameFromEngine
  :: String
  -> Int
  -> Effect { result :: DepthRenderResult, buffer :: DepthBufferHandle }
renderDepthFrameFromEngine = renderDepthFrameFromEngineImpl

-- ────────────────────────────────────────────────────────────────────────────
-- Format Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert depth buffer to export format
foreign import convertDepthToFormatImpl
  :: DepthBufferHandle
  -> DepthRenderResult
  -> String  -- ^ Format name
  -> Effect DepthBufferHandle

convertDepthToFormat
  :: DepthBufferHandle
  -> DepthRenderResult
  -> DepthMapFormat
  -> Effect DepthBufferHandle
convertDepthToFormat buffer result format =
  convertDepthToFormatImpl buffer result (formatToString format)

-- | Convert depth buffer to ImageData for display
foreign import depthToImageDataImpl
  :: DepthBufferHandle
  -> DepthRenderResult
  -> Effect ImageDataHandle

depthToImageData
  :: DepthBufferHandle
  -> DepthRenderResult
  -> Effect ImageDataHandle
depthToImageData = depthToImageDataImpl

-- | Apply colormap to depth buffer
foreign import applyColormapToBufferImpl
  :: DepthBufferHandle
  -> DepthRenderResult
  -> String  -- ^ Colormap name
  -> Effect ImageDataHandle

applyColormapToBuffer
  :: DepthBufferHandle
  -> DepthRenderResult
  -> Colormap
  -> Effect ImageDataHandle
applyColormapToBuffer buffer result colormap =
  applyColormapToBufferImpl buffer result (colormapToString colormap)

-- ────────────────────────────────────────────────────────────────────────────
-- Export
-- ────────────────────────────────────────────────────────────────────────────

-- | Export depth sequence as PNG files
foreign import exportDepthSequenceImpl
  :: { startFrame :: Int
     , endFrame :: Int
     , width :: Int
     , height :: Int
     , format :: String
     , outputDir :: String
     }
  -> EffectFnAff (Array String)

exportDepthSequence
  :: { startFrame :: Int
     , endFrame :: Int
     , width :: Int
     , height :: Int
     , format :: DepthMapFormat
     , outputDir :: String
     }
  -> Aff (Array String)
exportDepthSequence opts =
  fromEffectFnAff (exportDepthSequenceImpl
    { startFrame: opts.startFrame
    , endFrame: opts.endFrame
    , width: opts.width
    , height: opts.height
    , format: formatToString opts.format
    , outputDir: opts.outputDir
    })

-- ────────────────────────────────────────────────────────────────────────────
-- Metadata
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate depth metadata for export
generateDepthMetadata
  :: DepthMapFormat
  -> Int  -- ^ Frame count
  -> Int  -- ^ Width
  -> Int  -- ^ Height
  -> Number  -- ^ Min depth
  -> Number  -- ^ Max depth
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
    , generatedAt: ""  -- Set by FFI
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
