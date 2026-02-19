{-|
Module      : Lattice.Services.Depth.FormatConversion
Description : Depth format conversion and colormap application
Copyright   : (c) Lattice Compositor, 2026
License     : MIT

Pure functions for converting depth buffers between formats:
- Bit depth conversion (8/16/32-bit)
- Normalization and inversion
- Image data generation (RGBA)
- Colormap application for visualization

Source: ui/src/services/export/depthRenderer.ts (lines 600-997)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Depth.FormatConversion
  ( -- * Types
    DepthMapFormat(..)
  , DepthFormatSpec(..)
  , RGB(..)
  , RGBA(..)
  , Colormap(..)
    -- * Format Specifications
  , getFormatSpec
    -- * Normalization
  , clamp01
  , normalizeDepth
  , normalizeMetricDepth
  , invertDepth
    -- * Bit Depth Conversion
  , to8bit
  , to16bit
  , uint16To8bit
  , float32To8bit
    -- * Depth to Format Conversion
  , convertDepthValue
  , depthTo8bit
  , depthTo16bit
    -- * Image Data Generation
  , depthToGrayscalePixel
  , rgbToRGBA
  , pixelIndex
    -- * Colormap Colors
  , viridisColors
  , magmaColors
  , plasmaColors
  , infernoColors
  , turboColors
    -- * Colormap Interpolation
  , lerpWord8
  , lerpRGB
  , sampleColormap
    -- * Colormap Selection
  , getColormapColor
  , parseColormap
    -- * AI Model Convention
  , invertForAIVisualization
  ) where

import Data.Word (Word8, Word16)
import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Supported depth map formats.
data DepthMapFormat
  = FormatRaw           -- ^ Float32 raw depth
  | FormatMidas         -- ^ MiDaS format (16-bit, inverted, normalized)
  | FormatDepthAnything -- ^ Depth Anything format (16-bit, inverted, normalized)
  | FormatZoeDepth      -- ^ ZoeDepth format (16-bit, metric)
  | FormatMarigold      -- ^ Marigold format (16-bit, normalized)
  | FormatGrayscale8    -- ^ 8-bit grayscale
  | FormatGrayscale16   -- ^ 16-bit grayscale
  deriving (Show, Eq)

-- | Depth format specification.
data DepthFormatSpec = DepthFormatSpec
  { dfsbitDepth  :: Int      -- ^ 8, 16, or 32
  , dfsNearClip  :: Double   -- ^ Near clipping plane
  , dfsFarClip   :: Double   -- ^ Far clipping plane
  , dfsNormalize :: Bool     -- ^ Normalize to [0, 1] range
  , dfsInvert    :: Bool     -- ^ Invert (near=bright, far=dark)
  } deriving (Show, Eq)

-- | RGB color tuple.
data RGB = RGB
  { rgbR :: Word8
  , rgbG :: Word8
  , rgbB :: Word8
  } deriving (Show, Eq)

-- | RGBA pixel.
data RGBA = RGBA
  { rgbaR :: Word8
  , rgbaG :: Word8
  , rgbaB :: Word8
  , rgbaA :: Word8
  } deriving (Show, Eq)

-- | Supported colormaps.
data Colormap
  = ColormapGrayscale
  | ColormapViridis
  | ColormapMagma
  | ColormapPlasma
  | ColormapInferno
  | ColormapTurbo
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Format Specifications
--------------------------------------------------------------------------------

-- | Get format specification for depth format.
getFormatSpec :: DepthMapFormat -> DepthFormatSpec
getFormatSpec format = case format of
  FormatRaw ->
    DepthFormatSpec 32 0.1 100.0 False False
  FormatMidas ->
    DepthFormatSpec 16 0.1 100.0 True True
  FormatDepthAnything ->
    DepthFormatSpec 16 0.1 100.0 True True
  FormatZoeDepth ->
    DepthFormatSpec 16 0.001 80.0 False False
  FormatMarigold ->
    DepthFormatSpec 16 0.1 100.0 True False
  FormatGrayscale8 ->
    DepthFormatSpec 8 0.1 100.0 True False
  FormatGrayscale16 ->
    DepthFormatSpec 16 0.1 100.0 True False

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1] range.
clamp01 :: Double -> Double
clamp01 value = max 0.0 (min 1.0 value)

-- | Normalize depth value to [0, 1] range based on min/max.
normalizeDepth :: Double -> Double -> Double -> Double
normalizeDepth depth minDepth maxDepth =
  let range = maxDepth - minDepth
      safeRange = if range > 0.0 then range else 1.0
  in clamp01 ((depth - minDepth) / safeRange)

-- | Normalize depth for metric format (scale to far clip).
normalizeMetricDepth :: Double -> Double -> Double
normalizeMetricDepth depth farClip = clamp01 (depth / farClip)

-- | Invert normalized depth value.
invertDepth :: Double -> Double
invertDepth normalized = 1.0 - normalized

--------------------------------------------------------------------------------
-- Bit Depth Conversion
--------------------------------------------------------------------------------

-- | Convert normalized [0, 1] to 8-bit [0, 255].
to8bit :: Double -> Word8
to8bit normalized =
  let scaled = normalized * 255.0
      clamped = max 0.0 (min 255.0 scaled)
  in round clamped

-- | Convert normalized [0, 1] to 16-bit [0, 65535].
to16bit :: Double -> Word16
to16bit normalized =
  let scaled = normalized * 65535.0
      clamped = max 0.0 (min 65535.0 scaled)
  in round clamped

-- | Convert 16-bit to 8-bit (for display).
uint16To8bit :: Word16 -> Word8
uint16To8bit value = fromIntegral (value `div` 256)

-- | Convert Float32 depth (assumed 0-1) to 8-bit.
float32To8bit :: Double -> Word8
float32To8bit = to8bit . clamp01

--------------------------------------------------------------------------------
-- Depth to Format Conversion
--------------------------------------------------------------------------------

-- | Convert single depth value based on format specification.
convertDepthValue :: Double -> Double -> Double -> DepthFormatSpec -> Double
convertDepthValue depth minDepth maxDepth spec =
  let normalized = if dfsNormalize spec
                   then normalizeDepth depth minDepth maxDepth
                   else normalizeMetricDepth depth (dfsFarClip spec)
  in if dfsInvert spec then invertDepth normalized else normalized

-- | Convert depth value to 8-bit output.
depthTo8bit :: Double -> Double -> Double -> DepthFormatSpec -> Word8
depthTo8bit depth minDepth maxDepth spec =
  let normalized = convertDepthValue depth minDepth maxDepth spec
  in to8bit normalized

-- | Convert depth value to 16-bit output.
depthTo16bit :: Double -> Double -> Double -> DepthFormatSpec -> Word16
depthTo16bit depth minDepth maxDepth spec =
  let normalized = convertDepthValue depth minDepth maxDepth spec
  in to16bit normalized

--------------------------------------------------------------------------------
-- Image Data Generation
--------------------------------------------------------------------------------

-- | Create grayscale RGBA pixel from depth value.
depthToGrayscalePixel :: Word8 -> RGBA
depthToGrayscalePixel value = RGBA value value value 255

-- | Create RGBA pixel from RGB and alpha.
rgbToRGBA :: RGB -> Word8 -> RGBA
rgbToRGBA rgb alpha = RGBA (rgbR rgb) (rgbG rgb) (rgbB rgb) alpha

-- | Calculate pixel index in RGBA image data.
pixelIndex :: Int -> Int
pixelIndex i = i * 4

--------------------------------------------------------------------------------
-- Colormap Colors
--------------------------------------------------------------------------------

-- | Viridis colormap lookup table (10 colors).
viridisColors :: Vector RGB
viridisColors = V.fromList
  [ RGB 68  1   84
  , RGB 72  40  120
  , RGB 62  74  137
  , RGB 49  104 142
  , RGB 38  130 142
  , RGB 31  158 137
  , RGB 53  183 121
  , RGB 109 205 89
  , RGB 180 222 44
  , RGB 253 231 37
  ]

-- | Magma colormap lookup table (9 colors).
magmaColors :: Vector RGB
magmaColors = V.fromList
  [ RGB 0   0   4
  , RGB 28  16  68
  , RGB 79  18  123
  , RGB 129 37  129
  , RGB 181 54  122
  , RGB 229 80  100
  , RGB 251 135 97
  , RGB 254 194 135
  , RGB 252 253 191
  ]

-- | Plasma colormap lookup table (9 colors).
plasmaColors :: Vector RGB
plasmaColors = V.fromList
  [ RGB 13  8   135
  , RGB 75  3   161
  , RGB 125 3   168
  , RGB 168 34  150
  , RGB 203 70  121
  , RGB 229 107 93
  , RGB 248 148 65
  , RGB 253 195 40
  , RGB 240 249 33
  ]

-- | Inferno colormap lookup table (11 colors).
infernoColors :: Vector RGB
infernoColors = V.fromList
  [ RGB 0   0   4
  , RGB 22  11  57
  , RGB 66  10  104
  , RGB 106 23  110
  , RGB 147 38  103
  , RGB 188 55  84
  , RGB 221 81  58
  , RGB 243 118 27
  , RGB 252 165 10
  , RGB 246 215 70
  , RGB 252 255 164
  ]

-- | Turbo colormap lookup table (13 colors).
turboColors :: Vector RGB
turboColors = V.fromList
  [ RGB 48  18  59
  , RGB 70  68  172
  , RGB 62  121 229
  , RGB 38  170 225
  , RGB 31  212 182
  , RGB 76  237 123
  , RGB 149 249 67
  , RGB 212 241 31
  , RGB 253 207 37
  , RGB 252 150 38
  , RGB 239 85  33
  , RGB 205 33  28
  , RGB 122 4   3
  ]

--------------------------------------------------------------------------------
-- Colormap Interpolation
--------------------------------------------------------------------------------

-- | Linearly interpolate between two Word8 values.
lerpWord8 :: Word8 -> Word8 -> Double -> Word8
lerpWord8 a b t =
  let result = fromIntegral a + (fromIntegral b - fromIntegral a) * t
      clamped = max 0.0 (min 255.0 result)
  in round clamped

-- | Linearly interpolate between two RGB colors.
lerpRGB :: RGB -> RGB -> Double -> RGB
lerpRGB c1 c2 t = RGB
  { rgbR = lerpWord8 (rgbR c1) (rgbR c2) t
  , rgbG = lerpWord8 (rgbG c1) (rgbG c2) t
  , rgbB = lerpWord8 (rgbB c1) (rgbB c2) t
  }

-- | Sample color from colormap vector with interpolation.
sampleColormap :: Vector RGB -> Double -> RGB
sampleColormap colors t
  | V.null colors = RGB 0 0 0
  | otherwise =
      let clamped = clamp01 t
          n = V.length colors
          idx = clamped * fromIntegral (n - 1)
          i = floor idx
          f = idx - fromIntegral i
      in if i >= n - 1
         then colors V.! (n - 1)
         else lerpRGB (colors V.! i) (colors V.! (i + 1)) f

--------------------------------------------------------------------------------
-- Colormap Selection
--------------------------------------------------------------------------------

-- | Get color from colormap at normalized position.
getColormapColor :: Double -> Colormap -> RGB
getColormapColor t cmap = case cmap of
  ColormapGrayscale ->
    let v = to8bit (clamp01 t)
    in RGB v v v
  ColormapViridis -> sampleColormap viridisColors t
  ColormapMagma   -> sampleColormap magmaColors t
  ColormapPlasma  -> sampleColormap plasmaColors t
  ColormapInferno -> sampleColormap infernoColors t
  ColormapTurbo   -> sampleColormap turboColors t

-- | Parse colormap from string.
parseColormap :: String -> Colormap
parseColormap s = case s of
  "viridis" -> ColormapViridis
  "magma"   -> ColormapMagma
  "plasma"  -> ColormapPlasma
  "inferno" -> ColormapInferno
  "turbo"   -> ColormapTurbo
  _         -> ColormapGrayscale

--------------------------------------------------------------------------------
-- AI Model Depth Convention
--------------------------------------------------------------------------------

-- | AI models (MiDaS, Depth-Anything) expect near=bright, far=dark.
-- This inverts the normalized depth for proper visualization.
invertForAIVisualization :: Double -> Double
invertForAIVisualization normalized = 1.0 - clamp01 normalized
