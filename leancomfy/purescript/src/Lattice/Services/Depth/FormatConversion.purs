-- | Lattice.Services.Depth.FormatConversion - Depth Format Conversion
-- |
-- | Pure functions for converting depth buffers between formats:
-- | - Bit depth conversion (8/16/32-bit)
-- | - Normalization and inversion
-- | - Image data generation (RGBA)
-- | - Colormap application for visualization
-- |
-- | Source: ui/src/services/export/depthRenderer.ts (lines 600-997)

module Lattice.Services.Depth.FormatConversion
  ( DepthMapFormat(..)
  , DepthFormatSpec
  , RGB
  , RGBA
  , Colormap(..)
  , getFormatSpec
  , clamp01
  , normalizeDepth
  , normalizeMetricDepth
  , invertDepth
  , to8bit
  , to16bit
  , uint16To8bit
  , float32To8bit
  , convertDepthValue
  , depthTo8bit
  , depthTo16bit
  , depthToGrayscalePixel
  , rgbToRGBA
  , pixelIndex
  , viridisColors
  , magmaColors
  , plasmaColors
  , infernoColors
  , turboColors
  , lerpInt
  , lerpRGB
  , sampleColormap
  , getColormapColor
  , parseColormap
  , invertForAIVisualization
  ) where

import Prelude

import Data.Array (length, (!!))
import Data.Int (floor, round, toNumber)
import Data.Maybe (fromMaybe)
import Math (max, min)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Supported depth map formats.
data DepthMapFormat
  = FormatRaw
  | FormatMidas
  | FormatDepthAnything
  | FormatZoeDepth
  | FormatMarigold
  | FormatGrayscale8
  | FormatGrayscale16

derive instance eqDepthMapFormat :: Eq DepthMapFormat

-- | Depth format specification.
type DepthFormatSpec =
  { bitDepth :: Int
  , nearClip :: Number
  , farClip :: Number
  , normalize :: Boolean
  , invert :: Boolean
  }

-- | RGB color tuple.
type RGB =
  { r :: Int
  , g :: Int
  , b :: Int
  }

-- | RGBA pixel.
type RGBA =
  { r :: Int
  , g :: Int
  , b :: Int
  , a :: Int
  }

-- | Supported colormaps.
data Colormap
  = ColormapGrayscale
  | ColormapViridis
  | ColormapMagma
  | ColormapPlasma
  | ColormapInferno
  | ColormapTurbo

derive instance eqColormap :: Eq Colormap

--------------------------------------------------------------------------------
-- Format Specifications
--------------------------------------------------------------------------------

-- | Get format specification for depth format.
getFormatSpec :: DepthMapFormat -> DepthFormatSpec
getFormatSpec format = case format of
  FormatRaw ->
    { bitDepth: 32, nearClip: 0.1, farClip: 100.0, normalize: false, invert: false }
  FormatMidas ->
    { bitDepth: 16, nearClip: 0.1, farClip: 100.0, normalize: true, invert: true }
  FormatDepthAnything ->
    { bitDepth: 16, nearClip: 0.1, farClip: 100.0, normalize: true, invert: true }
  FormatZoeDepth ->
    { bitDepth: 16, nearClip: 0.001, farClip: 80.0, normalize: false, invert: false }
  FormatMarigold ->
    { bitDepth: 16, nearClip: 0.1, farClip: 100.0, normalize: true, invert: false }
  FormatGrayscale8 ->
    { bitDepth: 8, nearClip: 0.1, farClip: 100.0, normalize: true, invert: false }
  FormatGrayscale16 ->
    { bitDepth: 16, nearClip: 0.1, farClip: 100.0, normalize: true, invert: false }

--------------------------------------------------------------------------------
-- Normalization
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1] range.
clamp01 :: Number -> Number
clamp01 value = max 0.0 (min 1.0 value)

-- | Normalize depth value to [0, 1] range based on min/max.
normalizeDepth :: Number -> Number -> Number -> Number
normalizeDepth depth minDepth maxDepth =
  let range = maxDepth - minDepth
      safeRange = if range > 0.0 then range else 1.0
  in clamp01 ((depth - minDepth) / safeRange)

-- | Normalize depth for metric format (scale to far clip).
normalizeMetricDepth :: Number -> Number -> Number
normalizeMetricDepth depth farClip = clamp01 (depth / farClip)

-- | Invert normalized depth value.
invertDepth :: Number -> Number
invertDepth normalized = 1.0 - normalized

--------------------------------------------------------------------------------
-- Bit Depth Conversion
--------------------------------------------------------------------------------

-- | Convert normalized [0, 1] to 8-bit [0, 255].
to8bit :: Number -> Int
to8bit normalized =
  let scaled = normalized * 255.0
      clamped = max 0.0 (min 255.0 scaled)
  in round clamped

-- | Convert normalized [0, 1] to 16-bit [0, 65535].
to16bit :: Number -> Int
to16bit normalized =
  let scaled = normalized * 65535.0
      clamped = max 0.0 (min 65535.0 scaled)
  in round clamped

-- | Convert 16-bit to 8-bit (for display).
uint16To8bit :: Int -> Int
uint16To8bit value = value / 256

-- | Convert Float32 depth (assumed 0-1) to 8-bit.
float32To8bit :: Number -> Int
float32To8bit = to8bit <<< clamp01

--------------------------------------------------------------------------------
-- Depth to Format Conversion
--------------------------------------------------------------------------------

-- | Convert single depth value based on format specification.
convertDepthValue :: Number -> Number -> Number -> DepthFormatSpec -> Number
convertDepthValue depth minDepth maxDepth spec =
  let normalized = if spec.normalize
                   then normalizeDepth depth minDepth maxDepth
                   else normalizeMetricDepth depth spec.farClip
  in if spec.invert then invertDepth normalized else normalized

-- | Convert depth value to 8-bit output.
depthTo8bit :: Number -> Number -> Number -> DepthFormatSpec -> Int
depthTo8bit depth minDepth maxDepth spec =
  let normalized = convertDepthValue depth minDepth maxDepth spec
  in to8bit normalized

-- | Convert depth value to 16-bit output.
depthTo16bit :: Number -> Number -> Number -> DepthFormatSpec -> Int
depthTo16bit depth minDepth maxDepth spec =
  let normalized = convertDepthValue depth minDepth maxDepth spec
  in to16bit normalized

--------------------------------------------------------------------------------
-- Image Data Generation
--------------------------------------------------------------------------------

-- | Create grayscale RGBA pixel from depth value.
depthToGrayscalePixel :: Int -> RGBA
depthToGrayscalePixel value = { r: value, g: value, b: value, a: 255 }

-- | Create RGBA pixel from RGB and alpha.
rgbToRGBA :: RGB -> Int -> RGBA
rgbToRGBA rgb alpha = { r: rgb.r, g: rgb.g, b: rgb.b, a: alpha }

-- | Calculate pixel index in RGBA image data.
pixelIndex :: Int -> Int
pixelIndex i = i * 4

--------------------------------------------------------------------------------
-- Colormap Colors
--------------------------------------------------------------------------------

-- | Viridis colormap lookup table (10 colors).
viridisColors :: Array RGB
viridisColors =
  [ { r: 68,  g: 1,   b: 84  }
  , { r: 72,  g: 40,  b: 120 }
  , { r: 62,  g: 74,  b: 137 }
  , { r: 49,  g: 104, b: 142 }
  , { r: 38,  g: 130, b: 142 }
  , { r: 31,  g: 158, b: 137 }
  , { r: 53,  g: 183, b: 121 }
  , { r: 109, g: 205, b: 89  }
  , { r: 180, g: 222, b: 44  }
  , { r: 253, g: 231, b: 37  }
  ]

-- | Magma colormap lookup table (9 colors).
magmaColors :: Array RGB
magmaColors =
  [ { r: 0,   g: 0,   b: 4   }
  , { r: 28,  g: 16,  b: 68  }
  , { r: 79,  g: 18,  b: 123 }
  , { r: 129, g: 37,  b: 129 }
  , { r: 181, g: 54,  b: 122 }
  , { r: 229, g: 80,  b: 100 }
  , { r: 251, g: 135, b: 97  }
  , { r: 254, g: 194, b: 135 }
  , { r: 252, g: 253, b: 191 }
  ]

-- | Plasma colormap lookup table (9 colors).
plasmaColors :: Array RGB
plasmaColors =
  [ { r: 13,  g: 8,   b: 135 }
  , { r: 75,  g: 3,   b: 161 }
  , { r: 125, g: 3,   b: 168 }
  , { r: 168, g: 34,  b: 150 }
  , { r: 203, g: 70,  b: 121 }
  , { r: 229, g: 107, b: 93  }
  , { r: 248, g: 148, b: 65  }
  , { r: 253, g: 195, b: 40  }
  , { r: 240, g: 249, b: 33  }
  ]

-- | Inferno colormap lookup table (11 colors).
infernoColors :: Array RGB
infernoColors =
  [ { r: 0,   g: 0,   b: 4   }
  , { r: 22,  g: 11,  b: 57  }
  , { r: 66,  g: 10,  b: 104 }
  , { r: 106, g: 23,  b: 110 }
  , { r: 147, g: 38,  b: 103 }
  , { r: 188, g: 55,  b: 84  }
  , { r: 221, g: 81,  b: 58  }
  , { r: 243, g: 118, b: 27  }
  , { r: 252, g: 165, b: 10  }
  , { r: 246, g: 215, b: 70  }
  , { r: 252, g: 255, b: 164 }
  ]

-- | Turbo colormap lookup table (13 colors).
turboColors :: Array RGB
turboColors =
  [ { r: 48,  g: 18,  b: 59  }
  , { r: 70,  g: 68,  b: 172 }
  , { r: 62,  g: 121, b: 229 }
  , { r: 38,  g: 170, b: 225 }
  , { r: 31,  g: 212, b: 182 }
  , { r: 76,  g: 237, b: 123 }
  , { r: 149, g: 249, b: 67  }
  , { r: 212, g: 241, b: 31  }
  , { r: 253, g: 207, b: 37  }
  , { r: 252, g: 150, b: 38  }
  , { r: 239, g: 85,  b: 33  }
  , { r: 205, g: 33,  b: 28  }
  , { r: 122, g: 4,   b: 3   }
  ]

--------------------------------------------------------------------------------
-- Colormap Interpolation
--------------------------------------------------------------------------------

-- | Linearly interpolate between two Int values.
lerpInt :: Int -> Int -> Number -> Int
lerpInt a b t =
  let result = toNumber a + (toNumber b - toNumber a) * t
      clamped = max 0.0 (min 255.0 result)
  in round clamped

-- | Linearly interpolate between two RGB colors.
lerpRGB :: RGB -> RGB -> Number -> RGB
lerpRGB c1 c2 t =
  { r: lerpInt c1.r c2.r t
  , g: lerpInt c1.g c2.g t
  , b: lerpInt c1.b c2.b t
  }

-- | Sample color from colormap array with interpolation.
sampleColormap :: Array RGB -> Number -> RGB
sampleColormap colors t
  | length colors == 0 = { r: 0, g: 0, b: 0 }
  | otherwise =
      let clamped = clamp01 t
          n = length colors
          idx = clamped * toNumber (n - 1)
          i = floor idx
          f = idx - toNumber i
          c1 = fromMaybe { r: 0, g: 0, b: 0 } (colors !! i)
          c2 = fromMaybe c1 (colors !! (i + 1))
      in if i >= n - 1
         then fromMaybe { r: 0, g: 0, b: 0 } (colors !! (n - 1))
         else lerpRGB c1 c2 f

--------------------------------------------------------------------------------
-- Colormap Selection
--------------------------------------------------------------------------------

-- | Get color from colormap at normalized position.
getColormapColor :: Number -> Colormap -> RGB
getColormapColor t cmap = case cmap of
  ColormapGrayscale ->
    let v = to8bit (clamp01 t)
    in { r: v, g: v, b: v }
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
-- | This inverts the normalized depth for proper visualization.
invertForAIVisualization :: Number -> Number
invertForAIVisualization normalized = 1.0 - clamp01 normalized
