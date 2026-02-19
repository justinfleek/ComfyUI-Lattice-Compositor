-- | Lattice.Services.Export.DepthRenderer.Colormaps - Colormap functions
-- |
-- | Pure colormap implementations for depth visualization.
-- | Supports viridis, plasma, magma, inferno, and turbo colormaps.
-- |
-- | Source: ui/src/services/export/depthRenderer.ts

module Lattice.Services.Export.DepthRenderer.Colormaps
  ( -- * Colormap Application
    getColormapColor
  , applyColormapToValue
    -- * Individual Colormaps
  , viridisColormap
  , magmaColormap
  , plasmaColormap
  , infernoColormap
  , turboColormap
  , grayscaleColormap
    -- * Types
  , RGB
  ) where

import Prelude
import Data.Array ((!!), length)
import Data.Int (floor, round, toNumber)
import Data.Maybe (fromMaybe)

import Lattice.Services.Export.DepthRenderer.Types (Colormap(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGB color as tuple
type RGB = { r :: Int, g :: Int, b :: Int }

-- ────────────────────────────────────────────────────────────────────────────
-- Colormap Application
-- ────────────────────────────────────────────────────────────────────────────

-- | Get color from colormap at normalized position t ∈ [0, 1]
getColormapColor :: Number -> Colormap -> RGB
getColormapColor t colormap =
  let
    clampedT = max 0.0 (min 1.0 t)
  in
    case colormap of
      ColormapGrayscale -> grayscaleColormap clampedT
      ColormapViridis -> viridisColormap clampedT
      ColormapMagma -> magmaColormap clampedT
      ColormapPlasma -> plasmaColormap clampedT
      ColormapInferno -> infernoColormap clampedT
      ColormapTurbo -> turboColormap clampedT

-- | Apply colormap to a single value
applyColormapToValue :: Number -> Number -> Number -> Colormap -> RGB
applyColormapToValue minVal maxVal value colormap =
  let
    range = maxVal - minVal
    safeRange = if range > 0.0 then range else 1.0
    normalized = (value - minVal) / safeRange
    clampedT = max 0.0 (min 1.0 normalized)
  in
    getColormapColor clampedT colormap

-- ────────────────────────────────────────────────────────────────────────────
-- Individual Colormaps
-- ────────────────────────────────────────────────────────────────────────────

-- | Grayscale colormap
grayscaleColormap :: Number -> RGB
grayscaleColormap t =
  let
    v = round (t * 255.0)
    clamped = max 0 (min 255 v)
  in
    { r: clamped, g: clamped, b: clamped }

-- | Viridis colormap (perceptually uniform, colorblind-friendly)
viridisColormap :: Number -> RGB
viridisColormap = interpolateColormap viridisColors

-- | Magma colormap
magmaColormap :: Number -> RGB
magmaColormap = interpolateColormap magmaColors

-- | Plasma colormap
plasmaColormap :: Number -> RGB
plasmaColormap = interpolateColormap plasmaColors

-- | Inferno colormap (perceptually uniform, good for depth)
infernoColormap :: Number -> RGB
infernoColormap = interpolateColormap infernoColors

-- | Turbo colormap (Google's rainbow alternative)
turboColormap :: Number -> RGB
turboColormap = interpolateColormap turboColors

-- ────────────────────────────────────────────────────────────────────────────
-- Colormap Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Interpolate between colors in a colormap
interpolateColormap :: Array RGB -> Number -> RGB
interpolateColormap colors t =
  let
    n = length colors
    idx = t * toNumber (n - 1)
    i = floor idx
    f = idx - toNumber i

    -- Get colors with bounds checking
    c0 = fromMaybe { r: 0, g: 0, b: 0 } (colors !! i)
    c1 = fromMaybe c0 (colors !! (i + 1))
  in
    if i >= n - 1 then
      fromMaybe { r: 0, g: 0, b: 0 } (colors !! (n - 1))
    else
      { r: round (toNumber c0.r + (toNumber c1.r - toNumber c0.r) * f)
      , g: round (toNumber c0.g + (toNumber c1.g - toNumber c0.g) * f)
      , b: round (toNumber c0.b + (toNumber c1.b - toNumber c0.b) * f)
      }

-- ────────────────────────────────────────────────────────────────────────────
-- Colormap Data
-- ────────────────────────────────────────────────────────────────────────────

viridisColors :: Array RGB
viridisColors =
  [ { r: 68, g: 1, b: 84 }
  , { r: 72, g: 40, b: 120 }
  , { r: 62, g: 74, b: 137 }
  , { r: 49, g: 104, b: 142 }
  , { r: 38, g: 130, b: 142 }
  , { r: 31, g: 158, b: 137 }
  , { r: 53, g: 183, b: 121 }
  , { r: 109, g: 205, b: 89 }
  , { r: 180, g: 222, b: 44 }
  , { r: 253, g: 231, b: 37 }
  ]

magmaColors :: Array RGB
magmaColors =
  [ { r: 0, g: 0, b: 4 }
  , { r: 28, g: 16, b: 68 }
  , { r: 79, g: 18, b: 123 }
  , { r: 129, g: 37, b: 129 }
  , { r: 181, g: 54, b: 122 }
  , { r: 229, g: 80, b: 100 }
  , { r: 251, g: 135, b: 97 }
  , { r: 254, g: 194, b: 135 }
  , { r: 252, g: 253, b: 191 }
  ]

plasmaColors :: Array RGB
plasmaColors =
  [ { r: 13, g: 8, b: 135 }
  , { r: 75, g: 3, b: 161 }
  , { r: 125, g: 3, b: 168 }
  , { r: 168, g: 34, b: 150 }
  , { r: 203, g: 70, b: 121 }
  , { r: 229, g: 107, b: 93 }
  , { r: 248, g: 148, b: 65 }
  , { r: 253, g: 195, b: 40 }
  , { r: 240, g: 249, b: 33 }
  ]

infernoColors :: Array RGB
infernoColors =
  [ { r: 0, g: 0, b: 4 }
  , { r: 22, g: 11, b: 57 }
  , { r: 66, g: 10, b: 104 }
  , { r: 106, g: 23, b: 110 }
  , { r: 147, g: 38, b: 103 }
  , { r: 188, g: 55, b: 84 }
  , { r: 221, g: 81, b: 58 }
  , { r: 243, g: 118, b: 27 }
  , { r: 252, g: 165, b: 10 }
  , { r: 246, g: 215, b: 70 }
  , { r: 252, g: 255, b: 164 }
  ]

turboColors :: Array RGB
turboColors =
  [ { r: 48, g: 18, b: 59 }
  , { r: 70, g: 68, b: 172 }
  , { r: 62, g: 121, b: 229 }
  , { r: 38, g: 170, b: 225 }
  , { r: 31, g: 212, b: 182 }
  , { r: 76, g: 237, b: 123 }
  , { r: 149, g: 249, b: 67 }
  , { r: 212, g: 241, b: 31 }
  , { r: 253, g: 207, b: 37 }
  , { r: 252, g: 150, b: 38 }
  , { r: 239, g: 85, b: 33 }
  , { r: 205, g: 33, b: 28 }
  , { r: 122, g: 4, b: 3 }
  ]
