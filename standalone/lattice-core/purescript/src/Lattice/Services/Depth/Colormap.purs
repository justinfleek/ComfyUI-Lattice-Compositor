{-
  Lattice.Services.Depth.Colormap - Scientific Colormaps

  Pure mathematical functions for depth visualization colormaps:
  - Viridis (default matplotlib, perceptually uniform)
  - Magma (perceptually uniform, warm)
  - Plasma (perceptually uniform, bright)
  - Inferno (perceptually uniform, high contrast)
  - Turbo (Google's rainbow alternative)

  Source: ui/src/services/export/depthRenderer.ts (lines 826-997)
-}

module Lattice.Services.Depth.Colormap
  ( RGB
  , ColormapType(..)
  -- * Interpolation
  , clamp01
  , lerpInt
  , lerpRGB
  , sampleColorArray
  -- * Colormaps
  , grayscale
  , viridis
  , magma
  , plasma
  , inferno
  , turbo
  -- * Colormap Dispatcher
  , getColor
  -- * Lookup Tables
  , viridisColors
  , magmaColors
  , plasmaColors
  , infernoColors
  , turboColors
  ) where

import Prelude

import Data.Array (index, length)
import Data.Int (floor, round, toNumber)
import Data.Maybe (fromMaybe)
import Data.Tuple.Nested (Tuple3, tuple3, get1, get2, get3)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGB color as triple of values in [0, 255].
type RGB = Tuple3 Int Int Int

-- | Colormap enum.
data ColormapType
  = Grayscale
  | Viridis
  | Magma
  | Plasma
  | Inferno
  | Turbo

derive instance eqColormapType :: Eq ColormapType

instance showColormapType :: Show ColormapType where
  show Grayscale = "Grayscale"
  show Viridis = "Viridis"
  show Magma = "Magma"
  show Plasma = "Plasma"
  show Inferno = "Inferno"
  show Turbo = "Turbo"

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1].
clamp01 :: Number -> Number
clamp01 t
  | t < 0.0   = 0.0
  | t > 1.0   = 1.0
  | otherwise = t

-- | Linear interpolation between two integers.
lerpInt :: Int -> Int -> Number -> Int
lerpInt a b t =
  let result = toNumber a + (toNumber b - toNumber a) * t
  in floor result

-- | Interpolate between two RGB colors.
lerpRGB :: RGB -> RGB -> Number -> RGB
lerpRGB c1 c2 t =
  tuple3
    (lerpInt (get1 c1) (get1 c2) t)
    (lerpInt (get2 c1) (get2 c2) t)
    (lerpInt (get3 c1) (get3 c2) t)

-- | Sample from color array with interpolation.
--   t in [0, 1], colors is the lookup table.
sampleColorArray :: Array RGB -> Number -> RGB
sampleColorArray colors t
  | length colors == 0 = tuple3 0 0 0
  | otherwise =
      let clamped = clamp01 t
          n = length colors
          idx = clamped * toNumber (n - 1)
          i = floor idx
          f = idx - toNumber i
          defaultColor = tuple3 0 0 0
      in if i >= n - 1
         then fromMaybe defaultColor (index colors (n - 1))
         else
           let c1 = fromMaybe defaultColor (index colors i)
               c2 = fromMaybe defaultColor (index colors (i + 1))
           in lerpRGB c1 c2 f

-- ────────────────────────────────────────────────────────────────────────────
-- Grayscale
-- ────────────────────────────────────────────────────────────────────────────

-- | Grayscale colormap: t → (v, v, v) where v = t * 255.
grayscale :: Number -> RGB
grayscale t =
  let v = round (clamp01 t * 255.0)
  in tuple3 v v v

-- ────────────────────────────────────────────────────────────────────────────
-- Viridis Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Viridis colormap lookup table (10 control points).
viridisColors :: Array RGB
viridisColors =
  [ tuple3 68 1 84
  , tuple3 72 40 120
  , tuple3 62 74 137
  , tuple3 49 104 142
  , tuple3 38 130 142
  , tuple3 31 158 137
  , tuple3 53 183 121
  , tuple3 109 205 89
  , tuple3 180 222 44
  , tuple3 253 231 37
  ]

-- | Viridis colormap: perceptually uniform, blue-green-yellow.
viridis :: Number -> RGB
viridis = sampleColorArray viridisColors

-- ────────────────────────────────────────────────────────────────────────────
-- Magma Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Magma colormap lookup table (9 control points).
magmaColors :: Array RGB
magmaColors =
  [ tuple3 0 0 4
  , tuple3 28 16 68
  , tuple3 79 18 123
  , tuple3 129 37 129
  , tuple3 181 54 122
  , tuple3 229 80 100
  , tuple3 251 135 97
  , tuple3 254 194 135
  , tuple3 252 253 191
  ]

-- | Magma colormap: perceptually uniform, black-red-yellow-white.
magma :: Number -> RGB
magma = sampleColorArray magmaColors

-- ────────────────────────────────────────────────────────────────────────────
-- Plasma Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Plasma colormap lookup table (9 control points).
plasmaColors :: Array RGB
plasmaColors =
  [ tuple3 13 8 135
  , tuple3 75 3 161
  , tuple3 125 3 168
  , tuple3 168 34 150
  , tuple3 203 70 121
  , tuple3 229 107 93
  , tuple3 248 148 65
  , tuple3 253 195 40
  , tuple3 240 249 33
  ]

-- | Plasma colormap: perceptually uniform, purple-orange-yellow.
plasma :: Number -> RGB
plasma = sampleColorArray plasmaColors

-- ────────────────────────────────────────────────────────────────────────────
-- Inferno Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Inferno colormap lookup table (11 control points).
infernoColors :: Array RGB
infernoColors =
  [ tuple3 0 0 4
  , tuple3 22 11 57
  , tuple3 66 10 104
  , tuple3 106 23 110
  , tuple3 147 38 103
  , tuple3 188 55 84
  , tuple3 221 81 58
  , tuple3 243 118 27
  , tuple3 252 165 10
  , tuple3 246 215 70
  , tuple3 252 255 164
  ]

-- | Inferno colormap: perceptually uniform, black-purple-red-yellow-white.
inferno :: Number -> RGB
inferno = sampleColorArray infernoColors

-- ────────────────────────────────────────────────────────────────────────────
-- Turbo Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Turbo colormap lookup table (13 control points).
turboColors :: Array RGB
turboColors =
  [ tuple3 48 18 59
  , tuple3 70 68 172
  , tuple3 62 121 229
  , tuple3 38 170 225
  , tuple3 31 212 182
  , tuple3 76 237 123
  , tuple3 149 249 67
  , tuple3 212 241 31
  , tuple3 253 207 37
  , tuple3 252 150 38
  , tuple3 239 85 33
  , tuple3 205 33 28
  , tuple3 122 4 3
  ]

-- | Turbo colormap: Google's improved rainbow, perceptually smoother.
turbo :: Number -> RGB
turbo = sampleColorArray turboColors

-- ────────────────────────────────────────────────────────────────────────────
-- Colormap Dispatcher
-- ────────────────────────────────────────────────────────────────────────────

-- | Get color from specified colormap at position t ∈ [0, 1].
getColor :: ColormapType -> Number -> RGB
getColor Grayscale = grayscale
getColor Viridis = viridis
getColor Magma = magma
getColor Plasma = plasma
getColor Inferno = inferno
getColor Turbo = turbo
