{-# LANGUAGE Strict #-}
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
  ( -- * Types
    RGB
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

import Data.Vector (Vector)
import qualified Data.Vector as V

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGB color as triple of values in [0, 255].
type RGB = (Int, Int, Int)

-- | Colormap enum.
data ColormapType
  = Grayscale
  | Viridis
  | Magma
  | Plasma
  | Inferno
  | Turbo
  deriving (Show, Eq, Enum, Bounded)

-- ────────────────────────────────────────────────────────────────────────────
-- Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1].
clamp01 :: Double -> Double
clamp01 t
  | t < 0.0   = 0.0
  | t > 1.0   = 1.0
  | otherwise = t

-- | Linear interpolation between two integers.
lerpInt :: Int -> Int -> Double -> Int
lerpInt a b t =
  let result = fromIntegral a + (fromIntegral b - fromIntegral a) * t
  in floor result

-- | Interpolate between two RGB colors.
lerpRGB :: RGB -> RGB -> Double -> RGB
lerpRGB (r1, g1, b1) (r2, g2, b2) t =
  (lerpInt r1 r2 t, lerpInt g1 g2 t, lerpInt b1 b2 t)

-- | Sample from color array with interpolation.
--   t in [0, 1], colors is the lookup table.
sampleColorArray :: Vector RGB -> Double -> RGB
sampleColorArray colors t
  | V.null colors = (0, 0, 0)
  | otherwise =
      let clamped = clamp01 t
          n = V.length colors
          idx = clamped * fromIntegral (n - 1)
          i = floor idx
          f = idx - fromIntegral i
      in if i >= n - 1
         then colors V.! (n - 1)
         else lerpRGB (colors V.! i) (colors V.! (i + 1)) f

-- ────────────────────────────────────────────────────────────────────────────
-- Grayscale
-- ────────────────────────────────────────────────────────────────────────────

-- | Grayscale colormap: t → (v, v, v) where v = t * 255.
grayscale :: Double -> RGB
grayscale t =
  let v = floor (clamp01 t * 255.0)
  in (v, v, v)

-- ────────────────────────────────────────────────────────────────────────────
-- Viridis Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Viridis colormap lookup table (10 control points).
viridisColors :: Vector RGB
viridisColors = V.fromList
  [ (68, 1, 84)
  , (72, 40, 120)
  , (62, 74, 137)
  , (49, 104, 142)
  , (38, 130, 142)
  , (31, 158, 137)
  , (53, 183, 121)
  , (109, 205, 89)
  , (180, 222, 44)
  , (253, 231, 37)
  ]

-- | Viridis colormap: perceptually uniform, blue-green-yellow.
viridis :: Double -> RGB
viridis = sampleColorArray viridisColors

-- ────────────────────────────────────────────────────────────────────────────
-- Magma Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Magma colormap lookup table (9 control points).
magmaColors :: Vector RGB
magmaColors = V.fromList
  [ (0, 0, 4)
  , (28, 16, 68)
  , (79, 18, 123)
  , (129, 37, 129)
  , (181, 54, 122)
  , (229, 80, 100)
  , (251, 135, 97)
  , (254, 194, 135)
  , (252, 253, 191)
  ]

-- | Magma colormap: perceptually uniform, black-red-yellow-white.
magma :: Double -> RGB
magma = sampleColorArray magmaColors

-- ────────────────────────────────────────────────────────────────────────────
-- Plasma Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Plasma colormap lookup table (9 control points).
plasmaColors :: Vector RGB
plasmaColors = V.fromList
  [ (13, 8, 135)
  , (75, 3, 161)
  , (125, 3, 168)
  , (168, 34, 150)
  , (203, 70, 121)
  , (229, 107, 93)
  , (248, 148, 65)
  , (253, 195, 40)
  , (240, 249, 33)
  ]

-- | Plasma colormap: perceptually uniform, purple-orange-yellow.
plasma :: Double -> RGB
plasma = sampleColorArray plasmaColors

-- ────────────────────────────────────────────────────────────────────────────
-- Inferno Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Inferno colormap lookup table (11 control points).
infernoColors :: Vector RGB
infernoColors = V.fromList
  [ (0, 0, 4)
  , (22, 11, 57)
  , (66, 10, 104)
  , (106, 23, 110)
  , (147, 38, 103)
  , (188, 55, 84)
  , (221, 81, 58)
  , (243, 118, 27)
  , (252, 165, 10)
  , (246, 215, 70)
  , (252, 255, 164)
  ]

-- | Inferno colormap: perceptually uniform, black-purple-red-yellow-white.
inferno :: Double -> RGB
inferno = sampleColorArray infernoColors

-- ────────────────────────────────────────────────────────────────────────────
-- Turbo Colormap
-- ────────────────────────────────────────────────────────────────────────────

-- | Turbo colormap lookup table (13 control points).
turboColors :: Vector RGB
turboColors = V.fromList
  [ (48, 18, 59)
  , (70, 68, 172)
  , (62, 121, 229)
  , (38, 170, 225)
  , (31, 212, 182)
  , (76, 237, 123)
  , (149, 249, 67)
  , (212, 241, 31)
  , (253, 207, 37)
  , (252, 150, 38)
  , (239, 85, 33)
  , (205, 33, 28)
  , (122, 4, 3)
  ]

-- | Turbo colormap: Google's improved rainbow, perceptually smoother.
turbo :: Double -> RGB
turbo = sampleColorArray turboColors

-- ────────────────────────────────────────────────────────────────────────────
-- Colormap Dispatcher
-- ────────────────────────────────────────────────────────────────────────────

-- | Get color from specified colormap at position t ∈ [0, 1].
getColor :: ColormapType -> Double -> RGB
getColor Grayscale = grayscale
getColor Viridis   = viridis
getColor Magma     = magma
getColor Plasma    = plasma
getColor Inferno   = inferno
getColor Turbo     = turbo
