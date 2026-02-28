-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // element // widget // chart // palette
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Chart Color Palettes — Coordinated color schemes for chart series.
-- |
-- | Provides multiple palettes for different use cases:
-- | - Default: balanced, professional colors
-- | - Pastel: soft, accessible colors
-- | - Vibrant: high-contrast, attention-grabbing
-- | - Monochromatic: single-hue variations

module Hydrogen.Element.Compound.Widget.Chart.Palette
  ( -- * Palettes
    defaultPalette
  , pastelPalette
  , vibrantPalette
  , monochromaticPalette
  
  -- * Color Generation
  , generateSeriesColors
  , getColorAtIndex
  ) where

import Prelude
  ( mod
  , (<=)
  )

import Data.Array (index, length, mapWithIndex, replicate)
import Data.Maybe (fromMaybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // color palettes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default color palette for chart series.
-- |
-- | 10 distinct colors that work well together.
defaultPalette :: Array String
defaultPalette =
  [ "#3B82F6"  -- Blue
  , "#10B981"  -- Emerald
  , "#F59E0B"  -- Amber
  , "#EF4444"  -- Red
  , "#8B5CF6"  -- Violet
  , "#EC4899"  -- Pink
  , "#06B6D4"  -- Cyan
  , "#84CC16"  -- Lime
  , "#F97316"  -- Orange
  , "#6366F1"  -- Indigo
  ]

-- | Pastel color palette.
pastelPalette :: Array String
pastelPalette =
  [ "#93C5FD"  -- Light blue
  , "#6EE7B7"  -- Light emerald
  , "#FCD34D"  -- Light amber
  , "#FCA5A5"  -- Light red
  , "#C4B5FD"  -- Light violet
  , "#F9A8D4"  -- Light pink
  , "#67E8F9"  -- Light cyan
  , "#BEF264"  -- Light lime
  , "#FDBA74"  -- Light orange
  , "#A5B4FC"  -- Light indigo
  ]

-- | Vibrant color palette.
vibrantPalette :: Array String
vibrantPalette =
  [ "#2563EB"  -- Bright blue
  , "#059669"  -- Bright emerald
  , "#D97706"  -- Bright amber
  , "#DC2626"  -- Bright red
  , "#7C3AED"  -- Bright violet
  , "#DB2777"  -- Bright pink
  , "#0891B2"  -- Bright cyan
  , "#65A30D"  -- Bright lime
  , "#EA580C"  -- Bright orange
  , "#4F46E5"  -- Bright indigo
  ]

-- | Monochromatic palette (shades of blue).
monochromaticPalette :: Array String
monochromaticPalette =
  [ "#1E3A5F"
  , "#2A4A6F"
  , "#365B80"
  , "#426B90"
  , "#4E7CA1"
  , "#5A8CB1"
  , "#669DC2"
  , "#72ADD2"
  , "#7EBEE3"
  , "#8ACEF3"
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate colors for series based on palette.
generateSeriesColors :: Array String -> Int -> Array String
generateSeriesColors palette count =
  mapWithIndex (\idx _ -> getColorAtIndex palette idx) (replicate count "")

-- | Get color at index, wrapping around palette.
getColorAtIndex :: Array String -> Int -> String
getColorAtIndex palette idx =
  let paletteLen = length palette
      wrappedIdx = if paletteLen <= 0 then 0 else idx `mod` paletteLen
  in fromMaybe "#000000" (index palette wrappedIdx)
