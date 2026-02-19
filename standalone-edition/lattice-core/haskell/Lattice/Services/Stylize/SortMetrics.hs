{-|
  Lattice.Services.Stylize.SortMetrics - Pixel Sorting Value Calculations

  Pure mathematical functions for computing pixel sort metrics:
  - Brightness (average RGB)
  - Saturation (HSL-based)
  - Hue (from RGB)

  Used by pixel sort effect to determine sorting order within intervals.

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 73-96)
-}

module Lattice.Services.Stylize.SortMetrics
  ( SortBy(..)
  , brightness
  , saturation
  , hue
  , getSortValue
  , isIntervalBoundary
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Sort Metric Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Sort metric type for pixel sorting
data SortBy
  = Brightness    -- ^ Average of RGB
  | Saturation    -- ^ HSL saturation
  | Hue           -- ^ HSL hue in degrees
  deriving (Show, Eq, Enum, Bounded)

-- ────────────────────────────────────────────────────────────────────────────
-- Brightness
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate brightness as average of RGB channels.
--
--   @param r Red channel (0-255 normalized to 0-1)
--   @param g Green channel (0-255 normalized to 0-1)
--   @param b Blue channel (0-255 normalized to 0-1)
--   @return Brightness value in [0, 1]
brightness :: Double -> Double -> Double -> Double
brightness r g b = (r + g + b) / 3.0

-- ────────────────────────────────────────────────────────────────────────────
-- Saturation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate HSL saturation from RGB.
--
--   Saturation = (max - min) / (2 - max - min)  if L > 0.5
--                (max - min) / (max + min)       otherwise
--
--   @param r Red channel (0-1)
--   @param g Green channel (0-1)
--   @param b Blue channel (0-1)
--   @return Saturation value in [0, 1]
saturation :: Double -> Double -> Double -> Double
saturation r g b =
  let maxVal = max r (max g b)
      minVal = min r (min g b)
  in if maxVal == minVal
     then 0.0
     else
       let l = (maxVal + minVal) / 2.0
       in if l > 0.5
          then (maxVal - minVal) / (2.0 - maxVal - minVal)
          else (maxVal - minVal) / (maxVal + minVal)

-- ────────────────────────────────────────────────────────────────────────────
-- Hue
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate hue from RGB in degrees [0, 360).
--
--   Uses standard RGB to hue conversion.
--
--   @param r Red channel (0-1)
--   @param g Green channel (0-1)
--   @param b Blue channel (0-1)
--   @return Hue in degrees [0, 360)
hue :: Double -> Double -> Double -> Double
hue r g b =
  let maxVal = max r (max g b)
      minVal = min r (min g b)
  in if maxVal == minVal
     then 0.0
     else
       let delta = maxVal - minVal
           h = if maxVal == r
               then (g - b) / delta
               else if maxVal == g
               then 2.0 + (b - r) / delta
               else 4.0 + (r - g) / delta
           hDeg = h * 60.0
       -- Normalize to [0, 360)
       in if hDeg < 0.0 then hDeg + 360.0 else hDeg

-- ────────────────────────────────────────────────────────────────────────────
-- Sort Value Dispatcher
-- ────────────────────────────────────────────────────────────────────────────

-- | Get sort value for a pixel based on sorting criterion.
--
--   @param sortBy Which metric to use for sorting
--   @param r Red channel (0-1)
--   @param g Green channel (0-1)
--   @param b Blue channel (0-1)
--   @return Sort value (higher = different position in sort order)
getSortValue :: SortBy -> Double -> Double -> Double -> Double
getSortValue sortBy r g b =
  case sortBy of
    Brightness -> brightness r g b
    Saturation -> saturation r g b
    Hue        -> hue r g b

-- ────────────────────────────────────────────────────────────────────────────
-- Interval Detection
-- ────────────────────────────────────────────────────────────────────────────

-- | Check if pixel difference exceeds threshold for interval boundary.
--
--   Used to determine where to break sorting intervals.
--
--   @param sortVal1 Sort value of first pixel
--   @param sortVal2 Sort value of second pixel
--   @param threshold Edge detection threshold [0, 1]
--   @param smoothing Interval boundary smoothness [0, 1]
--   @return True if difference exceeds adjusted threshold
isIntervalBoundary :: Double -> Double -> Double -> Double -> Bool
isIntervalBoundary sortVal1 sortVal2 threshold smoothing =
  let diff = abs (sortVal2 - sortVal1)
      adjustedThreshold = threshold * (1.0 - smoothing)
  in diff > adjustedThreshold
