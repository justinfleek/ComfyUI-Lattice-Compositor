{-|
Module      : Lattice.Services.Effects.BlurDirectional
Description : Directional and Radial Blur
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for motion-style blurs:
- Directional blur (motion blur in a direction)
- Radial blur (zoom blur from center)
- Box blur (fast average blur)
- Sharpen filter

All functions are total and deterministic.

Source: ui/src/services/effects/blurRenderer.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Effects.BlurDirectional
  ( -- * Types
    DirectionalParams(..)
  , RadialParams(..)
  , BoxParams(..)
  , SharpenParams(..)
    -- * Default Values
  , defaultDirectionalParams
  , defaultRadialParams
  , defaultBoxParams
  , defaultSharpenParams
    -- * Blur Functions
  , directionalOffset
  , radialOffset
  , boxBlurKernel
  , sharpenKernel
    -- * Helpers
  , normalizeAngle
  , distance2D
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Directional (motion) blur parameters
data DirectionalParams = DirectionalParams
  { dpAngle    :: !Double  -- ^ Blur angle in radians [0, 2*pi]
  , dpDistance :: !Double  -- ^ Blur distance in pixels [0-500]
  , dpSamples  :: !Int     -- ^ Number of samples [1-64]
  } deriving (Eq, Show)

-- | Radial (zoom) blur parameters
data RadialParams = RadialParams
  { rpCenterX :: !Double  -- ^ Center X [0-1] normalized
  , rpCenterY :: !Double  -- ^ Center Y [0-1] normalized
  , rpAmount  :: !Double  -- ^ Blur amount [0-100]
  , rpSamples :: !Int     -- ^ Number of samples [1-64]
  , rpType    :: !RadialType  -- ^ Spin or Zoom
  } deriving (Eq, Show)

-- | Radial blur type
data RadialType
  = RadialSpin  -- ^ Rotational blur around center
  | RadialZoom  -- ^ Zoom blur toward/from center
  deriving (Eq, Show)

-- | Box blur parameters
data BoxParams = BoxParams
  { bpRadiusX :: !Int  -- ^ Horizontal radius [1-250]
  , bpRadiusY :: !Int  -- ^ Vertical radius [1-250]
  } deriving (Eq, Show)

-- | Sharpen parameters
data SharpenParams = SharpenParams
  { spAmount    :: !Double  -- ^ Sharpen amount [0-500%]
  , spRadius    :: !Int     -- ^ Radius [1-10]
  , spThreshold :: !Int     -- ^ Threshold [0-255]
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default directional blur
defaultDirectionalParams :: DirectionalParams
defaultDirectionalParams = DirectionalParams
  { dpAngle = 0
  , dpDistance = 10
  , dpSamples = 16
  }

-- | Default radial blur
defaultRadialParams :: RadialParams
defaultRadialParams = RadialParams
  { rpCenterX = 0.5
  , rpCenterY = 0.5
  , rpAmount = 10
  , rpSamples = 16
  , rpType = RadialZoom
  }

-- | Default box blur
defaultBoxParams :: BoxParams
defaultBoxParams = BoxParams
  { bpRadiusX = 5
  , bpRadiusY = 5
  }

-- | Default sharpen
defaultSharpenParams :: SharpenParams
defaultSharpenParams = SharpenParams
  { spAmount = 100
  , spRadius = 1
  , spThreshold = 0
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp integer to range
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi = max lo . min hi

-- | Clamp value to [0, 1]
clamp01 :: Double -> Double
clamp01 = max 0 . min 1

-- | Normalize angle to [0, 2*pi]
normalizeAngle :: Double -> Double
normalizeAngle angle =
  let twoPi = 2 * pi
      a = angle - twoPi * fromIntegral (floor (angle / twoPi) :: Int)
  in if a < 0 then a + twoPi else a

-- | 2D Euclidean distance
distance2D :: Double -> Double -> Double -> Double -> Double
distance2D x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in sqrt (dx * dx + dy * dy)

--------------------------------------------------------------------------------
-- Directional Blur
--------------------------------------------------------------------------------

-- | Calculate sample offsets for directional blur
--   Returns list of (dx, dy, weight) tuples
directionalOffset :: DirectionalParams -> Int -> (Double, Double, Double)
directionalOffset params sampleIdx =
  let angle = dpAngle params
      dist = dpDistance params
      samples = max 1 (dpSamples params)
      -- Distribute samples along the motion line
      t = fromIntegral sampleIdx / fromIntegral (samples - 1) - 0.5
      dx = cos angle * dist * t
      dy = sin angle * dist * t
      -- Weight (could be uniform or gaussian-weighted)
      weight = 1.0 / fromIntegral samples
  in (dx, dy, weight)

-- | Generate all sample offsets for directional blur
directionalOffsets :: DirectionalParams -> [(Double, Double, Double)]
directionalOffsets params =
  let samples = max 1 (dpSamples params)
  in map (directionalOffset params) [0 .. samples - 1]

--------------------------------------------------------------------------------
-- Radial Blur
--------------------------------------------------------------------------------

-- | Calculate sample offset for radial blur at a pixel position
--   x, y: pixel position [0-1] normalized
radialOffset :: RadialParams -> Double -> Double -> Int -> (Double, Double, Double)
radialOffset params x y sampleIdx =
  let cx = rpCenterX params
      cy = rpCenterY params
      amount = rpAmount params / 100  -- Convert percentage to factor
      samples = max 1 (rpSamples params)
      -- Distance from center
      dx = x - cx
      dy = y - cy
      dist = sqrt (dx * dx + dy * dy)
      -- Sample along radial direction
      t = fromIntegral sampleIdx / fromIntegral (samples - 1) - 0.5
      (offsetX, offsetY) = case rpType params of
        RadialZoom ->
          -- Zoom: sample along line from center
          (dx * amount * t, dy * amount * t)
        RadialSpin ->
          -- Spin: sample along tangent (perpendicular to radial)
          let angle = atan2 dy dx
              spinAngle = angle + amount * t
              newDist = dist
          in (cos spinAngle * newDist - dx, sin spinAngle * newDist - dy)
      weight = 1.0 / fromIntegral samples
  in (offsetX, offsetY, weight)

--------------------------------------------------------------------------------
-- Box Blur
--------------------------------------------------------------------------------

-- | Generate box blur kernel (uniform weights)
boxBlurKernel :: BoxParams -> [[Double]]
boxBlurKernel params =
  let rx = clampInt 1 250 (bpRadiusX params)
      ry = clampInt 1 250 (bpRadiusY params)
      width = rx * 2 + 1
      height = ry * 2 + 1
      total = fromIntegral (width * height)
      weight = 1.0 / total
  in replicate height (replicate width weight)

-- | Box blur kernel size
boxBlurSize :: BoxParams -> (Int, Int)
boxBlurSize params =
  let rx = clampInt 1 250 (bpRadiusX params)
      ry = clampInt 1 250 (bpRadiusY params)
  in (rx * 2 + 1, ry * 2 + 1)

--------------------------------------------------------------------------------
-- Sharpen
--------------------------------------------------------------------------------

-- | Generate sharpen kernel (unsharp mask style)
sharpenKernel :: SharpenParams -> [[Double]]
sharpenKernel params =
  let amount = spAmount params / 100
      r = clampInt 1 10 (spRadius params)
      size = r * 2 + 1
      center = r
      -- Create blur kernel for unsharp mask
      blurWeight = 1.0 / fromIntegral (size * size)
      -- Sharpen = original + amount * (original - blur)
      -- Which simplifies to: center = 1 + amount, neighbors = -amount * blurWeight
      neighborWeight = -amount * blurWeight
      centerWeight = 1 + amount * (1 - blurWeight)
  in [[if i == center && j == center then centerWeight else neighborWeight
      | j <- [0 .. size - 1]] | i <- [0 .. size - 1]]

-- | Apply sharpen threshold (only sharpen if difference exceeds threshold)
sharpenWithThreshold :: SharpenParams -> Double -> Double -> Double
sharpenWithThreshold params original sharpened =
  let threshold = fromIntegral (spThreshold params) / 255
      diff = abs (sharpened - original)
  in if diff < threshold then original else sharpened
