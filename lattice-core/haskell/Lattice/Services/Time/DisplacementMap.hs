{-|
  Lattice.Services.Time.DisplacementMap - Temporal Displacement Map Generation

  Pure mathematical functions for time displacement effect maps:
  - Gradient (horizontal, vertical, diagonal)
  - Radial (center-out, edge-in)
  - Sinusoidal patterns

  Source: ui/src/services/effects/timeRenderer.ts (lines 459-514)
-}

module Lattice.Services.Time.DisplacementMap
  ( -- * Gradient Patterns
    gradientH
  , gradientV
  , diagonal
    -- * Radial Patterns
  , radialDistance
  , radial
  , centerOut
    -- * Sinusoidal Patterns
  , sineH
  , sineV
    -- * Map Types
  , MapType(..)
  , getDisplacementValue
    -- * Frame Offset
  , applyBias
  , toFrameOffset
  , calculateTargetFrame
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Horizontal Gradient
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate horizontal gradient displacement value.
--   Returns 0 at left edge, 1 at right edge.
gradientH :: Int  -- ^ X coordinate
          -> Int  -- ^ Width
          -> Double
gradientH _ 0 = 0.5
gradientH x width = fromIntegral x / fromIntegral width

-- ────────────────────────────────────────────────────────────────────────────
-- Vertical Gradient
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate vertical gradient displacement value.
--   Returns 0 at top edge, 1 at bottom edge.
gradientV :: Int  -- ^ Y coordinate
          -> Int  -- ^ Height
          -> Double
gradientV _ 0 = 0.5
gradientV y height = fromIntegral y / fromIntegral height

-- ────────────────────────────────────────────────────────────────────────────
-- Diagonal Gradient
-- ────────────────────────────────────────────────────────────────────────────

-- | Generate diagonal gradient displacement value.
--   Averages horizontal and vertical gradients.
diagonal :: Int -> Int -> Int -> Int -> Double
diagonal x y width height =
  (gradientH x width + gradientV y height) / 2.0

-- ────────────────────────────────────────────────────────────────────────────
-- Radial Distance
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate distance from center, normalized to [0, 1].
--   Returns 0 at center, 1 at corners.
radialDistance :: Int  -- ^ X
               -> Int  -- ^ Y
               -> Int  -- ^ Width
               -> Int  -- ^ Height
               -> Double
radialDistance _ _ 0 _ = 0.5
radialDistance _ _ _ 0 = 0.5
radialDistance x y width height =
  let cx = fromIntegral width / 2.0
      cy = fromIntegral height / 2.0
      dx = fromIntegral x - cx
      dy = fromIntegral y - cy
      dist = sqrt (dx * dx + dy * dy)
      maxDist = sqrt (cx * cx + cy * cy)
  in if maxDist < 0.0001 then 0.0 else dist / maxDist

-- | Radial displacement: 0 at center, 1 at edges.
radial :: Int -> Int -> Int -> Int -> Double
radial = radialDistance

-- | Center-out displacement: 1 at center, 0 at edges (inverted radial).
centerOut :: Int -> Int -> Int -> Int -> Double
centerOut x y width height = 1.0 - radialDistance x y width height

-- ────────────────────────────────────────────────────────────────────────────
-- Sinusoidal Patterns
-- ────────────────────────────────────────────────────────────────────────────

-- | Horizontal sine wave displacement.
--   scale controls number of wave periods.
sineH :: Int     -- ^ X coordinate
      -> Int     -- ^ Width
      -> Double  -- ^ Scale (periods)
      -> Double
sineH _ 0 _ = 0.5
sineH x width scale =
  let normalizedX = fromIntegral x / fromIntegral width
  in 0.5 + 0.5 * sin (normalizedX * pi * 2.0 * scale)

-- | Vertical sine wave displacement.
--   scale controls number of wave periods.
sineV :: Int     -- ^ Y coordinate
      -> Int     -- ^ Height
      -> Double  -- ^ Scale (periods)
      -> Double
sineV _ 0 _ = 0.5
sineV y height scale =
  let normalizedY = fromIntegral y / fromIntegral height
  in 0.5 + 0.5 * sin (normalizedY * pi * 2.0 * scale)

-- ────────────────────────────────────────────────────────────────────────────
-- Map Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Map type enum.
data MapType
  = GradientH
  | GradientV
  | Radial
  | SineH
  | SineV
  | Diagonal
  | CenterOut
  deriving (Show, Eq)

-- | Get displacement value for a pixel based on map type.
--   Returns value in [0, 1] range.
getDisplacementValue :: MapType
                     -> Int     -- ^ X
                     -> Int     -- ^ Y
                     -> Int     -- ^ Width
                     -> Int     -- ^ Height
                     -> Double  -- ^ Scale (for sine patterns)
                     -> Double
getDisplacementValue mapType x y width height scale = case mapType of
  GradientH -> gradientH x width
  GradientV -> gradientV y height
  Radial    -> radial x y width height
  SineH     -> sineH x width scale
  SineV     -> sineV y height scale
  Diagonal  -> diagonal x y width height
  CenterOut -> centerOut x y width height

-- ────────────────────────────────────────────────────────────────────────────
-- Frame Offset Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply bias to displacement value.
--   Shifts the 0.5 neutral point.
applyBias :: Double  -- ^ Displacement value
          -> Double  -- ^ Bias
          -> Double
applyBias dispValue bias = dispValue + bias

-- | Convert biased displacement to frame offset.
--   Maps [0, 1] (with bias) to [-maxDisplacement, +maxDisplacement].
toFrameOffset :: Double  -- ^ Biased value
              -> Double  -- ^ Max displacement
              -> Int
toFrameOffset biasedValue maxDisplacement =
  round ((biasedValue - 0.5) * 2.0 * maxDisplacement)

-- | Calculate target frame from current frame and displacement.
--   Combines displacement value, bias, and max displacement.
calculateTargetFrame :: Int     -- ^ Current frame
                     -> Double  -- ^ Displacement value
                     -> Double  -- ^ Bias
                     -> Double  -- ^ Max displacement
                     -> Int
calculateTargetFrame currentFrame dispValue bias maxDisplacement =
  let biased = applyBias dispValue bias
      offset = toFrameOffset biased maxDisplacement
  in currentFrame + offset
