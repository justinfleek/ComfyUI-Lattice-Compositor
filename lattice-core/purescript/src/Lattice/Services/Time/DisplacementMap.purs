{-
  Lattice.Services.Time.DisplacementMap - Temporal Displacement Map Generation

  Pure mathematical functions for time displacement effect maps:
  - Gradient (horizontal, vertical, diagonal)
  - Radial (center-out, edge-in)
  - Sinusoidal patterns

  Source: ui/src/services/effects/timeRenderer.ts (lines 459-514)
-}

module Lattice.Services.Time.DisplacementMap
  ( gradientH
  , gradientV
  , diagonal
  , radialDistance
  , radial
  , centerOut
  , sineH
  , sineV
  , MapType(..)
  , getDisplacementValue
  , applyBias
  , toFrameOffset
  , calculateTargetFrame
  ) where

import Prelude

import Data.Int (round, toNumber)
import Math (floor, pi, sin, sqrt)

--------------------------------------------------------------------------------
-- Horizontal Gradient
--------------------------------------------------------------------------------

-- | Generate horizontal gradient displacement value.
gradientH :: Int -> Int -> Number
gradientH _ 0 = 0.5
gradientH x width = toNumber x / toNumber width

--------------------------------------------------------------------------------
-- Vertical Gradient
--------------------------------------------------------------------------------

-- | Generate vertical gradient displacement value.
gradientV :: Int -> Int -> Number
gradientV _ 0 = 0.5
gradientV y height = toNumber y / toNumber height

--------------------------------------------------------------------------------
-- Diagonal Gradient
--------------------------------------------------------------------------------

-- | Generate diagonal gradient displacement value.
diagonal :: Int -> Int -> Int -> Int -> Number
diagonal x y width height =
  (gradientH x width + gradientV y height) / 2.0

--------------------------------------------------------------------------------
-- Radial Distance
--------------------------------------------------------------------------------

-- | Calculate distance from center, normalized to [0, 1].
radialDistance :: Int -> Int -> Int -> Int -> Number
radialDistance _ _ 0 _ = 0.5
radialDistance _ _ _ 0 = 0.5
radialDistance x y width height =
  let cx = toNumber width / 2.0
      cy = toNumber height / 2.0
      dx = toNumber x - cx
      dy = toNumber y - cy
      dist = sqrt (dx * dx + dy * dy)
      maxDist = sqrt (cx * cx + cy * cy)
  in if maxDist < 0.0001 then 0.0 else dist / maxDist

-- | Radial displacement: 0 at center, 1 at edges.
radial :: Int -> Int -> Int -> Int -> Number
radial = radialDistance

-- | Center-out displacement: 1 at center, 0 at edges.
centerOut :: Int -> Int -> Int -> Int -> Number
centerOut x y width height = 1.0 - radialDistance x y width height

--------------------------------------------------------------------------------
-- Sinusoidal Patterns
--------------------------------------------------------------------------------

-- | Horizontal sine wave displacement.
sineH :: Int -> Int -> Number -> Number
sineH _ 0 _ = 0.5
sineH x width scale =
  let normalizedX = toNumber x / toNumber width
  in 0.5 + 0.5 * sin (normalizedX * pi * 2.0 * scale)

-- | Vertical sine wave displacement.
sineV :: Int -> Int -> Number -> Number
sineV _ 0 _ = 0.5
sineV y height scale =
  let normalizedY = toNumber y / toNumber height
  in 0.5 + 0.5 * sin (normalizedY * pi * 2.0 * scale)

--------------------------------------------------------------------------------
-- Map Types
--------------------------------------------------------------------------------

-- | Map type enum.
data MapType
  = GradientH
  | GradientV
  | Radial
  | SineH
  | SineV
  | Diagonal
  | CenterOut

derive instance eqMapType :: Eq MapType

-- | Get displacement value for a pixel based on map type.
getDisplacementValue :: MapType -> Int -> Int -> Int -> Int -> Number -> Number
getDisplacementValue mapType x y width height scale = case mapType of
  GradientH -> gradientH x width
  GradientV -> gradientV y height
  Radial    -> radial x y width height
  SineH     -> sineH x width scale
  SineV     -> sineV y height scale
  Diagonal  -> diagonal x y width height
  CenterOut -> centerOut x y width height

--------------------------------------------------------------------------------
-- Frame Offset Calculation
--------------------------------------------------------------------------------

-- | Apply bias to displacement value.
applyBias :: Number -> Number -> Number
applyBias dispValue bias = dispValue + bias

-- | Convert biased displacement to frame offset.
toFrameOffset :: Number -> Number -> Int
toFrameOffset biasedValue maxDisplacement =
  round ((biasedValue - 0.5) * 2.0 * maxDisplacement)

-- | Calculate target frame from current frame and displacement.
calculateTargetFrame :: Int -> Number -> Number -> Number -> Int
calculateTargetFrame currentFrame dispValue bias maxDisplacement =
  let biased = applyBias dispValue bias
      offset = toFrameOffset biased maxDisplacement
  in currentFrame + offset
