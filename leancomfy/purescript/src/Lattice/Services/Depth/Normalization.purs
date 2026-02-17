{-
  Lattice.Services.Depth.Normalization - Depth Value Normalization

  Pure mathematical functions for depth map processing:
  - Depth normalization to [0, 1] range
  - Bit depth conversion (8-bit, 16-bit, 32-bit)
  - Depth inversion (near/far swap)

  Source: ui/src/services/export/depthRenderer.ts (lines 600-676)
-}

module Lattice.Services.Depth.Normalization
  ( -- * Depth Range Normalization
    safeDepthRange
  , normalizeDepth
  , clampNormalized
  , invertDepth
    -- * Bit Depth Conversion
  , toUint8
  , toUint16
  , fromUint8
  , fromUint16
    -- * Metric Depth Conversion
  , toWorldDepth
  , fromWorldDepth
  , scaleByFarClip
    -- * Complete Pipeline
  , convertDepth
  , isCloser
  , depthBufferUpdate
  ) where

import Prelude

import Data.Int (floor, round, toNumber)

--------------------------------------------------------------------------------
-- Depth Range Normalization
--------------------------------------------------------------------------------

-- | Calculate safe depth range, avoiding division by zero.
--   Returns 1.0 if minDepth == maxDepth.
safeDepthRange :: Number -> Number -> Number
safeDepthRange minDepth maxDepth =
  let range = maxDepth - minDepth
  in if range <= 0.0 then 1.0 else range

-- | Normalize depth value to [0, 1] range.
--   0 = minDepth, 1 = maxDepth.
normalizeDepth :: Number -> Number -> Number -> Number
normalizeDepth depth minDepth maxDepth =
  let range = safeDepthRange minDepth maxDepth
  in (depth - minDepth) / range

-- | Clamp normalized value to [0, 1].
clampNormalized :: Number -> Number
clampNormalized value
  | value < 0.0 = 0.0
  | value > 1.0 = 1.0
  | otherwise   = value

-- | Invert depth: converts near=low/far=high to near=high/far=low.
--   Used for AI depth models that expect near=bright, far=dark.
invertDepth :: Number -> Number
invertDepth normalized = 1.0 - clampNormalized normalized

--------------------------------------------------------------------------------
-- Bit Depth Conversion
--------------------------------------------------------------------------------

-- | Convert normalized [0, 1] to 8-bit [0, 255].
toUint8 :: Number -> Int
toUint8 normalized =
  let clamped = clampNormalized normalized
  in round (clamped * 255.0)

-- | Convert normalized [0, 1] to 16-bit [0, 65535].
toUint16 :: Number -> Int
toUint16 normalized =
  let clamped = clampNormalized normalized
  in round (clamped * 65535.0)

-- | Convert 8-bit [0, 255] to normalized [0, 1].
fromUint8 :: Int -> Number
fromUint8 value = toNumber value / 255.0

-- | Convert 16-bit [0, 65535] to normalized [0, 1].
fromUint16 :: Int -> Number
fromUint16 value = toNumber value / 65535.0

--------------------------------------------------------------------------------
-- Metric Depth Conversion
--------------------------------------------------------------------------------

-- | Convert normalized depth to world units.
--   worldDepth = nearClip + normalized * (farClip - nearClip)
toWorldDepth :: Number -> Number -> Number -> Number
toWorldDepth normalized nearClip farClip =
  nearClip + clampNormalized normalized * (farClip - nearClip)

-- | Convert world depth to normalized [0, 1].
--   Inverse of toWorldDepth.
fromWorldDepth :: Number -> Number -> Number -> Number
fromWorldDepth worldDepth nearClip farClip =
  if farClip <= nearClip
  then 0.0
  else clampNormalized ((worldDepth - nearClip) / (farClip - nearClip))

-- | Scale normalized depth by far clip (for non-normalized formats).
scaleByFarClip :: Number -> Number -> Number
scaleByFarClip normalized farClip =
  clampNormalized normalized * farClip

--------------------------------------------------------------------------------
-- Complete Depth Conversion Pipeline
--------------------------------------------------------------------------------

-- | Full depth conversion: world → normalized → inverted (optional) → quantized.
--   This matches the convertDepthToFormat pipeline.
convertDepth :: Number -> Number -> Number -> Boolean -> Int -> Int
convertDepth depth minDepth maxDepth invert bitDepth =
  let normalized = normalizeDepth depth minDepth maxDepth
      clamped = clampNormalized normalized
      inverted = if invert then invertDepth clamped else clamped
  in case bitDepth of
       8  -> toUint8 inverted
       16 -> toUint16 inverted
       _  -> toUint16 inverted  -- Default to 16-bit

-- | Depth comparison for z-buffer: returns true if newDepth is closer (smaller).
isCloser :: Number -> Number -> Boolean
isCloser newDepth currentDepth = newDepth < currentDepth

-- | Depth buffer update: return closer depth.
depthBufferUpdate :: Number -> Number -> Number
depthBufferUpdate newDepth currentDepth =
  if isCloser newDepth currentDepth then newDepth else currentDepth
