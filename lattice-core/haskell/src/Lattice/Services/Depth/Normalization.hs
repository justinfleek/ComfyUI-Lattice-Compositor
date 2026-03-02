{-# LANGUAGE Strict #-}
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

-- ────────────────────────────────────────────────────────────────────────────
-- Depth Range Normalization
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate safe depth range, avoiding division by zero.
--   Returns 1.0 if minDepth == maxDepth.
safeDepthRange :: Double -> Double -> Double
safeDepthRange minDepth maxDepth =
  let range = maxDepth - minDepth
  in if range <= 0.0 then 1.0 else range

-- | Normalize depth value to [0, 1] range.
--   0 = minDepth, 1 = maxDepth.
normalizeDepth :: Double -> Double -> Double -> Double
normalizeDepth depth minDepth maxDepth =
  let range = safeDepthRange minDepth maxDepth
  in (depth - minDepth) / range

-- | Clamp normalized value to [0, 1].
clampNormalized :: Double -> Double
clampNormalized value
  | value < 0.0 = 0.0
  | value > 1.0 = 1.0
  | otherwise   = value

-- | Invert depth: converts near=low/far=high to near=high/far=low.
--   Used for AI depth models that expect near=bright, far=dark.
invertDepth :: Double -> Double
invertDepth normalized = 1.0 - clampNormalized normalized

-- ────────────────────────────────────────────────────────────────────────────
-- Bit Depth Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert normalized [0, 1] to 8-bit [0, 255].
toUint8 :: Double -> Int
toUint8 normalized =
  let clamped = clampNormalized normalized
  in floor (clamped * 255.0)

-- | Convert normalized [0, 1] to 16-bit [0, 65535].
toUint16 :: Double -> Int
toUint16 normalized =
  let clamped = clampNormalized normalized
  in floor (clamped * 65535.0)

-- | Convert 8-bit [0, 255] to normalized [0, 1].
fromUint8 :: Int -> Double
fromUint8 value = fromIntegral value / 255.0

-- | Convert 16-bit [0, 65535] to normalized [0, 1].
fromUint16 :: Int -> Double
fromUint16 value = fromIntegral value / 65535.0

-- ────────────────────────────────────────────────────────────────────────────
-- Metric Depth Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert normalized depth to world units.
--   worldDepth = nearClip + normalized * (farClip - nearClip)
toWorldDepth :: Double -> Double -> Double -> Double
toWorldDepth normalized nearClip farClip =
  nearClip + clampNormalized normalized * (farClip - nearClip)

-- | Convert world depth to normalized [0, 1].
--   Inverse of toWorldDepth.
fromWorldDepth :: Double -> Double -> Double -> Double
fromWorldDepth worldDepth nearClip farClip =
  if farClip <= nearClip
  then 0.0
  else clampNormalized ((worldDepth - nearClip) / (farClip - nearClip))

-- | Scale normalized depth by far clip (for non-normalized formats).
scaleByFarClip :: Double -> Double -> Double
scaleByFarClip normalized farClip =
  clampNormalized normalized * farClip

-- ────────────────────────────────────────────────────────────────────────────
-- Complete Depth Conversion Pipeline
-- ────────────────────────────────────────────────────────────────────────────

-- | Full depth conversion: world → normalized → inverted (optional) → quantized.
--   This matches the convertDepthToFormat pipeline.
convertDepth :: Double -> Double -> Double -> Bool -> Int -> Int
convertDepth depth minDepth maxDepth invert bitDepth =
  let normalized = normalizeDepth depth minDepth maxDepth
      clamped = clampNormalized normalized
      inverted = if invert then invertDepth clamped else clamped
  in case bitDepth of
       8  -> toUint8 inverted
       16 -> toUint16 inverted
       _  -> toUint16 inverted  -- Default to 16-bit

-- | Depth comparison for z-buffer: returns true if newDepth is closer (smaller).
isCloser :: Double -> Double -> Bool
isCloser newDepth currentDepth = newDepth < currentDepth

-- | Depth buffer update: return closer depth.
depthBufferUpdate :: Double -> Double -> Double
depthBufferUpdate newDepth currentDepth =
  if isCloser newDepth currentDepth then newDepth else currentDepth
