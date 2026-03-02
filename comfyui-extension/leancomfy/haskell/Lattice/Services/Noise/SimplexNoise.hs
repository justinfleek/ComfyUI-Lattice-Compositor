{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.Noise.SimplexNoise
Description : 2D Simplex/Perlin Noise
Copyright   : (c) Lattice, 2026
License     : MIT

Pure deterministic noise function for organic motion.
Uses improved Perlin gradient noise with better bit mixing
to avoid seed collisions.

Source: ui/src/services/export/wanMoveFlowGenerators.ts (simplexNoise2D)
-}

module Lattice.Services.Noise.SimplexNoise
  ( -- * Main Noise Function
    simplexNoise2D
    -- * Octave Noise
  , fbm, turbulence, ridgeNoise
    -- * Low-Level
  , hash, grad, fade, lerp
  ) where

import Data.Bits (xor, (.&.), shiftR)
import Data.Word (Word32)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Prime for x coordinate hashing
primeX :: Word32
primeX = 374761393

-- | Prime for y coordinate hashing
primeY :: Word32
primeY = 668265263

-- | MurmurHash3 mixing constant 1
mixConstant1 :: Word32
mixConstant1 = 0x85ebca6b

-- | MurmurHash3 mixing constant 2
mixConstant2 :: Word32
mixConstant2 = 0xc2b2ae35

-- | Final mixing constant
mixConstant3 :: Word32
mixConstant3 = 0x5bd1e995

--------------------------------------------------------------------------------
-- Hash Function
--------------------------------------------------------------------------------

-- | Hash function with improved bit mixing for seed/coordinate combination.
--
--   Combines seed and 2D coordinates using MurmurHash3-style mixing
--   to produce well-distributed pseudo-random values.
hash :: Word32 -> Int -> Int -> Word32
hash seed px py =
  let h0 = seed
      h1 = h0 `xor` (h0 `shiftR` 16)
      h2 = h1 * mixConstant1
      h3 = h2 `xor` (h2 `shiftR` 13)
      h4 = h3 * mixConstant2
      h5 = h4 `xor` (h4 `shiftR` 16)
      pxu = fromIntegral px :: Word32
      pyu = fromIntegral py :: Word32
      h6 = h5 + pxu * primeX + pyu * primeY
      h7 = h6 `xor` (h6 `shiftR` 13)
      h8 = h7 * mixConstant3
  in h8 `xor` (h8 `shiftR` 15)

--------------------------------------------------------------------------------
-- Gradient Function
--------------------------------------------------------------------------------

-- | Calculate gradient contribution from hash and offset.
--
--   Uses 8 gradient directions for 2D noise:
--   - h & 7 selects direction
--   - Returns weighted sum of dx, dy based on direction
grad :: Word32 -> Double -> Double -> Double
grad h dx dy =
  let sel = h .&. 7
      u = if sel < 4 then dx else dy
      v = if sel < 4 then dy else dx
      signU = if sel .&. 1 == 0 then u else -u
      signV = if sel .&. 2 == 0 then 2 * v else -2 * v
  in signU + signV

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Linear interpolation
lerp :: Double -> Double -> Double -> Double
lerp a b t = a + t * (b - a)

-- | Quintic fade curve: 6t⁵ - 15t⁴ + 10t³
--   Provides smooth derivative at boundaries
fade :: Double -> Double
fade t = t * t * t * (t * (t * 6 - 15) + 10)

--------------------------------------------------------------------------------
-- Main Noise Function
--------------------------------------------------------------------------------

-- | 2D Simplex/Perlin noise.
--
--   Generates smooth, continuous pseudo-random values based on
--   2D coordinates and a seed. Output is normalized to [0, 1].
--
--   x, y: Sample coordinates
--   seed: Random seed for determinism
--
--   Returns value in [0, 1] range.
simplexNoise2D :: Double -> Double -> Word32 -> Double
simplexNoise2D x y seed =
  let -- Grid cell coordinates
      ix = floor x
      iy = floor y

      -- Fractional position within cell
      fx = x - fromIntegral ix
      fy = y - fromIntegral iy

      -- Hash the four corners
      n00 = grad (hash seed ix iy) fx fy
      n10 = grad (hash seed (ix + 1) iy) (fx - 1) fy
      n01 = grad (hash seed ix (iy + 1)) fx (fy - 1)
      n11 = grad (hash seed (ix + 1) (iy + 1)) (fx - 1) (fy - 1)

      -- Fade curves for interpolation
      u = fade fx
      v = fade fy

      -- Bilinear interpolation of corner values
      nx0 = lerp n00 n10 u
      nx1 = lerp n01 n11 u
      result = lerp nx0 nx1 v

  -- Normalize to [0, 1] (raw range is approximately [-1, 1])
  in result * 0.5 + 0.5

--------------------------------------------------------------------------------
-- Octave Noise (Fractal Brownian Motion)
--------------------------------------------------------------------------------

-- | Multi-octave noise for more natural-looking patterns.
--
--   Sums multiple noise layers at different frequencies and amplitudes.
--
--   x, y: Sample coordinates
--   seed: Random seed
--   octaves: Number of layers (1-8 recommended)
--   persistence: Amplitude multiplier per octave (0.5 typical)
--   lacunarity: Frequency multiplier per octave (2.0 typical)
fbm :: Double -> Double -> Word32 -> Int -> Double -> Double -> Double
fbm x y seed octaves persistence lacunarity =
  let go i freq amp total maxVal
        | i >= octaves = (total, maxVal)
        | otherwise =
            let noise = simplexNoise2D (x * freq) (y * freq) seed
                total' = total + noise * amp
                maxVal' = maxVal + amp
            in go (i + 1) (freq * lacunarity) (amp * persistence) total' maxVal'
      (total, maxVal) = go 0 1 1 0 0
  in if maxVal > 0 then total / maxVal else 0.5

-- | Turbulence noise using absolute value of noise layers.
--
--   Creates sharper, more "turbulent" patterns than regular FBM.
turbulence :: Double -> Double -> Word32 -> Int -> Double -> Double -> Double
turbulence x y seed octaves persistence lacunarity =
  let go i freq amp total maxVal
        | i >= octaves = (total, maxVal)
        | otherwise =
            let noise = simplexNoise2D (x * freq) (y * freq) seed
                absNoise = abs (noise * 2 - 1)
                total' = total + absNoise * amp
                maxVal' = maxVal + amp
            in go (i + 1) (freq * lacunarity) (amp * persistence) total' maxVal'
      (total, maxVal) = go 0 1 1 0 0
  in if maxVal > 0 then total / maxVal else 0.5

--------------------------------------------------------------------------------
-- Ridge Noise
--------------------------------------------------------------------------------

-- | Ridge noise for mountain-like patterns.
--
--   Creates sharp ridges by inverting absolute noise.
ridgeNoise :: Double -> Double -> Word32 -> Int -> Double -> Double -> Double -> Double
ridgeNoise x y seed octaves persistence lacunarity gain =
  let go i freq amp total weight
        | i >= octaves = total
        | otherwise =
            let noise = simplexNoise2D (x * freq) (y * freq) seed
                ridge = 1 - abs (noise * 2 - 1)
                ridge' = ridge * ridge * weight
                total' = total + ridge' * amp
                weight' = min 1 (ridge' * gain)
            in go (i + 1) (freq * lacunarity) (amp * persistence) total' weight'
  in go 0 1 1 0 1
