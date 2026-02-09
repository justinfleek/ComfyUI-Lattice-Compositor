-- | Lattice.Services.Noise.SimplexNoise - 2D Simplex/Perlin Noise
-- |
-- | Pure deterministic noise function for organic motion.
-- | Uses improved Perlin gradient noise with better bit mixing
-- | to avoid seed collisions.
-- |
-- | Source: ui/src/services/export/wanMoveFlowGenerators.ts (simplexNoise2D)

module Lattice.Services.Noise.SimplexNoise
  ( -- * Main Noise Function
    simplexNoise2D
    -- * Octave Noise
  , fbm, turbulence, ridgeNoise
    -- * Low-Level
  , hash, grad, fade, lerp
  ) where

import Prelude
import Data.Int (floor, toNumber)
import Data.Int.Bits (xor, and, shr)
import Math (abs, cos, pi, sin, sqrt) as Math

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | Prime for x coordinate hashing
primeX :: Int
primeX = 374761393

-- | Prime for y coordinate hashing
primeY :: Int
primeY = 668265263

-- | MurmurHash3 mixing constant 1
mixConstant1 :: Int
mixConstant1 = -2048144789  -- 0x85ebca6b as signed 32-bit

-- | MurmurHash3 mixing constant 2
mixConstant2 :: Int
mixConstant2 = -1028477387  -- 0xc2b2ae35 as signed 32-bit

-- | Final mixing constant
mixConstant3 :: Int
mixConstant3 = 0x5bd1e995

--------------------------------------------------------------------------------
-- Utility
--------------------------------------------------------------------------------

-- | Integer multiplication (for hash mixing)
imul :: Int -> Int -> Int
imul a b = (a * b) `and` (-1)

--------------------------------------------------------------------------------
-- Hash Function
--------------------------------------------------------------------------------

-- | Hash function with improved bit mixing for seed/coordinate combination.
-- |
-- | Combines seed and 2D coordinates using MurmurHash3-style mixing
-- | to produce well-distributed pseudo-random values.
hash :: Int -> Int -> Int -> Int
hash seed px py =
  let h0 = seed `and` (-1)
      h1 = h0 `xor` (h0 `shr` 16)
      h2 = imul h1 mixConstant1
      h3 = h2 `xor` (h2 `shr` 13)
      h4 = imul h3 mixConstant2
      h5 = h4 `xor` (h4 `shr` 16)
      h6 = (h5 + imul px primeX + imul py primeY) `and` (-1)
      h7 = h6 `xor` (h6 `shr` 13)
      h8 = imul h7 mixConstant3
  in h8 `xor` (h8 `shr` 15)

--------------------------------------------------------------------------------
-- Gradient Function
--------------------------------------------------------------------------------

-- | Calculate gradient contribution from hash and offset.
-- |
-- | Uses 8 gradient directions for 2D noise:
-- | - h & 7 selects direction
-- | - Returns weighted sum of dx, dy based on direction
grad :: Int -> Number -> Number -> Number
grad h dx dy =
  let sel = h `and` 7
      u = if sel < 4 then dx else dy
      v = if sel < 4 then dy else dx
      signU = if (sel `and` 1) == 0 then u else -u
      signV = if (sel `and` 2) == 0 then 2.0 * v else -2.0 * v
  in signU + signV

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

-- | Linear interpolation
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + t * (b - a)

-- | Quintic fade curve: 6t⁵ - 15t⁴ + 10t³
-- | Provides smooth derivative at boundaries
fade :: Number -> Number
fade t = t * t * t * (t * (t * 6.0 - 15.0) + 10.0)

--------------------------------------------------------------------------------
-- Main Noise Function
--------------------------------------------------------------------------------

-- | 2D Simplex/Perlin noise.
-- |
-- | Generates smooth, continuous pseudo-random values based on
-- | 2D coordinates and a seed. Output is normalized to [0, 1].
-- |
-- | x, y: Sample coordinates
-- | seed: Random seed for determinism
-- |
-- | Returns value in [0, 1] range.
simplexNoise2D :: Number -> Number -> Int -> Number
simplexNoise2D x y seed =
  let -- Grid cell coordinates
      ix = floor x
      iy = floor y

      -- Fractional position within cell
      fx = x - toNumber ix
      fy = y - toNumber iy

      -- Hash the four corners
      n00 = grad (hash seed ix iy) fx fy
      n10 = grad (hash seed (ix + 1) iy) (fx - 1.0) fy
      n01 = grad (hash seed ix (iy + 1)) fx (fy - 1.0)
      n11 = grad (hash seed (ix + 1) (iy + 1)) (fx - 1.0) (fy - 1.0)

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
-- |
-- | Sums multiple noise layers at different frequencies and amplitudes.
-- |
-- | x, y: Sample coordinates
-- | seed: Random seed
-- | octaves: Number of layers (1-8 recommended)
-- | persistence: Amplitude multiplier per octave (0.5 typical)
-- | lacunarity: Frequency multiplier per octave (2.0 typical)
fbm :: Number -> Number -> Int -> Int -> Number -> Number -> Number
fbm x y seed octaves persistence lacunarity =
  let go i freq amp total maxVal
        | i >= octaves = { total, maxVal }
        | otherwise =
            let noise = simplexNoise2D (x * freq) (y * freq) seed
                total' = total + noise * amp
                maxVal' = maxVal + amp
            in go (i + 1) (freq * lacunarity) (amp * persistence) total' maxVal'
      result = go 0 1.0 1.0 0.0 0.0
  in if result.maxVal > 0.0 then result.total / result.maxVal else 0.5

-- | Turbulence noise using absolute value of noise layers.
-- |
-- | Creates sharper, more "turbulent" patterns than regular FBM.
turbulence :: Number -> Number -> Int -> Int -> Number -> Number -> Number
turbulence x y seed octaves persistence lacunarity =
  let go i freq amp total maxVal
        | i >= octaves = { total, maxVal }
        | otherwise =
            let noise = simplexNoise2D (x * freq) (y * freq) seed
                absNoise = Math.abs (noise * 2.0 - 1.0)
                total' = total + absNoise * amp
                maxVal' = maxVal + amp
            in go (i + 1) (freq * lacunarity) (amp * persistence) total' maxVal'
      result = go 0 1.0 1.0 0.0 0.0
  in if result.maxVal > 0.0 then result.total / result.maxVal else 0.5

--------------------------------------------------------------------------------
-- Ridge Noise
--------------------------------------------------------------------------------

-- | Ridge noise for mountain-like patterns.
-- |
-- | Creates sharp ridges by inverting absolute noise.
ridgeNoise :: Number -> Number -> Int -> Int -> Number -> Number -> Number -> Number
ridgeNoise x y seed octaves persistence lacunarity gain =
  let go i freq amp total weight
        | i >= octaves = total
        | otherwise =
            let noise = simplexNoise2D (x * freq) (y * freq) seed
                ridge = 1.0 - Math.abs (noise * 2.0 - 1.0)
                ridge' = ridge * ridge * weight
                total' = total + ridge' * amp
                weight' = min 1.0 (ridge' * gain)
            in go (i + 1) (freq * lacunarity) (amp * persistence) total' weight'
  in go 0 1.0 1.0 0.0 1.0
