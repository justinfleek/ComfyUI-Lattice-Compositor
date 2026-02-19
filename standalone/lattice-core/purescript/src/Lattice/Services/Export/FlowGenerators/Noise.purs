-- | Lattice.Services.Export.FlowGenerators.Noise - Simplex noise generation
-- |
-- | Perlin-style noise function for organic motion in flow generators.
-- | Uses improved bit mixing to avoid seed collisions.
-- |
-- | Source: ui/src/services/export/wanMoveFlowGenerators.ts (simplexNoise2D)

module Lattice.Services.Export.FlowGenerators.Noise
  ( simplexNoise2D
  , octaveNoise2D
  , fractalNoise2D
  ) where

import Prelude
import Data.Int (floor, toNumber)
import Data.Int.Bits as Bits

-- ────────────────────────────────────────────────────────────────────────────
--                                                               // bitwise ops
-- ────────────────────────────────────────────────────────────────────────────

-- | Bitwise zero-fill right shift
zshr :: Int -> Int -> Int
zshr = Bits.zshr

-- | Bitwise AND
and :: Int -> Int -> Int
and = Bits.(.&.)

-- | Bitwise XOR
xor :: Int -> Int -> Int
xor = Bits.xor

-- | Integer multiplication with overflow (JavaScript imul equivalent)
imul :: Int -> Int -> Int
imul a b = Bits.(.&.) (a * b) 0x7FFFFFFF

-- ────────────────────────────────────────────────────────────────────────────
-- Simplex Noise
-- ────────────────────────────────────────────────────────────────────────────

-- | Simplex noise 2D
-- | Returns value in range [0, 1]
simplexNoise2D :: Number -> Number -> Int -> Number
simplexNoise2D x y seed =
  let
    -- Grid coordinates
    ix = floor x
    iy = floor y
    fx = x - toNumber ix
    fy = y - toNumber iy

    -- Hash function with improved bit mixing
    hash :: Int -> Int -> Int
    hash px py =
      let
        h0 = seed `zshr` 0  -- Ensure unsigned
        h1 = imul (h0 `xor` (h0 `zshr` 16)) (-2048144789)  -- 0x85EBCA6B as signed 32-bit
        h2 = imul (h1 `xor` (h1 `zshr` 13)) (-1028477387)  -- 0xC2B2AE35 as signed 32-bit
        h3 = h2 `xor` (h2 `zshr` 16)
        h4 = h3 + px * 374761393 + py * 668265263
        h5 = imul (h4 `xor` (h4 `zshr` 13)) 0x5BD1E995
        h6 = h5 `xor` (h5 `zshr` 15)
      in
        h6 `zshr` 0  -- Return unsigned

    -- Gradient function
    grad :: Int -> Number -> Number -> Number
    grad h dx dy =
      let
        hMod = h `and` 7
        u = if hMod < 4 then dx else dy
        v = if hMod < 4 then dy else dx
        signU = if (h `and` 1) /= 0 then -u else u
        signV = if (h `and` 2) /= 0 then -2.0 * v else 2.0 * v
      in
        signU + signV

    -- Linear interpolation
    lerp :: Number -> Number -> Number -> Number
    lerp a b t = a + t * (b - a)

    -- Quintic fade function (smoother interpolation)
    fade :: Number -> Number -> Number
    fade t _ = t * t * t * (t * (t * 6.0 - 15.0) + 10.0)

    -- Compute noise at corners
    n00 = grad (hash ix iy) fx fy
    n10 = grad (hash (ix + 1) iy) (fx - 1.0) fy
    n01 = grad (hash ix (iy + 1)) fx (fy - 1.0)
    n11 = grad (hash (ix + 1) (iy + 1)) (fx - 1.0) (fy - 1.0)

    -- Interpolation weights
    u = fade fx 0.0
    v = fade fy 0.0

    -- Bilinear interpolation
    nx0 = lerp n00 n10 u
    nx1 = lerp n01 n11 u
    result = lerp nx0 nx1 v
  in
    -- Normalize to [0, 1]
    result * 0.5 + 0.5

-- ────────────────────────────────────────────────────────────────────────────
-- Higher-Order Noise Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Octave noise (multiple layers at different frequencies)
octaveNoise2D :: Int -> Number -> Number -> Number -> Int -> Number
octaveNoise2D octaves persistence x y seed =
  let
    go :: Int -> Number -> Number -> Number -> Number -> Number
    go oct amplitude freq total maxVal
      | oct >= octaves = total / maxVal
      | otherwise =
          let
            noise = simplexNoise2D (x * freq) (y * freq) (seed + oct)
            newTotal = total + noise * amplitude
            newMax = maxVal + amplitude
          in
            go (oct + 1) (amplitude * persistence) (freq * 2.0) newTotal newMax
  in
    go 0 1.0 1.0 0.0 0.0

-- | Fractal Brownian Motion noise
fractalNoise2D :: Int -> Number -> Number -> Number -> Number -> Int -> Number
fractalNoise2D octaves lacunarity gain x y seed =
  let
    go :: Int -> Number -> Number -> Number -> Number -> Number
    go oct amplitude freq total maxVal
      | oct >= octaves = total / maxVal
      | otherwise =
          let
            noise = simplexNoise2D (x * freq) (y * freq) (seed + oct * 1000)
            newTotal = total + noise * amplitude
            newMax = maxVal + amplitude
          in
            go (oct + 1) (amplitude * gain) (freq * lacunarity) newTotal newMax
  in
    go 0 1.0 1.0 0.0 0.0
