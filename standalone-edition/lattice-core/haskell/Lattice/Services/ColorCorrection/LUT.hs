{-|
Module      : Lattice.Services.ColorCorrection.LUT
Description : 3D Look-Up Table Math
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for 3D LUT operations:
- Trilinear interpolation
- LUT index calculation
- Value sampling

All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts (lines 1706-1773)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.ColorCorrection.LUT
  ( -- * Types
    LUTSample(..)
  , TrilinearParams(..)
    -- * Index Calculation
  , lutIndex
  , trilinearParams
    -- * Trilinear Interpolation
  , trilinearInterpolateChannel
  , trilinearInterpolate
    -- * Blending
  , blendWithOriginal
  , sampleToRGB255
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Result of trilinear interpolation
data LUTSample = LUTSample
  { lutR :: Double
  , lutG :: Double
  , lutB :: Double
  } deriving (Show, Eq)

-- | Parameters for trilinear interpolation
data TrilinearParams = TrilinearParams
  { tpR0 :: Int       -- ^ Lower R index
  , tpR1 :: Int       -- ^ Upper R index
  , tpG0 :: Int       -- ^ Lower G index
  , tpG1 :: Int       -- ^ Upper G index
  , tpB0 :: Int       -- ^ Lower B index
  , tpB1 :: Int       -- ^ Upper B index
  , tpRFrac :: Double -- ^ R fractional part
  , tpGFrac :: Double -- ^ G fractional part
  , tpBFrac :: Double -- ^ B fractional part
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Index Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate LUT array index from 3D coordinates.
lutIndex :: Int  -- ^ r index
         -> Int  -- ^ g index
         -> Int  -- ^ b index
         -> Int  -- ^ size
         -> Int  -- ^ channel (0=R, 1=G, 2=B)
         -> Int
lutIndex r g b size channel = ((b * size + g) * size + r) * 3 + channel

-- | Calculate trilinear interpolation parameters.
trilinearParams :: Double  -- ^ r (0-1)
                -> Double  -- ^ g (0-1)
                -> Double  -- ^ b (0-1)
                -> Int     -- ^ size
                -> TrilinearParams
trilinearParams r g b size =
  let maxIdx = size - 1
      maxIdxF = fromIntegral maxIdx

      rIdx = r * maxIdxF
      gIdx = g * maxIdxF
      bIdx = b * maxIdxF

      r0 = min (floor rIdx) maxIdx
      g0 = min (floor gIdx) maxIdx
      b0 = min (floor bIdx) maxIdx

      r1 = min (r0 + 1) maxIdx
      g1 = min (g0 + 1) maxIdx
      b1 = min (b0 + 1) maxIdx

      rFrac = rIdx - fromIntegral (floor rIdx :: Int)
      gFrac = gIdx - fromIntegral (floor gIdx :: Int)
      bFrac = bIdx - fromIntegral (floor bIdx :: Int)
  in TrilinearParams r0 r1 g0 g1 b0 b1 rFrac gFrac bFrac

-- ────────────────────────────────────────────────────────────────────────────
-- Trilinear Interpolation
-- ────────────────────────────────────────────────────────────────────────────

-- | Perform trilinear interpolation for one channel.
trilinearInterpolateChannel :: Double -> Double -> Double -> Double
                            -> Double -> Double -> Double -> Double
                            -> Double -> Double -> Double
                            -> Double
trilinearInterpolateChannel c000 c100 c010 c110 c001 c101 c011 c111 rFrac gFrac bFrac =
  -- Interpolate along R axis
  let c00 = c000 + (c100 - c000) * rFrac
      c10 = c010 + (c110 - c010) * rFrac
      c01 = c001 + (c101 - c001) * rFrac
      c11 = c011 + (c111 - c011) * rFrac

      -- Interpolate along G axis
      c0 = c00 + (c10 - c00) * gFrac
      c1 = c01 + (c11 - c01) * gFrac

      -- Interpolate along B axis
  in c0 + (c1 - c0) * bFrac

-- | Perform full trilinear interpolation for RGB.
trilinearInterpolate :: LUTSample -> LUTSample -> LUTSample -> LUTSample
                     -> LUTSample -> LUTSample -> LUTSample -> LUTSample
                     -> TrilinearParams
                     -> LUTSample
trilinearInterpolate c000 c100 c010 c110 c001 c101 c011 c111 params =
  LUTSample
    { lutR = trilinearInterpolateChannel
               (lutR c000) (lutR c100) (lutR c010) (lutR c110)
               (lutR c001) (lutR c101) (lutR c011) (lutR c111)
               (tpRFrac params) (tpGFrac params) (tpBFrac params)
    , lutG = trilinearInterpolateChannel
               (lutG c000) (lutG c100) (lutG c010) (lutG c110)
               (lutG c001) (lutG c101) (lutG c011) (lutG c111)
               (tpRFrac params) (tpGFrac params) (tpBFrac params)
    , lutB = trilinearInterpolateChannel
               (lutB c000) (lutB c100) (lutB c010) (lutB c110)
               (lutB c001) (lutB c101) (lutB c011) (lutB c111)
               (tpRFrac params) (tpGFrac params) (tpBFrac params)
    }

-- ────────────────────────────────────────────────────────────────────────────
-- Blending
-- ────────────────────────────────────────────────────────────────────────────

-- | Blend LUT result with original color.
blendWithOriginal :: Double  -- ^ originalR
                  -> Double  -- ^ originalG
                  -> Double  -- ^ originalB
                  -> LUTSample
                  -> Double  -- ^ intensity
                  -> LUTSample
blendWithOriginal origR origG origB lutResult intensity =
  let invIntensity = 1 - intensity
  in LUTSample
       { lutR = origR * invIntensity + lutR lutResult * intensity
       , lutG = origG * invIntensity + lutG lutResult * intensity
       , lutB = origB * invIntensity + lutB lutResult * intensity
       }

-- | Convert LUT sample to 8-bit RGB values.
sampleToRGB255 :: LUTSample -> (Double, Double, Double)
sampleToRGB255 sample =
  ( max 0 (min 255 (lutR sample * 255))
  , max 0 (min 255 (lutG sample * 255))
  , max 0 (min 255 (lutB sample * 255))
  )
