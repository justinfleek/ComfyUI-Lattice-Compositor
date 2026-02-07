-- | Lattice.Services.ColorCorrection.LUT - 3D Look-Up Table Math
-- |
-- | Pure mathematical functions for 3D LUT operations:
-- | - Trilinear interpolation
-- | - LUT index calculation
-- | - Value sampling
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/effects/colorRenderer.ts (lines 1706-1773)

module Lattice.Services.ColorCorrection.LUT
  ( LUTSample
  , TrilinearParams
  , lutIndex
  , trilinearParams
  , trilinearInterpolateChannel
  , trilinearInterpolate
  , blendWithOriginal
  , sampleToRGB255
  ) where

import Prelude

import Data.Int (toNumber, floor) as Int
import Data.Tuple (Tuple(..))
import Math (floor, max, min)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of trilinear interpolation
type LUTSample =
  { r :: Number
  , g :: Number
  , b :: Number
  }

-- | Parameters for trilinear interpolation
type TrilinearParams =
  { r0 :: Int       -- ^ Lower R index
  , r1 :: Int       -- ^ Upper R index
  , g0 :: Int       -- ^ Lower G index
  , g1 :: Int       -- ^ Upper G index
  , b0 :: Int       -- ^ Lower B index
  , b1 :: Int       -- ^ Upper B index
  , rFrac :: Number -- ^ R fractional part
  , gFrac :: Number -- ^ G fractional part
  , bFrac :: Number -- ^ B fractional part
  }

--------------------------------------------------------------------------------
-- Index Calculation
--------------------------------------------------------------------------------

-- | Calculate LUT array index from 3D coordinates.
lutIndex :: Int -> Int -> Int -> Int -> Int -> Int
lutIndex r g b size channel = ((b * size + g) * size + r) * 3 + channel

-- | Calculate trilinear interpolation parameters.
trilinearParams :: Number -> Number -> Number -> Int -> TrilinearParams
trilinearParams r g b size =
  let maxIdx = size - 1
      maxIdxF = Int.toNumber maxIdx

      rIdx = r * maxIdxF
      gIdx = g * maxIdxF
      bIdx = b * maxIdxF

      r0 = min (Int.floor rIdx) maxIdx
      g0 = min (Int.floor gIdx) maxIdx
      b0 = min (Int.floor bIdx) maxIdx

      r1 = min (r0 + 1) maxIdx
      g1 = min (g0 + 1) maxIdx
      b1 = min (b0 + 1) maxIdx

      rFrac = rIdx - floor rIdx
      gFrac = gIdx - floor gIdx
      bFrac = bIdx - floor bIdx
  in { r0, r1, g0, g1, b0, b1, rFrac, gFrac, bFrac }

--------------------------------------------------------------------------------
-- Trilinear Interpolation
--------------------------------------------------------------------------------

-- | Perform trilinear interpolation for one channel.
trilinearInterpolateChannel :: Number -> Number -> Number -> Number
                            -> Number -> Number -> Number -> Number
                            -> Number -> Number -> Number
                            -> Number
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
  { r: trilinearInterpolateChannel
         c000.r c100.r c010.r c110.r c001.r c101.r c011.r c111.r
         params.rFrac params.gFrac params.bFrac
  , g: trilinearInterpolateChannel
         c000.g c100.g c010.g c110.g c001.g c101.g c011.g c111.g
         params.rFrac params.gFrac params.bFrac
  , b: trilinearInterpolateChannel
         c000.b c100.b c010.b c110.b c001.b c101.b c011.b c111.b
         params.rFrac params.gFrac params.bFrac
  }

--------------------------------------------------------------------------------
-- Blending
--------------------------------------------------------------------------------

-- | Blend LUT result with original color.
blendWithOriginal :: Number -> Number -> Number -> LUTSample -> Number -> LUTSample
blendWithOriginal origR origG origB lutResult intensity =
  let invIntensity = 1.0 - intensity
  in { r: origR * invIntensity + lutResult.r * intensity
     , g: origG * invIntensity + lutResult.g * intensity
     , b: origB * invIntensity + lutResult.b * intensity
     }

-- | Convert LUT sample to 8-bit RGB values.
sampleToRGB255 :: LUTSample -> Tuple Number (Tuple Number Number)
sampleToRGB255 sample =
  Tuple (max 0.0 (min 255.0 (sample.r * 255.0)))
        (Tuple (max 0.0 (min 255.0 (sample.g * 255.0)))
               (max 0.0 (min 255.0 (sample.b * 255.0))))
