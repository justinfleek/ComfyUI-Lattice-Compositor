{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Services.ColorSpace.TransferFunctions
Description : Gamma/Transfer Functions
Copyright   : (c) Lattice, 2026
License     : MIT

Pure transfer functions for color space conversions:
- sRGB gamma encoding/decoding
- Simple power-law gamma
- Linearization and gamma application

Source: ui/src/services/colorManagement/ColorProfileService.ts
-}

module Lattice.Services.ColorSpace.TransferFunctions
  ( -- * Types
    RGB(..), GammaType(..)
    -- * sRGB Transfer
  , sRGBToLinear, linearToSRGB
    -- * Power-Law Gamma
  , gammaToLinear, linearToGamma
    -- * RGB Operations
  , mapRGB, linearizeRGB, applyGammaRGB
    -- * Common Gamma Values
  , gammaSRGB, gammaLinear, gammaWideGamut, gammaProPhoto
  , gammaRec709, gammaRec2020
    -- * Clamping
  , clamp01, clampRGB
    -- * Bit Depth Conversion
  , from8bit, to8bit, rgb8, toRGB8
  ) where

import Data.Word (Word8)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | RGB triplet (0-1 normalized)
data RGB = RGB
  { rgbR :: Double
  , rgbG :: Double
  , rgbB :: Double
  } deriving (Eq, Show)

-- | Color space gamma type
data GammaType
  = Linear           -- ^ No gamma (linear)
  | SRGB             -- ^ sRGB transfer function
  | Power Double     -- ^ Simple power-law gamma
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

-- | sRGB linear threshold for encoding
srgbLinearThreshold :: Double
srgbLinearThreshold = 0.0031308

-- | sRGB linear threshold for decoding
srgbDecodeThreshold :: Double
srgbDecodeThreshold = 0.04045

-- | sRGB linear scale factor
srgbLinearScale :: Double
srgbLinearScale = 12.92

-- | sRGB gamma exponent
srgbGamma :: Double
srgbGamma = 2.4

-- | sRGB offset constant
srgbOffset :: Double
srgbOffset = 0.055

-- | sRGB scale constant
srgbScale :: Double
srgbScale = 1.055

--------------------------------------------------------------------------------
-- sRGB Transfer Functions
--------------------------------------------------------------------------------

-- | sRGB transfer function: linearize a single value.
--
--   Maps sRGB-encoded value to linear light value.
--   Uses piecewise function: linear near black, power for rest.
sRGBToLinear :: Double -> Double
sRGBToLinear value
  | value <= srgbDecodeThreshold = value / srgbLinearScale
  | otherwise = ((value + srgbOffset) / srgbScale) ** srgbGamma

-- | sRGB inverse transfer: apply gamma to linear value.
--
--   Maps linear light value to sRGB-encoded value.
linearToSRGB :: Double -> Double
linearToSRGB value
  | value <= srgbLinearThreshold = value * srgbLinearScale
  | otherwise = srgbScale * (value ** (1 / srgbGamma)) - srgbOffset

--------------------------------------------------------------------------------
-- Simple Power-Law Gamma
--------------------------------------------------------------------------------

-- | Apply gamma expansion (linearize) with power law.
--
--   value^gamma
gammaToLinear :: Double -> Double -> Double
gammaToLinear value gamma = max 0 value ** gamma

-- | Apply gamma compression with power law.
--
--   value^(1/gamma)
linearToGamma :: Double -> Double -> Double
linearToGamma value gamma
  | gamma == 0 = value
  | otherwise = max 0 value ** (1 / gamma)

--------------------------------------------------------------------------------
-- RGB Operations
--------------------------------------------------------------------------------

-- | Apply function to each RGB component
mapRGB :: (Double -> Double) -> RGB -> RGB
mapRGB f (RGB r g b) = RGB (f r) (f g) (f b)

-- | Linearize RGB based on gamma type
linearizeRGB :: RGB -> GammaType -> RGB
linearizeRGB rgb gammaType = case gammaType of
  Linear -> rgb
  SRGB -> mapRGB sRGBToLinear rgb
  Power g -> mapRGB (`gammaToLinear` g) rgb

-- | Apply gamma to linear RGB
applyGammaRGB :: RGB -> GammaType -> RGB
applyGammaRGB rgb gammaType = case gammaType of
  Linear -> rgb
  SRGB -> mapRGB linearToSRGB rgb
  Power g -> mapRGB (`linearToGamma` g) rgb

--------------------------------------------------------------------------------
-- Common Gamma Values
--------------------------------------------------------------------------------

-- | sRGB gamma type
gammaSRGB :: GammaType
gammaSRGB = SRGB

-- | Linear gamma type
gammaLinear :: GammaType
gammaLinear = Linear

-- | Wide-Gamut RGB gamma (2.2)
gammaWideGamut :: GammaType
gammaWideGamut = Power 2.2

-- | ProPhoto RGB gamma (1.8)
gammaProPhoto :: GammaType
gammaProPhoto = Power 1.8

-- | Rec. 709 gamma (2.4)
gammaRec709 :: GammaType
gammaRec709 = Power 2.4

-- | Rec. 2020 gamma (2.4)
gammaRec2020 :: GammaType
gammaRec2020 = Power 2.4

--------------------------------------------------------------------------------
-- Clamping
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1] range
clamp01 :: Double -> Double
clamp01 v = max 0 (min 1 v)

-- | Clamp RGB to [0, 1] range
clampRGB :: RGB -> RGB
clampRGB = mapRGB clamp01

--------------------------------------------------------------------------------
-- Bit Depth Conversion
--------------------------------------------------------------------------------

-- | Convert 8-bit value (0-255) to normalized (0-1)
from8bit :: Word8 -> Double
from8bit v = fromIntegral v / 255

-- | Convert normalized (0-1) to 8-bit (0-255)
to8bit :: Double -> Word8
to8bit v = round (clamp01 v * 255)

-- | Create RGB from 8-bit values
rgb8 :: Word8 -> Word8 -> Word8 -> RGB
rgb8 r g b = RGB (from8bit r) (from8bit g) (from8bit b)

-- | Convert RGB to 8-bit tuple
toRGB8 :: RGB -> (Word8, Word8, Word8)
toRGB8 (RGB r g b) = (to8bit r, to8bit g, to8bit b)
