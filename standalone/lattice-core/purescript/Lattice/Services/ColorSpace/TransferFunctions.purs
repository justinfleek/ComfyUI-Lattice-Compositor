-- | Lattice.Services.ColorSpace.TransferFunctions - Gamma/Transfer Functions
-- |
-- | Pure transfer functions for color space conversions:
-- | - sRGB gamma encoding/decoding
-- | - Simple power-law gamma
-- | - Linearization and gamma application
-- |
-- | Source: ui/src/services/colorManagement/ColorProfileService.ts

module Lattice.Services.ColorSpace.TransferFunctions
  ( -- * Types
    RGB, GammaType(..)
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

import Prelude
import Data.Int (floor, round, toNumber)
import Math (max, min, pow) as Math

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGB triplet (0-1 normalized)
type RGB =
  { r :: Number
  , g :: Number
  , b :: Number
  }

-- | Color space gamma type
data GammaType
  = Linear           -- No gamma (linear)
  | SRGB             -- sRGB transfer function
  | Power Number     -- Simple power-law gamma

derive instance eqGammaType :: Eq GammaType

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

-- | sRGB linear threshold for encoding
srgbLinearThreshold :: Number
srgbLinearThreshold = 0.0031308

-- | sRGB linear threshold for decoding
srgbDecodeThreshold :: Number
srgbDecodeThreshold = 0.04045

-- | sRGB linear scale factor
srgbLinearScale :: Number
srgbLinearScale = 12.92

-- | sRGB gamma exponent
srgbGamma :: Number
srgbGamma = 2.4

-- | sRGB offset constant
srgbOffset :: Number
srgbOffset = 0.055

-- | sRGB scale constant
srgbScale :: Number
srgbScale = 1.055

-- ────────────────────────────────────────────────────────────────────────────
-- sRGB Transfer Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | sRGB transfer function: linearize a single value.
-- |
-- | Maps sRGB-encoded value to linear light value.
-- | Uses piecewise function: linear near black, power for rest.
sRGBToLinear :: Number -> Number
sRGBToLinear value
  | value <= srgbDecodeThreshold = value / srgbLinearScale
  | otherwise = Math.pow ((value + srgbOffset) / srgbScale) srgbGamma

-- | sRGB inverse transfer: apply gamma to linear value.
-- |
-- | Maps linear light value to sRGB-encoded value.
linearToSRGB :: Number -> Number
linearToSRGB value
  | value <= srgbLinearThreshold = value * srgbLinearScale
  | otherwise = srgbScale * Math.pow value (1.0 / srgbGamma) - srgbOffset

-- ────────────────────────────────────────────────────────────────────────────
-- Simple Power-Law Gamma
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply gamma expansion (linearize) with power law.
-- |
-- | value^gamma
gammaToLinear :: Number -> Number -> Number
gammaToLinear value gamma = Math.pow (Math.max 0.0 value) gamma

-- | Apply gamma compression with power law.
-- |
-- | value^(1/gamma)
linearToGamma :: Number -> Number -> Number
linearToGamma value gamma
  | gamma == 0.0 = value
  | otherwise = Math.pow (Math.max 0.0 value) (1.0 / gamma)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // rgb // o
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply function to each RGB component
mapRGB :: (Number -> Number) -> RGB -> RGB
mapRGB f rgb = { r: f rgb.r, g: f rgb.g, b: f rgb.b }

-- | Linearize RGB based on gamma type
linearizeRGB :: RGB -> GammaType -> RGB
linearizeRGB rgb gammaType = case gammaType of
  Linear -> rgb
  SRGB -> mapRGB sRGBToLinear rgb
  Power g -> mapRGB (\v -> gammaToLinear v g) rgb

-- | Apply gamma to linear RGB
applyGammaRGB :: RGB -> GammaType -> RGB
applyGammaRGB rgb gammaType = case gammaType of
  Linear -> rgb
  SRGB -> mapRGB linearToSRGB rgb
  Power g -> mapRGB (\v -> linearToGamma v g) rgb

-- ────────────────────────────────────────────────────────────────────────────
-- Common Gamma Values
-- ────────────────────────────────────────────────────────────────────────────

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

-- ────────────────────────────────────────────────────────────────────────────
-- Clamping
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to [0, 1] range
clamp01 :: Number -> Number
clamp01 v = Math.max 0.0 (Math.min 1.0 v)

-- | Clamp RGB to [0, 1] range
clampRGB :: RGB -> RGB
clampRGB = mapRGB clamp01

-- ────────────────────────────────────────────────────────────────────────────
-- Bit Depth Conversion
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert 8-bit value (0-255) to normalized (0-1)
from8bit :: Int -> Number
from8bit v = toNumber v / 255.0

-- | Convert normalized (0-1) to 8-bit (0-255)
to8bit :: Number -> Int
to8bit v = round (clamp01 v * 255.0)

-- | Create RGB from 8-bit values
rgb8 :: Int -> Int -> Int -> RGB
rgb8 r g b = { r: from8bit r, g: from8bit g, b: from8bit b }

-- | Convert RGB to 8-bit tuple
toRGB8 :: RGB -> { r :: Int, g :: Int, b :: Int }
toRGB8 rgb = { r: to8bit rgb.r, g: to8bit rgb.g, b: to8bit rgb.b }
