{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.BlendModes.Operations
Description : Blend mode operations
Copyright   : (c) Lattice, 2026
License     : MIT

Pure math functions implementing individual blend mode formulas.
All operations work on 0-255 channel values.

Source: ui/src/services/blendModes.ts (lines 150-361)
-}

module Lattice.Services.BlendModes.Operations
  ( -- * Helpers
    clamp
    -- * Basic Blend Modes
  , blendNormal, blendMultiply, blendScreen, blendOverlay
  , blendDarken, blendLighten
  , blendColorDodge, blendColorBurn
  , blendHardLight, blendSoftLight
  , blendDifference, blendExclusion, blendAdd
    -- * Extended Blend Modes
  , blendLinearBurn, blendVividLight, blendLinearLight
  , blendPinLight, blendHardMix
  , blendSubtract, blendDivide
    -- * Luminance-Based
  , blendDarkerColor, blendLighterColor
    -- * HSL Component Blend Modes
  , blendHue, blendSaturation, blendColor, blendLuminosity
    -- * Alpha Blend Modes
  , blendStencilAlpha, blendStencilLuma
  , blendSilhouetteAlpha, blendSilhouetteLuma
  , blendAlphaAdd
  ) where

import Lattice.Services.BlendModes.ColorSpace

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

-- | Clamp value to 0-255 range
clamp :: Double -> Double
clamp = max 0 . min 255 . fromIntegral . (round :: Double -> Int)

--------------------------------------------------------------------------------
-- Basic Blend Modes
--------------------------------------------------------------------------------

-- | Normal blend (returns blend value)
blendNormal :: Double -> Double -> Double
blendNormal _ blend = blend

-- | Multiply: (Base * Blend) / 255
blendMultiply :: Double -> Double -> Double
blendMultiply base blend = (base * blend) / 255.0

-- | Screen: 255 - ((255 - Base) * (255 - Blend)) / 255
blendScreen :: Double -> Double -> Double
blendScreen base blend = 255.0 - ((255.0 - base) * (255.0 - blend)) / 255.0

-- | Overlay: Multiply if base < 128, Screen otherwise
blendOverlay :: Double -> Double -> Double
blendOverlay base blend
  | base < 128.0 = (2.0 * base * blend) / 255.0
  | otherwise = 255.0 - (2.0 * (255.0 - base) * (255.0 - blend)) / 255.0

-- | Darken: min(Base, Blend)
blendDarken :: Double -> Double -> Double
blendDarken = min

-- | Lighten: max(Base, Blend)
blendLighten :: Double -> Double -> Double
blendLighten = max

-- | Color Dodge: Base / (1 - Blend/255) * 255
blendColorDodge :: Double -> Double -> Double
blendColorDodge base blend
  | blend >= 255.0 = 255.0
  | otherwise = clamp ((base * 255.0) / (255.0 - blend))

-- | Color Burn: 255 - (255 - Base) / (Blend/255)
blendColorBurn :: Double -> Double -> Double
blendColorBurn base blend
  | blend <= 0.0 = 0.0
  | otherwise = clamp (255.0 - ((255.0 - base) * 255.0) / blend)

-- | Hard Light: Overlay with base and blend swapped
blendHardLight :: Double -> Double -> Double
blendHardLight base blend
  | blend < 128.0 = (2.0 * base * blend) / 255.0
  | otherwise = 255.0 - (2.0 * (255.0 - base) * (255.0 - blend)) / 255.0

-- | Soft Light: Pegtop formula
blendSoftLight :: Double -> Double -> Double
blendSoftLight base blend =
  let b = base / 255.0
      s = blend / 255.0
      result = (1.0 - 2.0 * s) * b * b + 2.0 * s * b
  in clamp (result * 255.0)

-- | Difference: |Base - Blend|
blendDifference :: Double -> Double -> Double
blendDifference base blend = abs (base - blend)

-- | Exclusion: Base + Blend - 2 * Base * Blend / 255
blendExclusion :: Double -> Double -> Double
blendExclusion base blend = base + blend - (2.0 * base * blend) / 255.0

-- | Add (Linear Dodge): min(255, Base + Blend)
blendAdd :: Double -> Double -> Double
blendAdd base blend = min 255.0 (base + blend)

--------------------------------------------------------------------------------
-- Extended Blend Modes
--------------------------------------------------------------------------------

-- | Linear Burn: Base + Blend - 255
blendLinearBurn :: Double -> Double -> Double
blendLinearBurn base blend = clamp (base + blend - 255.0)

-- | Vivid Light: Color Burn if blend <= 128, Color Dodge otherwise
blendVividLight :: Double -> Double -> Double
blendVividLight base blend
  | blend <= 128.0 =
      if blend == 0.0 then 0.0
      else clamp (255.0 - ((255.0 - base) * 255.0) / (2.0 * blend))
  | otherwise =
      let adjusted = 2.0 * (blend - 128.0)
      in if adjusted >= 255.0 then 255.0
         else clamp ((base * 255.0) / (255.0 - adjusted))

-- | Linear Light: Linear Burn if blend <= 128, Linear Dodge otherwise
blendLinearLight :: Double -> Double -> Double
blendLinearLight base blend
  | blend <= 128.0 = clamp (base + 2.0 * blend - 255.0)
  | otherwise = clamp (base + 2.0 * (blend - 128.0))

-- | Pin Light: Darken if blend <= 128, Lighten otherwise
blendPinLight :: Double -> Double -> Double
blendPinLight base blend
  | blend <= 128.0 = min base (2.0 * blend)
  | otherwise = max base (2.0 * (blend - 128.0))

-- | Hard Mix: 0 or 255 based on Vivid Light threshold
blendHardMix :: Double -> Double -> Double
blendHardMix base blend =
  let vivid = blendVividLight base blend
  in if vivid < 128.0 then 0.0 else 255.0

-- | Subtract: Base - Blend
blendSubtract :: Double -> Double -> Double
blendSubtract base blend = clamp (base - blend)

-- | Divide: Base / Blend * 256
blendDivide :: Double -> Double -> Double
blendDivide base blend
  | blend == 0.0 = 255.0
  | otherwise = clamp ((base * 256.0) / blend)

--------------------------------------------------------------------------------
-- Luminance-Based Blend Modes
--------------------------------------------------------------------------------

-- | Darker Color: Return color with lower luminance
blendDarkerColor :: Double -> Double -> Double -> Double -> Double -> Double -> RGB
blendDarkerColor baseR baseG baseB blendR blendG blendB =
  let baseLum = getLuminance baseR baseG baseB
      blendLum = getLuminance blendR blendG blendB
  in if baseLum < blendLum
     then RGB baseR baseG baseB
     else RGB blendR blendG blendB

-- | Lighter Color: Return color with higher luminance
blendLighterColor :: Double -> Double -> Double -> Double -> Double -> Double -> RGB
blendLighterColor baseR baseG baseB blendR blendG blendB =
  let baseLum = getLuminance baseR baseG baseB
      blendLum = getLuminance blendR blendG blendB
  in if baseLum > blendLum
     then RGB baseR baseG baseB
     else RGB blendR blendG blendB

--------------------------------------------------------------------------------
-- HSL Component Blend Modes
--------------------------------------------------------------------------------

-- | Hue blend: Take hue from blend, saturation and luminance from base
blendHue :: Double -> Double -> Double -> Double -> Double -> Double -> RGB
blendHue baseR baseG baseB blendR blendG blendB =
  let baseHsl = rgbToHsl baseR baseG baseB
      blendHsl = rgbToHsl blendR blendG blendB
  in hslToRgb (HSL (hslH blendHsl) (hslS baseHsl) (hslL baseHsl))

-- | Saturation blend: Take saturation from blend, hue and luminance from base
blendSaturation :: Double -> Double -> Double -> Double -> Double -> Double -> RGB
blendSaturation baseR baseG baseB blendR blendG blendB =
  let baseHsl = rgbToHsl baseR baseG baseB
      blendHsl = rgbToHsl blendR blendG blendB
  in hslToRgb (HSL (hslH baseHsl) (hslS blendHsl) (hslL baseHsl))

-- | Color blend: Take hue and saturation from blend, luminance from base
blendColor :: Double -> Double -> Double -> Double -> Double -> Double -> RGB
blendColor baseR baseG baseB blendR blendG blendB =
  let baseHsl = rgbToHsl baseR baseG baseB
      blendHsl = rgbToHsl blendR blendG blendB
  in hslToRgb (HSL (hslH blendHsl) (hslS blendHsl) (hslL baseHsl))

-- | Luminosity blend: Take luminance from blend, hue and saturation from base
blendLuminosity :: Double -> Double -> Double -> Double -> Double -> Double -> RGB
blendLuminosity baseR baseG baseB blendR blendG blendB =
  let baseHsl = rgbToHsl baseR baseG baseB
      blendHsl = rgbToHsl blendR blendG blendB
  in hslToRgb (HSL (hslH baseHsl) (hslS baseHsl) (hslL blendHsl))

--------------------------------------------------------------------------------
-- Alpha Blend Modes
--------------------------------------------------------------------------------

-- | Stencil Alpha: Multiply base alpha by blend alpha
blendStencilAlpha :: Double -> Double -> Double
blendStencilAlpha baseA blendA =
  fromIntegral (round ((baseA / 255.0) * (blendA / 255.0) * 255.0) :: Int)

-- | Stencil Luma: Multiply base alpha by blend luminance
blendStencilLuma :: Double -> Double -> Double -> Double -> Double
blendStencilLuma baseA blendR blendG blendB =
  let blendLum = getLuminance blendR blendG blendB / 255.0
  in fromIntegral (round ((baseA / 255.0) * blendLum * 255.0) :: Int)

-- | Silhouette Alpha: base * (1 - blend alpha)
blendSilhouetteAlpha :: Double -> Double -> Double
blendSilhouetteAlpha baseA blendA =
  fromIntegral (round ((baseA / 255.0) * (1.0 - blendA / 255.0) * 255.0) :: Int)

-- | Silhouette Luma: base * (1 - blend luminance)
blendSilhouetteLuma :: Double -> Double -> Double -> Double -> Double
blendSilhouetteLuma baseA blendR blendG blendB =
  let blendLum = getLuminance blendR blendG blendB / 255.0
  in fromIntegral (round ((baseA / 255.0) * (1.0 - blendLum) * 255.0) :: Int)

-- | Alpha Add: min(255, baseA + blendA)
blendAlphaAdd :: Double -> Double -> Double
blendAlphaAdd baseA blendA = clamp (baseA + blendA)
