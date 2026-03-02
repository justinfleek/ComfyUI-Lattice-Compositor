-- | Lattice.Services.BlendModes.Operations - Blend mode operations
-- |
-- | Pure math functions implementing individual blend mode formulas.
-- | All operations work on 0-255 channel values.
-- |
-- | Source: ui/src/services/blendModes.ts (lines 150-361)

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

import Prelude
import Math (abs, round, max, min) as Math
import Lattice.Services.BlendModes.ColorSpace (RGB(..), HSL(..), rgbToHsl, hslToRgb, getLuminance)

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp value to 0-255 range
clamp :: Number -> Number
clamp = Math.max 0.0 <<< Math.min 255.0 <<< Math.round

-- ────────────────────────────────────────────────────────────────────────────
-- Basic Blend Modes
-- ────────────────────────────────────────────────────────────────────────────

-- | Normal blend (returns blend value)
blendNormal :: Number -> Number -> Number
blendNormal _ blend = blend

-- | Multiply: (Base * Blend) / 255
blendMultiply :: Number -> Number -> Number
blendMultiply base blend = (base * blend) / 255.0

-- | Screen: 255 - ((255 - Base) * (255 - Blend)) / 255
blendScreen :: Number -> Number -> Number
blendScreen base blend = 255.0 - ((255.0 - base) * (255.0 - blend)) / 255.0

-- | Overlay: Multiply if base < 128, Screen otherwise
blendOverlay :: Number -> Number -> Number
blendOverlay base blend
  | base < 128.0 = (2.0 * base * blend) / 255.0
  | otherwise = 255.0 - (2.0 * (255.0 - base) * (255.0 - blend)) / 255.0

-- | Darken: min(Base, Blend)
blendDarken :: Number -> Number -> Number
blendDarken = Math.min

-- | Lighten: max(Base, Blend)
blendLighten :: Number -> Number -> Number
blendLighten = Math.max

-- | Color Dodge: Base / (1 - Blend/255) * 255
blendColorDodge :: Number -> Number -> Number
blendColorDodge base blend
  | blend >= 255.0 = 255.0
  | otherwise = clamp ((base * 255.0) / (255.0 - blend))

-- | Color Burn: 255 - (255 - Base) / (Blend/255)
blendColorBurn :: Number -> Number -> Number
blendColorBurn base blend
  | blend <= 0.0 = 0.0
  | otherwise = clamp (255.0 - ((255.0 - base) * 255.0) / blend)

-- | Hard Light: Overlay with base and blend swapped
blendHardLight :: Number -> Number -> Number
blendHardLight base blend
  | blend < 128.0 = (2.0 * base * blend) / 255.0
  | otherwise = 255.0 - (2.0 * (255.0 - base) * (255.0 - blend)) / 255.0

-- | Soft Light: Pegtop formula
blendSoftLight :: Number -> Number -> Number
blendSoftLight base blend =
  let b = base / 255.0
      s = blend / 255.0
      result = (1.0 - 2.0 * s) * b * b + 2.0 * s * b
  in clamp (result * 255.0)

-- | Difference: |Base - Blend|
blendDifference :: Number -> Number -> Number
blendDifference base blend = Math.abs (base - blend)

-- | Exclusion: Base + Blend - 2 * Base * Blend / 255
blendExclusion :: Number -> Number -> Number
blendExclusion base blend = base + blend - (2.0 * base * blend) / 255.0

-- | Add (Linear Dodge): min(255, Base + Blend)
blendAdd :: Number -> Number -> Number
blendAdd base blend = Math.min 255.0 (base + blend)

-- ────────────────────────────────────────────────────────────────────────────
-- Extended Blend Modes
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear Burn: Base + Blend - 255
blendLinearBurn :: Number -> Number -> Number
blendLinearBurn base blend = clamp (base + blend - 255.0)

-- | Vivid Light: Color Burn if blend <= 128, Color Dodge otherwise
blendVividLight :: Number -> Number -> Number
blendVividLight base blend
  | blend <= 128.0 =
      if blend == 0.0 then 0.0
      else clamp (255.0 - ((255.0 - base) * 255.0) / (2.0 * blend))
  | otherwise =
      let adjusted = 2.0 * (blend - 128.0)
      in if adjusted >= 255.0 then 255.0
         else clamp ((base * 255.0) / (255.0 - adjusted))

-- | Linear Light: Linear Burn if blend <= 128, Linear Dodge otherwise
blendLinearLight :: Number -> Number -> Number
blendLinearLight base blend
  | blend <= 128.0 = clamp (base + 2.0 * blend - 255.0)
  | otherwise = clamp (base + 2.0 * (blend - 128.0))

-- | Pin Light: Darken if blend <= 128, Lighten otherwise
blendPinLight :: Number -> Number -> Number
blendPinLight base blend
  | blend <= 128.0 = Math.min base (2.0 * blend)
  | otherwise = Math.max base (2.0 * (blend - 128.0))

-- | Hard Mix: 0 or 255 based on Vivid Light threshold
blendHardMix :: Number -> Number -> Number
blendHardMix base blend =
  let vivid = blendVividLight base blend
  in if vivid < 128.0 then 0.0 else 255.0

-- | Subtract: Base - Blend
blendSubtract :: Number -> Number -> Number
blendSubtract base blend = clamp (base - blend)

-- | Divide: Base / Blend * 256
blendDivide :: Number -> Number -> Number
blendDivide base blend
  | blend == 0.0 = 255.0
  | otherwise = clamp ((base * 256.0) / blend)

-- ────────────────────────────────────────────────────────────────────────────
-- Luminance-Based Blend Modes
-- ────────────────────────────────────────────────────────────────────────────

-- | Darker Color: Return color with lower luminance
blendDarkerColor :: Number -> Number -> Number -> Number -> Number -> Number -> RGB
blendDarkerColor baseR baseG baseB blendR blendG blendB =
  let baseLum = getLuminance baseR baseG baseB
      blendLum = getLuminance blendR blendG blendB
  in if baseLum < blendLum
     then RGB { r: baseR, g: baseG, b: baseB }
     else RGB { r: blendR, g: blendG, b: blendB }

-- | Lighter Color: Return color with higher luminance
blendLighterColor :: Number -> Number -> Number -> Number -> Number -> Number -> RGB
blendLighterColor baseR baseG baseB blendR blendG blendB =
  let baseLum = getLuminance baseR baseG baseB
      blendLum = getLuminance blendR blendG blendB
  in if baseLum > blendLum
     then RGB { r: baseR, g: baseG, b: baseB }
     else RGB { r: blendR, g: blendG, b: blendB }

-- ────────────────────────────────────────────────────────────────────────────
--                                                                  // hsl // c
-- ────────────────────────────────────────────────────────────────────────────

-- | Hue blend: Take hue from blend, saturation and luminance from base
blendHue :: Number -> Number -> Number -> Number -> Number -> Number -> RGB
blendHue baseR baseG baseB blendR blendG blendB =
  case rgbToHsl baseR baseG baseB of
    HSL baseHsl -> case rgbToHsl blendR blendG blendB of
      HSL blendHsl -> hslToRgb (HSL { h: blendHsl.h, s: baseHsl.s, l: baseHsl.l })

-- | Saturation blend: Take saturation from blend, hue and luminance from base
blendSaturation :: Number -> Number -> Number -> Number -> Number -> Number -> RGB
blendSaturation baseR baseG baseB blendR blendG blendB =
  case rgbToHsl baseR baseG baseB of
    HSL baseHsl -> case rgbToHsl blendR blendG blendB of
      HSL blendHsl -> hslToRgb (HSL { h: baseHsl.h, s: blendHsl.s, l: baseHsl.l })

-- | Color blend: Take hue and saturation from blend, luminance from base
blendColor :: Number -> Number -> Number -> Number -> Number -> Number -> RGB
blendColor baseR baseG baseB blendR blendG blendB =
  case rgbToHsl baseR baseG baseB of
    HSL baseHsl -> case rgbToHsl blendR blendG blendB of
      HSL blendHsl -> hslToRgb (HSL { h: blendHsl.h, s: blendHsl.s, l: baseHsl.l })

-- | Luminosity blend: Take luminance from blend, hue and saturation from base
blendLuminosity :: Number -> Number -> Number -> Number -> Number -> Number -> RGB
blendLuminosity baseR baseG baseB blendR blendG blendB =
  case rgbToHsl baseR baseG baseB of
    HSL baseHsl -> case rgbToHsl blendR blendG blendB of
      HSL blendHsl -> hslToRgb (HSL { h: baseHsl.h, s: baseHsl.s, l: blendHsl.l })

-- ────────────────────────────────────────────────────────────────────────────
-- Alpha Blend Modes
-- ────────────────────────────────────────────────────────────────────────────

-- | Stencil Alpha: Multiply base alpha by blend alpha
blendStencilAlpha :: Number -> Number -> Number
blendStencilAlpha baseA blendA =
  Math.round ((baseA / 255.0) * (blendA / 255.0) * 255.0)

-- | Stencil Luma: Multiply base alpha by blend luminance
blendStencilLuma :: Number -> Number -> Number -> Number -> Number
blendStencilLuma baseA blendR blendG blendB =
  let blendLum = getLuminance blendR blendG blendB / 255.0
  in Math.round ((baseA / 255.0) * blendLum * 255.0)

-- | Silhouette Alpha: base * (1 - blend alpha)
blendSilhouetteAlpha :: Number -> Number -> Number
blendSilhouetteAlpha baseA blendA =
  Math.round ((baseA / 255.0) * (1.0 - blendA / 255.0) * 255.0)

-- | Silhouette Luma: base * (1 - blend luminance)
blendSilhouetteLuma :: Number -> Number -> Number -> Number -> Number
blendSilhouetteLuma baseA blendR blendG blendB =
  let blendLum = getLuminance blendR blendG blendB / 255.0
  in Math.round ((baseA / 255.0) * (1.0 - blendLum) * 255.0)

-- | Alpha Add: min(255, baseA + blendA)
blendAlphaAdd :: Number -> Number -> Number
blendAlphaAdd baseA blendA = clamp (baseA + blendA)
