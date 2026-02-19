-- |
-- Module      : Lattice.Services.BlendModes
-- Description : Pure blend mode functions for image compositing
-- 
-- Migrated from ui/src/services/blendModes.ts
-- Pure pixel-level blend mode calculations
-- Note: Canvas operations (blendImages) deferred
--
-- HSL-based blend modes (Hue, Saturation, Color, Luminosity) use proven
-- color conversions from Lattice.Types.Color, which are proven correct
-- in Lean4 (lattice-core/lean/Color/Color.lean and Color.BlendModes.lean)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.BlendModes
  ( -- Color space functions
    rgbToHsl
  , hslToRgb
  , getLuminance
  , clampRGB
  -- Blend mode functions
  , blendDissolve
  , blendLinearBurn
  , blendDarkerColor
  , blendLighterColor
  , blendVividLight
  , blendLinearLight
  , blendPinLight
  , blendHardMix
  , blendSubtract
  , blendDivide
  , blendHue
  , blendSaturation
  , blendColor
  , blendLuminosity
  -- Pixel blend function
  , blendPixel
  -- Utility functions
  , isNativeBlendMode
  , getNativeBlendOp
  , getBlendModeDisplayName
  -- Types
  , PixelRGBA(..)
  ) where

import Data.Bits (xor)
import qualified Data.Text as T
import Lattice.Types.Primitives (BlendMode(..))
import Lattice.Types.Color
  ( HSL(..)
  , Hue(..)
  , Saturation(..)
  , Lightness(..)
  , RGB(..)
  , RGB8(..)
  , rgbToHSL
  , hslToRGB
  , rgb8Value
  )
import Lattice.Utils.NumericSafety (ensureFinite)

-- ============================================================================
-- TYPES
-- ============================================================================

-- Note: RGB and HSL types are imported from Lattice.Types.Color (proven)
-- These use the Lean4-proven color system from lattice-core/lean/Color/Color.lean

-- | RGBA pixel
data PixelRGBA = PixelRGBA
  { pixelR :: Int
  , pixelG :: Int
  , pixelB :: Int
  , pixelA :: Int
  }
  deriving (Eq, Show)

-- ============================================================================
-- COLOR SPACE FUNCTIONS (USING PROVEN CONVERSIONS)
-- ============================================================================

-- | Convert RGB (Int components) to HSL using proven conversion
-- Uses Lattice.Types.Color.rgbToHSL (proven in Lean4)
rgbToHsl :: Int -> Int -> Int -> HSL
rgbToHsl r g b =
  let rgb = RGB (RGB8 r) (RGB8 g) (RGB8 b)
  in rgbToHSL rgb

-- | Convert HSL to RGB (Int components) using proven conversion
-- Uses Lattice.Types.Color.hslToRGB (proven in Lean4)
hslToRgb :: Double -> Double -> Double -> RGB
hslToRgb hDeg s l =
  let hsl = HSL
        { hslHue = Hue hDeg
        , hslSaturation = Saturation s
        , hslLightness = Lightness l
        }
      rgb = hslToRGB hsl
  in RGB (RGB8 (rgb8Value (rgbR rgb))) (RGB8 (rgb8Value (rgbG rgb))) (RGB8 (rgb8Value (rgbB rgb)))

-- | Get luminance of RGB color (0-255 scale)
-- Pure function: same inputs → same outputs
getLuminance :: Int -> Int -> Int -> Double
getLuminance r g b =
  let rD = fromIntegral r
      gD = fromIntegral g
      bD = fromIntegral b
  in ensureFinite (0.299 * rD + 0.587 * gD + 0.114 * bD) 0.0

-- | Clamp value to 0-255
-- Pure function: same inputs → same outputs
clampRGB :: Int -> Int
clampRGB value = max 0 (min 255 value)

-- ============================================================================
-- BLEND MODE FUNCTIONS
-- ============================================================================

-- | Dissolve blend (requires seeded random)
-- Pure function: same inputs → same outputs
-- Uses deterministic seeded random based on position and frame
blendDissolve ::
  Int -> Int -> Int -> Int ->  -- Base RGBA
  Int -> Int -> Int -> Int ->  -- Blend RGBA
  Int -> Int -> Int ->          -- x, y, frame (for seeded random)
  (Int, Int, Int, Int)          -- Result RGBA
blendDissolve baseR baseG baseB baseA blendR blendG blendB blendA x y frame =
  let -- Seeded random based on position and frame
      seed = ((x * 73856093) `xor` (y * 19349663) `xor` (frame * 83492791)) `mod` 1000000
      randomVal = fromIntegral seed / 1000000.0
      blendOpacity = fromIntegral blendA / 255.0
  in if randomVal < blendOpacity
     then (blendR, blendG, blendB, 255)
     else (baseR, baseG, baseB, baseA)

-- | Linear Burn: Base + Blend - 255
-- Pure function: same inputs → same outputs
blendLinearBurn :: Int -> Int -> Int
blendLinearBurn base blend = clampRGB (base + blend - 255)

-- | Darker Color: Return pixel with lower luminance
-- Pure function: same inputs → same outputs
blendDarkerColor :: Int -> Int -> Int -> Int -> Int -> Int -> (Int, Int, Int)
blendDarkerColor baseR baseG baseB blendR blendG blendB =
  let baseLum = getLuminance baseR baseG baseB
      blendLum = getLuminance blendR blendG blendB
  in if baseLum < blendLum
     then (baseR, baseG, baseB)
     else (blendR, blendG, blendB)

-- | Lighter Color: Return pixel with higher luminance
-- Pure function: same inputs → same outputs
blendLighterColor :: Int -> Int -> Int -> Int -> Int -> Int -> (Int, Int, Int)
blendLighterColor baseR baseG baseB blendR blendG blendB =
  let baseLum = getLuminance baseR baseG baseB
      blendLum = getLuminance blendR blendG blendB
  in if baseLum > blendLum
     then (baseR, baseG, baseB)
     else (blendR, blendG, blendB)

-- | Vivid Light: Combination of Color Burn and Color Dodge
-- Pure function: same inputs → same outputs
blendVividLight :: Int -> Int -> Int
blendVividLight base blend =
  if blend <= 128
  then
    -- Color Burn
    if blend == 0
    then 0
    else clampRGB (255 - ((255 - base) * 255) `div` (2 * blend))
  else
    -- Color Dodge
    let adjusted = 2 * (blend - 128)
    in if adjusted == 255
       then 255
       else clampRGB ((base * 255) `div` (255 - adjusted))

-- | Linear Light: Combination of Linear Burn and Linear Dodge
-- Pure function: same inputs → same outputs
blendLinearLight :: Int -> Int -> Int
blendLinearLight base blend =
  if blend <= 128
  then clampRGB (base + 2 * blend - 255)  -- Linear Burn
  else clampRGB (base + 2 * (blend - 128))  -- Linear Dodge

-- | Pin Light: Combination of Darken and Lighten
-- Pure function: same inputs → same outputs
blendPinLight :: Int -> Int -> Int
blendPinLight base blend =
  if blend <= 128
  then min base (2 * blend)  -- Darken with 2x blend
  else max base (2 * (blend - 128))  -- Lighten with 2x (blend - 128)

-- | Hard Mix: Extreme contrast - result is either 0 or 255
-- Pure function: same inputs → same outputs
blendHardMix :: Int -> Int -> Int
blendHardMix base blend =
  let vivid = blendVividLight base blend
  in if vivid < 128 then 0 else 255

-- | Subtract: Base - Blend
-- Pure function: same inputs → same outputs
blendSubtract :: Int -> Int -> Int
blendSubtract base blend = clampRGB (base - blend)

-- | Divide: Base / Blend (scaled)
-- Pure function: same inputs → same outputs
blendDivide :: Int -> Int -> Int
blendDivide base blend =
  if blend == 0
  then 255  -- Avoid division by zero
  else clampRGB ((base * 256) `div` blend)

-- | Hue blend: Take hue from blend, saturation and lightness from base
-- Uses proven HSL conversions (Lean4 proofs: Color.BlendModes.lean)
blendHue :: Int -> Int -> Int -> Int -> Int -> Int -> (Int, Int, Int)
blendHue baseR baseG baseB blendR blendG blendB =
  let baseHSL = rgbToHsl baseR baseG baseB
      blendHSL = rgbToHsl blendR blendG blendB
      -- Extract components using proven operations
      baseSat = saturationValue (hslSaturation baseHSL)
      baseLum = lightnessValue (hslLightness baseHSL)
      blendHueVal = hueValue (hslHue blendHSL)
      -- Recombine: hue from blend, saturation/lightness from base
      blendedHSL = HSL
        { hslHue = Hue blendHueVal
        , hslSaturation = Saturation baseSat
        , hslLightness = Lightness baseLum
        }
      resultRGB = hslToRGB blendedHSL
  in (rgb8Value (rgbR resultRGB), rgb8Value (rgbG resultRGB), rgb8Value (rgbB resultRGB))

-- | Saturation blend: Take saturation from blend, hue and lightness from base
-- Uses proven HSL conversions (Lean4 proofs: Color.BlendModes.lean)
blendSaturation :: Int -> Int -> Int -> Int -> Int -> Int -> (Int, Int, Int)
blendSaturation baseR baseG baseB blendR blendG blendB =
  let baseHSL = rgbToHsl baseR baseG baseB
      blendHSL = rgbToHsl blendR blendG blendB
      baseHueVal = hueValue (hslHue baseHSL)
      baseLum = lightnessValue (hslLightness baseHSL)
      blendSat = saturationValue (hslSaturation blendHSL)
      blendedHSL = HSL
        { hslHue = Hue baseHueVal
        , hslSaturation = Saturation blendSat
        , hslLightness = Lightness baseLum
        }
      resultRGB = hslToRGB blendedHSL
  in (rgb8Value (rgbR resultRGB), rgb8Value (rgbG resultRGB), rgb8Value (rgbB resultRGB))

-- | Color blend: Take hue and saturation from blend, lightness from base
-- Uses proven HSL conversions (Lean4 proofs: Color.BlendModes.lean)
blendColor :: Int -> Int -> Int -> Int -> Int -> Int -> (Int, Int, Int)
blendColor baseR baseG baseB blendR blendG blendB =
  let baseHSL = rgbToHsl baseR baseG baseB
      blendHSL = rgbToHsl blendR blendG blendB
      baseLum = lightnessValue (hslLightness baseHSL)
      blendHueVal = hueValue (hslHue blendHSL)
      blendSat = saturationValue (hslSaturation blendHSL)
      blendedHSL = HSL
        { hslHue = Hue blendHueVal
        , hslSaturation = Saturation blendSat
        , hslLightness = Lightness baseLum
        }
      resultRGB = hslToRGB blendedHSL
  in (rgb8Value (rgbR resultRGB), rgb8Value (rgbG resultRGB), rgb8Value (rgbB resultRGB))

-- | Luminosity blend: Take lightness from blend, hue and saturation from base
-- Uses proven HSL conversions (Lean4 proofs: Color.BlendModes.lean)
blendLuminosity :: Int -> Int -> Int -> Int -> Int -> Int -> (Int, Int, Int)
blendLuminosity baseR baseG baseB blendR blendG blendB =
  let baseHSL = rgbToHsl baseR baseG baseB
      blendHSL = rgbToHsl blendR blendG blendB
      baseHueVal = hueValue (hslHue baseHSL)
      baseSat = saturationValue (hslSaturation baseHSL)
      blendLum = lightnessValue (hslLightness blendHSL)
      blendedHSL = HSL
        { hslHue = Hue baseHueVal
        , hslSaturation = Saturation baseSat
        , hslLightness = Lightness blendLum
        }
      resultRGB = hslToRGB blendedHSL
  in (rgb8Value (rgbR resultRGB), rgb8Value (rgbG resultRGB), rgb8Value (rgbB resultRGB))

-- ============================================================================
-- PIXEL BLEND FUNCTION
-- ============================================================================

-- | Apply blend mode to a single pixel
-- Pure function: same inputs → same outputs
blendPixel ::
  Int -> Int -> Int -> Int ->  -- Base RGBA
  Int -> Int -> Int -> Int ->  -- Blend RGBA
  BlendMode ->                 -- Blend mode
  Double ->                     -- Opacity (0-1)
  (Int, Int, Int, Int)          -- Result RGBA
blendPixel baseR baseG baseB baseA blendR blendG blendB blendA mode opacity =
  let finiteOpacity = max 0.0 (min 1.0 (ensureFinite opacity 1.0))
      (resultR, resultG, resultB, resultA) = case mode of
        BlendNormal -> (blendR, blendG, blendB, blendA)
        BlendMultiply ->
          (clampRGB ((baseR * blendR) `div` 255),
           clampRGB ((baseG * blendG) `div` 255),
           clampRGB ((baseB * blendB) `div` 255),
           baseA)
        BlendScreen ->
          (clampRGB (255 - ((255 - baseR) * (255 - blendR)) `div` 255),
           clampRGB (255 - ((255 - baseG) * (255 - blendG)) `div` 255),
           clampRGB (255 - ((255 - baseB) * (255 - blendB)) `div` 255),
           baseA)
        BlendOverlay ->
          (if baseR < 128
           then clampRGB ((2 * baseR * blendR) `div` 255)
           else clampRGB (255 - ((2 * (255 - baseR) * (255 - blendR)) `div` 255)),
           if baseG < 128
           then clampRGB ((2 * baseG * blendG) `div` 255)
           else clampRGB (255 - ((2 * (255 - baseG) * (255 - blendG)) `div` 255)),
           if baseB < 128
           then clampRGB ((2 * baseB * blendB) `div` 255)
           else clampRGB (255 - ((2 * (255 - baseB) * (255 - blendB)) `div` 255)),
           baseA)
        BlendLinearBurn ->
          (blendLinearBurn baseR blendR,
           blendLinearBurn baseG blendG,
           blendLinearBurn baseB blendB,
           baseA)
        BlendVividLight ->
          (blendVividLight baseR blendR,
           blendVividLight baseG blendG,
           blendVividLight baseB blendB,
           baseA)
        BlendLinearLight ->
          (blendLinearLight baseR blendR,
           blendLinearLight baseG blendG,
           blendLinearLight baseB blendB,
           baseA)
        BlendPinLight ->
          (blendPinLight baseR blendR,
           blendPinLight baseG blendG,
           blendPinLight baseB blendB,
           baseA)
        BlendHardMix ->
          (blendHardMix baseR blendR,
           blendHardMix baseG blendG,
           blendHardMix baseB blendB,
           baseA)
        BlendSubtract ->
          (blendSubtract baseR blendR,
           blendSubtract baseG blendG,
           blendSubtract baseB blendB,
           baseA)
        BlendDivide ->
          (blendDivide baseR blendR,
           blendDivide baseG blendG,
           blendDivide baseB blendB,
           baseA)
        BlendHue ->
          let (r, g, b) = blendHue baseR baseG baseB blendR blendG blendB
          in (r, g, b, baseA)
        BlendSaturation ->
          let (r, g, b) = blendSaturation baseR baseG baseB blendR blendG blendB
          in (r, g, b, baseA)
        BlendColor ->
          let (r, g, b) = blendColor baseR baseG baseB blendR blendG blendB
          in (r, g, b, baseA)
        BlendLuminosity ->
          let (r, g, b) = blendLuminosity baseR baseG baseB blendR blendG blendB
          in (r, g, b, baseA)
        _ -> (blendR, blendG, blendB, blendA)  -- Fallback to normal
      -- Apply opacity
      (finalR, finalG, finalB, finalA) = if finiteOpacity < 1.0
                                          then
                                            let rMix = round (fromIntegral baseR + (fromIntegral resultR - fromIntegral baseR) * finiteOpacity)
                                                gMix = round (fromIntegral baseG + (fromIntegral resultG - fromIntegral baseG) * finiteOpacity)
                                                bMix = round (fromIntegral baseB + (fromIntegral resultB - fromIntegral baseB) * finiteOpacity)
                                                aMix = round (fromIntegral baseA + (fromIntegral resultA - fromIntegral baseA) * finiteOpacity)
                                            in (rMix, gMix, bMix, aMix)
                                          else (resultR, resultG, resultB, resultA)
  in (clampRGB finalR, clampRGB finalG, clampRGB finalB, clampRGB finalA)

-- ============================================================================
-- UTILITY FUNCTIONS
-- ============================================================================

-- | Check if a blend mode can use Canvas 2D native operation
-- Pure function: same inputs → same outputs
isNativeBlendMode :: BlendMode -> Bool
isNativeBlendMode mode = case mode of
  BlendNormal -> True
  BlendMultiply -> True
  BlendScreen -> True
  BlendOverlay -> True
  BlendDarken -> True
  BlendLighten -> True
  BlendColorDodge -> True
  BlendColorBurn -> True
  BlendHardLight -> True
  BlendSoftLight -> True
  BlendDifference -> True
  BlendExclusion -> True
  BlendAdd -> True
  BlendLinearDodge -> True
  _ -> False

-- | Get the native Canvas 2D operation for a blend mode (if supported)
-- Pure function: same inputs → same outputs
-- Returns Nothing if not natively supported
getNativeBlendOp :: BlendMode -> Maybe T.Text
getNativeBlendOp mode = case mode of
  BlendNormal -> Just (T.pack "source-over")
  BlendMultiply -> Just (T.pack "multiply")
  BlendScreen -> Just (T.pack "screen")
  BlendOverlay -> Just (T.pack "overlay")
  BlendDarken -> Just (T.pack "darken")
  BlendLighten -> Just (T.pack "lighten")
  BlendColorDodge -> Just (T.pack "color-dodge")
  BlendColorBurn -> Just (T.pack "color-burn")
  BlendHardLight -> Just (T.pack "hard-light")
  BlendSoftLight -> Just (T.pack "soft-light")
  BlendDifference -> Just (T.pack "difference")
  BlendExclusion -> Just (T.pack "exclusion")
  BlendAdd -> Just (T.pack "lighter")
  BlendLinearDodge -> Just (T.pack "lighter")
  _ -> Nothing

-- | Get display name for a blend mode
-- Pure function: same inputs → same outputs
getBlendModeDisplayName :: BlendMode -> T.Text
getBlendModeDisplayName mode = case mode of
  BlendNormal -> T.pack "Normal"
  BlendDissolve -> T.pack "Dissolve"
  BlendDarken -> T.pack "Darken"
  BlendMultiply -> T.pack "Multiply"
  BlendColorBurn -> T.pack "Color Burn"
  BlendLinearBurn -> T.pack "Linear Burn"
  BlendDarkerColor -> T.pack "Darker Color"
  BlendLighten -> T.pack "Lighten"
  BlendScreen -> T.pack "Screen"
  BlendColorDodge -> T.pack "Color Dodge"
  BlendLinearDodge -> T.pack "Linear Dodge (Add)"
  BlendLighterColor -> T.pack "Lighter Color"
  BlendAdd -> T.pack "Add"
  BlendOverlay -> T.pack "Overlay"
  BlendSoftLight -> T.pack "Soft Light"
  BlendHardLight -> T.pack "Hard Light"
  BlendVividLight -> T.pack "Vivid Light"
  BlendLinearLight -> T.pack "Linear Light"
  BlendPinLight -> T.pack "Pin Light"
  BlendHardMix -> T.pack "Hard Mix"
  BlendDifference -> T.pack "Difference"
  BlendExclusion -> T.pack "Exclusion"
  BlendSubtract -> T.pack "Subtract"
  BlendDivide -> T.pack "Divide"
  BlendHue -> T.pack "Hue"
  BlendSaturation -> T.pack "Saturation"
  BlendColor -> T.pack "Color"
  BlendLuminosity -> T.pack "Luminosity"
  BlendStencilAlpha -> T.pack "Stencil Alpha"
  BlendStencilLuma -> T.pack "Stencil Luma"
  BlendSilhouetteAlpha -> T.pack "Silhouette Alpha"
  BlendSilhouetteLuma -> T.pack "Silhouette Luma"
  BlendBehind -> T.pack "Behind"
  BlendAlphaAdd -> T.pack "Alpha Add"
  BlendLuminescentPremul -> T.pack "Luminescent Premul"
  BlendClassicColorBurn -> T.pack "Classic Color Burn"
  BlendClassicColorDodge -> T.pack "Classic Color Dodge"
