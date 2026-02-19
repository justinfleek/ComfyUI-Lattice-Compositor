{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Effects.ColorAdjustment
Description : Color Adjustment Functions
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for color adjustment:
- Hue/Saturation/Lightness
- Vibrance (smart saturation)
- Tint (black/white mapping)
- Color Balance (shadows/midtones/highlights)

All functions operate on normalized [0,1] color values.
All functions are total and deterministic.

Source: ui/src/services/effects/colorRenderer.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Effects.ColorAdjustment
  ( -- * Types
    HueSatParams(..)
  , VibranceParams(..)
  , TintParams(..)
  , ColorBalanceParams(..)
    -- * Default Values
  , defaultHueSatParams
  , defaultVibranceParams
  , defaultTintParams
  , defaultColorBalanceParams
    -- * Color Adjustment Functions
  , hueSaturation
  , vibrance
  , tint
  , colorBalance
    -- * HSL Conversion Helpers
  , rgbToHsl
  , hslToRgb
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Hue/Saturation parameters
data HueSatParams = HueSatParams
  { hspHueShift       :: !Double  -- ^ -0.5 to 0.5 (normalized from -180 to 180)
  , hspSaturationShift :: !Double  -- ^ -1 to 1 (normalized from -100 to 100)
  , hspLightnessShift :: !Double  -- ^ -1 to 1 (normalized from -100 to 100)
  , hspColorize       :: !Bool    -- ^ Colorize mode
  } deriving (Eq, Show)

-- | Vibrance parameters
data VibranceParams = VibranceParams
  { vpVibrance   :: !Double  -- ^ -1 to 1 (smart saturation)
  , vpSaturation :: !Double  -- ^ -1 to 1 (standard saturation)
  } deriving (Eq, Show)

-- | Tint parameters (map black/white to colors)
data TintParams = TintParams
  { tpBlackR :: !Double  -- ^ Black point R [0,1]
  , tpBlackG :: !Double  -- ^ Black point G [0,1]
  , tpBlackB :: !Double  -- ^ Black point B [0,1]
  , tpWhiteR :: !Double  -- ^ White point R [0,1]
  , tpWhiteG :: !Double  -- ^ White point G [0,1]
  , tpWhiteB :: !Double  -- ^ White point B [0,1]
  , tpAmount :: !Double  -- ^ Blend amount 0-1
  } deriving (Eq, Show)

-- | Color Balance parameters
data ColorBalanceParams = ColorBalanceParams
  { cbpShadowR    :: !Double  -- ^ -1 to 1 (cyan to red in shadows)
  , cbpShadowG    :: !Double  -- ^ -1 to 1 (magenta to green in shadows)
  , cbpShadowB    :: !Double  -- ^ -1 to 1 (yellow to blue in shadows)
  , cbpMidtoneR   :: !Double  -- ^ -1 to 1 (cyan to red in midtones)
  , cbpMidtoneG   :: !Double  -- ^ -1 to 1 (magenta to green in midtones)
  , cbpMidtoneB   :: !Double  -- ^ -1 to 1 (yellow to blue in midtones)
  , cbpHighlightR :: !Double  -- ^ -1 to 1 (cyan to red in highlights)
  , cbpHighlightG :: !Double  -- ^ -1 to 1 (magenta to green in highlights)
  , cbpHighlightB :: !Double  -- ^ -1 to 1 (yellow to blue in highlights)
  , cbpPreserveLuminosity :: !Bool
  } deriving (Eq, Show)

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

-- | Default hue/saturation (no change)
defaultHueSatParams :: HueSatParams
defaultHueSatParams = HueSatParams
  { hspHueShift = 0
  , hspSaturationShift = 0
  , hspLightnessShift = 0
  , hspColorize = False
  }

-- | Default vibrance (no change)
defaultVibranceParams :: VibranceParams
defaultVibranceParams = VibranceParams
  { vpVibrance = 0
  , vpSaturation = 0
  }

-- | Default tint (identity - black to black, white to white)
defaultTintParams :: TintParams
defaultTintParams = TintParams
  { tpBlackR = 0, tpBlackG = 0, tpBlackB = 0
  , tpWhiteR = 1, tpWhiteG = 1, tpWhiteB = 1
  , tpAmount = 1
  }

-- | Default color balance (no change)
defaultColorBalanceParams :: ColorBalanceParams
defaultColorBalanceParams = ColorBalanceParams
  { cbpShadowR = 0, cbpShadowG = 0, cbpShadowB = 0
  , cbpMidtoneR = 0, cbpMidtoneG = 0, cbpMidtoneB = 0
  , cbpHighlightR = 0, cbpHighlightG = 0, cbpHighlightB = 0
  , cbpPreserveLuminosity = True
  }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

-- | Clamp value to [0, 1]
clamp01 :: Double -> Double
clamp01 = max 0 . min 1

-- | Calculate luminance from RGB [0,1]
luminance :: Double -> Double -> Double -> Double
luminance r g b = r * 0.299 + g * 0.587 + b * 0.114

--------------------------------------------------------------------------------
-- HSL Conversion
--------------------------------------------------------------------------------

-- | Convert RGB [0,1] to HSL [0,1]
rgbToHsl :: (Double, Double, Double) -> (Double, Double, Double)
rgbToHsl (r, g, b) =
  let maxC = maximum [r, g, b]
      minC = minimum [r, g, b]
      l = (maxC + minC) / 2
      d = maxC - minC
      (h, s)
        | d == 0 = (0, 0)
        | otherwise =
            let s' = if l > 0.5 then d / (2 - maxC - minC) else d / (maxC + minC)
                h' | maxC == r = ((g - b) / d + (if g < b then 6 else 0)) / 6
                   | maxC == g = ((b - r) / d + 2) / 6
                   | otherwise = ((r - g) / d + 4) / 6
            in (h', s')
  in (h, s, l)

-- | Convert HSL [0,1] to RGB [0,1]
hslToRgb :: (Double, Double, Double) -> (Double, Double, Double)
hslToRgb (h, s, l)
  | s == 0 = (l, l, l)
  | otherwise =
      let q = if l < 0.5 then l * (1 + s) else l + s - l * s
          p = 2 * l - q
          hue2rgb t
            | t < 0 = hue2rgb (t + 1)
            | t > 1 = hue2rgb (t - 1)
            | t < 1/6 = p + (q - p) * 6 * t
            | t < 1/2 = q
            | t < 2/3 = p + (q - p) * (2/3 - t) * 6
            | otherwise = p
      in (hue2rgb (h + 1/3), hue2rgb h, hue2rgb (h - 1/3))

--------------------------------------------------------------------------------
-- Hue/Saturation
--------------------------------------------------------------------------------

-- | Apply hue/saturation adjustment.
hueSaturation :: HueSatParams -> (Double, Double, Double) -> (Double, Double, Double)
hueSaturation params (r, g, b) =
  let (h0, s0, l0) = rgbToHsl (r, g, b)
      hueShift = hspHueShift params
      satShift = hspSaturationShift params
      lightShift = hspLightnessShift params
      colorize = hspColorize params
      (h, s) = if colorize
               then (hueShift, abs satShift + 0.25)
               else let h' = h0 + hueShift
                        hWrapped = h' - fromIntegral (floor h' :: Int)
                    in (hWrapped, s0 + s0 * satShift)
      l = l0 + l0 * lightShift
      sClamped = clamp01 s
      lClamped = clamp01 l
  in hslToRgb (h, sClamped, lClamped)

--------------------------------------------------------------------------------
-- Vibrance
--------------------------------------------------------------------------------

-- | Apply vibrance (smart saturation protecting skin tones).
vibrance :: VibranceParams -> (Double, Double, Double) -> (Double, Double, Double)
vibrance params (r, g, b) =
  let vib = vpVibrance params
      sat = vpSaturation params
      maxC = maximum [r, g, b]
      minC = minimum [r, g, b]
      currentSat = maxC - minC
      lum = luminance r g b
      -- Skin tone protection (orange-ish colors)
      skinProtection = 1 - max 0 (min 1
        (abs (r - 0.8) * 2 + abs (g - 0.5) * 2 + abs (b - 0.3) * 3))
      -- Vibrance inversely proportional to current saturation
      vibranceAmount = vib * (1 - currentSat) * (1 - skinProtection * 0.5)
      -- Combined saturation adjustment
      satAdjust = 1 + sat + vibranceAmount
      -- Apply saturation change
      r' = lum + (r - lum) * satAdjust
      g' = lum + (g - lum) * satAdjust
      b' = lum + (b - lum) * satAdjust
  in (clamp01 r', clamp01 g', clamp01 b')

--------------------------------------------------------------------------------
-- Tint
--------------------------------------------------------------------------------

-- | Apply tint (map black to one color, white to another).
tint :: TintParams -> (Double, Double, Double) -> (Double, Double, Double)
tint params (r, g, b) =
  let amount = tpAmount params
      lum = luminance r g b
      -- Interpolate between black and white colors
      tintR = tpBlackR params + (tpWhiteR params - tpBlackR params) * lum
      tintG = tpBlackG params + (tpWhiteG params - tpBlackG params) * lum
      tintB = tpBlackB params + (tpWhiteB params - tpBlackB params) * lum
      -- Blend with original
      r' = r + (tintR - r) * amount
      g' = g + (tintG - g) * amount
      b' = b + (tintB - b) * amount
  in (clamp01 r', clamp01 g', clamp01 b')

--------------------------------------------------------------------------------
-- Color Balance
--------------------------------------------------------------------------------

-- | Apply color balance (shadows/midtones/highlights).
colorBalance :: ColorBalanceParams -> (Double, Double, Double) -> (Double, Double, Double)
colorBalance params (r, g, b) =
  let lum = luminance r g b
      -- Calculate weights for tonal ranges
      shadowWeight = max 0 (1 - lum * 3)
      highlightWeight = max 0 ((lum - 0.67) * 3)
      midtoneWeight = 1 - shadowWeight - highlightWeight
      -- Apply adjustments per tonal range
      rAdj = cbpShadowR params * shadowWeight
           + cbpMidtoneR params * midtoneWeight
           + cbpHighlightR params * highlightWeight
      gAdj = cbpShadowG params * shadowWeight
           + cbpMidtoneG params * midtoneWeight
           + cbpHighlightG params * highlightWeight
      bAdj = cbpShadowB params * shadowWeight
           + cbpMidtoneB params * midtoneWeight
           + cbpHighlightB params * highlightWeight
      r' = r + rAdj
      g' = g + gAdj
      b' = b + bAdj
      -- Preserve luminosity if enabled
      (rFinal, gFinal, bFinal)
        | cbpPreserveLuminosity params =
            let newLum = luminance r' g' b'
                ratio = if newLum > 0.001 then lum / newLum else 1
            in (r' * ratio, g' * ratio, b' * ratio)
        | otherwise = (r', g', b')
  in (clamp01 rFinal, clamp01 gFinal, clamp01 bFinal)
