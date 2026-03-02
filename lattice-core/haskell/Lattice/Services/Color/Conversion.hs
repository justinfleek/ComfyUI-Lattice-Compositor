{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Color.Conversion
Description : Color Space Conversions
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for color space conversion:
- RGB ↔ HSV conversion
- BT.709 luminance (brightness)
- Color sample creation with derived values

Source: ui/src/services/colorDepthReactivity.ts
-}

module Lattice.Services.Color.Conversion
  ( -- * Types
    RGB(..), RGBA(..), HSV(..), ColorSample(..), ColorFeature(..)
    -- * Color Conversion
  , rgbToHsv, hsvToRgb
    -- * Brightness
  , calculateBrightness, rgbBrightness
    -- * Color Sample
  , createColorSample, colorSampleFromRGB, colorSampleFromRGBA
  , emptyColorSample
    -- * Feature Extraction
  , getFeatureValue
    -- * Utilities
  , clamp01, clampRGB, clampRGBA, lerpRGB, lerpRGBA
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | RGB color with components in 0-1 range
data RGB = RGB
  { rgbR :: Double  -- ^ 0-1
  , rgbG :: Double  -- ^ 0-1
  , rgbB :: Double  -- ^ 0-1
  } deriving (Eq, Show)

-- | RGBA color with alpha
data RGBA = RGBA
  { rgbaR :: Double  -- ^ 0-1
  , rgbaG :: Double  -- ^ 0-1
  , rgbaB :: Double  -- ^ 0-1
  , rgbaA :: Double  -- ^ 0-1
  } deriving (Eq, Show)

-- | HSV color with components in 0-1 range
data HSV = HSV
  { hsvH :: Double  -- ^ 0-1 (0 = red, 0.33 = green, 0.67 = blue)
  , hsvS :: Double  -- ^ 0-1
  , hsvV :: Double  -- ^ 0-1
  } deriving (Eq, Show)

-- | Complete color sample with all derived values
data ColorSample = ColorSample
  { csR :: Double          -- ^ 0-1
  , csG :: Double          -- ^ 0-1
  , csB :: Double          -- ^ 0-1
  , csA :: Double          -- ^ 0-1
  , csBrightness :: Double -- ^ 0-1 (BT.709 luminance)
  , csHue :: Double        -- ^ 0-1
  , csSaturation :: Double -- ^ 0-1
  , csValue :: Double      -- ^ 0-1 (HSV V)
  } deriving (Eq, Show)

-- | Color feature type for sampling
data ColorFeature
  = FeatureBrightness
  | FeatureHue
  | FeatureSaturation
  | FeatureValue
  | FeatureRed
  | FeatureGreen
  | FeatureBlue
  | FeatureAlpha
  deriving (Eq, Show, Enum, Bounded)

-- ────────────────────────────────────────────────────────────────────────────
--                                                                       // rgb
-- ────────────────────────────────────────────────────────────────────────────

-- | Convert RGB to HSV.
--
--   Algorithm:
--   - V = max(R, G, B)
--   - S = (V - min) / V (0 if V = 0)
--   - H based on which channel is max
rgbToHsv :: RGB -> HSV
rgbToHsv (RGB r g b) = HSV h s v
  where
    maxVal = max r (max g b)
    minVal = min r (min g b)
    d = maxVal - minVal

    v = maxVal
    s = if maxVal == 0 then 0 else d / maxVal

    h | maxVal == minVal = 0  -- Achromatic
      | maxVal == r =
          let hRaw = (g - b) / d
              hAdj = if g < b then hRaw + 6 else hRaw
          in hAdj / 6
      | maxVal == g = ((b - r) / d + 2) / 6
      | otherwise = ((r - g) / d + 4) / 6  -- maxVal == b

-- | Convert HSV to RGB.
--
--   Standard HSV to RGB conversion algorithm.
hsvToRgb :: HSV -> RGB
hsvToRgb (HSV h s v)
  | s == 0 = RGB v v v  -- Achromatic
  | otherwise =
      let h6 = h * 6
          i = floor h6 `mod` 6 :: Int
          f = h6 - fromIntegral (floor h6 :: Int)
          p = v * (1 - s)
          q = v * (1 - s * f)
          t = v * (1 - s * (1 - f))
      in case i of
           0 -> RGB v t p
           1 -> RGB q v p
           2 -> RGB p v t
           3 -> RGB p q v
           4 -> RGB t p v
           _ -> RGB v p q  -- i == 5

-- ────────────────────────────────────────────────────────────────────────────
-- Brightness (Luminance)
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate brightness using ITU-R BT.709 luminance coefficients.
--
--   Y = 0.2126 * R + 0.7152 * G + 0.0722 * B
--
--   This is the standard formula for perceived brightness.
calculateBrightness :: Double -> Double -> Double -> Double
calculateBrightness r g b = 0.2126 * r + 0.7152 * g + 0.0722 * b

-- | Calculate brightness from RGB structure.
rgbBrightness :: RGB -> Double
rgbBrightness (RGB r g b) = calculateBrightness r g b

-- ────────────────────────────────────────────────────────────────────────────
-- Color Sample Creation
-- ────────────────────────────────────────────────────────────────────────────

-- | Create a complete color sample from RGBA values.
--
--   Derives all color properties:
--   - HSV components
--   - BT.709 brightness
createColorSample :: Double -> Double -> Double -> Double -> ColorSample
createColorSample r g b a =
  let HSV h s v = rgbToHsv (RGB r g b)
      brightness = calculateBrightness r g b
  in ColorSample r g b a brightness h s v

-- | Create color sample from RGB.
colorSampleFromRGB :: RGB -> Double -> ColorSample
colorSampleFromRGB (RGB r g b) a = createColorSample r g b a

-- | Create color sample from RGBA.
colorSampleFromRGBA :: RGBA -> ColorSample
colorSampleFromRGBA (RGBA r g b a) = createColorSample r g b a

-- | Empty/black color sample.
emptyColorSample :: ColorSample
emptyColorSample = createColorSample 0 0 0 0

-- ────────────────────────────────────────────────────────────────────────────
-- Feature Extraction
-- ────────────────────────────────────────────────────────────────────────────

-- | Extract a specific feature value from a color sample.
getFeatureValue :: ColorSample -> ColorFeature -> Double
getFeatureValue sample feature = case feature of
  FeatureBrightness -> csBrightness sample
  FeatureHue -> csHue sample
  FeatureSaturation -> csSaturation sample
  FeatureValue -> csValue sample
  FeatureRed -> csR sample
  FeatureGreen -> csG sample
  FeatureBlue -> csB sample
  FeatureAlpha -> csA sample

-- ────────────────────────────────────────────────────────────────────────────
-- Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Clamp a value to 0-1 range.
clamp01 :: Double -> Double
clamp01 x = max 0 (min 1 x)

-- | Clamp RGB to valid range.
clampRGB :: RGB -> RGB
clampRGB (RGB r g b) = RGB (clamp01 r) (clamp01 g) (clamp01 b)

-- | Clamp RGBA to valid range.
clampRGBA :: RGBA -> RGBA
clampRGBA (RGBA r g b a) = RGBA (clamp01 r) (clamp01 g) (clamp01 b) (clamp01 a)

-- | Linear interpolation between two colors.
lerpRGB :: RGB -> RGB -> Double -> RGB
lerpRGB (RGB r1 g1 b1) (RGB r2 g2 b2) t =
  let tc = clamp01 t
  in RGB (r1 + (r2 - r1) * tc)
         (g1 + (g2 - g1) * tc)
         (b1 + (b2 - b1) * tc)

-- | Linear interpolation between two RGBA colors.
lerpRGBA :: RGBA -> RGBA -> Double -> RGBA
lerpRGBA (RGBA r1 g1 b1 a1) (RGBA r2 g2 b2 a2) t =
  let tc = clamp01 t
  in RGBA (r1 + (r2 - r1) * tc)
          (g1 + (g2 - g1) * tc)
          (b1 + (b2 - b1) * tc)
          (a1 + (a2 - a1) * tc)
