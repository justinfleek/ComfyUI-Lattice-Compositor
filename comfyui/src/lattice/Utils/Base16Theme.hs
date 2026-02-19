-- |
-- Module      : Lattice.Utils.Base16Theme
-- Description : Base16 color theme generator using 211° hero hue
-- 
-- Generates base16 color schemes with HSL(211° ...) hero hue lock
-- Based on ono-sendai color scheme patterns
-- Lean4 proofs: lattice-core/lean/Color/Base16.lean
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Base16Theme
  ( -- Types
    Base16Palette(..)
    -- Theme generators
  , generateBase16Theme
  , onoSendaiTuned
  , onoSendaiGithub
  , onoSendaiMemphis
  , onoSendaiChiba
  , onoSendaiRazorgirl
  , onoSendaiSprawl
    -- Export functions
  , paletteToHex
  , paletteToCSS
  , paletteToNix
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Text.Printf (printf)
import Lattice.Types.Color
  ( HSL(..)
  , RGB(..)
  , RGB8(..)
  , Hue(..)
  , Saturation(..)
  , Lightness(..)
  , heroHue
  , hslWithHeroHue
  , hslToRGB
  , rgbToHex
  , validateHue
  , validateSaturation
  , validateLightness
  , rgb8Value
  )

-- ============================================================================
-- BASE16 COLOR STRUCTURE
-- ============================================================================

-- | Base16 color palette (16 colors)
data Base16Palette = Base16Palette
  { base00 :: RGB  -- Background (darkest)
  , base01 :: RGB  -- Lighter background
  , base02 :: RGB  -- Selection background
  , base03 :: RGB  -- Comments/inactive
  , base04 :: RGB  -- Dark foreground
  , base05 :: RGB  -- Default foreground
  , base06 :: RGB  -- Light foreground
  , base07 :: RGB  -- Lightest background
  , base08 :: RGB  -- Variables/errors
  , base09 :: RGB  -- Integers
  , base0A :: RGB  -- Classes (HERO: 211°)
  , base0B :: RGB  -- Strings
  , base0C :: RGB  -- Support/functions
  , base0D :: RGB  -- Functions/links
  , base0E :: RGB  -- Keywords
  , base0F :: RGB  -- Deprecated/markers
  }
  deriving (Eq, Show)

-- ============================================================================
-- ACCENT COLORS WITH 211° HERO HUE
-- ============================================================================

-- | Generate accent colors with 211° hero hue
-- Creates systematic relationships to hero blue
generateAccentColors :: [HSL]
generateAccentColors =
  [
    -- base08: Ice blue (shifted cool, high luminance) HSL(201° 100% 86%)
    HSL (validateHue 201.0) (validateSaturation 1.0) (validateLightness 0.86)
    -- base09: Sky blue (same hue, darker) HSL(201° 100% 75%)
  , HSL (validateHue 201.0) (validateSaturation 1.0) (validateLightness 0.75)
    -- base0A: HERO Electric blue HSL(211° 100% 66%) - #54aeff
  , HSL heroHue (validateSaturation 1.0) (validateLightness 0.66)
    -- base0B: Deep blue (same hue, darker) HSL(211° 100% 57%)
  , HSL heroHue (validateSaturation 1.0) (validateLightness 0.57)
    -- base0C: Matrix blue (desaturated) HSL(211° 94% 45%)
  , HSL heroHue (validateSaturation 0.94) (validateLightness 0.45)
    -- base0D: Link blue (tiny luminance shift) HSL(211° 100% 65%)
  , HSL heroHue (validateSaturation 1.0) (validateLightness 0.65)
    -- base0E: Soft electric (lighter variant) HSL(211° 100% 71%)
  , HSL heroHue (validateSaturation 1.0) (validateLightness 0.71)
    -- base0F: Corp blue (desaturated dark) HSL(211° 86% 53%)
  , HSL heroHue (validateSaturation 0.86) (validateLightness 0.53)
  ]

-- ============================================================================
-- BASE16 THEME GENERATOR
-- ============================================================================

-- | Generate base16 palette with 211° hero hue
generateBase16Theme :: Double -> Base16Palette
generateBase16Theme backgroundLightness =
  let bgL = max 0.0 (min 1.0 backgroundLightness)
      -- Grayscale ramp (base00-base07) with 211° hue tint
      base00HSL = hslWithHeroHue (validateSaturation 0.12) (validateLightness bgL)
      base01HSL = hslWithHeroHue (validateSaturation 0.16) (validateLightness (min 1.0 (bgL + 0.03)))
      base02HSL = hslWithHeroHue (validateSaturation 0.17) (validateLightness (min 1.0 (bgL + 0.08)))
      base03HSL = hslWithHeroHue (validateSaturation 0.15) (validateLightness (min 1.0 (bgL + 0.17)))
      base04HSL = hslWithHeroHue (validateSaturation 0.12) (validateLightness 0.48)
      base05HSL = hslWithHeroHue (validateSaturation 0.28) (validateLightness 0.81)
      base06HSL = hslWithHeroHue (validateSaturation 0.32) (validateLightness 0.89)
      base07HSL = hslWithHeroHue (validateSaturation 0.36) (validateLightness 0.95)
      accents = generateAccentColors
      -- Safe list access (no !! operator) - explicit pattern matching
      safeGet i = case drop i accents of
        [] -> HSL heroHue (validateSaturation 1.0) (validateLightness 0.66)  -- Default to hero
        (x:xs) -> x  -- Explicitly match head and tail (even though tail unused)
  in Base16Palette
    { base00 = hslToRGB base00HSL
    , base01 = hslToRGB base01HSL
    , base02 = hslToRGB base02HSL
    , base03 = hslToRGB base03HSL
    , base04 = hslToRGB base04HSL
    , base05 = hslToRGB base05HSL
    , base06 = hslToRGB base06HSL
    , base07 = hslToRGB base07HSL
    , base08 = hslToRGB (safeGet 0)
    , base09 = hslToRGB (safeGet 1)
    , base0A = hslToRGB (safeGet 2)  -- HERO: #54aeff
    , base0B = hslToRGB (safeGet 3)
    , base0C = hslToRGB (safeGet 4)
    , base0D = hslToRGB (safeGet 5)
    , base0E = hslToRGB (safeGet 6)
    , base0F = hslToRGB (safeGet 7)
    }

-- ============================================================================
-- PREDEFINED THEMES
-- ============================================================================

-- | Generate ono-sendai tuned theme (L=11% background)
-- HSL(211° 12% 11%) - OLED-safe background
onoSendaiTuned :: Base16Palette
onoSendaiTuned = generateBase16Theme 0.11

-- | Generate ono-sendai github theme (L=16% background)
-- HSL(211° 12% 16%) - GitHub's de-facto default dark mode
onoSendaiGithub :: Base16Palette
onoSendaiGithub = generateBase16Theme 0.16

-- | Generate ono-sendai memphis theme (L=0% background - pure black)
-- HSL(211° 0% 0%) - Pure black
onoSendaiMemphis :: Base16Palette
onoSendaiMemphis = generateBase16Theme 0.0

-- | Generate ono-sendai chiba theme (L=4% background)
-- HSL(211° 12% 4%) - Problematic on Samsung panels
onoSendaiChiba :: Base16Palette
onoSendaiChiba = generateBase16Theme 0.04

-- | Generate ono-sendai razorgirl theme (L=8% background)
-- HSL(211° 12% 8%) - Attempt to preserve strokes
onoSendaiRazorgirl :: Base16Palette
onoSendaiRazorgirl = generateBase16Theme 0.08

-- | Generate ono-sendai sprawl theme (L=11% background - best compromise)
-- HSL(211° 12% 11%) - Best compromise
onoSendaiSprawl :: Base16Palette
onoSendaiSprawl = generateBase16Theme 0.11

-- ============================================================================
-- EXPORT FUNCTIONS
-- ============================================================================

-- | Convert palette to hex format (for CSS/HTML)
paletteToHex :: Base16Palette -> [(Text, Text)]
paletteToHex p =
  [ ("base00", rgbToHex (base00 p))
  , ("base01", rgbToHex (base01 p))
  , ("base02", rgbToHex (base02 p))
  , ("base03", rgbToHex (base03 p))
  , ("base04", rgbToHex (base04 p))
  , ("base05", rgbToHex (base05 p))
  , ("base06", rgbToHex (base06 p))
  , ("base07", rgbToHex (base07 p))
  , ("base08", rgbToHex (base08 p))
  , ("base09", rgbToHex (base09 p))
  , ("base0A", rgbToHex (base0A p))
  , ("base0B", rgbToHex (base0B p))
  , ("base0C", rgbToHex (base0C p))
  , ("base0D", rgbToHex (base0D p))
  , ("base0E", rgbToHex (base0E p))
  , ("base0F", rgbToHex (base0F p))
  ]

-- | Convert palette to CSS variables format
paletteToCSS :: Base16Palette -> Text
paletteToCSS p =
  T.unlines
    [ ":root {"
    , "  --base00: " <> rgbToHex (base00 p) <> ";"
    , "  --base01: " <> rgbToHex (base01 p) <> ";"
    , "  --base02: " <> rgbToHex (base02 p) <> ";"
    , "  --base03: " <> rgbToHex (base03 p) <> ";"
    , "  --base04: " <> rgbToHex (base04 p) <> ";"
    , "  --base05: " <> rgbToHex (base05 p) <> ";"
    , "  --base06: " <> rgbToHex (base06 p) <> ";"
    , "  --base07: " <> rgbToHex (base07 p) <> ";"
    , "  --base08: " <> rgbToHex (base08 p) <> ";"
    , "  --base09: " <> rgbToHex (base09 p) <> ";"
    , "  --base0A: " <> rgbToHex (base0A p) <> ";  /* HERO */"
    , "  --base0B: " <> rgbToHex (base0B p) <> ";"
    , "  --base0C: " <> rgbToHex (base0C p) <> ";"
    , "  --base0D: " <> rgbToHex (base0D p) <> ";"
    , "  --base0E: " <> rgbToHex (base0E p) <> ";"
    , "  --base0F: " <> rgbToHex (base0F p) <> ";"
    , "}"
    ]

-- | Convert palette to Nix format (matching ono-sendai.nix structure)
paletteToNix :: Text -> Base16Palette -> Text
paletteToNix themeName p =
  T.unlines
    [ themeName <> " = {"
    , "  slug = \"" <> T.toLower themeName <> "\";"
    , "  name = \"" <> themeName <> "\";"
    , "  author = \"lattice-compositor\";"
    , "  variant = \"dark\";"
    , "  palette = {"
    , "    base00 = \"" <> rgbToHex (base00 p) <> "\";"
    , "    base01 = \"" <> rgbToHex (base01 p) <> "\";"
    , "    base02 = \"" <> rgbToHex (base02 p) <> "\";"
    , "    base03 = \"" <> rgbToHex (base03 p) <> "\";"
    , "    base04 = \"" <> rgbToHex (base04 p) <> "\";"
    , "    base05 = \"" <> rgbToHex (base05 p) <> "\";"
    , "    base06 = \"" <> rgbToHex (base06 p) <> "\";"
    , "    base07 = \"" <> rgbToHex (base07 p) <> "\";"
    , "    base08 = \"" <> rgbToHex (base08 p) <> "\";"
    , "    base09 = \"" <> rgbToHex (base09 p) <> "\";"
    , "    base0A = \"" <> rgbToHex (base0A p) <> "\";  # HERO: HSL(211° 100% 66%)"
    , "    base0B = \"" <> rgbToHex (base0B p) <> "\";"
    , "    base0C = \"" <> rgbToHex (base0C p) <> "\";"
    , "    base0D = \"" <> rgbToHex (base0D p) <> "\";"
    , "    base0E = \"" <> rgbToHex (base0E p) <> "\";"
    , "    base0F = \"" <> rgbToHex (base0F p) <> "\";"
    , "  };"
    , "};"
    ]
