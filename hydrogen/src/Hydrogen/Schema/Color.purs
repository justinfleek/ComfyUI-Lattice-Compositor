-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                // hydrogen // schema // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pillar 1: Color
-- |
-- | Color science, theory, and application.
-- |
-- | ## Submodules
-- |
-- | ### Core
-- | - `Hydrogen.Schema.Color.RGB` — Generic RGB (0-255)
-- | - `Hydrogen.Schema.Color.SRGB` — Standard RGB (Web)
-- | - `Hydrogen.Schema.Color.Channel` — 8-bit channel atom
-- | - `Hydrogen.Schema.Color.Opacity` — Alpha/Opacity atom
-- |
-- | ### Spaces
-- | - `Hydrogen.Schema.Color.HSL` — Hue, Saturation, Lightness
-- | - `Hydrogen.Schema.Color.HSLA` — HSL + Alpha
-- | - `Hydrogen.Schema.Color.HWB` — Hue, Whiteness, Blackness
-- | - `Hydrogen.Schema.Color.CMYK` — Cyan, Magenta, Yellow, Key
-- | - `Hydrogen.Schema.Color.LAB` — CIE LAB
-- | - `Hydrogen.Schema.Color.LCH` — CIE LCH
-- | - `Hydrogen.Schema.Color.OKLAB` — Oklab
-- | - `Hydrogen.Schema.Color.OKLCH` — Oklch
-- | - `Hydrogen.Schema.Color.XYZ` — CIE XYZ
-- | - `Hydrogen.Schema.Color.YUV` — YUV/YCbCr
-- |
-- | ### Atoms
-- | - `Hydrogen.Schema.Color.Hue`
-- | - `Hydrogen.Schema.Color.Saturation`
-- | - `Hydrogen.Schema.Color.Lightness`
-- | - `Hydrogen.Schema.Color.Luminance`
-- | - `Hydrogen.Schema.Color.Kelvin`
-- | - `Hydrogen.Schema.Color.Temperature`
-- |
-- | ### Utilities
-- | - `Hydrogen.Schema.Color.Conversion` — Space conversions
-- | - `Hydrogen.Schema.Color.Blend` — Blend modes
-- | - `Hydrogen.Schema.Color.Gradient` — Gradient definitions
-- | - `Hydrogen.Schema.Color.Harmony` — Color harmonies
-- | - `Hydrogen.Schema.Color.Palette` — Palette generation
-- |
-- | This module exists as documentation. Import submodules directly.

module Hydrogen.Schema.Color
  ( module Hydrogen.Schema.Color
  ) where

-- | Color pillar version for compatibility checks.
colorVersion :: String
colorVersion = "0.1.0"
