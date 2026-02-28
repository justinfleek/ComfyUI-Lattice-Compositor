-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // color // ono-sendai
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Ono-Sendai Base16 Theme Generator
-- |
-- | Fin-bounded color primitives for deterministic theme generation.
-- |
-- | The grayscale ramp is fixed: 211° hue, perceptually stepped lightness.
-- | The accent ramp admits two degrees of freedom:
-- |
-- |   - **Hero hue**: the dominant accent (default 211°, the electric blue)
-- |   - **Axis hue**: a secondary hue for shifted accents (default 201°, the cool shift)
-- |
-- | Everything else is derived.
-- |
-- | ## Base16 slot assignments
-- |
-- | ```
-- |     base00–base07  grayscale ramp (211° locked, lightness only)
-- |     base08         axis, high luminance    (variables)
-- |     base09         axis, mid luminance     (integers)
-- |     base0A         hero, full              (classes — the heresy)
-- |     base0B         hero, darker            (strings)
-- |     base0C         hero, desaturated       (support)
-- |     base0D         hero, slight shift      (functions)
-- |     base0E         hero, lighter           (keywords)
-- |     base0F         hero, desat dark        (deprecated)
-- | ```
-- |
-- | ## Why Bounded?
-- |
-- | At billion-agent scale, agents must compose colors deterministically:
-- | - Channel is bounded 0-255 — No out-of-range RGB values possible
-- | - Hue is bounded 0-359 — Hue is always valid, wrapping is explicit
-- | - Pct is bounded 0-100 — Percentages are always valid
-- |
-- | Same inputs → same outputs. Guaranteed.
-- |
-- | Status: ✓ PROVEN (Hydrogen.Schema.Color.OnoSendai)

module Hydrogen.Schema.Color.OnoSendai
  ( -- * Types
    BlackLevel(..)
  , OnoSendaiPalette
  
  -- * Palette Generation
  , generatePalette
  , defaultPalette
  
  -- * Black Level Operations
  , baseL
  
  -- * Palette Accessors
  , slug
  , name
  , base00, base01, base02, base03
  , base04, base05, base06, base07
  , base08, base09, base0A, base0B
  , base0C, base0D, base0E, base0F
  , slots
  
  -- * Slot Information
  , slotName
  , slotRole
  ) where

import Prelude

import Data.Array (index)
import Data.Maybe (fromMaybe)
import Hydrogen.Schema.Color.Channel (Channel)
import Hydrogen.Schema.Color.Channel as Ch
import Hydrogen.Schema.Color.Hue (Hue)
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.RGB (RGB)
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL (HSL)
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Conversion as Conv

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // black // level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Black level variants for theme generation.
-- |
-- | The background lightness ladder. Each variant shifts the entire
-- | base00–base03 ramp. base04–base07 are stable across variants.
-- |
-- | From the Nix source:
-- |
-- | - **Void**: L=0% — true black (kills some foundry fonts)
-- | - **Deep**: L=4% — hand-tuned default
-- | - **Night**: L=8% — OLED threshold
-- | - **Carbon**: L=11% — good default (recommended)
-- | - **GitHub**: L=16% — highly robust
data BlackLevel
  = Void    -- ^ L=0%
  | Deep    -- ^ L=4%
  | Night   -- ^ L=8%
  | Carbon  -- ^ L=11%
  | GitHub  -- ^ L=16%

derive instance eqBlackLevel :: Eq BlackLevel
derive instance ordBlackLevel :: Ord BlackLevel

instance showBlackLevel :: Show BlackLevel where
  show Void = "void"
  show Deep = "deep"
  show Night = "night"
  show Carbon = "carbon"
  show GitHub = "github"

-- | Base lightness for each black level variant.
-- |
-- | Status: ✓ PROVEN (BlackLevel.baseL_le_16, BlackLevel.baseL_lt_100)
baseL :: BlackLevel -> Int
baseL Void   = 0
baseL Deep   = 4
baseL Night  = 8
baseL Carbon = 11
baseL GitHub = 16

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // palette
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete Base16 palette with 16 slots.
-- |
-- | Each slot is an RGB color generated from the hero/axis hue configuration.
type OnoSendaiPalette =
  { slug :: String
  , name :: String
  , base00 :: RGB
  , base01 :: RGB
  , base02 :: RGB
  , base03 :: RGB
  , base04 :: RGB
  , base05 :: RGB
  , base06 :: RGB
  , base07 :: RGB
  , base08 :: RGB
  , base09 :: RGB
  , base0A :: RGB
  , base0B :: RGB
  , base0C :: RGB
  , base0D :: RGB
  , base0E :: RGB
  , base0F :: RGB
  }

-- Palette accessors
slug :: OnoSendaiPalette -> String
slug p = p.slug

name :: OnoSendaiPalette -> String
name p = p.name

base00 :: OnoSendaiPalette -> RGB
base00 p = p.base00

base01 :: OnoSendaiPalette -> RGB
base01 p = p.base01

base02 :: OnoSendaiPalette -> RGB
base02 p = p.base02

base03 :: OnoSendaiPalette -> RGB
base03 p = p.base03

base04 :: OnoSendaiPalette -> RGB
base04 p = p.base04

base05 :: OnoSendaiPalette -> RGB
base05 p = p.base05

base06 :: OnoSendaiPalette -> RGB
base06 p = p.base06

base07 :: OnoSendaiPalette -> RGB
base07 p = p.base07

base08 :: OnoSendaiPalette -> RGB
base08 p = p.base08

base09 :: OnoSendaiPalette -> RGB
base09 p = p.base09

base0A :: OnoSendaiPalette -> RGB
base0A p = p.base0A

base0B :: OnoSendaiPalette -> RGB
base0B p = p.base0B

base0C :: OnoSendaiPalette -> RGB
base0C p = p.base0C

base0D :: OnoSendaiPalette -> RGB
base0D p = p.base0D

base0E :: OnoSendaiPalette -> RGB
base0E p = p.base0E

base0F :: OnoSendaiPalette -> RGB
base0F p = p.base0F

-- | Get palette slots as an array.
-- |
-- | Status: ✓ PROVEN (OnoSendaiPalette.slots_size = 16)
slots :: OnoSendaiPalette -> Array RGB
slots p =
  [ p.base00, p.base01, p.base02, p.base03
  , p.base04, p.base05, p.base06, p.base07
  , p.base08, p.base09, p.base0A, p.base0B
  , p.base0C, p.base0D, p.base0E, p.base0F
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // slot // metadata
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the Base16 slot name for an index (0-15).
slotName :: Int -> String
slotName i = case i of
  0x0 -> "base00"
  0x1 -> "base01"
  0x2 -> "base02"
  0x3 -> "base03"
  0x4 -> "base04"
  0x5 -> "base05"
  0x6 -> "base06"
  0x7 -> "base07"
  0x8 -> "base08"
  0x9 -> "base09"
  0xA -> "base0A"
  0xB -> "base0B"
  0xC -> "base0C"
  0xD -> "base0D"
  0xE -> "base0E"
  0xF -> "base0F"
  _   -> "base??"

-- | Get the semantic role for a Base16 slot index (0-15).
slotRole :: Int -> String
slotRole i = case i of
  0x0 -> "background"
  0x1 -> "raised surface"
  0x2 -> "selection"
  0x3 -> "comments"
  0x4 -> "dark fg"
  0x5 -> "foreground"
  0x6 -> "light fg"
  0x7 -> "light bg"
  0x8 -> "variables"
  0x9 -> "integers"
  0xA -> "classes (hero)"
  0xB -> "strings"
  0xC -> "support"
  0xD -> "functions"
  0xE -> "keywords"
  0xF -> "deprecated"
  _   -> "unknown"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create HSL with the locked hue (211°).
hsl211 :: Int -> Int -> HSL
hsl211 s l = HSL.hsl 211 s l

-- | Create HSL at arbitrary hue.
hslAt :: Int -> Int -> Int -> HSL
hslAt h s l = HSL.hsl h s l

-- | Generate the full base16 palette.
-- |
-- | - `level`: black level variant (shifts base00–base03)
-- | - `heroHue`: hue for the dominant accent ramp (default: 211)
-- | - `axisHue`: hue for the cool-shifted accents (default: 201)
-- |
-- | The grayscale ramp (base00–base07) is always 211°.
-- | The accent ramp (base08–base0F) is derived from hero and axis.
-- |
-- | Status: ✓ PROVEN (generatePalette_deterministic)
generatePalette :: BlackLevel -> Int -> Int -> OnoSendaiPalette
generatePalette level heroHue axisHue =
  let
    l = baseL level
    -- Grayscale ramp: 211° locked, saturation tapers up with lightness
    b00 = Conv.hslToRgb (hsl211 12 (l + 0))
    b01 = Conv.hslToRgb (hsl211 16 (l + 3))
    b02 = Conv.hslToRgb (hsl211 17 (l + 8))
    b03 = Conv.hslToRgb (hsl211 15 (l + 17))
    -- Stable foreground tones
    b04 = Conv.hslToRgb (hsl211 12 48)
    b05 = Conv.hslToRgb (hsl211 28 81)
    b06 = Conv.hslToRgb (hsl211 32 89)
    b07 = Conv.hslToRgb (hsl211 36 95)
    -- Accent ramp: axis pair (cool-shifted)
    b08 = Conv.hslToRgb (hslAt axisHue 100 86)   -- variables, high lum
    b09 = Conv.hslToRgb (hslAt axisHue 100 75)   -- integers, mid lum
    -- Hero ramp
    b0A = Conv.hslToRgb (hslAt heroHue 100 66)   -- classes — the heresy
    b0B = Conv.hslToRgb (hslAt heroHue 100 57)   -- strings
    b0C = Conv.hslToRgb (hslAt heroHue 94 45)    -- support, desaturated
    b0D = Conv.hslToRgb (hslAt heroHue 100 65)   -- functions
    b0E = Conv.hslToRgb (hslAt heroHue 100 71)   -- keywords, lighter
    b0F = Conv.hslToRgb (hslAt heroHue 86 53)    -- deprecated, desat dark
    -- Build slug from level
    suffix = show level
  in
    { slug: "ono-sendai-" <> suffix
    , name: "Ono-Sendai " <> suffix <> " (hero=" <> show heroHue <> "° axis=" <> show axisHue <> "°)"
    , base00: b00
    , base01: b01
    , base02: b02
    , base03: b03
    , base04: b04
    , base05: b05
    , base06: b06
    , base07: b07
    , base08: b08
    , base09: b09
    , base0A: b0A
    , base0B: b0B
    , base0C: b0C
    , base0D: b0D
    , base0E: b0E
    , base0F: b0F
    }

-- | The default palette: Carbon with hero=211° and axis=201°.
-- |
-- | Carbon (L=11%) is the recommended black level for most use cases.
defaultPalette :: OnoSendaiPalette
defaultPalette = generatePalette Carbon 211 201
