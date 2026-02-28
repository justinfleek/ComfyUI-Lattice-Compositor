-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                 // hydrogen // style // color
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Color algebra and semantic color tokens
-- |
-- | This module provides:
-- | - Semantic color tokens (background, foreground, primary, etc.)
-- | - Color manipulation (lighten, darken, opacity)
-- | - HSL color representation
-- |
-- | ## Design Philosophy
-- |
-- | Colors are defined semantically, not by hue. This allows themes to
-- | swap entire color palettes while maintaining visual hierarchy.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Style.Color as Color
-- |
-- | -- Semantic colors (map to CSS variables)
-- | Color.bg Color.Background      -- "bg-background"
-- | Color.bg Color.Primary         -- "bg-primary"
-- | Color.text Color.Foreground    -- "text-foreground"
-- |
-- | -- With opacity
-- | Color.bgOpacity Color.Primary 50  -- "bg-primary/50"
-- |
-- | -- Tailwind palette colors
-- | Color.bg (Color.Slate Color.C500)  -- "bg-slate-500"
-- | ```
module Hydrogen.Style.Color
  ( -- * Semantic Colors
    SemanticColor(..)
  , bg
  , text
  , border
  , ring
  , bgOpacity
  , textOpacity
  , borderOpacity
    -- * Palette Colors
  , PaletteColor(..)
  , ColorShade(..)
  , palette
    -- * HSL Color Type
  , HSL(..)
  , hsl
  , toHslString
  , toLegacyCssVar
    -- * Color Manipulation
  , lighten
  , darken
  , saturate
  , desaturate
  , opacity
  , withOpacity
    -- * Contrast
  , contrastColor
  ) where

import Prelude

import Data.Int (floor, toNumber)
import Data.Number ((%))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // semantic colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic color tokens (shadcn/ui style)
-- |
-- | These map to CSS custom properties that can be themed.
data SemanticColor
  = Background        -- Default background
  | Foreground        -- Default text color
  | Card              -- Card background
  | CardForeground    -- Card text
  | Popover           -- Popover background
  | PopoverForeground -- Popover text
  | Primary           -- Primary brand color
  | PrimaryForeground -- Text on primary
  | Secondary         -- Secondary color
  | SecondaryForeground
  | Muted             -- Muted backgrounds
  | MutedForeground   -- Muted text
  | Accent            -- Accent color
  | AccentForeground
  | Destructive       -- Error/danger color
  | DestructiveForeground
  | Border            -- Default border color
  | Input             -- Input border color
  | Ring              -- Focus ring color
  | Success           -- Success state
  | SuccessForeground
  | Warning           -- Warning state
  | WarningForeground
  | Info              -- Info state
  | InfoForeground

derive instance eqSemanticColor :: Eq SemanticColor

-- | Background color class
bg :: SemanticColor -> String
bg = ("bg-" <> _) <<< semanticColorName

-- | Text color class
text :: SemanticColor -> String
text = ("text-" <> _) <<< semanticColorName

-- | Border color class
border :: SemanticColor -> String
border = ("border-" <> _) <<< semanticColorName

-- | Ring color class
ring :: SemanticColor -> String
ring = ("ring-" <> _) <<< semanticColorName

-- | Background with opacity (0-100)
bgOpacity :: SemanticColor -> Int -> String
bgOpacity color op = "bg-" <> semanticColorName color <> "/" <> show op

-- | Text with opacity
textOpacity :: SemanticColor -> Int -> String
textOpacity color op = "text-" <> semanticColorName color <> "/" <> show op

-- | Border with opacity
borderOpacity :: SemanticColor -> Int -> String
borderOpacity color op = "border-" <> semanticColorName color <> "/" <> show op

semanticColorName :: SemanticColor -> String
semanticColorName = case _ of
  Background -> "background"
  Foreground -> "foreground"
  Card -> "card"
  CardForeground -> "card-foreground"
  Popover -> "popover"
  PopoverForeground -> "popover-foreground"
  Primary -> "primary"
  PrimaryForeground -> "primary-foreground"
  Secondary -> "secondary"
  SecondaryForeground -> "secondary-foreground"
  Muted -> "muted"
  MutedForeground -> "muted-foreground"
  Accent -> "accent"
  AccentForeground -> "accent-foreground"
  Destructive -> "destructive"
  DestructiveForeground -> "destructive-foreground"
  Border -> "border"
  Input -> "input"
  Ring -> "ring"
  Success -> "success"
  SuccessForeground -> "success-foreground"
  Warning -> "warning"
  WarningForeground -> "warning-foreground"
  Info -> "info"
  InfoForeground -> "info-foreground"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // palette colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tailwind color shades
data ColorShade
  = C50
  | C100
  | C200
  | C300
  | C400
  | C500
  | C600
  | C700
  | C800
  | C900
  | C950

derive instance eqColorShade :: Eq ColorShade
derive instance ordColorShade :: Ord ColorShade

-- | Tailwind palette colors
data PaletteColor
  = Slate ColorShade
  | Gray ColorShade
  | Zinc ColorShade
  | Neutral ColorShade
  | Stone ColorShade
  | Red ColorShade
  | Orange ColorShade
  | Amber ColorShade
  | Yellow ColorShade
  | Lime ColorShade
  | Green ColorShade
  | Emerald ColorShade
  | Teal ColorShade
  | Cyan ColorShade
  | Sky ColorShade
  | Blue ColorShade
  | Indigo ColorShade
  | Violet ColorShade
  | Purple ColorShade
  | Fuchsia ColorShade
  | Pink ColorShade
  | Rose ColorShade
  | White
  | Black
  | Transparent
  | Current

derive instance eqPaletteColor :: Eq PaletteColor

-- | Convert palette color to Tailwind class suffix
palette :: PaletteColor -> String
palette = case _ of
  Slate shade -> "slate-" <> shadeStr shade
  Gray shade -> "gray-" <> shadeStr shade
  Zinc shade -> "zinc-" <> shadeStr shade
  Neutral shade -> "neutral-" <> shadeStr shade
  Stone shade -> "stone-" <> shadeStr shade
  Red shade -> "red-" <> shadeStr shade
  Orange shade -> "orange-" <> shadeStr shade
  Amber shade -> "amber-" <> shadeStr shade
  Yellow shade -> "yellow-" <> shadeStr shade
  Lime shade -> "lime-" <> shadeStr shade
  Green shade -> "green-" <> shadeStr shade
  Emerald shade -> "emerald-" <> shadeStr shade
  Teal shade -> "teal-" <> shadeStr shade
  Cyan shade -> "cyan-" <> shadeStr shade
  Sky shade -> "sky-" <> shadeStr shade
  Blue shade -> "blue-" <> shadeStr shade
  Indigo shade -> "indigo-" <> shadeStr shade
  Violet shade -> "violet-" <> shadeStr shade
  Purple shade -> "purple-" <> shadeStr shade
  Fuchsia shade -> "fuchsia-" <> shadeStr shade
  Pink shade -> "pink-" <> shadeStr shade
  Rose shade -> "rose-" <> shadeStr shade
  White -> "white"
  Black -> "black"
  Transparent -> "transparent"
  Current -> "current"

shadeStr :: ColorShade -> String
shadeStr = case _ of
  C50 -> "50"
  C100 -> "100"
  C200 -> "200"
  C300 -> "300"
  C400 -> "400"
  C500 -> "500"
  C600 -> "600"
  C700 -> "700"
  C800 -> "800"
  C900 -> "900"
  C950 -> "950"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // hsl colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | HSL color representation
-- |
-- | - h: Hue (0-360)
-- | - s: Saturation (0-100)
-- | - l: Lightness (0-100)
-- | - a: Alpha (0-100)
type HSL =
  { h :: Number
  , s :: Number
  , l :: Number
  , a :: Number
  }

-- | Create an HSL color
hsl :: Number -> Number -> Number -> HSL
hsl h s l = { h, s, l, a: 100.0 }

-- | Convert to CSS hsl() string
toHslString :: HSL -> String
toHslString c
  | c.a < 100.0 = "hsla(" <> show c.h <> ", " <> show c.s <> "%, " <> show c.l <> "%, " <> show (c.a / 100.0) <> ")"
  | otherwise = "hsl(" <> show c.h <> ", " <> show c.s <> "%, " <> show c.l <> "%)"

-- | Convert to Legacy CSS variable format (shadcn style)
-- | Returns "H S% L%" for use with CSS custom properties
toLegacyCssVar :: HSL -> String
toLegacyCssVar c = show c.h <> " " <> show c.s <> "% " <> show c.l <> "%"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // color manipulation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Lighten a color by a percentage
lighten :: Number -> HSL -> HSL
lighten amount c = c { l = clamp 0.0 100.0 (c.l + amount) }

-- | Darken a color by a percentage
darken :: Number -> HSL -> HSL
darken amount c = c { l = clamp 0.0 100.0 (c.l - amount) }

-- | Increase saturation by a percentage
saturate :: Number -> HSL -> HSL
saturate amount c = c { s = clamp 0.0 100.0 (c.s + amount) }

-- | Decrease saturation by a percentage
desaturate :: Number -> HSL -> HSL
desaturate amount c = c { s = clamp 0.0 100.0 (c.s - amount) }

-- | Set opacity (0-100)
opacity :: Number -> HSL -> HSL
opacity a c = c { a = clamp 0.0 100.0 a }

-- | Apply opacity to a color
withOpacity :: Number -> HSL -> HSL
withOpacity = opacity

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // contrast
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get contrasting foreground color (black or white)
-- | Based on lightness threshold
contrastColor :: HSL -> HSL
contrastColor c
  | c.l > 55.0 = hsl 0.0 0.0 0.0   -- Dark text on light bg
  | otherwise = hsl 0.0 0.0 100.0   -- Light text on dark bg

-- Note: Using Prelude.clamp for Number bounds checking
