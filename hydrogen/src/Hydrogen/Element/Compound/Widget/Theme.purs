-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // widget // theme
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Widget Theme System — Neon/Emissive visual effects.
-- |
-- | ## Design Philosophy
-- |
-- | Based on COMPASS bento reference images, widgets use:
-- | - Solid dark backgrounds (NOT glassmorphism)
-- | - Glowing/emissive chart elements with neon colors
-- | - Subtle shadows for depth
-- | - High contrast between dark containers and bright charts
-- |
-- | This module provides color palettes, glow effects, and theming
-- | primitives that can be applied to any chart or widget.
-- |
-- | ## NVIDIA-Inspired Rainbow Spectrum
-- |
-- | The color palette draws from NVIDIA's visual identity:
-- | purples, blues, cyans, greens, yellows, oranges, reds, pinks.

module Hydrogen.Element.Compound.Widget.Theme
  ( -- * Color Palettes
    NeonPalette
  , defaultNeonPalette
  , rainbowPalette
  , monochromeGreenPalette
  , warmPalette
  , coolPalette
  
  -- * Individual Colors
  , neonPurple
  , neonBlue
  , neonCyan
  , neonGreen
  , neonYellow
  , neonOrange
  , neonRed
  , neonPink
  
  -- * Glow Effects
  , GlowIntensity(..)
  , glowFilter
  , glowFilterId
  , textGlow
  , boxGlow
  
  -- * Theme Modes
  , ThemeMode(..)
  , containerBackground
  , containerBorder
  , textPrimary
  , textSecondary
  , textMuted
  
  -- * Widget Sizing
  , WidgetSize(..)
  , widgetWidth
  , widgetHeight
  , chartHeight
  
  -- * Gradient Helpers
  , verticalGradient
  , horizontalGradient
  , radialGlow
  ) where

import Prelude
  ( class Show
  , class Eq
  , show
  , (==)
  , (<>)
  , (*)
  )

import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color palette
-- ═════════════════════════════════════════════════════════════════════════════

-- | Neon color palette for widget charts.
type NeonPalette =
  { primary :: String
  , secondary :: String
  , tertiary :: String
  , quaternary :: String
  , quinary :: String
  , positive :: String
  , negative :: String
  , neutral :: String
  }

-- | Default neon palette (NVIDIA-inspired rainbow).
defaultNeonPalette :: NeonPalette
defaultNeonPalette =
  { primary: neonBlue
  , secondary: neonGreen
  , tertiary: neonPurple
  , quaternary: neonYellow
  , quinary: neonPink
  , positive: neonGreen
  , negative: neonRed
  , neutral: neonBlue
  }

-- | Full rainbow palette for multi-series charts.
rainbowPalette :: Array String
rainbowPalette =
  [ neonPurple
  , neonBlue
  , neonCyan
  , neonGreen
  , neonYellow
  , neonOrange
  , neonRed
  , neonPink
  ]

-- | Monochrome green palette for single-color charts.
monochromeGreenPalette :: Array String
monochromeGreenPalette =
  [ "#22C55E"  -- Bright
  , "#16A34A"  -- Medium
  , "#15803D"  -- Dark
  , "#166534"  -- Darker
  , "#14532D"  -- Darkest
  ]

-- | Warm palette (yellows, oranges, reds).
warmPalette :: Array String
warmPalette =
  [ neonYellow
  , neonOrange
  , neonRed
  , neonPink
  , "#FCD34D"  -- Light yellow
  ]

-- | Cool palette (blues, cyans, purples).
coolPalette :: Array String
coolPalette =
  [ neonBlue
  , neonCyan
  , neonPurple
  , "#818CF8"  -- Light indigo
  , "#38BDF8"  -- Light sky
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // individual colors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Neon purple (primary accent).
neonPurple :: String
neonPurple = "#9333EA"

-- | Neon blue (data visualization primary).
neonBlue :: String
neonBlue = "#3B82F6"

-- | Neon cyan (secondary accent).
neonCyan :: String
neonCyan = "#22D3EE"

-- | Neon green (positive/success).
neonGreen :: String
neonGreen = "#22C55E"

-- | Neon yellow (warning/attention).
neonYellow :: String
neonYellow = "#FBBF24"

-- | Neon orange (highlight).
neonOrange :: String
neonOrange = "#FB923C"

-- | Neon red (negative/error).
neonRed :: String
neonRed = "#EF4444"

-- | Neon pink (accent).
neonPink :: String
neonPink = "#EC4899"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // glow effects
-- ═════════════════════════════════════════════════════════════════════════════

-- | Glow intensity levels.
data GlowIntensity
  = GlowSubtle    -- ^ Soft glow, 4px blur
  | GlowMedium    -- ^ Standard glow, 8px blur
  | GlowIntense   -- ^ Strong glow, 16px blur
  | GlowExtreme   -- ^ Maximum glow, 24px blur

derive instance eqGlowIntensity :: Eq GlowIntensity

instance showGlowIntensity :: Show GlowIntensity where
  show GlowSubtle = "subtle"
  show GlowMedium = "medium"
  show GlowIntense = "intense"
  show GlowExtreme = "extreme"

-- | Generate glow blur radius from intensity.
glowBlur :: GlowIntensity -> Number
glowBlur intensity = case intensity of
  GlowSubtle -> 4.0
  GlowMedium -> 8.0
  GlowIntense -> 16.0
  GlowExtreme -> 24.0

-- | Generate SVG filter for glow effect.
-- |
-- | Returns an SVG `<filter>` element that can be placed in `<defs>`.
-- | Apply with `filter: url(#filter-id)`.
glowFilter :: forall msg. String -> String -> GlowIntensity -> E.Element msg
glowFilter filterId color intensity =
  let
    blur = glowBlur intensity
  in
    E.element "filter"
      [ E.attr "id" filterId
      , E.attr "x" "-50%"
      , E.attr "y" "-50%"
      , E.attr "width" "200%"
      , E.attr "height" "200%"
      ]
      [ E.element "feGaussianBlur"
          [ E.attr "in" "SourceGraphic"
          , E.attr "stdDeviation" (show blur)
          , E.attr "result" "blur"
          ]
          []
      , E.element "feFlood"
          [ E.attr "flood-color" color
          , E.attr "flood-opacity" "0.6"
          , E.attr "result" "color"
          ]
          []
      , E.element "feComposite"
          [ E.attr "in" "color"
          , E.attr "in2" "blur"
          , E.attr "operator" "in"
          , E.attr "result" "glow"
          ]
          []
      , E.element "feMerge"
          []
          [ E.element "feMergeNode"
              [ E.attr "in" "glow" ]
              []
          , E.element "feMergeNode"
              [ E.attr "in" "SourceGraphic" ]
              []
          ]
      ]

-- | Generate filter ID for a color.
glowFilterId :: String -> String
glowFilterId color = "glow-" <> stripHash color
  where
    stripHash s = if s == "" then "default" else s

-- | CSS text-shadow for glow effect.
textGlow :: String -> GlowIntensity -> String
textGlow color intensity =
  let blur = glowBlur intensity
  in "0 0 " <> show blur <> "px " <> color <> "99"

-- | CSS box-shadow for container glow.
boxGlow :: String -> GlowIntensity -> String
boxGlow color intensity =
  let blur = glowBlur intensity
  in "0 0 " <> show blur <> "px " <> color <> "66"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // theme modes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Theme mode for widget rendering.
data ThemeMode
  = ModeDark   -- ^ Dashboard mode: dark background, bright elements
  | ModeLight  -- ^ Export/print mode: light background

derive instance eqThemeMode :: Eq ThemeMode

instance showThemeMode :: Show ThemeMode where
  show ModeDark = "dark"
  show ModeLight = "light"

-- | Background color for widget container.
containerBackground :: ThemeMode -> String
containerBackground mode = case mode of
  ModeDark -> "#000000"   -- Pure black
  ModeLight -> "#FFFFFF"  -- Pure white

-- | Border color for widget container.
containerBorder :: ThemeMode -> String
containerBorder mode = case mode of
  ModeDark -> "rgba(255, 255, 255, 0.1)"
  ModeLight -> "rgba(0, 0, 0, 0.1)"

-- | Primary text color.
textPrimary :: ThemeMode -> String
textPrimary mode = case mode of
  ModeDark -> "#FFFFFF"
  ModeLight -> "#0F172A"

-- | Secondary text color.
textSecondary :: ThemeMode -> String
textSecondary mode = case mode of
  ModeDark -> "rgba(255, 255, 255, 0.7)"
  ModeLight -> "rgba(15, 23, 42, 0.7)"

-- | Muted text color.
textMuted :: ThemeMode -> String
textMuted mode = case mode of
  ModeDark -> "rgba(255, 255, 255, 0.5)"
  ModeLight -> "rgba(15, 23, 42, 0.5)"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // widget sizing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Standard widget sizes.
data WidgetSize
  = SizeSmall   -- ^ Compact: 200x150
  | SizeMedium  -- ^ Standard: 300x200
  | SizeLarge   -- ^ Expanded: 400x300
  | SizeWide    -- ^ Horizontal: 600x200
  | SizeTall    -- ^ Vertical: 300x400

derive instance eqWidgetSize :: Eq WidgetSize

instance showWidgetSize :: Show WidgetSize where
  show SizeSmall = "small"
  show SizeMedium = "medium"
  show SizeLarge = "large"
  show SizeWide = "wide"
  show SizeTall = "tall"

-- | Widget width for size.
widgetWidth :: WidgetSize -> Number
widgetWidth size = case size of
  SizeSmall -> 200.0
  SizeMedium -> 300.0
  SizeLarge -> 400.0
  SizeWide -> 600.0
  SizeTall -> 300.0

-- | Widget height for size.
widgetHeight :: WidgetSize -> Number
widgetHeight size = case size of
  SizeSmall -> 150.0
  SizeMedium -> 200.0
  SizeLarge -> 300.0
  SizeWide -> 200.0
  SizeTall -> 400.0

-- | Chart area height (excluding header).
chartHeight :: WidgetSize -> Number
chartHeight size = case size of
  SizeSmall -> 80.0
  SizeMedium -> 120.0
  SizeLarge -> 200.0
  SizeWide -> 120.0
  SizeTall -> 300.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // gradient helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate vertical gradient definition for SVG.
verticalGradient :: forall msg. String -> String -> String -> E.Element msg
verticalGradient gradientId colorTop colorBottom =
  E.element "linearGradient"
    [ E.attr "id" gradientId
    , E.attr "x1" "0%"
    , E.attr "y1" "0%"
    , E.attr "x2" "0%"
    , E.attr "y2" "100%"
    ]
    [ E.element "stop"
        [ E.attr "offset" "0%"
        , E.attr "stop-color" colorTop
        ]
        []
    , E.element "stop"
        [ E.attr "offset" "100%"
        , E.attr "stop-color" colorBottom
        ]
        []
    ]

-- | Generate horizontal gradient definition for SVG.
horizontalGradient :: forall msg. String -> String -> String -> E.Element msg
horizontalGradient gradientId colorLeft colorRight =
  E.element "linearGradient"
    [ E.attr "id" gradientId
    , E.attr "x1" "0%"
    , E.attr "y1" "0%"
    , E.attr "x2" "100%"
    , E.attr "y2" "0%"
    ]
    [ E.element "stop"
        [ E.attr "offset" "0%"
        , E.attr "stop-color" colorLeft
        ]
        []
    , E.element "stop"
        [ E.attr "offset" "100%"
        , E.attr "stop-color" colorRight
        ]
        []
    ]

-- | Generate radial gradient for glow effect.
radialGlow :: forall msg. String -> String -> E.Element msg
radialGlow gradientId color =
  E.element "radialGradient"
    [ E.attr "id" gradientId
    , E.attr "cx" "50%"
    , E.attr "cy" "50%"
    , E.attr "r" "50%"
    ]
    [ E.element "stop"
        [ E.attr "offset" "0%"
        , E.attr "stop-color" color
        , E.attr "stop-opacity" "0.9"
        ]
        []
    , E.element "stop"
        [ E.attr "offset" "70%"
        , E.attr "stop-color" color
        , E.attr "stop-opacity" "0.3"
        ]
        []
    , E.element "stop"
        [ E.attr "offset" "100%"
        , E.attr "stop-color" color
        , E.attr "stop-opacity" "0"
        ]
        []
    ]
