-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                          // hydrogen // schema // typography // type-contrast
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TypeContrast - typographic contrast levels and accessibility variants.
-- |
-- | "Contrast" in typography refers to:
-- | 1. **Stroke contrast**: Variation between thick and thin strokes in letterforms
-- | 2. **Size contrast**: Ratio between heading and body sizes
-- | 3. **Weight contrast**: Difference between light and bold weights
-- | 4. **Color contrast**: Luminance ratio for accessibility (WCAG)
-- |
-- | This module focuses on accessibility contrast and readability adaptations
-- | for different visual contexts and user needs.
-- |
-- | ## Contrast levels
-- |
-- | - **High**: Maximum differentiation (accessibility mode)
-- | - **Normal**: Standard contrast (default)
-- | - **Reduced**: Softer contrast (reduced eye strain)
-- |
-- | ## Use cases
-- |
-- | - **High contrast**: Vision impairment, bright ambient light, aging users
-- | - **Reduced contrast**: Dark mode refinement, extended reading, luxury aesthetics

module Hydrogen.Schema.Typography.TypeContrast
  ( -- * Types
    ContrastLevel(..)
  , ContrastMode(..)
  , TypeContrast(..)
  
  -- * Constructors
  , normal
  , high
  , reduced
  , auto
  , custom
  
  -- * Modifiers
  , withMinimumRatio
  , withPrefersDarkMode
  
  -- * Predicates
  , isHighContrast
  , isReducedContrast
  , isAccessibilityMode
  , meetsWCAGAA
  , meetsWCAGAAA
  
  -- * Calculations
  , minimumContrastRatio
  , recommendedForeground
  , recommendedBackground
  
  -- * CSS Output
  , toMediaQuery
  , toCustomProperties
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // contrast level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Semantic contrast levels
-- |
-- | These map to design system tokens and accessibility requirements.
data ContrastLevel
  = LevelHigh     -- ^ Maximum contrast for accessibility
  | LevelNormal   -- ^ Standard contrast (default)
  | LevelReduced  -- ^ Softer contrast for reduced eye strain

derive instance eqContrastLevel :: Eq ContrastLevel
derive instance ordContrastLevel :: Ord ContrastLevel

instance showContrastLevel :: Show ContrastLevel where
  show LevelHigh = "LevelHigh"
  show LevelNormal = "LevelNormal"
  show LevelReduced = "LevelReduced"

-- | Get the WCAG minimum contrast ratio for each level
levelToRatio :: ContrastLevel -> Number
levelToRatio LevelHigh = 7.0    -- WCAG AAA for normal text
levelToRatio LevelNormal = 4.5  -- WCAG AA for normal text
levelToRatio LevelReduced = 3.0 -- WCAG AA for large text

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // contrast mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Contrast mode selection
-- |
-- | How contrast level is determined.
data ContrastMode
  = ModeFixed ContrastLevel   -- ^ Fixed contrast level
  | ModeAuto                  -- ^ Respect system preferences
  | ModeCustomRatio Number    -- ^ Custom contrast ratio target

derive instance eqContrastMode :: Eq ContrastMode
derive instance ordContrastMode :: Ord ContrastMode

instance showContrastMode :: Show ContrastMode where
  show (ModeFixed level) = "ModeFixed " <> show level
  show ModeAuto = "ModeAuto"
  show (ModeCustomRatio ratio) = "ModeCustomRatio " <> show ratio

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // type contrast
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete contrast specification
-- |
-- | Combines contrast mode with additional settings for foreground/background.
newtype TypeContrast = TypeContrast
  { mode :: ContrastMode
  , minimumRatio :: Maybe Number  -- Override minimum ratio if needed
  , prefersDarkMode :: Boolean    -- Hint for color selection
  }

derive instance eqTypeContrast :: Eq TypeContrast

instance showTypeContrast :: Show TypeContrast where
  show (TypeContrast tc) =
    "TypeContrast { mode: " <> show tc.mode <>
    ", minimumRatio: " <> show tc.minimumRatio <>
    ", prefersDarkMode: " <> show tc.prefersDarkMode <> " }"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // constructors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Normal contrast (default)
normal :: TypeContrast
normal = TypeContrast
  { mode: ModeFixed LevelNormal
  , minimumRatio: Nothing
  , prefersDarkMode: false
  }

-- | High contrast (accessibility mode)
-- |
-- | Use when:
-- | - User has enabled system high contrast mode
-- | - Content must meet WCAG AAA standards
-- | - Ambient lighting conditions are challenging
high :: TypeContrast
high = TypeContrast
  { mode: ModeFixed LevelHigh
  , minimumRatio: Nothing
  , prefersDarkMode: false
  }

-- | Reduced contrast (softer appearance)
-- |
-- | Use when:
-- | - Extended reading experiences
-- | - Dark mode refinement
-- | - Premium/luxury aesthetic
-- |
-- | Note: Only appropriate when accessibility requirements allow.
reduced :: TypeContrast
reduced = TypeContrast
  { mode: ModeFixed LevelReduced
  , minimumRatio: Nothing
  , prefersDarkMode: false
  }

-- | Auto contrast (respects system preferences)
-- |
-- | Automatically adapts to:
-- | - prefers-contrast: more/less
-- | - prefers-color-scheme: dark/light
-- | - forced-colors: active
auto :: TypeContrast
auto = TypeContrast
  { mode: ModeAuto
  , minimumRatio: Nothing
  , prefersDarkMode: false
  }

-- | Custom contrast with specific ratio target
custom :: Number -> TypeContrast
custom ratio = TypeContrast
  { mode: ModeCustomRatio ratio
  , minimumRatio: Just ratio
  , prefersDarkMode: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // modifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set a minimum contrast ratio override
withMinimumRatio :: Number -> TypeContrast -> TypeContrast
withMinimumRatio ratio (TypeContrast tc) = TypeContrast tc { minimumRatio = Just ratio }

-- | Indicate preference for dark mode color calculations
withPrefersDarkMode :: Boolean -> TypeContrast -> TypeContrast
withPrefersDarkMode pref (TypeContrast tc) = TypeContrast tc { prefersDarkMode = pref }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // predicates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Is this high contrast mode?
isHighContrast :: TypeContrast -> Boolean
isHighContrast (TypeContrast { mode: ModeFixed LevelHigh }) = true
isHighContrast _ = false

-- | Is this reduced contrast mode?
isReducedContrast :: TypeContrast -> Boolean
isReducedContrast (TypeContrast { mode: ModeFixed LevelReduced }) = true
isReducedContrast _ = false

-- | Is this an accessibility-focused mode?
-- |
-- | True for high contrast and auto mode (which may adapt to accessibility needs).
isAccessibilityMode :: TypeContrast -> Boolean
isAccessibilityMode (TypeContrast { mode: ModeFixed LevelHigh }) = true
isAccessibilityMode (TypeContrast { mode: ModeAuto }) = true
isAccessibilityMode _ = false

-- | Does this contrast setting meet WCAG AA requirements?
-- |
-- | WCAG AA requires:
-- | - 4.5:1 for normal text
-- | - 3:1 for large text (18pt+ or 14pt+ bold)
meetsWCAGAA :: TypeContrast -> Boolean
meetsWCAGAA tc = minimumContrastRatio tc >= 4.5

-- | Does this contrast setting meet WCAG AAA requirements?
-- |
-- | WCAG AAA requires:
-- | - 7:1 for normal text
-- | - 4.5:1 for large text
meetsWCAGAAA :: TypeContrast -> Boolean
meetsWCAGAAA tc = minimumContrastRatio tc >= 7.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // calculations
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the minimum contrast ratio for this setting
-- |
-- | Returns the explicit minimum if set, otherwise derives from mode.
minimumContrastRatio :: TypeContrast -> Number
minimumContrastRatio (TypeContrast tc) = case tc.minimumRatio of
  Just ratio -> ratio
  Nothing -> case tc.mode of
    ModeFixed level -> levelToRatio level
    ModeAuto -> 4.5  -- Default to WCAG AA
    ModeCustomRatio ratio -> ratio

-- | Recommend foreground color value (0-1 luminance) for given background
-- |
-- | Returns a luminance value that achieves the minimum contrast ratio.
-- | For light backgrounds (luminance > 0.5), returns dark foreground.
-- | For dark backgrounds (luminance <= 0.5), returns light foreground.
recommendedForeground :: Number -> TypeContrast -> Number
recommendedForeground bgLuminance tc =
  let ratio = minimumContrastRatio tc
  in if bgLuminance > 0.5
     then calculateDarkForeground bgLuminance ratio
     else calculateLightForeground bgLuminance ratio
  where
  -- Calculate dark foreground for light background
  -- WCAG contrast formula: (L1 + 0.05) / (L2 + 0.05) >= ratio
  -- For L1 > L2: L2 <= (L1 + 0.05) / ratio - 0.05
  calculateDarkForeground :: Number -> Number -> Number
  calculateDarkForeground bg r =
    let maxLum = (bg + 0.05) / r - 0.05
    in clampUnit maxLum

  -- Calculate light foreground for dark background
  -- L1 >= ratio * (L2 + 0.05) - 0.05
  calculateLightForeground :: Number -> Number -> Number
  calculateLightForeground bg r =
    let minLum = r * (bg + 0.05) - 0.05
    in clampUnit minLum

  clampUnit :: Number -> Number
  clampUnit n
    | n < 0.0 = 0.0
    | n > 1.0 = 1.0
    | otherwise = n

-- | Recommend background color value (0-1 luminance) for given foreground
-- |
-- | Inverse of recommendedForeground.
recommendedBackground :: Number -> TypeContrast -> Number
recommendedBackground fgLuminance tc =
  let ratio = minimumContrastRatio tc
  in if fgLuminance > 0.5
     then calculateDarkBackground fgLuminance ratio
     else calculateLightBackground fgLuminance ratio
  where
  calculateDarkBackground :: Number -> Number -> Number
  calculateDarkBackground fg r =
    let maxLum = (fg + 0.05) / r - 0.05
    in clampUnit maxLum

  calculateLightBackground :: Number -> Number -> Number
  calculateLightBackground fg r =
    let minLum = r * (fg + 0.05) - 0.05
    in clampUnit minLum

  clampUnit :: Number -> Number
  clampUnit n
    | n < 0.0 = 0.0
    | n > 1.0 = 1.0
    | otherwise = n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // css output
-- ═════════════════════════════════════════════════════════════════════════════

-- NOT an FFI boundary — pure string generation.
-- | Generate CSS media query for contrast preferences
toMediaQuery :: TypeContrast -> String
toMediaQuery (TypeContrast tc) = case tc.mode of
  ModeFixed LevelHigh -> "@media (prefers-contrast: more), (forced-colors: active)"
  ModeFixed LevelReduced -> "@media (prefers-contrast: less)"
  ModeFixed LevelNormal -> "@media (prefers-contrast: no-preference)"
  ModeAuto ->
    "@media (prefers-contrast: more) { /* high contrast styles */ }\n" <>
    "@media (prefers-contrast: less) { /* reduced contrast styles */ }"
  ModeCustomRatio _ -> "/* custom ratio - no standard media query */"

-- | Generate CSS custom properties for contrast settings
toCustomProperties :: TypeContrast -> String
toCustomProperties tc =
  ":root {\n" <>
  "  --type-contrast-mode: " <> modeToString tc <> ";\n" <>
  "  --type-contrast-ratio: " <> show (minimumContrastRatio tc) <> ";\n" <>
  "  --type-meets-wcag-aa: " <> boolToString (meetsWCAGAA tc) <> ";\n" <>
  "  --type-meets-wcag-aaa: " <> boolToString (meetsWCAGAAA tc) <> ";\n" <>
  "}"
  where
  modeToString :: TypeContrast -> String
  modeToString (TypeContrast { mode: ModeFixed LevelHigh }) = "high"
  modeToString (TypeContrast { mode: ModeFixed LevelNormal }) = "normal"
  modeToString (TypeContrast { mode: ModeFixed LevelReduced }) = "reduced"
  modeToString (TypeContrast { mode: ModeAuto }) = "auto"
  modeToString (TypeContrast { mode: ModeCustomRatio _ }) = "custom"

  boolToString :: Boolean -> String
  boolToString true = "1"
  boolToString false = "0"
