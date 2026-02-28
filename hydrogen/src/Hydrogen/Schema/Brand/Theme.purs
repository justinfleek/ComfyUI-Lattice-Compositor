-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                       // hydrogen // schema // brand // theme
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Theme Configuration Compound.
-- |
-- | Themes organize all design tokens into coherent, switchable configurations.
-- | A complete theme contains:
-- |
-- | - Color tokens for all semantic roles
-- | - Spacing tokens for layout consistency
-- | - Typography tokens for text styling
-- | - Effects tokens (shadows, radii, blurs)
-- | - Motion tokens (durations, easings)
-- | - Component tokens (button, input, card styling)
-- |
-- | ## Theme Modes
-- |
-- | - **ThemeLight** — Default light mode appearance
-- | - **ThemeDark** — Dark mode with inverted luminance
-- | - **ThemeContrast** — High contrast for accessibility (WCAG AAA)
-- | - **ThemeCustom** — User-defined branded variant
-- | - **ThemeAuto** — Respects system preference (prefers-color-scheme)
-- |
-- | ## At Billion-Agent Scale
-- |
-- | Themes enable deterministic appearance switching. An agent composing UI
-- | references semantic tokens (`color.primary`, `spacing.md`), and the theme
-- | resolves these to concrete values. Same tokens, different themes, different
-- | output — but always deterministic.

module Hydrogen.Schema.Brand.Theme
  ( -- * Theme Mode
    ThemeMode(..)
  , themeModeToString
  , themeModeFromString
  , allThemeModes
  , isAccessibilityMode
  
  -- * Theme Tokens
  , ThemeTokens
  , mkThemeTokens
  , emptyThemeTokens
  , themeColors
  , themeSpacing
  , themeTypography
  , themeEffects
  , themeMotion
  , themeTokenCount
  
  -- * Theme
  , Theme
  , mkTheme
  , themeName
  , themeDesc
  , themeMode
  , themeTokens
  , themeDisplay
  
  -- * Theme Set
  , ThemeSet
  , mkThemeSet
  , emptyThemeSet
  , lightTheme
  , darkTheme
  , contrastTheme
  , customThemes
  , getThemeForMode
  , addCustomTheme
  , themeSetModes
  
  -- * Auto Theme Resolution
  , ThemePreference(..)
  , resolveAutoTheme
  , preferenceToMode
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , Ordering(LT, EQ, GT)
  , show
  , compare
  , (==)
  , (<)
  , (+)
  , (<>)
  , map
  , otherwise
  )

import Data.Array (filter, length, snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Token (TokenName, TokenDesc, unTokenName, unTokenDesc)
import Hydrogen.Schema.Brand.Token.Color (ColorToken)
import Hydrogen.Schema.Brand.Token.Spacing (SpacingToken)
import Hydrogen.Schema.Brand.Token.Type (TypeToken)
import Hydrogen.Schema.Brand.Token.Shadow (ShadowToken)
import Hydrogen.Schema.Brand.Token.Radius (RadiusToken)
import Hydrogen.Schema.Brand.Token.Duration (DurationToken)
import Hydrogen.Schema.Brand.Token.Easing (EasingToken)
import Hydrogen.Schema.Brand.Token.ZIndex (ZIndexToken)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // theme // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Theme mode selector.
-- |
-- | Determines which token values to use for rendering.
data ThemeMode
  = ThemeModeLight       -- ^ Light mode (default)
  | ThemeModeDark        -- ^ Dark mode
  | ThemeModeContrast    -- ^ High contrast (accessibility)
  | ThemeModeAuto        -- ^ System preference
  | ThemeModeCustom String  -- ^ Named custom mode

derive instance eqThemeMode :: Eq ThemeMode

instance ordThemeMode :: Ord ThemeMode where
  compare ThemeModeLight ThemeModeLight = EQ
  compare ThemeModeLight _ = LT
  compare ThemeModeDark ThemeModeLight = GT
  compare ThemeModeDark ThemeModeDark = EQ
  compare ThemeModeDark _ = LT
  compare ThemeModeContrast ThemeModeLight = GT
  compare ThemeModeContrast ThemeModeDark = GT
  compare ThemeModeContrast ThemeModeContrast = EQ
  compare ThemeModeContrast _ = LT
  compare ThemeModeAuto ThemeModeLight = GT
  compare ThemeModeAuto ThemeModeDark = GT
  compare ThemeModeAuto ThemeModeContrast = GT
  compare ThemeModeAuto ThemeModeAuto = EQ
  compare ThemeModeAuto _ = LT
  compare (ThemeModeCustom a) (ThemeModeCustom b) = compareStrings a b
  compare (ThemeModeCustom _) _ = GT

-- | Compare strings lexicographically.
compareStrings :: String -> String -> Ordering
compareStrings a b
  | a == b = EQ
  | a < b = LT
  | otherwise = GT

instance showThemeMode :: Show ThemeMode where
  show = themeModeToString

-- | Convert mode to string.
themeModeToString :: ThemeMode -> String
themeModeToString = case _ of
  ThemeModeLight -> "light"
  ThemeModeDark -> "dark"
  ThemeModeContrast -> "contrast"
  ThemeModeAuto -> "auto"
  ThemeModeCustom name -> name

-- | Parse mode from string.
themeModeFromString :: String -> ThemeMode
themeModeFromString s = case toLower (trim s) of
  "light" -> ThemeModeLight
  "dark" -> ThemeModeDark
  "contrast" -> ThemeModeContrast
  "high-contrast" -> ThemeModeContrast
  "auto" -> ThemeModeAuto
  "system" -> ThemeModeAuto
  name -> ThemeModeCustom name

-- | All standard theme modes (excludes custom).
allThemeModes :: Array ThemeMode
allThemeModes = [ThemeModeLight, ThemeModeDark, ThemeModeContrast, ThemeModeAuto]

-- | Check if mode is an accessibility mode.
isAccessibilityMode :: ThemeMode -> Boolean
isAccessibilityMode ThemeModeContrast = true
isAccessibilityMode _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // theme // tokens
-- ═════════════════════════════════════════════════════════════════════════════

-- | All tokens for a single theme.
-- |
-- | Contains complete token sets for every token category.
type ThemeTokens =
  { colors :: Array ColorToken
  , spacing :: Array SpacingToken
  , typography :: Array TypeToken
  , shadows :: Array ShadowToken
  , radii :: Array RadiusToken
  , durations :: Array DurationToken
  , easings :: Array EasingToken
  , zIndices :: Array ZIndexToken
  }

-- | Create theme tokens.
mkThemeTokens
  :: Array ColorToken
  -> Array SpacingToken
  -> Array TypeToken
  -> Array ShadowToken
  -> Array RadiusToken
  -> Array DurationToken
  -> Array EasingToken
  -> Array ZIndexToken
  -> ThemeTokens
mkThemeTokens colors spacing typography shadows radii durations easings zIndices =
  { colors: colors
  , spacing: spacing
  , typography: typography
  , shadows: shadows
  , radii: radii
  , durations: durations
  , easings: easings
  , zIndices: zIndices
  }

-- | Empty theme tokens.
emptyThemeTokens :: ThemeTokens
emptyThemeTokens =
  { colors: []
  , spacing: []
  , typography: []
  , shadows: []
  , radii: []
  , durations: []
  , easings: []
  , zIndices: []
  }

-- | Get color tokens.
themeColors :: ThemeTokens -> Array ColorToken
themeColors t = t.colors

-- | Get spacing tokens.
themeSpacing :: ThemeTokens -> Array SpacingToken
themeSpacing t = t.spacing

-- | Get typography tokens.
themeTypography :: ThemeTokens -> Array TypeToken
themeTypography t = t.typography

-- | Get effects tokens (shadows and radii combined).
themeEffects :: ThemeTokens -> { shadows :: Array ShadowToken, radii :: Array RadiusToken }
themeEffects t = { shadows: t.shadows, radii: t.radii }

-- | Get motion tokens (durations and easings combined).
themeMotion :: ThemeTokens -> { durations :: Array DurationToken, easings :: Array EasingToken }
themeMotion t = { durations: t.durations, easings: t.easings }

-- | Get total token count.
themeTokenCount :: ThemeTokens -> Int
themeTokenCount t =
  length t.colors +
  length t.spacing +
  length t.typography +
  length t.shadows +
  length t.radii +
  length t.durations +
  length t.easings +
  length t.zIndices

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // theme
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete theme configuration.
-- |
-- | Combines metadata with token values for a specific mode.
type Theme =
  { name :: TokenName
  , description :: TokenDesc
  , mode :: ThemeMode
  , tokens :: ThemeTokens
  }

-- | Create a theme.
mkTheme :: TokenName -> TokenDesc -> ThemeMode -> ThemeTokens -> Theme
mkTheme name description mode tokens =
  { name: name
  , description: description
  , mode: mode
  , tokens: tokens
  }

-- | Get theme name.
themeName :: Theme -> TokenName
themeName t = t.name

-- | Get theme description.
themeDesc :: Theme -> TokenDesc
themeDesc t = t.description

-- | Get theme mode.
themeMode :: Theme -> ThemeMode
themeMode t = t.mode

-- | Get theme tokens.
themeTokens :: Theme -> ThemeTokens
themeTokens t = t.tokens

-- | Display theme summary.
themeDisplay :: Theme -> String
themeDisplay t =
  "Theme(" <>
  unTokenName t.name <> ", " <>
  themeModeToString t.mode <> ", " <>
  show (themeTokenCount t.tokens) <> " tokens): " <>
  unTokenDesc t.description

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // theme // set
-- ═════════════════════════════════════════════════════════════════════════════

-- | A complete set of themes for an application.
-- |
-- | Contains the three standard modes plus any custom variants.
type ThemeSet =
  { light :: Theme
  , dark :: Theme
  , contrast :: Theme
  , custom :: Array Theme
  }

-- | Create a theme set.
mkThemeSet :: Theme -> Theme -> Theme -> ThemeSet
mkThemeSet light dark contrast =
  { light: light
  , dark: dark
  , contrast: contrast
  , custom: []
  }

-- | Create an empty theme set with placeholder themes.
emptyThemeSet :: TokenName -> TokenDesc -> ThemeSet
emptyThemeSet name desc =
  { light: mkTheme name desc ThemeModeLight emptyThemeTokens
  , dark: mkTheme name desc ThemeModeDark emptyThemeTokens
  , contrast: mkTheme name desc ThemeModeContrast emptyThemeTokens
  , custom: []
  }

-- | Get light theme.
lightTheme :: ThemeSet -> Theme
lightTheme ts = ts.light

-- | Get dark theme.
darkTheme :: ThemeSet -> Theme
darkTheme ts = ts.dark

-- | Get contrast theme.
contrastTheme :: ThemeSet -> Theme
contrastTheme ts = ts.contrast

-- | Get custom themes.
customThemes :: ThemeSet -> Array Theme
customThemes ts = ts.custom

-- | Get theme for a specific mode.
getThemeForMode :: ThemeMode -> ThemeSet -> Maybe Theme
getThemeForMode mode ts = case mode of
  ThemeModeLight -> Just ts.light
  ThemeModeDark -> Just ts.dark
  ThemeModeContrast -> Just ts.contrast
  ThemeModeAuto -> Just ts.light  -- Default to light for auto
  ThemeModeCustom name ->
    case filter (\t -> themeModeToString t.mode == name) ts.custom of
      [t] -> Just t
      _ -> Nothing

-- | Add a custom theme to the set.
addCustomTheme :: Theme -> ThemeSet -> ThemeSet
addCustomTheme theme ts =
  { light: ts.light
  , dark: ts.dark
  , contrast: ts.contrast
  , custom: snoc ts.custom theme
  }

-- | Get all available modes in a theme set.
themeSetModes :: ThemeSet -> Array ThemeMode
themeSetModes ts =
  [ThemeModeLight, ThemeModeDark, ThemeModeContrast] <>
  map themeMode ts.custom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // auto // resolution
-- ═════════════════════════════════════════════════════════════════════════════

-- | User/system theme preference.
-- |
-- | At runtime, these values come from:
-- | - System: `prefers-color-scheme` media query
-- | - User: Explicit preference stored in settings
-- | - Time: Automatic based on time of day
data ThemePreference
  = PreferLight
  | PreferDark
  | PreferContrast
  | PreferSystem
  | PreferTime { lightStart :: Int, darkStart :: Int }  -- ^ Hours (0-23)

derive instance eqThemePreference :: Eq ThemePreference

instance ordThemePreference :: Ord ThemePreference where
  compare PreferLight PreferLight = EQ
  compare PreferLight _ = LT
  compare PreferDark PreferLight = GT
  compare PreferDark PreferDark = EQ
  compare PreferDark _ = LT
  compare PreferContrast PreferLight = GT
  compare PreferContrast PreferDark = GT
  compare PreferContrast PreferContrast = EQ
  compare PreferContrast _ = LT
  compare PreferSystem PreferLight = GT
  compare PreferSystem PreferDark = GT
  compare PreferSystem PreferContrast = GT
  compare PreferSystem PreferSystem = EQ
  compare PreferSystem _ = LT
  compare (PreferTime a) (PreferTime b) = compare a.lightStart b.lightStart
  compare (PreferTime _) _ = GT

instance showThemePreference :: Show ThemePreference where
  show PreferLight = "PreferLight"
  show PreferDark = "PreferDark"
  show PreferContrast = "PreferContrast"
  show PreferSystem = "PreferSystem"
  show (PreferTime r) = "PreferTime(" <> show r.lightStart <> "-" <> show r.darkStart <> ")"

-- | Resolve auto theme to concrete mode.
-- |
-- | Given user preference and system state, determines the actual theme mode.
-- | - PreferSystem with dark system → ThemeModeDark
-- | - PreferTime at night → ThemeModeDark
-- | - etc.
resolveAutoTheme 
  :: ThemePreference  -- ^ User preference
  -> Boolean          -- ^ System prefers dark (from media query)
  -> Int              -- ^ Current hour (0-23)
  -> ThemeMode
resolveAutoTheme pref systemDark currentHour = case pref of
  PreferLight -> ThemeModeLight
  PreferDark -> ThemeModeDark
  PreferContrast -> ThemeModeContrast
  PreferSystem -> if systemDark then ThemeModeDark else ThemeModeLight
  PreferTime { lightStart, darkStart } ->
    if currentHour < lightStart then ThemeModeDark
    else if currentHour < darkStart then ThemeModeLight
    else ThemeModeDark

-- | Convert preference to default mode (without system/time context).
preferenceToMode :: ThemePreference -> ThemeMode
preferenceToMode = case _ of
  PreferLight -> ThemeModeLight
  PreferDark -> ThemeModeDark
  PreferContrast -> ThemeModeContrast
  PreferSystem -> ThemeModeAuto
  PreferTime _ -> ThemeModeAuto
