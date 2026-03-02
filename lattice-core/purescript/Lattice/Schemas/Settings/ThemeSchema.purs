-- | Lattice.Schemas.Settings.ThemeSchema - Theme validation schema
-- |
-- | Validates theme preferences stored in localStorage.
-- |
-- | Source: lattice-core/lean/Lattice/Schemas/Settings/ThemeSchema.lean

module Lattice.Schemas.Settings.ThemeSchema
  ( -- Theme Name
    ThemeName(..)
  , themeNameFromString
  , themeNameToString
  , allThemeNames
    -- Theme State
  , ThemeState
    -- Validation
  , validateThemeName
  , validateThemeState
    -- Safe Validation
  , safeValidateThemeName
  , safeValidateThemeState
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Schemas.SharedValidation (ValidationError, mkError)

-- ────────────────────────────────────────────────────────────────────────────
-- Theme Name
-- ────────────────────────────────────────────────────────────────────────────

-- | Valid theme names
data ThemeName
  = ThemeViolet
  | ThemeOcean
  | ThemeSunset
  | ThemeForest
  | ThemeEmber
  | ThemeMono

derive instance Eq ThemeName
derive instance Generic ThemeName _

instance Show ThemeName where
  show = genericShow

-- | Convert string to ThemeName
themeNameFromString :: String -> Maybe ThemeName
themeNameFromString = case _ of
  "violet" -> Just ThemeViolet
  "ocean" -> Just ThemeOcean
  "sunset" -> Just ThemeSunset
  "forest" -> Just ThemeForest
  "ember" -> Just ThemeEmber
  "mono" -> Just ThemeMono
  _ -> Nothing

-- | Convert ThemeName to string
themeNameToString :: ThemeName -> String
themeNameToString = case _ of
  ThemeViolet -> "violet"
  ThemeOcean -> "ocean"
  ThemeSunset -> "sunset"
  ThemeForest -> "forest"
  ThemeEmber -> "ember"
  ThemeMono -> "mono"

-- | All valid theme names
allThemeNames :: Array ThemeName
allThemeNames =
  [ThemeViolet, ThemeOcean, ThemeSunset, ThemeForest, ThemeEmber, ThemeMono]

-- ────────────────────────────────────────────────────────────────────────────
-- Theme State
-- ────────────────────────────────────────────────────────────────────────────

-- | Theme state
type ThemeState =
  { currentTheme :: ThemeName
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Validate theme name from string
validateThemeName :: String -> String -> Either ValidationError ThemeName
validateThemeName field value =
  case themeNameFromString value of
    Just name -> Right name
    Nothing -> Left $ mkError field
      "must be one of: violet, ocean, sunset, forest, ember, mono"

-- | Validate theme state from raw data
validateThemeState :: String -> Either ValidationError ThemeState
validateThemeState currentTheme = do
  theme <- validateThemeName "currentTheme" currentTheme
  pure { currentTheme: theme }

-- ────────────────────────────────────────────────────────────────────────────
-- Safe Validation
-- ────────────────────────────────────────────────────────────────────────────

-- | Safe validate theme name (returns Maybe)
safeValidateThemeName :: String -> Maybe ThemeName
safeValidateThemeName = themeNameFromString

-- | Safe validate theme state (returns Maybe)
safeValidateThemeState :: String -> Maybe ThemeState
safeValidateThemeState currentTheme =
  case validateThemeState currentTheme of
    Right state -> Just state
    Left _ -> Nothing
