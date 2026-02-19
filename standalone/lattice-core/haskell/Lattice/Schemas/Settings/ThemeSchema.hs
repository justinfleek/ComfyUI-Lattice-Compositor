{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.ThemeSchema
Description : Theme validation schema
Copyright   : (c) Lattice, 2026
License     : MIT

Validates theme preferences stored in localStorage.

Source: lattice-core/lean/Lattice/Schemas/Settings/ThemeSchema.lean
-}

module Lattice.Schemas.Settings.ThemeSchema
  ( -- * Theme Name
    ThemeName(..)
  , themeNameFromText
  , themeNameToText
  , allThemeNames
    -- * Theme State
  , ThemeState(..)
    -- * Validation
  , validateThemeName
  , validateThemeState
    -- * Safe Validation
  , safeValidateThemeName
  , safeValidateThemeState
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Maybe (isJust)

import Lattice.Schemas.SharedValidation (ValidationError, mkError)

--------------------------------------------------------------------------------
-- Theme Name
--------------------------------------------------------------------------------

-- | Valid theme names
data ThemeName
  = ThemeViolet
  | ThemeOcean
  | ThemeSunset
  | ThemeForest
  | ThemeEmber
  | ThemeMono
  deriving stock (Eq, Show, Generic, Enum, Bounded)

-- | Convert text to ThemeName
themeNameFromText :: Text -> Maybe ThemeName
themeNameFromText "violet" = Just ThemeViolet
themeNameFromText "ocean" = Just ThemeOcean
themeNameFromText "sunset" = Just ThemeSunset
themeNameFromText "forest" = Just ThemeForest
themeNameFromText "ember" = Just ThemeEmber
themeNameFromText "mono" = Just ThemeMono
themeNameFromText _ = Nothing

-- | Convert ThemeName to text
themeNameToText :: ThemeName -> Text
themeNameToText ThemeViolet = "violet"
themeNameToText ThemeOcean = "ocean"
themeNameToText ThemeSunset = "sunset"
themeNameToText ThemeForest = "forest"
themeNameToText ThemeEmber = "ember"
themeNameToText ThemeMono = "mono"

-- | All valid theme names
allThemeNames :: [ThemeName]
allThemeNames = [minBound .. maxBound]

--------------------------------------------------------------------------------
-- Theme State
--------------------------------------------------------------------------------

-- | Theme state
data ThemeState = ThemeState
  { themeStateCurrent :: !ThemeName
  }
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate theme name from text
validateThemeName :: Text -> Text -> Either ValidationError ThemeName
validateThemeName field value =
  case themeNameFromText value of
    Just name -> Right name
    Nothing -> Left $ mkError field
      "must be one of: violet, ocean, sunset, forest, ember, mono"

-- | Validate theme state from raw data
validateThemeState :: Text -> Either ValidationError ThemeState
validateThemeState currentTheme = do
  theme <- validateThemeName "currentTheme" currentTheme
  Right ThemeState { themeStateCurrent = theme }

--------------------------------------------------------------------------------
-- Safe Validation
--------------------------------------------------------------------------------

-- | Safe validate theme name (returns Maybe)
safeValidateThemeName :: Text -> Maybe ThemeName
safeValidateThemeName = themeNameFromText

-- | Safe validate theme state (returns Maybe)
safeValidateThemeState :: Text -> Maybe ThemeState
safeValidateThemeState currentTheme =
  case validateThemeState currentTheme of
    Right state -> Just state
    Left _ -> Nothing
