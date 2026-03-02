-- |
-- Module      : Lattice.State.Theme
-- Description : Pure theme state functions
-- 
-- Migrated from ui/src/stores/themeStore.ts
-- Pure query and constant functions extracted - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.State.Theme
  ( -- Pure queries (getters)
    themeGradient
  , themePrimary
  , themeSecondary
  -- Pure constants
  , getGlowColor
  -- Types
  , ThemeName(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withText
  )
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Theme name
data ThemeName
  = ThemeNameViolet
  | ThemeNameOcean
  | ThemeNameSunset
  | ThemeNameForest
  | ThemeNameEmber
  | ThemeNameMono
  deriving (Eq, Show, Generic)

instance ToJSON ThemeName where
  toJSON ThemeNameViolet = "violet"
  toJSON ThemeNameOcean = "ocean"
  toJSON ThemeNameSunset = "sunset"
  toJSON ThemeNameForest = "forest"
  toJSON ThemeNameEmber = "ember"
  toJSON ThemeNameMono = "mono"

instance FromJSON ThemeName where
  parseJSON = withText "ThemeName" $ \s ->
    case s of
      "violet" -> return ThemeNameViolet
      "ocean" -> return ThemeNameOcean
      "sunset" -> return ThemeNameSunset
      "forest" -> return ThemeNameForest
      "ember" -> return ThemeNameEmber
      "mono" -> return ThemeNameMono
      _ -> fail "Invalid ThemeName"

-- ============================================================================
-- PURE QUERIES (GETTERS)
-- ============================================================================

-- | Get theme gradient CSS variable
-- Pure function: takes theme name, returns CSS variable string
themeGradient ::
  ThemeName ->
  Text
themeGradient theme =
  let themeStr = themeNameToString theme
  in T.pack ("var(--lattice-theme-" ++ T.unpack themeStr ++ "-gradient)")

-- | Get theme primary CSS variable
-- Pure function: takes theme name, returns CSS variable string
themePrimary ::
  ThemeName ->
  Text
themePrimary theme =
  let themeStr = themeNameToString theme
  in T.pack ("var(--lattice-theme-" ++ T.unpack themeStr ++ "-primary)")

-- | Get theme secondary CSS variable
-- Pure function: takes theme name, returns CSS variable string
themeSecondary ::
  ThemeName ->
  Text
themeSecondary theme =
  let themeStr = themeNameToString theme
  in T.pack ("var(--lattice-theme-" ++ T.unpack themeStr ++ "-secondary)")

-- ============================================================================
-- PURE CONSTANTS
-- ============================================================================

-- | Get glow color for theme
-- Pure function: takes theme name, returns glow color string
getGlowColor ::
  ThemeName ->
  Text
getGlowColor ThemeNameViolet = "rgba(139, 92, 246, 0.3)"
getGlowColor ThemeNameOcean = "rgba(6, 182, 212, 0.3)"
getGlowColor ThemeNameSunset = "rgba(251, 113, 133, 0.3)"
getGlowColor ThemeNameForest = "rgba(16, 185, 129, 0.3)"
getGlowColor ThemeNameEmber = "rgba(239, 68, 68, 0.3)"
getGlowColor ThemeNameMono = "rgba(107, 114, 128, 0.3)"

-- ============================================================================
-- INTERNAL HELPERS
-- ============================================================================

-- | Convert theme name to string
themeNameToString ::
  ThemeName ->
  Text
themeNameToString ThemeNameViolet = "violet"
themeNameToString ThemeNameOcean = "ocean"
themeNameToString ThemeNameSunset = "sunset"
themeNameToString ThemeNameForest = "forest"
themeNameToString ThemeNameEmber = "ember"
themeNameToString ThemeNameMono = "mono"
