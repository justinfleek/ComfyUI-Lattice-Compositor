{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Settings.UserSettingsSchema
Description : User settings validation
Copyright   : (c) Lattice, 2026
License     : MIT

Validates user settings stored in localStorage.

Source: lattice-core/lean/Lattice/Schemas/Settings/UserSettingsSchema.lean
-}

module Lattice.Schemas.Settings.UserSettingsSchema
  ( -- * Enums
    ThemeMode(..)
  , themeModeFromText
  , themeModeToText
  , AIModel(..)
  , aiModelFromText
  , aiModelToText
  , PanelLayout(..)
  , panelLayoutFromText
  , panelLayoutToText
    -- * Constants
  , maxAutosaveIntervalMs
  , maxTimelineHeight
  , maxRecentProjects
    -- * User Settings
  , UserSettings(..)
  , defaultUserSettings
  , validateUserSettings
  , safeValidateUserSettings
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError, maxNameLength
  , validateString, validatePositiveInt, validateNonNegativeInt
  )

--------------------------------------------------------------------------------
-- Enums
--------------------------------------------------------------------------------

-- | UI theme modes
data ThemeMode = ThemeDark | ThemeLight | ThemeSystem
  deriving stock (Eq, Show, Generic, Enum, Bounded)

themeModeFromText :: Text -> Maybe ThemeMode
themeModeFromText "dark" = Just ThemeDark
themeModeFromText "light" = Just ThemeLight
themeModeFromText "system" = Just ThemeSystem
themeModeFromText _ = Nothing

themeModeToText :: ThemeMode -> Text
themeModeToText ThemeDark = "dark"
themeModeToText ThemeLight = "light"
themeModeToText ThemeSystem = "system"

-- | AI models
data AIModel = AIModelGPT4o | AIModelClaudeSonnet
  deriving stock (Eq, Show, Generic, Enum, Bounded)

aiModelFromText :: Text -> Maybe AIModel
aiModelFromText "gpt-4o" = Just AIModelGPT4o
aiModelFromText "claude-sonnet" = Just AIModelClaudeSonnet
aiModelFromText _ = Nothing

aiModelToText :: AIModel -> Text
aiModelToText AIModelGPT4o = "gpt-4o"
aiModelToText AIModelClaudeSonnet = "claude-sonnet"

-- | Panel layout modes
data PanelLayout = LayoutDefault | LayoutCompact | LayoutExpanded
  deriving stock (Eq, Show, Generic, Enum, Bounded)

panelLayoutFromText :: Text -> Maybe PanelLayout
panelLayoutFromText "default" = Just LayoutDefault
panelLayoutFromText "compact" = Just LayoutCompact
panelLayoutFromText "expanded" = Just LayoutExpanded
panelLayoutFromText _ = Nothing

panelLayoutToText :: PanelLayout -> Text
panelLayoutToText LayoutDefault = "default"
panelLayoutToText LayoutCompact = "compact"
panelLayoutToText LayoutExpanded = "expanded"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxAutosaveIntervalMs :: Int
maxAutosaveIntervalMs = 3600000  -- 1 hour

maxTimelineHeight :: Int
maxTimelineHeight = 1000

maxRecentProjects :: Int
maxRecentProjects = 100

--------------------------------------------------------------------------------
-- User Settings
--------------------------------------------------------------------------------

-- | User settings structure
data UserSettings = UserSettings
  { usTheme :: !ThemeMode
  , usAutosaveEnabled :: !Bool
  , usAutosaveIntervalMs :: !Int
  , usAiModel :: !AIModel
  , usShowWelcome :: !Bool
  , usCanvasBackground :: !Text
  , usTimelineHeight :: !Int
  , usPanelLayout :: !PanelLayout
  , usRecentProjectsMax :: !Int
  , usKeyboardShortcutsEnabled :: !Bool
  }
  deriving stock (Eq, Show, Generic)

-- | Default user settings
defaultUserSettings :: UserSettings
defaultUserSettings = UserSettings
  { usTheme = ThemeDark
  , usAutosaveEnabled = True
  , usAutosaveIntervalMs = 60000
  , usAiModel = AIModelClaudeSonnet
  , usShowWelcome = True
  , usCanvasBackground = "#1a1a1a"
  , usTimelineHeight = 200
  , usPanelLayout = LayoutDefault
  , usRecentProjectsMax = 20
  , usKeyboardShortcutsEnabled = True
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate UserSettings
validateUserSettings :: UserSettings -> Either ValidationError UserSettings
validateUserSettings us = do
  _ <- validateNonNegativeInt "autosaveIntervalMs" maxAutosaveIntervalMs (usAutosaveIntervalMs us)
  _ <- validateString "canvasBackground" maxNameLength (usCanvasBackground us)
  _ <- validatePositiveInt "timelineHeight" maxTimelineHeight (usTimelineHeight us)
  _ <- validatePositiveInt "recentProjectsMax" maxRecentProjects (usRecentProjectsMax us)
  Right us

-- | Safe validation
safeValidateUserSettings :: UserSettings -> Maybe UserSettings
safeValidateUserSettings us =
  case validateUserSettings us of
    Right s -> Just s
    Left _ -> Nothing
