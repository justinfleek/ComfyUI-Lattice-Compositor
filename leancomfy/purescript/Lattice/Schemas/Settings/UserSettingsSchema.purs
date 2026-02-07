-- | Lattice.Schemas.Settings.UserSettingsSchema - User settings validation
-- |
-- | Validates user settings stored in localStorage.
-- |
-- | Source: leancomfy/lean/Lattice/Schemas/Settings/UserSettingsSchema.lean

module Lattice.Schemas.Settings.UserSettingsSchema
  ( -- Enums
    ThemeMode(..)
  , themeModeFromString
  , themeModeToString
  , AIModel(..)
  , aiModelFromString
  , aiModelToString
  , PanelLayout(..)
  , panelLayoutFromString
  , panelLayoutToString
    -- Constants
  , maxAutosaveIntervalMs
  , maxTimelineHeight
  , maxRecentProjects
    -- User Settings
  , UserSettings
  , defaultUserSettings
  , validateUserSettings
  , safeValidateUserSettings
  ) where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

import Lattice.Schemas.SharedValidation
  ( ValidationError, mkError, maxNameLength
  , validateString, validatePositiveInt, validateNonNegativeInt
  )

--------------------------------------------------------------------------------
-- Enums
--------------------------------------------------------------------------------

-- | UI theme modes
data ThemeMode = ThemeDark | ThemeLight | ThemeSystem

derive instance Eq ThemeMode
derive instance Generic ThemeMode _

instance Show ThemeMode where
  show = genericShow

themeModeFromString :: String -> Maybe ThemeMode
themeModeFromString = case _ of
  "dark" -> Just ThemeDark
  "light" -> Just ThemeLight
  "system" -> Just ThemeSystem
  _ -> Nothing

themeModeToString :: ThemeMode -> String
themeModeToString = case _ of
  ThemeDark -> "dark"
  ThemeLight -> "light"
  ThemeSystem -> "system"

-- | AI models
data AIModel = AIModelGPT4o | AIModelClaudeSonnet

derive instance Eq AIModel
derive instance Generic AIModel _

instance Show AIModel where
  show = genericShow

aiModelFromString :: String -> Maybe AIModel
aiModelFromString = case _ of
  "gpt-4o" -> Just AIModelGPT4o
  "claude-sonnet" -> Just AIModelClaudeSonnet
  _ -> Nothing

aiModelToString :: AIModel -> String
aiModelToString = case _ of
  AIModelGPT4o -> "gpt-4o"
  AIModelClaudeSonnet -> "claude-sonnet"

-- | Panel layout modes
data PanelLayout = LayoutDefault | LayoutCompact | LayoutExpanded

derive instance Eq PanelLayout
derive instance Generic PanelLayout _

instance Show PanelLayout where
  show = genericShow

panelLayoutFromString :: String -> Maybe PanelLayout
panelLayoutFromString = case _ of
  "default" -> Just LayoutDefault
  "compact" -> Just LayoutCompact
  "expanded" -> Just LayoutExpanded
  _ -> Nothing

panelLayoutToString :: PanelLayout -> String
panelLayoutToString = case _ of
  LayoutDefault -> "default"
  LayoutCompact -> "compact"
  LayoutExpanded -> "expanded"

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
type UserSettings =
  { theme :: ThemeMode
  , autosaveEnabled :: Boolean
  , autosaveIntervalMs :: Int
  , aiModel :: AIModel
  , showWelcome :: Boolean
  , canvasBackground :: String
  , timelineHeight :: Int
  , panelLayout :: PanelLayout
  , recentProjectsMax :: Int
  , keyboardShortcutsEnabled :: Boolean
  }

-- | Default user settings
defaultUserSettings :: UserSettings
defaultUserSettings =
  { theme: ThemeDark
  , autosaveEnabled: true
  , autosaveIntervalMs: 60000
  , aiModel: AIModelClaudeSonnet
  , showWelcome: true
  , canvasBackground: "#1a1a1a"
  , timelineHeight: 200
  , panelLayout: LayoutDefault
  , recentProjectsMax: 20
  , keyboardShortcutsEnabled: true
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

-- | Validate UserSettings
validateUserSettings :: UserSettings -> Either ValidationError UserSettings
validateUserSettings us = do
  _ <- validateNonNegativeInt "autosaveIntervalMs" maxAutosaveIntervalMs us.autosaveIntervalMs
  _ <- validateString "canvasBackground" maxNameLength us.canvasBackground
  _ <- validatePositiveInt "timelineHeight" maxTimelineHeight us.timelineHeight
  _ <- validatePositiveInt "recentProjectsMax" maxRecentProjects us.recentProjectsMax
  pure us

-- | Safe validation
safeValidateUserSettings :: UserSettings -> Maybe UserSettings
safeValidateUserSettings us =
  case validateUserSettings us of
    Right s -> Just s
    Left _ -> Nothing
