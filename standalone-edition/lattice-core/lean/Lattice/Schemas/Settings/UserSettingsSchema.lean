/-
  Lattice.Schemas.Settings.UserSettingsSchema - User settings validation

  Validates user settings stored in localStorage.

  Source: ui/src/schemas/settings/user-settings-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.Settings.UserSettingsSchema

open Lattice.Schemas.SharedValidation

/-! ## Enums -/

/-- UI theme modes -/
inductive ThemeMode
  | dark
  | light
  | system
  deriving Repr, BEq, DecidableEq

def ThemeMode.fromString : String → Option ThemeMode
  | "dark" => some .dark
  | "light" => some .light
  | "system" => some .system
  | _ => none

def ThemeMode.toString : ThemeMode → String
  | .dark => "dark"
  | .light => "light"
  | .system => "system"

/-- AI models -/
inductive AIModel
  | gpt4o
  | claudeSonnet
  deriving Repr, BEq, DecidableEq

def AIModel.fromString : String → Option AIModel
  | "gpt-4o" => some .gpt4o
  | "claude-sonnet" => some .claudeSonnet
  | _ => none

def AIModel.toString : AIModel → String
  | .gpt4o => "gpt-4o"
  | .claudeSonnet => "claude-sonnet"

/-- Panel layout modes -/
inductive PanelLayout
  | default
  | compact
  | expanded
  deriving Repr, BEq, DecidableEq

def PanelLayout.fromString : String → Option PanelLayout
  | "default" => some .default
  | "compact" => some .compact
  | "expanded" => some .expanded
  | _ => none

def PanelLayout.toString : PanelLayout → String
  | .default => "default"
  | .compact => "compact"
  | .expanded => "expanded"

/-! ## Constants -/

def MAX_AUTOSAVE_INTERVAL_MS : Nat := 3600000  -- 1 hour
def MAX_TIMELINE_HEIGHT : Nat := 1000
def MAX_RECENT_PROJECTS : Nat := 100

/-! ## User Settings -/

/-- User settings structure -/
structure UserSettings where
  theme : ThemeMode
  autosaveEnabled : Bool
  autosaveIntervalMs : Nat
  aiModel : AIModel
  showWelcome : Bool
  canvasBackground : String
  timelineHeight : Nat
  panelLayout : PanelLayout
  recentProjectsMax : Nat
  keyboardShortcutsEnabled : Bool
  deriving Repr, BEq

/-- Default user settings -/
def defaultUserSettings : UserSettings :=
  { theme := .dark
  , autosaveEnabled := true
  , autosaveIntervalMs := 60000  -- 1 minute
  , aiModel := .claudeSonnet
  , showWelcome := true
  , canvasBackground := "#1a1a1a"
  , timelineHeight := 200
  , panelLayout := .default
  , recentProjectsMax := 20
  , keyboardShortcutsEnabled := true
  }

/-! ## Validation -/

/-- Validate UserSettings -/
def validateUserSettings (us : UserSettings) : Except ValidationError UserSettings := do
  let _ ← validateNonNegativeInt "autosaveIntervalMs" MAX_AUTOSAVE_INTERVAL_MS us.autosaveIntervalMs
  let _ ← validateString "canvasBackground" MAX_NAME_LENGTH us.canvasBackground
  let _ ← validatePositiveInt "timelineHeight" MAX_TIMELINE_HEIGHT us.timelineHeight
  let _ ← validatePositiveInt "recentProjectsMax" MAX_RECENT_PROJECTS us.recentProjectsMax
  pure us

/-- Validate UserSettings from raw string values -/
def validateUserSettingsFromRaw
    (theme aiModel panelLayout canvasBackground : String)
    (autosaveEnabled showWelcome keyboardShortcutsEnabled : Bool)
    (autosaveIntervalMs timelineHeight recentProjectsMax : Nat)
    : Except ValidationError UserSettings := do
  let themeMode ← match ThemeMode.fromString theme with
    | some t => pure t
    | none => throw (mkError "theme" "must be one of: dark, light, system")
  let ai ← match AIModel.fromString aiModel with
    | some a => pure a
    | none => throw (mkError "aiModel" "must be one of: gpt-4o, claude-sonnet")
  let layout ← match PanelLayout.fromString panelLayout with
    | some l => pure l
    | none => throw (mkError "panelLayout" "must be one of: default, compact, expanded")
  let settings : UserSettings := {
    theme := themeMode
    autosaveEnabled := autosaveEnabled
    autosaveIntervalMs := autosaveIntervalMs
    aiModel := ai
    showWelcome := showWelcome
    canvasBackground := canvasBackground
    timelineHeight := timelineHeight
    panelLayout := layout
    recentProjectsMax := recentProjectsMax
    keyboardShortcutsEnabled := keyboardShortcutsEnabled
  }
  validateUserSettings settings

/-! ## Safe Validation -/

def safeValidateUserSettings (us : UserSettings) : Option UserSettings :=
  match validateUserSettings us with
  | .ok s => some s
  | .error _ => none

end Lattice.Schemas.Settings.UserSettingsSchema
