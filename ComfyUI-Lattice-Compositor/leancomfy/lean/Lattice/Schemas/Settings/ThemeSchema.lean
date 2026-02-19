/-
  Lattice.Schemas.Settings.ThemeSchema - Theme validation schema

  Validates theme preferences stored in localStorage.

  Source: ui/src/schemas/settings/theme-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.Settings.ThemeSchema

open Lattice.Schemas.SharedValidation

/-! ## Theme Name -/

/-- Valid theme names -/
inductive ThemeName
  | violet
  | ocean
  | sunset
  | forest
  | ember
  | mono
  deriving Repr, BEq, DecidableEq

/-- Convert string to ThemeName -/
def ThemeName.fromString : String → Option ThemeName
  | "violet" => some .violet
  | "ocean" => some .ocean
  | "sunset" => some .sunset
  | "forest" => some .forest
  | "ember" => some .ember
  | "mono" => some .mono
  | _ => none

/-- Convert ThemeName to string -/
def ThemeName.toString : ThemeName → String
  | .violet => "violet"
  | .ocean => "ocean"
  | .sunset => "sunset"
  | .forest => "forest"
  | .ember => "ember"
  | .mono => "mono"

/-- All valid theme names -/
def allThemeNames : List ThemeName :=
  [.violet, .ocean, .sunset, .forest, .ember, .mono]

/-! ## Theme State -/

/-- Theme state -/
structure ThemeState where
  currentTheme : ThemeName
  deriving Repr, BEq

/-! ## Validation -/

/-- Validate theme name from string -/
def validateThemeName (field : String) (value : String) : Except ValidationError ThemeName :=
  match ThemeName.fromString value with
  | some name => pure name
  | none => throw (mkError field s!"must be one of: violet, ocean, sunset, forest, ember, mono")

/-- Validate theme state from raw data -/
def validateThemeState (currentTheme : String) : Except ValidationError ThemeState := do
  let theme ← validateThemeName "currentTheme" currentTheme
  pure { currentTheme := theme }

/-! ## Safe Validation (returns Option) -/

/-- Safe validate theme name -/
def safeValidateThemeName (value : String) : Option ThemeName :=
  match validateThemeName "value" value with
  | .ok name => some name
  | .error _ => none

/-- Safe validate theme state -/
def safeValidateThemeState (currentTheme : String) : Option ThemeState :=
  match validateThemeState currentTheme with
  | .ok state => some state
  | .error _ => none

end Lattice.Schemas.Settings.ThemeSchema
