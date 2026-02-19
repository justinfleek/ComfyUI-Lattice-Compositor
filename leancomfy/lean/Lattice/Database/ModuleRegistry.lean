/-
  Lattice.Database.ModuleRegistry - Database module registry definitions
  
  Defines types for modular database schema loading.
  Types are extracted to PureScript and Haskell.
-/

import Lattice.Primitives

namespace Lattice.Database.ModuleRegistry

open Lattice.Primitives

/-- Module identifier - unique string for each module -/
structure ModuleId where
  value : NonEmptyString
  deriving Repr

/-- Feature flag name that controls module loading -/
structure FeatureFlagName where
  value : NonEmptyString
  deriving Repr

/-- SQL file path relative to scripts/database/ -/
structure SqlFilePath where
  value : NonEmptyString
  deriving Repr

/-- Table name in database -/
structure TableName where
  value : NonEmptyString
  deriving Repr

/-- Module configuration -/
structure ModuleConfig where
  sqlFile : SqlFilePath
  featureFlag : Option FeatureFlagName  -- None means always loaded (core)
  dependencies : List ModuleId
  tables : List TableName
  isPlugin : Bool  -- True if this is a plugin module
  deriving Repr

/-- Module registry - maps module ID to configuration -/
structure ModuleRegistry where
  modules : List (ModuleId × ModuleConfig)
  deriving Repr

/-- Module load order - resolved dependencies -/
structure ModuleLoadOrder where
  modules : List ModuleId  -- In dependency order
  deriving Repr

/-- Module loading result -/
inductive ModuleLoadResult where
  | success : ModuleLoadResult
  | dependencyMissing : ModuleId → ModuleLoadResult
  | sqlFileNotFound : SqlFilePath → ModuleLoadResult
  | sqlError : String → ModuleLoadResult
  deriving Repr

/-- Resolve module load order based on dependencies -/
def resolveLoadOrder (registry : ModuleRegistry) (moduleIds : List ModuleId) : ModuleLoadOrder :=
  -- TODO: Implement topological sort
  -- For now, return modules in order
  ModuleLoadOrder.mk moduleIds

/-- Check if module should be loaded based on feature flags -/
def shouldLoadModule (config : ModuleConfig) (enabledFlags : List FeatureFlagName) : Bool :=
  match config.featureFlag with
  | none => true  -- Core modules always load
  | some flag => enabledFlags.contains flag
