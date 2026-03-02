/-
  Lattice.TemplateBuilder - Template Builder System Types

  Max 500 lines.

  Source: ui/src/types/templateBuilder.ts (486 lines)

  Key concepts:
  - TemplateConfig: Configuration for a composition as a template
  - ExposedProperty: A layer property exposed in the Template Builder panel
  - PropertyGroup: Organizational grouping for exposed properties
  - ExpressionControl: Special controls (Slider, Checkbox, Dropdown) that provide values
  - SavedTemplate: A template that has been imported and saved for reuse
-/

import Lattice.Primitives

namespace Lattice.TemplateBuilder

open Lattice.Primitives

/-! ## Enumerations -/

/-- Expression control type -/
inductive ExpressionControlType where
  | slider      -- Numeric value with range
  | checkbox    -- Boolean toggle
  | dropdown    -- Predefined options
  | color       -- Color picker
  | point       -- 2D coordinate
  | angle       -- Rotation dial
  deriving Repr, BEq, DecidableEq

/-- Exposed property type -/
inductive ExposedPropertyType where
  | sourceText  -- Editable text content
  | color       -- Color picker
  | number      -- Numeric value
  | checkbox    -- Boolean toggle
  | dropdown    -- Predefined options
  | point       -- 2D position
  | media       -- Replaceable image/video
  | font        -- Font selector
  | layer       -- Layer reference picker
  deriving Repr, BEq, DecidableEq

/-- Angle display unit -/
inductive AngleDisplayUnit where
  | degrees
  | radians
  | rotations
  deriving Repr, BEq, DecidableEq

/-- Poster quality level -/
inductive PosterQuality where
  | low
  | medium
  | high
  deriving Repr, BEq, DecidableEq

/-- Accepted media types -/
inductive MediaType where
  | image
  | video
  deriving Repr, BEq, DecidableEq

/-- Template builder tab -/
inductive TemplateBuilderTab where
  | browse
  | edit
  deriving Repr, BEq, DecidableEq

/-- Font source -/
inductive FontSource where
  | google
  | cloud
  | local
  | system
  deriving Repr, BEq, DecidableEq

/-- Asset type -/
inductive TemplateAssetType where
  | depthMap
  | image
  | video
  | audio
  | model
  | pointcloud
  | texture
  | material
  | hdri
  | svg
  | sprite
  | spritesheet
  | lut
  deriving Repr, BEq, DecidableEq

/-! ## Dropdown Option -/

/-- Dropdown option value -/
inductive DropdownValue where
  | stringValue : String → DropdownValue
  | numberValue : Float → DropdownValue
  deriving Repr

/-- Dropdown option -/
structure DropdownOption where
  label : NonEmptyString
  value : DropdownValue
  deriving Repr

/-! ## Expression Control Config -/

/-- Configuration for expression control types -/
structure ExpressionControlConfig where
  -- For slider
  min : Option Float
  max : Option Float
  step : Option Float
  -- For dropdown
  options : Array DropdownOption
  -- For color
  includeAlpha : Bool
  -- For point
  is3D : Bool
  -- For angle
  displayUnit : Option AngleDisplayUnit
  deriving Repr

/-! ## Expression Control -/

/-- Expression control - a controllable value attached to a layer -/
structure ExpressionControl where
  id : NonEmptyString
  name : NonEmptyString                  -- Display name
  controlType : ExpressionControlType
  valuePropertyId : NonEmptyString       -- AnimatableProperty ID
  config : ExpressionControlConfig
  expanded : Bool
  deriving Repr

/-! ## Exposed Property Config -/

/-- Configuration for exposed properties -/
structure ExposedPropertyConfig where
  -- For numeric properties
  min : Option Float
  max : Option Float
  step : Option Float
  -- For dropdown
  options : Array DropdownOption
  -- For text
  maxLength : Option Nat
  multiline : Bool
  -- For media
  acceptedTypes : Array MediaType
  aspectRatio : Option Float
  -- For font
  allowFontChange : Bool
  allowSizeChange : Bool
  allowColorChange : Bool
  deriving Repr

/-! ## Exposed Property Default Value -/

/-- Default value for exposed properties -/
inductive ExposedPropertyDefault where
  | stringValue : String → ExposedPropertyDefault
  | numberValue : Float → ExposedPropertyDefault
  | boolValue : Bool → ExposedPropertyDefault
  | colorValue : RGBA → ExposedPropertyDefault
  | pointValue : { x : Float // y : Float } → ExposedPropertyDefault
  deriving Repr

/-! ## Exposed Property -/

/-- An exposed property in the Essential Graphics panel -/
structure ExposedProperty where
  id : NonEmptyString
  name : NonEmptyString                  -- User-friendly name
  propertyType : ExposedPropertyType
  -- Source binding
  sourceLayerId : NonEmptyString
  sourcePropertyPath : NonEmptyString    -- e.g., "data.text", "transform.position.x"
  sourceControlId : Option NonEmptyString  -- If from expression control
  -- Organization
  groupId : Option NonEmptyString
  order : Nat
  -- Configuration
  config : ExposedPropertyConfig
  -- Comment/instructions
  comment : Option String
  -- Default value
  defaultValue : Option ExposedPropertyDefault
  deriving Repr

/-! ## Property Group -/

/-- A group/folder in the Essential Graphics panel -/
structure PropertyGroup where
  id : NonEmptyString
  name : NonEmptyString
  expanded : Bool
  order : Nat
  color : Option HexColor                -- Optional accent color
  deriving Repr

/-! ## Template Comment -/

/-- A standalone comment in the Essential Graphics panel -/
structure TemplateComment where
  id : NonEmptyString
  text : String
  order : Nat
  groupId : Option NonEmptyString
  deriving Repr

/-! ## Template Export Settings -/

/-- Settings for template export -/
structure TemplateExportSettings where
  includeFonts : Bool
  includeMedia : Bool
  allowDurationChange : Bool
  posterQuality : PosterQuality
  deriving Repr

/-! ## Template Config -/

/-- Template configuration for a composition -/
structure TemplateConfig where
  name : NonEmptyString
  description : Option String
  author : Option String
  version : Option String
  tags : Array String
  masterCompositionId : NonEmptyString
  exposedProperties : Array ExposedProperty
  groups : Array PropertyGroup
  comments : Array TemplateComment
  posterFrame : FrameNumber
  exportSettings : TemplateExportSettings
  created : NonEmptyString               -- ISO 8601
  modified : NonEmptyString              -- ISO 8601
  deriving Repr

/-! ## Template Asset -/

/-- Embedded asset in template -/
structure TemplateAsset where
  id : NonEmptyString
  name : NonEmptyString
  assetType : TemplateAssetType
  data : String                          -- Base64 encoded or URL
  mimeType : NonEmptyString
  deriving Repr

/-! ## Template Font -/

/-- Font reference in template -/
structure TemplateFont where
  family : NonEmptyString
  style : NonEmptyString
  embedded : Bool
  data : Option String                   -- Base64 encoded if embedded
  source : Option FontSource
  deriving Repr

/-! ## Serialized Composition -/

/-- Serialized composition data for templates (subset of Composition) -/
structure SerializedComposition where
  id : NonEmptyString
  name : NonEmptyString
  -- Settings and layers would be full structures in practice
  currentFrame : FrameNumber
  isNestedComp : Bool
  parentCompositionId : Option NonEmptyString
  workflowId : Option NonEmptyString
  deriving Repr

/-! ## Lattice Template -/

/-- Complete Lattice template file structure -/
structure LatticeTemplate where
  formatVersion : NonEmptyString
  templateConfig : TemplateConfig
  composition : SerializedComposition
  assets : Array TemplateAsset
  fonts : Array TemplateFont
  posterImage : String                   -- Base64 encoded
  deriving Repr

/-! ## Saved Template -/

/-- A saved template in the browse panel -/
structure SavedTemplate where
  id : NonEmptyString
  name : NonEmptyString
  importedFrom : Option String           -- Original file location
  posterImage : String                   -- Thumbnail
  author : Option String
  tags : Array String
  importDate : NonEmptyString            -- ISO 8601
  templateData : Option LatticeTemplate
  deriving Repr

/-! ## Template Builder State -/

/-- Template Builder panel UI state -/
structure TemplateBuilderState where
  activeTab : TemplateBuilderTab
  -- Edit mode state
  masterCompositionId : Option NonEmptyString
  selectedPropertyIds : Array NonEmptyString
  selectedGroupId : Option NonEmptyString
  -- Browse mode state
  searchQuery : String
  filterTags : Array String
  savedTemplates : Array SavedTemplate
  deriving Repr

/-! ## Default Values -/

/-- Default export settings -/
def defaultExportSettings : TemplateExportSettings :=
  { includeFonts := true
  , includeMedia := true
  , allowDurationChange := false
  , posterQuality := PosterQuality.high
  }

/-- Default expression control config -/
def defaultExpressionControlConfig : ExpressionControlConfig :=
  { min := none
  , max := none
  , step := none
  , options := #[]
  , includeAlpha := false
  , is3D := false
  , displayUnit := none
  }

/-- Default exposed property config -/
def defaultExposedPropertyConfig : ExposedPropertyConfig :=
  { min := none
  , max := none
  , step := none
  , options := #[]
  , maxLength := none
  , multiline := false
  , acceptedTypes := #[]
  , aspectRatio := none
  , allowFontChange := true
  , allowSizeChange := true
  , allowColorChange := true
  }

end Lattice.TemplateBuilder
