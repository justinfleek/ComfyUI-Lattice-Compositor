/-
  Lattice.Schemas.TemplateBuilder.TemplateBuilderSchema - Template builder enums

  Template builder system enums for Essential Graphics panel.

  Source: ui/src/schemas/templateBuilder/templateBuilder-schema.ts
-/

namespace Lattice.Schemas.TemplateBuilder.TemplateBuilderSchema

--------------------------------------------------------------------------------
-- Expression Control Type
--------------------------------------------------------------------------------

/-- Expression control types for expression parameters -/
inductive ExpressionControlType where
  | slider
  | checkbox
  | dropdown
  | color
  | point
  | angle
  deriving Repr, DecidableEq, Inhabited

def ExpressionControlType.fromString : String → Option ExpressionControlType
  | "slider" => some ExpressionControlType.slider
  | "checkbox" => some ExpressionControlType.checkbox
  | "dropdown" => some ExpressionControlType.dropdown
  | "color" => some ExpressionControlType.color
  | "point" => some ExpressionControlType.point
  | "angle" => some ExpressionControlType.angle
  | _ => none

def ExpressionControlType.toString : ExpressionControlType → String
  | ExpressionControlType.slider => "slider"
  | ExpressionControlType.checkbox => "checkbox"
  | ExpressionControlType.dropdown => "dropdown"
  | ExpressionControlType.color => "color"
  | ExpressionControlType.point => "point"
  | ExpressionControlType.angle => "angle"

--------------------------------------------------------------------------------
-- Display Unit
--------------------------------------------------------------------------------

/-- Display units for angle controls -/
inductive DisplayUnit where
  | degrees
  | radians
  | rotations
  deriving Repr, DecidableEq, Inhabited

def DisplayUnit.fromString : String → Option DisplayUnit
  | "degrees" => some DisplayUnit.degrees
  | "radians" => some DisplayUnit.radians
  | "rotations" => some DisplayUnit.rotations
  | _ => none

def DisplayUnit.toString : DisplayUnit → String
  | DisplayUnit.degrees => "degrees"
  | DisplayUnit.radians => "radians"
  | DisplayUnit.rotations => "rotations"

--------------------------------------------------------------------------------
-- Exposed Property Type
--------------------------------------------------------------------------------

/-- Exposed property types for template controls -/
inductive ExposedPropertyType where
  | sourceText
  | color
  | number
  | checkbox
  | dropdown
  | point
  | media
  | font
  | layer
  deriving Repr, DecidableEq, Inhabited

def ExposedPropertyType.fromString : String → Option ExposedPropertyType
  | "sourceText" => some ExposedPropertyType.sourceText
  | "color" => some ExposedPropertyType.color
  | "number" => some ExposedPropertyType.number
  | "checkbox" => some ExposedPropertyType.checkbox
  | "dropdown" => some ExposedPropertyType.dropdown
  | "point" => some ExposedPropertyType.point
  | "media" => some ExposedPropertyType.media
  | "font" => some ExposedPropertyType.font
  | "layer" => some ExposedPropertyType.layer
  | _ => none

def ExposedPropertyType.toString : ExposedPropertyType → String
  | ExposedPropertyType.sourceText => "sourceText"
  | ExposedPropertyType.color => "color"
  | ExposedPropertyType.number => "number"
  | ExposedPropertyType.checkbox => "checkbox"
  | ExposedPropertyType.dropdown => "dropdown"
  | ExposedPropertyType.point => "point"
  | ExposedPropertyType.media => "media"
  | ExposedPropertyType.font => "font"
  | ExposedPropertyType.layer => "layer"

--------------------------------------------------------------------------------
-- Accepted Media Type
--------------------------------------------------------------------------------

/-- Accepted media types for media controls -/
inductive AcceptedMediaType where
  | image
  | video
  deriving Repr, DecidableEq, Inhabited

def AcceptedMediaType.fromString : String → Option AcceptedMediaType
  | "image" => some AcceptedMediaType.image
  | "video" => some AcceptedMediaType.video
  | _ => none

def AcceptedMediaType.toString : AcceptedMediaType → String
  | AcceptedMediaType.image => "image"
  | AcceptedMediaType.video => "video"

--------------------------------------------------------------------------------
-- Poster Quality
--------------------------------------------------------------------------------

/-- Poster export quality levels -/
inductive PosterQuality where
  | low
  | medium
  | high
  deriving Repr, DecidableEq, Inhabited

def PosterQuality.fromString : String → Option PosterQuality
  | "low" => some PosterQuality.low
  | "medium" => some PosterQuality.medium
  | "high" => some PosterQuality.high
  | _ => none

def PosterQuality.toString : PosterQuality → String
  | PosterQuality.low => "low"
  | PosterQuality.medium => "medium"
  | PosterQuality.high => "high"

--------------------------------------------------------------------------------
-- Template Asset Type
--------------------------------------------------------------------------------

/-- Template asset types -/
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
  deriving Repr, DecidableEq, Inhabited

def TemplateAssetType.fromString : String → Option TemplateAssetType
  | "depth_map" => some TemplateAssetType.depthMap
  | "image" => some TemplateAssetType.image
  | "video" => some TemplateAssetType.video
  | "audio" => some TemplateAssetType.audio
  | "model" => some TemplateAssetType.model
  | "pointcloud" => some TemplateAssetType.pointcloud
  | "texture" => some TemplateAssetType.texture
  | "material" => some TemplateAssetType.material
  | "hdri" => some TemplateAssetType.hdri
  | "svg" => some TemplateAssetType.svg
  | "sprite" => some TemplateAssetType.sprite
  | "spritesheet" => some TemplateAssetType.spritesheet
  | "lut" => some TemplateAssetType.lut
  | _ => none

def TemplateAssetType.toString : TemplateAssetType → String
  | TemplateAssetType.depthMap => "depth_map"
  | TemplateAssetType.image => "image"
  | TemplateAssetType.video => "video"
  | TemplateAssetType.audio => "audio"
  | TemplateAssetType.model => "model"
  | TemplateAssetType.pointcloud => "pointcloud"
  | TemplateAssetType.texture => "texture"
  | TemplateAssetType.material => "material"
  | TemplateAssetType.hdri => "hdri"
  | TemplateAssetType.svg => "svg"
  | TemplateAssetType.sprite => "sprite"
  | TemplateAssetType.spritesheet => "spritesheet"
  | TemplateAssetType.lut => "lut"

--------------------------------------------------------------------------------
-- Font Source
--------------------------------------------------------------------------------

/-- Font sources for embedded fonts -/
inductive FontSource where
  | google
  | cloud
  | local
  | system
  deriving Repr, DecidableEq, Inhabited

def FontSource.fromString : String → Option FontSource
  | "google" => some FontSource.google
  | "cloud" => some FontSource.cloud
  | "local" => some FontSource.local
  | "system" => some FontSource.system
  | _ => none

def FontSource.toString : FontSource → String
  | FontSource.google => "google"
  | FontSource.cloud => "cloud"
  | FontSource.local => "local"
  | FontSource.system => "system"

--------------------------------------------------------------------------------
-- Template Builder Tab
--------------------------------------------------------------------------------

/-- Template builder panel tabs -/
inductive TemplateBuilderTab where
  | browse
  | edit
  deriving Repr, DecidableEq, Inhabited

def TemplateBuilderTab.fromString : String → Option TemplateBuilderTab
  | "browse" => some TemplateBuilderTab.browse
  | "edit" => some TemplateBuilderTab.edit
  | _ => none

def TemplateBuilderTab.toString : TemplateBuilderTab → String
  | TemplateBuilderTab.browse => "browse"
  | TemplateBuilderTab.edit => "edit"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def maxNameLength : Nat := 200
def maxDescriptionLength : Nat := 2000
def maxCommentLength : Nat := 5000
def maxTagLength : Nat := 50
def maxTagsCount : Nat := 50
def maxPathLength : Nat := 500
def maxIdLength : Nat := 200
def maxMimeTypeLength : Nat := 100
def maxFontFamilyLength : Nat := 200
def maxFontStyleLength : Nat := 100
def maxUrlLength : Nat := 2048
def maxBase64Length : Nat := 50 * 1024 * 1024  -- 50MB

end Lattice.Schemas.TemplateBuilder.TemplateBuilderSchema
