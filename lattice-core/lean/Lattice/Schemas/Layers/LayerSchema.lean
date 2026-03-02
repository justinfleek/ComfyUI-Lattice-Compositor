/-
  Lattice.Schemas.Layers.LayerSchema - Layer type enum

  All layer types supported by the compositor.

  Source: ui/src/schemas/layers/layer-schema.ts
-/

namespace Lattice.Schemas.Layers.LayerSchema

--------------------------------------------------------------------------------
-- Layer Type
--------------------------------------------------------------------------------

/-- All layer types supported by the compositor -/
inductive LayerType where
  | depth
  | normal
  | spline
  | path
  | text
  | shape
  | particle
  | particles
  | depthflow
  | image
  | video
  | audio
  | generated
  | camera
  | light
  | solid
  | control
  | null_  -- @deprecated
  | group
  | nestedComp
  | matte
  | model
  | pointcloud
  | pose
  | effectLayer
  | adjustment  -- @deprecated
  deriving Repr, DecidableEq, Inhabited

def LayerType.fromString : String → Option LayerType
  | "depth" => some LayerType.depth
  | "normal" => some LayerType.normal
  | "spline" => some LayerType.spline
  | "path" => some LayerType.path
  | "text" => some LayerType.text
  | "shape" => some LayerType.shape
  | "particle" => some LayerType.particle
  | "particles" => some LayerType.particles
  | "depthflow" => some LayerType.depthflow
  | "image" => some LayerType.image
  | "video" => some LayerType.video
  | "audio" => some LayerType.audio
  | "generated" => some LayerType.generated
  | "camera" => some LayerType.camera
  | "light" => some LayerType.light
  | "solid" => some LayerType.solid
  | "control" => some LayerType.control
  | "null" => some LayerType.null_
  | "group" => some LayerType.group
  | "nestedComp" => some LayerType.nestedComp
  | "matte" => some LayerType.matte
  | "model" => some LayerType.model
  | "pointcloud" => some LayerType.pointcloud
  | "pose" => some LayerType.pose
  | "effectLayer" => some LayerType.effectLayer
  | "adjustment" => some LayerType.adjustment
  | _ => none

def LayerType.toString : LayerType → String
  | LayerType.depth => "depth"
  | LayerType.normal => "normal"
  | LayerType.spline => "spline"
  | LayerType.path => "path"
  | LayerType.text => "text"
  | LayerType.shape => "shape"
  | LayerType.particle => "particle"
  | LayerType.particles => "particles"
  | LayerType.depthflow => "depthflow"
  | LayerType.image => "image"
  | LayerType.video => "video"
  | LayerType.audio => "audio"
  | LayerType.generated => "generated"
  | LayerType.camera => "camera"
  | LayerType.light => "light"
  | LayerType.solid => "solid"
  | LayerType.control => "control"
  | LayerType.null_ => "null"
  | LayerType.group => "group"
  | LayerType.nestedComp => "nestedComp"
  | LayerType.matte => "matte"
  | LayerType.model => "model"
  | LayerType.pointcloud => "pointcloud"
  | LayerType.pose => "pose"
  | LayerType.effectLayer => "effectLayer"
  | LayerType.adjustment => "adjustment"

/-- Check if layer type is deprecated -/
def LayerType.isDeprecated : LayerType → Bool
  | LayerType.null_ => true
  | LayerType.adjustment => true
  | _ => false

/-- Get the modern replacement for deprecated layer types -/
def LayerType.getModernReplacement : LayerType → Option LayerType
  | LayerType.null_ => some LayerType.control
  | LayerType.adjustment => some LayerType.effectLayer
  | _ => none

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def maxMasksPerLayer : Nat := 100
def maxPropertiesPerLayer : Nat := 10000
def maxEffectsPerLayer : Nat := 1000
def maxTimeStretch : Float := 100.0
def minTimeStretch : Float := 0.01

end Lattice.Schemas.Layers.LayerSchema
