/-
  Lattice.Schemas.Exports.TTMSchema

  TTM (Time-to-Move) export format enums and types.

  Source: ui/src/schemas/exports/ttm-schema.ts
-/

namespace Lattice.Schemas.Exports.TTMSchema

--------------------------------------------------------------------------------
-- TTM Model
--------------------------------------------------------------------------------

/-- TTM model options -/
inductive TTMModel where
  | wan
  | cogvideox
  | svd
  deriving Repr, DecidableEq, Inhabited

def ttmModelFromString : String → Option TTMModel
  | "wan" => some .wan
  | "cogvideox" => some .cogvideox
  | "svd" => some .svd
  | _ => Option.none

def ttmModelToString : TTMModel → String
  | .wan => "wan"
  | .cogvideox => "cogvideox"
  | .svd => "svd"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_FRAMES : Nat := 100000
def MAX_DIMENSION : Nat := 16384
def MAX_LAYERS : Nat := 1000
def MAX_TWEAK_INDEX : Float := 100.0
def MAX_INFERENCE_STEPS : Nat := 1000

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Trajectory point -/
structure TrajectoryPoint where
  frame : Nat
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- TTM layer export data -/
structure TTMLayerExport where
  layerId : String
  layerName : String
  motionMask : String        -- Base64 PNG
  trajectory : Array TrajectoryPoint
  visibility : Array Bool
  deriving Repr, Inhabited

/-- TTM model configuration -/
structure TTMModelConfig where
  model : TTMModel
  tweakIndex : Float
  tstrongIndex : Float
  inferenceSteps : Nat
  deriving Repr, Inhabited

/-- TTM export metadata -/
structure TTMMetadata where
  layerCount : Nat
  frameCount : Nat
  width : Nat
  height : Nat
  deriving Repr, Inhabited

/-- TTM export format (multi-layer) -/
structure TTMExport where
  referenceImage : String    -- Base64 or path
  lastFrame : Option String := Option.none  -- Last frame for temporal context
  layers : Array TTMLayerExport
  combinedMotionMask : String  -- Base64 PNG
  modelConfig : TTMModelConfig
  metadata : TTMMetadata
  deriving Repr, Inhabited

/-- Legacy single trajectory point (no frame) -/
structure LegacyTrajectoryPoint where
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- TTM single layer export (legacy) -/
structure TTMSingleLayerExport where
  referenceImage : String
  motionMask : String
  trajectory : Array LegacyTrajectoryPoint
  modelConfig : TTMModelConfig
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if trajectory point is valid -/
def TrajectoryPoint.isValid (p : TrajectoryPoint) : Bool :=
  p.frame <= MAX_FRAMES &&
  p.x >= 0 && p.x <= MAX_DIMENSION.toFloat &&
  p.y >= 0 && p.y <= MAX_DIMENSION.toFloat

/-- Check if layer export is valid -/
def TTMLayerExport.isValid (l : TTMLayerExport) : Bool :=
  l.trajectory.size == l.visibility.size &&
  l.trajectory.size <= MAX_FRAMES

/-- Check if model config is valid -/
def TTMModelConfig.isValid (c : TTMModelConfig) : Bool :=
  c.tweakIndex >= 0 && c.tweakIndex <= MAX_TWEAK_INDEX &&
  c.tstrongIndex >= 0 && c.tstrongIndex <= MAX_TWEAK_INDEX &&
  c.inferenceSteps > 0 && c.inferenceSteps <= MAX_INFERENCE_STEPS

/-- Check if metadata is valid -/
def TTMMetadata.isValid (m : TTMMetadata) : Bool :=
  m.layerCount <= MAX_LAYERS &&
  m.frameCount > 0 && m.frameCount <= MAX_FRAMES &&
  m.width > 0 && m.width <= MAX_DIMENSION &&
  m.height > 0 && m.height <= MAX_DIMENSION

/-- Check if TTM export is valid -/
def TTMExport.isValid (e : TTMExport) : Bool :=
  e.metadata.isValid &&
  e.modelConfig.isValid &&
  e.layers.size == e.metadata.layerCount

end Lattice.Schemas.Exports.TTMSchema
