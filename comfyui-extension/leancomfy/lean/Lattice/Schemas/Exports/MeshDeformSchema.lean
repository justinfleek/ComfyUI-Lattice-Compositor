/-
  Lattice.Schemas.Exports.MeshDeformSchema

  Mesh deformation export format enums and types.

  Source: ui/src/schemas/exports/meshdeform-schema.ts
-/

namespace Lattice.Schemas.Exports.MeshDeformSchema

--------------------------------------------------------------------------------
-- Mesh Deform Depth Format
--------------------------------------------------------------------------------

/-- Mesh deformation depth format options -/
inductive MeshDeformDepthFormat where
  | uint8
  | uint16
  | float32
  deriving Repr, DecidableEq, Inhabited

def meshDeformDepthFormatFromString : String → Option MeshDeformDepthFormat
  | "uint8" => some .uint8
  | "uint16" => some .uint16
  | "float32" => some .float32
  | _ => Option.none

def meshDeformDepthFormatToString : MeshDeformDepthFormat → String
  | .uint8 => "uint8"
  | .uint16 => "uint16"
  | .float32 => "float32"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_DIMENSION : Nat := 16384
def MAX_FPS : Float := 120.0
def MAX_FRAMES : Nat := 100000
def MAX_PINS : Nat := 10000
def MAX_DEPTH : Float := 100000.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Composition info -/
structure CompositionInfo where
  width : Nat
  height : Nat
  frameRate : Float
  deriving Repr, Inhabited

/-- Pin metadata -/
structure PinMetadata where
  id : String
  name : String
  pinType : String
  deriving Repr, Inhabited

/-- Mesh mask export metadata -/
structure MeshMaskExportMetadata where
  width : Nat
  height : Nat
  format : String := "ImageData"
  deriving Repr, Inhabited

/-- Overlap depth export metadata -/
structure OverlapDepthExportMetadata where
  width : Nat
  height : Nat
  minDepth : Float
  maxDepth : Float
  format : String := "ImageData"
  deriving Repr, Inhabited

/-- Single frame mask data -/
structure MeshMaskFrame where
  frame : Nat
  mask : String  -- Base64 PNG or filename
  deriving Repr, Inhabited

/-- Single frame depth data -/
structure OverlapDepthFrame where
  frame : Nat
  depth : String  -- Base64 PNG or filename
  deriving Repr, Inhabited

/-- Mesh mask sequence export metadata -/
structure MeshMaskSequenceMetadata where
  frameCount : Nat
  width : Nat
  height : Nat
  deriving Repr, Inhabited

/-- Mesh mask sequence export -/
structure MeshMaskSequenceExport where
  frames : Array MeshMaskFrame
  metadata : MeshMaskSequenceMetadata
  deriving Repr, Inhabited

/-- Overlap depth sequence export metadata -/
structure OverlapDepthSequenceMetadata where
  frameCount : Nat
  width : Nat
  height : Nat
  minDepth : Float
  maxDepth : Float
  deriving Repr, Inhabited

/-- Overlap depth sequence export -/
structure OverlapDepthSequenceExport where
  frames : Array OverlapDepthFrame
  metadata : OverlapDepthSequenceMetadata
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if composition info is valid -/
def CompositionInfo.isValid (c : CompositionInfo) : Bool :=
  c.width > 0 && c.width <= MAX_DIMENSION &&
  c.height > 0 && c.height <= MAX_DIMENSION &&
  c.frameRate > 0 && c.frameRate <= MAX_FPS

/-- Check if overlap depth export metadata is valid -/
def OverlapDepthExportMetadata.isValid (m : OverlapDepthExportMetadata) : Bool :=
  m.width > 0 && m.width <= MAX_DIMENSION &&
  m.height > 0 && m.height <= MAX_DIMENSION &&
  m.maxDepth > m.minDepth &&
  m.maxDepth <= MAX_DEPTH

/-- Check if mesh mask sequence export is valid -/
def MeshMaskSequenceExport.isValid (e : MeshMaskSequenceExport) : Bool :=
  e.metadata.width > 0 && e.metadata.width <= MAX_DIMENSION &&
  e.metadata.height > 0 && e.metadata.height <= MAX_DIMENSION &&
  e.metadata.frameCount <= MAX_FRAMES &&
  e.frames.size == e.metadata.frameCount

/-- Check if overlap depth sequence metadata is valid -/
def OverlapDepthSequenceMetadata.isValid (m : OverlapDepthSequenceMetadata) : Bool :=
  m.width > 0 && m.width <= MAX_DIMENSION &&
  m.height > 0 && m.height <= MAX_DIMENSION &&
  m.frameCount <= MAX_FRAMES &&
  m.maxDepth > m.minDepth &&
  m.maxDepth <= MAX_DEPTH

end Lattice.Schemas.Exports.MeshDeformSchema
