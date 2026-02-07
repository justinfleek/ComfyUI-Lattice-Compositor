/-
  Lattice.Schemas.Exports.NormalSchema

  Normal map export format enums and types.

  Source: ui/src/schemas/exports/normal-schema.ts
-/

namespace Lattice.Schemas.Exports.NormalSchema

--------------------------------------------------------------------------------
-- Normal Generation Method
--------------------------------------------------------------------------------

/-- Normal generation method options -/
inductive NormalGenerationMethod where
  | algebraic
  | normalcrafter
  deriving Repr, DecidableEq, Inhabited

def normalGenerationMethodFromString : String → Option NormalGenerationMethod
  | "algebraic" => some .algebraic
  | "normalcrafter" => some .normalcrafter
  | _ => Option.none

def normalGenerationMethodToString : NormalGenerationMethod → String
  | .algebraic => "algebraic"
  | .normalcrafter => "normalcrafter"

--------------------------------------------------------------------------------
-- Normal Depth Model
--------------------------------------------------------------------------------

/-- Normal depth model options -/
inductive NormalDepthModel where
  | DA3_LARGE_1_1
  | DA3_GIANT_1_1
  | DA3NESTED_GIANT_LARGE_1_1
  deriving Repr, DecidableEq, Inhabited

def normalDepthModelFromString : String → Option NormalDepthModel
  | "DA3-LARGE-1.1" => some .DA3_LARGE_1_1
  | "DA3-GIANT-1.1" => some .DA3_GIANT_1_1
  | "DA3NESTED-GIANT-LARGE-1.1" => some .DA3NESTED_GIANT_LARGE_1_1
  | _ => Option.none

def normalDepthModelToString : NormalDepthModel → String
  | .DA3_LARGE_1_1 => "DA3-LARGE-1.1"
  | .DA3_GIANT_1_1 => "DA3-GIANT-1.1"
  | .DA3NESTED_GIANT_LARGE_1_1 => "DA3NESTED-GIANT-LARGE-1.1"

--------------------------------------------------------------------------------
-- Generation Status
--------------------------------------------------------------------------------

/-- Generation status options -/
inductive GenerationStatus where
  | success
  | error
  deriving Repr, DecidableEq, Inhabited

def generationStatusFromString : String → Option GenerationStatus
  | "success" => some .success
  | "error" => some .error
  | _ => Option.none

def generationStatusToString : GenerationStatus → String
  | .success => "success"
  | .error => "error"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_DIMENSION : Nat := 16384

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Normal generation options -/
structure NormalGenerationOptions where
  method : Option NormalGenerationMethod := Option.none
  depthModel : Option NormalDepthModel := Option.none
  deriving Repr, Inhabited

/-- Normal generation metadata -/
structure NormalGenerationMetadata where
  method : String
  width : Nat
  height : Nat
  deriving Repr, Inhabited

/-- Normal generation result -/
structure NormalGenerationResult where
  status : GenerationStatus
  normal : String           -- Base64 encoded PNG (RGB normal map)
  depth : Option String := Option.none  -- Base64 depth map used (if generated)
  fallback : Option Bool := Option.none
  message : Option String := Option.none
  metadata : Option NormalGenerationMetadata := Option.none
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if metadata is valid -/
def NormalGenerationMetadata.isValid (m : NormalGenerationMetadata) : Bool :=
  m.width > 0 && m.width <= MAX_DIMENSION &&
  m.height > 0 && m.height <= MAX_DIMENSION

end Lattice.Schemas.Exports.NormalSchema
