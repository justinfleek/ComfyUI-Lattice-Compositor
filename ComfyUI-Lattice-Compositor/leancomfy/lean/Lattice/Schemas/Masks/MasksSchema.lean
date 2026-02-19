/-
  Lattice.Schemas.Masks.MasksSchema

  Layer masks and track matte type enums.

  Source: ui/src/schemas/masks/masks-schema.ts
-/

namespace Lattice.Schemas.Masks.MasksSchema

--------------------------------------------------------------------------------
-- Matte Type
--------------------------------------------------------------------------------

/-- Track matte type options -/
inductive MatteType where
  | none
  | alpha
  | alpha_inverted
  | luma
  | luma_inverted
  deriving Repr, DecidableEq, Inhabited

def matteTypeFromString : String → Option MatteType
  | "none" => some .none
  | "alpha" => some .alpha
  | "alpha_inverted" => some .alpha_inverted
  | "luma" => some .luma
  | "luma_inverted" => some .luma_inverted
  | _ => Option.none

def matteTypeToString : MatteType → String
  | .none => "none"
  | .alpha => "alpha"
  | .alpha_inverted => "alpha_inverted"
  | .luma => "luma"
  | .luma_inverted => "luma_inverted"

--------------------------------------------------------------------------------
-- Mask Mode
--------------------------------------------------------------------------------

/-- Mask mode options -/
inductive MaskMode where
  | add
  | subtract
  | intersect
  | lighten
  | darken
  | difference
  | none
  deriving Repr, DecidableEq, Inhabited

def maskModeFromString : String → Option MaskMode
  | "add" => some .add
  | "subtract" => some .subtract
  | "intersect" => some .intersect
  | "lighten" => some .lighten
  | "darken" => some .darken
  | "difference" => some .difference
  | "none" => some .none
  | _ => Option.none

def maskModeToString : MaskMode → String
  | .add => "add"
  | .subtract => "subtract"
  | .intersect => "intersect"
  | .lighten => "lighten"
  | .darken => "darken"
  | .difference => "difference"
  | .none => "none"

--------------------------------------------------------------------------------
-- Mask Vertex
--------------------------------------------------------------------------------

/-- Mask vertex with bezier tangents -/
structure MaskVertex where
  x : Float
  y : Float
  inTangentX : Float
  inTangentY : Float
  outTangentX : Float
  outTangentY : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Mask Path
--------------------------------------------------------------------------------

/-- Mask path structure -/
structure MaskPath where
  closed : Bool
  vertices : List MaskVertex
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_VERTICES : Nat := 10000
def MIN_CLOSED_VERTICES : Nat := 3

end Lattice.Schemas.Masks.MasksSchema
