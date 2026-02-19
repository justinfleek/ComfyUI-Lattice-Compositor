/-
  Lattice.Schemas.MeshWarp.MeshWarpSchema

  Mesh deformation pin types and weight methods.

  Source: ui/src/schemas/meshWarp/meshWarp-schema.ts
-/

namespace Lattice.Schemas.MeshWarp.MeshWarpSchema

--------------------------------------------------------------------------------
-- Warp Pin Type
--------------------------------------------------------------------------------

/-- Warp pin type options -/
inductive WarpPinType where
  | position
  | rotation
  | starch
  | overlap
  | bend
  | advanced
  deriving Repr, DecidableEq, Inhabited

def warpPinTypeFromString : String → Option WarpPinType
  | "position" => some .position
  | "rotation" => some .rotation
  | "starch" => some .starch
  | "overlap" => some .overlap
  | "bend" => some .bend
  | "advanced" => some .advanced
  | _ => Option.none

def warpPinTypeToString : WarpPinType → String
  | .position => "position"
  | .rotation => "rotation"
  | .starch => "starch"
  | .overlap => "overlap"
  | .bend => "bend"
  | .advanced => "advanced"

--------------------------------------------------------------------------------
-- Warp Weight Method
--------------------------------------------------------------------------------

/-- Warp weight method options -/
inductive WarpWeightMethod where
  | inverse_distance
  | heat_diffusion
  | radial_basis
  | bounded
  deriving Repr, DecidableEq, Inhabited

def warpWeightMethodFromString : String → Option WarpWeightMethod
  | "inverse-distance" => some .inverse_distance
  | "heat-diffusion" => some .heat_diffusion
  | "radial-basis" => some .radial_basis
  | "bounded" => some .bounded
  | _ => Option.none

def warpWeightMethodToString : WarpWeightMethod → String
  | .inverse_distance => "inverse-distance"
  | .heat_diffusion => "heat-diffusion"
  | .radial_basis => "radial-basis"
  | .bounded => "bounded"

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- 2D position -/
structure Position2D where
  x : Float
  y : Float
  deriving Repr, Inhabited

/-- Warp weight options -/
structure WarpWeightOptions where
  method : WarpWeightMethod
  falloffPower : Float
  normalize : Bool
  minWeight : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_PINS : Nat := 10000
def MAX_RADIUS : Float := 10000.0
def MAX_DEPTH : Float := 10000.0
def MAX_SCALE : Float := 100.0
def MAX_FALLOFF_POWER : Float := 100.0
def MAX_VERTICES : Nat := 10000000
def MAX_CONTROL_POINTS : Nat := 100000
def MAX_WEIGHTS : Nat := 100000000
def MAX_TRIANGLES : Nat := 10000000

end Lattice.Schemas.MeshWarp.MeshWarpSchema
