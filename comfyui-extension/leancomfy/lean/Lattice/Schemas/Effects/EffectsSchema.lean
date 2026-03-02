/-
  Lattice.Schemas.Effects.EffectsSchema

  Effect category and parameter type enums.

  Source: ui/src/schemas/effects/effects-schema.ts
-/

namespace Lattice.Schemas.Effects.EffectsSchema

--------------------------------------------------------------------------------
-- Effect Category
--------------------------------------------------------------------------------

/-- Effect category options -/
inductive EffectCategory where
  | blur_sharpen
  | color_correction
  | distort
  | generate
  | keying
  | matte
  | noise_grain
  | perspective
  | stylize
  | time
  | transition
  | utility
  deriving Repr, DecidableEq, Inhabited

def effectCategoryFromString : String → Option EffectCategory
  | "blur-sharpen" => some .blur_sharpen
  | "color-correction" => some .color_correction
  | "distort" => some .distort
  | "generate" => some .generate
  | "keying" => some .keying
  | "matte" => some .matte
  | "noise-grain" => some .noise_grain
  | "perspective" => some .perspective
  | "stylize" => some .stylize
  | "time" => some .time
  | "transition" => some .transition
  | "utility" => some .utility
  | _ => Option.none

def effectCategoryToString : EffectCategory → String
  | .blur_sharpen => "blur-sharpen"
  | .color_correction => "color-correction"
  | .distort => "distort"
  | .generate => "generate"
  | .keying => "keying"
  | .matte => "matte"
  | .noise_grain => "noise-grain"
  | .perspective => "perspective"
  | .stylize => "stylize"
  | .time => "time"
  | .transition => "transition"
  | .utility => "utility"

--------------------------------------------------------------------------------
-- Effect Parameter Type
--------------------------------------------------------------------------------

/-- Effect parameter type options -/
inductive EffectParameterType where
  | number
  | color
  | point
  | point3D
  | angle
  | checkbox
  | dropdown
  | layer
  | string
  | curve
  | data
  deriving Repr, DecidableEq, Inhabited

def effectParameterTypeFromString : String → Option EffectParameterType
  | "number" => some .number
  | "color" => some .color
  | "point" => some .point
  | "point3D" => some .point3D
  | "angle" => some .angle
  | "checkbox" => some .checkbox
  | "dropdown" => some .dropdown
  | "layer" => some .layer
  | "string" => some .string
  | "curve" => some .curve
  | "data" => some .data
  | _ => Option.none

def effectParameterTypeToString : EffectParameterType → String
  | .number => "number"
  | .color => "color"
  | .point => "point"
  | .point3D => "point3D"
  | .angle => "angle"
  | .checkbox => "checkbox"
  | .dropdown => "dropdown"
  | .layer => "layer"
  | .string => "string"
  | .curve => "curve"
  | .data => "data"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_PARAMETERS : Nat := 1000
def MAX_PINS : Nat := 10000
def MAX_LABEL_LENGTH : Nat := 200
def MAX_VALUE_LENGTH : Nat := 500

end Lattice.Schemas.Effects.EffectsSchema
