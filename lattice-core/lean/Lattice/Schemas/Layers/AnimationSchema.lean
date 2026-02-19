/-
  Lattice.Schemas.Layers.AnimationSchema - Animation keyframe and interpolation enums

  Animation keyframe and interpolation enums.

  Source: ui/src/schemas/layers/animation-schema.ts
-/

namespace Lattice.Schemas.Layers.AnimationSchema

--------------------------------------------------------------------------------
-- Base Interpolation Type
--------------------------------------------------------------------------------

/-- Base interpolation types -/
inductive BaseInterpolationType where
  | linear
  | bezier
  | hold
  deriving Repr, DecidableEq, Inhabited

def BaseInterpolationType.fromString : String → Option BaseInterpolationType
  | "linear" => some BaseInterpolationType.linear
  | "bezier" => some BaseInterpolationType.bezier
  | "hold" => some BaseInterpolationType.hold
  | _ => none

def BaseInterpolationType.toString : BaseInterpolationType → String
  | BaseInterpolationType.linear => "linear"
  | BaseInterpolationType.bezier => "bezier"
  | BaseInterpolationType.hold => "hold"

--------------------------------------------------------------------------------
-- Easing Type
--------------------------------------------------------------------------------

/-- All easing function names -/
inductive EasingType where
  | easeInSine
  | easeOutSine
  | easeInOutSine
  | easeInQuad
  | easeOutQuad
  | easeInOutQuad
  | easeInCubic
  | easeOutCubic
  | easeInOutCubic
  | easeInQuart
  | easeOutQuart
  | easeInOutQuart
  | easeInQuint
  | easeOutQuint
  | easeInOutQuint
  | easeInExpo
  | easeOutExpo
  | easeInOutExpo
  | easeInCirc
  | easeOutCirc
  | easeInOutCirc
  | easeInBack
  | easeOutBack
  | easeInOutBack
  | easeInElastic
  | easeOutElastic
  | easeInOutElastic
  | easeInBounce
  | easeOutBounce
  | easeInOutBounce
  deriving Repr, DecidableEq, Inhabited

def EasingType.fromString : String → Option EasingType
  | "easeInSine" => some EasingType.easeInSine
  | "easeOutSine" => some EasingType.easeOutSine
  | "easeInOutSine" => some EasingType.easeInOutSine
  | "easeInQuad" => some EasingType.easeInQuad
  | "easeOutQuad" => some EasingType.easeOutQuad
  | "easeInOutQuad" => some EasingType.easeInOutQuad
  | "easeInCubic" => some EasingType.easeInCubic
  | "easeOutCubic" => some EasingType.easeOutCubic
  | "easeInOutCubic" => some EasingType.easeInOutCubic
  | "easeInQuart" => some EasingType.easeInQuart
  | "easeOutQuart" => some EasingType.easeOutQuart
  | "easeInOutQuart" => some EasingType.easeInOutQuart
  | "easeInQuint" => some EasingType.easeInQuint
  | "easeOutQuint" => some EasingType.easeOutQuint
  | "easeInOutQuint" => some EasingType.easeInOutQuint
  | "easeInExpo" => some EasingType.easeInExpo
  | "easeOutExpo" => some EasingType.easeOutExpo
  | "easeInOutExpo" => some EasingType.easeInOutExpo
  | "easeInCirc" => some EasingType.easeInCirc
  | "easeOutCirc" => some EasingType.easeOutCirc
  | "easeInOutCirc" => some EasingType.easeInOutCirc
  | "easeInBack" => some EasingType.easeInBack
  | "easeOutBack" => some EasingType.easeOutBack
  | "easeInOutBack" => some EasingType.easeInOutBack
  | "easeInElastic" => some EasingType.easeInElastic
  | "easeOutElastic" => some EasingType.easeOutElastic
  | "easeInOutElastic" => some EasingType.easeInOutElastic
  | "easeInBounce" => some EasingType.easeInBounce
  | "easeOutBounce" => some EasingType.easeOutBounce
  | "easeInOutBounce" => some EasingType.easeInOutBounce
  | _ => none

def EasingType.toString : EasingType → String
  | EasingType.easeInSine => "easeInSine"
  | EasingType.easeOutSine => "easeOutSine"
  | EasingType.easeInOutSine => "easeInOutSine"
  | EasingType.easeInQuad => "easeInQuad"
  | EasingType.easeOutQuad => "easeOutQuad"
  | EasingType.easeInOutQuad => "easeInOutQuad"
  | EasingType.easeInCubic => "easeInCubic"
  | EasingType.easeOutCubic => "easeOutCubic"
  | EasingType.easeInOutCubic => "easeInOutCubic"
  | EasingType.easeInQuart => "easeInQuart"
  | EasingType.easeOutQuart => "easeOutQuart"
  | EasingType.easeInOutQuart => "easeInOutQuart"
  | EasingType.easeInQuint => "easeInQuint"
  | EasingType.easeOutQuint => "easeOutQuint"
  | EasingType.easeInOutQuint => "easeInOutQuint"
  | EasingType.easeInExpo => "easeInExpo"
  | EasingType.easeOutExpo => "easeOutExpo"
  | EasingType.easeInOutExpo => "easeInOutExpo"
  | EasingType.easeInCirc => "easeInCirc"
  | EasingType.easeOutCirc => "easeOutCirc"
  | EasingType.easeInOutCirc => "easeInOutCirc"
  | EasingType.easeInBack => "easeInBack"
  | EasingType.easeOutBack => "easeOutBack"
  | EasingType.easeInOutBack => "easeInOutBack"
  | EasingType.easeInElastic => "easeInElastic"
  | EasingType.easeOutElastic => "easeOutElastic"
  | EasingType.easeInOutElastic => "easeInOutElastic"
  | EasingType.easeInBounce => "easeInBounce"
  | EasingType.easeOutBounce => "easeOutBounce"
  | EasingType.easeInOutBounce => "easeInOutBounce"

--------------------------------------------------------------------------------
-- Control Mode
--------------------------------------------------------------------------------

/-- Control mode for bezier handles -/
inductive ControlMode where
  | symmetric
  | smooth
  | corner
  deriving Repr, DecidableEq, Inhabited

def ControlMode.fromString : String → Option ControlMode
  | "symmetric" => some ControlMode.symmetric
  | "smooth" => some ControlMode.smooth
  | "corner" => some ControlMode.corner
  | _ => none

def ControlMode.toString : ControlMode → String
  | ControlMode.symmetric => "symmetric"
  | ControlMode.smooth => "smooth"
  | ControlMode.corner => "corner"

--------------------------------------------------------------------------------
-- Property Type
--------------------------------------------------------------------------------

/-- Property type enum -/
inductive PropertyType where
  | number
  | position
  | color
  | enum_
  | vector3
  deriving Repr, DecidableEq, Inhabited

def PropertyType.fromString : String → Option PropertyType
  | "number" => some PropertyType.number
  | "position" => some PropertyType.position
  | "color" => some PropertyType.color
  | "enum" => some PropertyType.enum_
  | "vector3" => some PropertyType.vector3
  | _ => none

def PropertyType.toString : PropertyType → String
  | PropertyType.number => "number"
  | PropertyType.position => "position"
  | PropertyType.color => "color"
  | PropertyType.enum_ => "enum"
  | PropertyType.vector3 => "vector3"

--------------------------------------------------------------------------------
-- Expression Type
--------------------------------------------------------------------------------

/-- Expression type (preset vs custom) -/
inductive ExpressionType where
  | preset
  | custom
  deriving Repr, DecidableEq, Inhabited

def ExpressionType.fromString : String → Option ExpressionType
  | "preset" => some ExpressionType.preset
  | "custom" => some ExpressionType.custom
  | _ => none

def ExpressionType.toString : ExpressionType → String
  | ExpressionType.preset => "preset"
  | ExpressionType.custom => "custom"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def maxKeyframesPerProperty : Nat := 10000
def maxNameLength : Nat := 200
def maxStringLength : Nat := 10000
def maxExpressionParams : Nat := 1000

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Bezier handle for keyframe curves -/
structure BezierHandle where
  frame : Float
  value : Float
  enabled : Bool
  deriving Repr, DecidableEq, Inhabited

/-- 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

def isValidBezierHandle (h : BezierHandle) : Bool :=
  h.frame.isFinite && h.value.isFinite

def isValidVec3 (v : Vec3) : Bool :=
  v.x.isFinite && v.y.isFinite && v.z.isFinite

end Lattice.Schemas.Layers.AnimationSchema
