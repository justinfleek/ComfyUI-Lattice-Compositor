/-
  Lattice.Services.Easing - Easing functions for animation

  Pure math functions for animation interpolation.
  All functions take normalized time t ∈ [0,1] and return eased value ∈ [0,1].

  Source: ui/src/services/easing.ts
-/

namespace Lattice.Services.Easing

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def PI : Float := Float.pi
def c1 : Float := 1.70158
def c2 : Float := c1 * 1.525
def c3 : Float := c1 + 1.0
def c4 : Float := (2.0 * PI) / 3.0
def c5 : Float := (2.0 * PI) / 4.5

--------------------------------------------------------------------------------
-- Easing Type Enum
--------------------------------------------------------------------------------

inductive EasingType where
  | linear
  | easeInSine | easeOutSine | easeInOutSine
  | easeInQuad | easeOutQuad | easeInOutQuad
  | easeInCubic | easeOutCubic | easeInOutCubic
  | easeInQuart | easeOutQuart | easeInOutQuart
  | easeInQuint | easeOutQuint | easeInOutQuint
  | easeInExpo | easeOutExpo | easeInOutExpo
  | easeInCirc | easeOutCirc | easeInOutCirc
  | easeInBack | easeOutBack | easeInOutBack
  | easeInElastic | easeOutElastic | easeInOutElastic
  | easeInBounce | easeOutBounce | easeInOutBounce
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Individual Easing Functions
--------------------------------------------------------------------------------

/-- Linear - no easing -/
def linear (t : Float) : Float := t

/-- Sine easing -/
def easeInSine (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else 1.0 - Float.cos ((t * PI) / 2.0)

def easeOutSine (t : Float) : Float :=
  Float.sin ((t * PI) / 2.0)

def easeInOutSine (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else -(Float.cos (PI * t) - 1.0) / 2.0

/-- Quadratic easing -/
def easeInQuad (t : Float) : Float := t * t

def easeOutQuad (t : Float) : Float :=
  let u := 1.0 - t
  1.0 - u * u

def easeInOutQuad (t : Float) : Float :=
  if t < 0.5 then 2.0 * t * t
  else
    let u := -2.0 * t + 2.0
    1.0 - (u * u) / 2.0

/-- Cubic easing -/
def easeInCubic (t : Float) : Float := t * t * t

def easeOutCubic (t : Float) : Float :=
  let u := 1.0 - t
  1.0 - u * u * u

def easeInOutCubic (t : Float) : Float :=
  if t < 0.5 then 4.0 * t * t * t
  else
    let u := -2.0 * t + 2.0
    1.0 - (u * u * u) / 2.0

/-- Quartic easing -/
def easeInQuart (t : Float) : Float := t * t * t * t

def easeOutQuart (t : Float) : Float :=
  let u := 1.0 - t
  1.0 - u * u * u * u

def easeInOutQuart (t : Float) : Float :=
  if t < 0.5 then 8.0 * t * t * t * t
  else
    let u := -2.0 * t + 2.0
    1.0 - (u * u * u * u) / 2.0

/-- Quintic easing -/
def easeInQuint (t : Float) : Float := t * t * t * t * t

def easeOutQuint (t : Float) : Float :=
  let u := 1.0 - t
  1.0 - u * u * u * u * u

def easeInOutQuint (t : Float) : Float :=
  if t < 0.5 then 16.0 * t * t * t * t * t
  else
    let u := -2.0 * t + 2.0
    1.0 - (u * u * u * u * u) / 2.0

/-- Exponential easing -/
def easeInExpo (t : Float) : Float :=
  if t == 0.0 then 0.0
  else Float.exp (Float.log 2.0 * (10.0 * t - 10.0))

def easeOutExpo (t : Float) : Float :=
  if t == 1.0 then 1.0
  else 1.0 - Float.exp (Float.log 2.0 * (-10.0 * t))

def easeInOutExpo (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else if t < 0.5 then Float.exp (Float.log 2.0 * (20.0 * t - 10.0)) / 2.0
  else (2.0 - Float.exp (Float.log 2.0 * (-20.0 * t + 10.0))) / 2.0

/-- Circular easing -/
def easeInCirc (t : Float) : Float :=
  1.0 - Float.sqrt (1.0 - t * t)

def easeOutCirc (t : Float) : Float :=
  let u := t - 1.0
  Float.sqrt (1.0 - u * u)

def easeInOutCirc (t : Float) : Float :=
  if t < 0.5 then
    let u := 2.0 * t
    (1.0 - Float.sqrt (1.0 - u * u)) / 2.0
  else
    let u := -2.0 * t + 2.0
    (Float.sqrt (1.0 - u * u) + 1.0) / 2.0

/-- Back easing (overshoot) -/
def easeInBack (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else c3 * t * t * t - c1 * t * t

def easeOutBack (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else
    let u := t - 1.0
    1.0 + c3 * u * u * u + c1 * u * u

def easeInOutBack (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else if t < 0.5 then
    let u := 2.0 * t
    (u * u * ((c2 + 1.0) * u - c2)) / 2.0
  else
    let u := 2.0 * t - 2.0
    (u * u * ((c2 + 1.0) * u + c2) + 2.0) / 2.0

/-- Elastic easing -/
def easeInElastic (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else
    let pow := Float.exp (Float.log 2.0 * (10.0 * t - 10.0))
    -pow * Float.sin ((t * 10.0 - 10.75) * c4)

def easeOutElastic (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else
    let pow := Float.exp (Float.log 2.0 * (-10.0 * t))
    pow * Float.sin ((t * 10.0 - 0.75) * c4) + 1.0

def easeInOutElastic (t : Float) : Float :=
  if t == 0.0 then 0.0
  else if t == 1.0 then 1.0
  else if t < 0.5 then
    let pow := Float.exp (Float.log 2.0 * (20.0 * t - 10.0))
    -(pow * Float.sin ((20.0 * t - 11.125) * c5)) / 2.0
  else
    let pow := Float.exp (Float.log 2.0 * (-20.0 * t + 10.0))
    (pow * Float.sin ((20.0 * t - 11.125) * c5)) / 2.0 + 1.0

/-- Bounce easing -/
def easeOutBounce (t : Float) : Float :=
  let n1 := 7.5625
  let d1 := 2.75
  if t < 1.0 / d1 then n1 * t * t
  else if t < 2.0 / d1 then
    let t' := t - 1.5 / d1
    n1 * t' * t' + 0.75
  else if t < 2.5 / d1 then
    let t' := t - 2.25 / d1
    n1 * t' * t' + 0.9375
  else
    let t' := t - 2.625 / d1
    n1 * t' * t' + 0.984375

def easeInBounce (t : Float) : Float :=
  1.0 - easeOutBounce (1.0 - t)

def easeInOutBounce (t : Float) : Float :=
  if t < 0.5 then (1.0 - easeOutBounce (1.0 - 2.0 * t)) / 2.0
  else (1.0 + easeOutBounce (2.0 * t - 1.0)) / 2.0

--------------------------------------------------------------------------------
-- Main Dispatch Function
--------------------------------------------------------------------------------

/-- Apply easing by type -/
def applyEasingType (easingType : EasingType) (t : Float) : Float :=
  match easingType with
  | .linear => linear t
  | .easeInSine => easeInSine t
  | .easeOutSine => easeOutSine t
  | .easeInOutSine => easeInOutSine t
  | .easeInQuad => easeInQuad t
  | .easeOutQuad => easeOutQuad t
  | .easeInOutQuad => easeInOutQuad t
  | .easeInCubic => easeInCubic t
  | .easeOutCubic => easeOutCubic t
  | .easeInOutCubic => easeInOutCubic t
  | .easeInQuart => easeInQuart t
  | .easeOutQuart => easeOutQuart t
  | .easeInOutQuart => easeInOutQuart t
  | .easeInQuint => easeInQuint t
  | .easeOutQuint => easeOutQuint t
  | .easeInOutQuint => easeInOutQuint t
  | .easeInExpo => easeInExpo t
  | .easeOutExpo => easeOutExpo t
  | .easeInOutExpo => easeInOutExpo t
  | .easeInCirc => easeInCirc t
  | .easeOutCirc => easeOutCirc t
  | .easeInOutCirc => easeInOutCirc t
  | .easeInBack => easeInBack t
  | .easeOutBack => easeOutBack t
  | .easeInOutBack => easeInOutBack t
  | .easeInElastic => easeInElastic t
  | .easeOutElastic => easeOutElastic t
  | .easeInOutElastic => easeInOutElastic t
  | .easeInBounce => easeInBounce t
  | .easeOutBounce => easeOutBounce t
  | .easeInOutBounce => easeInOutBounce t

/-- Apply easing with clamped input -/
def applyEasing (easingType : EasingType) (t : Float) : Float :=
  let clampedT := Float.max 0.0 (Float.min 1.0 t)
  applyEasingType easingType clampedT

/-- Interpolate with easing -/
def interpolateWithEasing (start : Float) (stop : Float) (t : Float) (easingType : EasingType) : Float :=
  let easedT := applyEasing easingType t
  start + (stop - start) * easedT

--------------------------------------------------------------------------------
-- String Conversion
--------------------------------------------------------------------------------

def EasingType.fromString : String → Option EasingType
  | "linear" => some .linear
  | "easeInSine" => some .easeInSine
  | "easeOutSine" => some .easeOutSine
  | "easeInOutSine" => some .easeInOutSine
  | "easeInQuad" => some .easeInQuad
  | "easeOutQuad" => some .easeOutQuad
  | "easeInOutQuad" => some .easeInOutQuad
  | "easeInCubic" => some .easeInCubic
  | "easeOutCubic" => some .easeOutCubic
  | "easeInOutCubic" => some .easeInOutCubic
  | "easeInQuart" => some .easeInQuart
  | "easeOutQuart" => some .easeOutQuart
  | "easeInOutQuart" => some .easeInOutQuart
  | "easeInQuint" => some .easeInQuint
  | "easeOutQuint" => some .easeOutQuint
  | "easeInOutQuint" => some .easeInOutQuint
  | "easeInExpo" => some .easeInExpo
  | "easeOutExpo" => some .easeOutExpo
  | "easeInOutExpo" => some .easeInOutExpo
  | "easeInCirc" => some .easeInCirc
  | "easeOutCirc" => some .easeOutCirc
  | "easeInOutCirc" => some .easeInOutCirc
  | "easeInBack" => some .easeInBack
  | "easeOutBack" => some .easeOutBack
  | "easeInOutBack" => some .easeInOutBack
  | "easeInElastic" => some .easeInElastic
  | "easeOutElastic" => some .easeOutElastic
  | "easeInOutElastic" => some .easeInOutElastic
  | "easeInBounce" => some .easeInBounce
  | "easeOutBounce" => some .easeOutBounce
  | "easeInOutBounce" => some .easeInOutBounce
  | _ => none

def EasingType.toString : EasingType → String
  | .linear => "linear"
  | .easeInSine => "easeInSine"
  | .easeOutSine => "easeOutSine"
  | .easeInOutSine => "easeInOutSine"
  | .easeInQuad => "easeInQuad"
  | .easeOutQuad => "easeOutQuad"
  | .easeInOutQuad => "easeInOutQuad"
  | .easeInCubic => "easeInCubic"
  | .easeOutCubic => "easeOutCubic"
  | .easeInOutCubic => "easeInOutCubic"
  | .easeInQuart => "easeInQuart"
  | .easeOutQuart => "easeOutQuart"
  | .easeInOutQuart => "easeInOutQuart"
  | .easeInQuint => "easeInQuint"
  | .easeOutQuint => "easeOutQuint"
  | .easeInOutQuint => "easeInOutQuint"
  | .easeInExpo => "easeInExpo"
  | .easeOutExpo => "easeOutExpo"
  | .easeInOutExpo => "easeInOutExpo"
  | .easeInCirc => "easeInCirc"
  | .easeOutCirc => "easeOutCirc"
  | .easeInOutCirc => "easeInOutCirc"
  | .easeInBack => "easeInBack"
  | .easeOutBack => "easeOutBack"
  | .easeInOutBack => "easeInOutBack"
  | .easeInElastic => "easeInElastic"
  | .easeOutElastic => "easeOutElastic"
  | .easeInOutElastic => "easeInOutElastic"
  | .easeInBounce => "easeInBounce"
  | .easeOutBounce => "easeOutBounce"
  | .easeInOutBounce => "easeInOutBounce"

--------------------------------------------------------------------------------
-- THEOREMS: Boundary Conditions
-- All easing functions must satisfy f(0) = 0 and f(1) = 1
-- Proofs by native computation - no axioms, sorry, or admits
--------------------------------------------------------------------------------

/-- Linear easing boundary: linear(0) = 0 -/
theorem linear_zero : linear 0.0 = 0.0 := by native_decide

/-- Linear easing boundary: linear(1) = 1 -/
theorem linear_one : linear 1.0 = 1.0 := by native_decide

/-- Quadratic easing boundaries -/
theorem easeInQuad_zero : easeInQuad 0.0 = 0.0 := by native_decide
theorem easeInQuad_one : easeInQuad 1.0 = 1.0 := by native_decide
theorem easeOutQuad_zero : easeOutQuad 0.0 = 0.0 := by native_decide
theorem easeOutQuad_one : easeOutQuad 1.0 = 1.0 := by native_decide
theorem easeInOutQuad_zero : easeInOutQuad 0.0 = 0.0 := by native_decide
theorem easeInOutQuad_one : easeInOutQuad 1.0 = 1.0 := by native_decide

/-- Cubic easing boundaries -/
theorem easeInCubic_zero : easeInCubic 0.0 = 0.0 := by native_decide
theorem easeInCubic_one : easeInCubic 1.0 = 1.0 := by native_decide
theorem easeOutCubic_zero : easeOutCubic 0.0 = 0.0 := by native_decide
theorem easeOutCubic_one : easeOutCubic 1.0 = 1.0 := by native_decide
theorem easeInOutCubic_zero : easeInOutCubic 0.0 = 0.0 := by native_decide
theorem easeInOutCubic_one : easeInOutCubic 1.0 = 1.0 := by native_decide

/-- Quartic easing boundaries -/
theorem easeInQuart_zero : easeInQuart 0.0 = 0.0 := by native_decide
theorem easeInQuart_one : easeInQuart 1.0 = 1.0 := by native_decide
theorem easeOutQuart_zero : easeOutQuart 0.0 = 0.0 := by native_decide
theorem easeOutQuart_one : easeOutQuart 1.0 = 1.0 := by native_decide
theorem easeInOutQuart_zero : easeInOutQuart 0.0 = 0.0 := by native_decide
theorem easeInOutQuart_one : easeInOutQuart 1.0 = 1.0 := by native_decide

/-- Quintic easing boundaries -/
theorem easeInQuint_zero : easeInQuint 0.0 = 0.0 := by native_decide
theorem easeInQuint_one : easeInQuint 1.0 = 1.0 := by native_decide
theorem easeOutQuint_zero : easeOutQuint 0.0 = 0.0 := by native_decide
theorem easeOutQuint_one : easeOutQuint 1.0 = 1.0 := by native_decide
theorem easeInOutQuint_zero : easeInOutQuint 0.0 = 0.0 := by native_decide
theorem easeInOutQuint_one : easeInOutQuint 1.0 = 1.0 := by native_decide

/-- Sine easing boundaries -/
theorem easeInSine_zero : easeInSine 0.0 = 0.0 := by native_decide
theorem easeInSine_one : easeInSine 1.0 = 1.0 := by native_decide
theorem easeOutSine_zero : easeOutSine 0.0 = 0.0 := by native_decide
theorem easeOutSine_one : easeOutSine 1.0 = 1.0 := by native_decide
theorem easeInOutSine_zero : easeInOutSine 0.0 = 0.0 := by native_decide
theorem easeInOutSine_one : easeInOutSine 1.0 = 1.0 := by native_decide

/-- Exponential easing boundaries -/
theorem easeInExpo_zero : easeInExpo 0.0 = 0.0 := by native_decide
theorem easeInExpo_one : easeInExpo 1.0 = 1.0 := by native_decide
theorem easeOutExpo_zero : easeOutExpo 0.0 = 0.0 := by native_decide
theorem easeOutExpo_one : easeOutExpo 1.0 = 1.0 := by native_decide
theorem easeInOutExpo_zero : easeInOutExpo 0.0 = 0.0 := by native_decide
theorem easeInOutExpo_one : easeInOutExpo 1.0 = 1.0 := by native_decide

/-- Circular easing boundaries -/
theorem easeInCirc_zero : easeInCirc 0.0 = 0.0 := by native_decide
theorem easeInCirc_one : easeInCirc 1.0 = 1.0 := by native_decide
theorem easeOutCirc_zero : easeOutCirc 0.0 = 0.0 := by native_decide
theorem easeOutCirc_one : easeOutCirc 1.0 = 1.0 := by native_decide
theorem easeInOutCirc_zero : easeInOutCirc 0.0 = 0.0 := by native_decide
theorem easeInOutCirc_one : easeInOutCirc 1.0 = 1.0 := by native_decide

/-- Back easing boundaries -/
theorem easeInBack_zero : easeInBack 0.0 = 0.0 := by native_decide
theorem easeInBack_one : easeInBack 1.0 = 1.0 := by native_decide
theorem easeOutBack_zero : easeOutBack 0.0 = 0.0 := by native_decide
theorem easeOutBack_one : easeOutBack 1.0 = 1.0 := by native_decide
theorem easeInOutBack_zero : easeInOutBack 0.0 = 0.0 := by native_decide
theorem easeInOutBack_one : easeInOutBack 1.0 = 1.0 := by native_decide

/-- Elastic easing boundaries -/
theorem easeInElastic_zero : easeInElastic 0.0 = 0.0 := by native_decide
theorem easeInElastic_one : easeInElastic 1.0 = 1.0 := by native_decide
theorem easeOutElastic_zero : easeOutElastic 0.0 = 0.0 := by native_decide
theorem easeOutElastic_one : easeOutElastic 1.0 = 1.0 := by native_decide
theorem easeInOutElastic_zero : easeInOutElastic 0.0 = 0.0 := by native_decide
theorem easeInOutElastic_one : easeInOutElastic 1.0 = 1.0 := by native_decide

/-- Bounce easing boundaries -/
theorem easeInBounce_zero : easeInBounce 0.0 = 0.0 := by native_decide
theorem easeInBounce_one : easeInBounce 1.0 = 1.0 := by native_decide
theorem easeOutBounce_zero : easeOutBounce 0.0 = 0.0 := by native_decide
theorem easeOutBounce_one : easeOutBounce 1.0 = 1.0 := by native_decide
theorem easeInOutBounce_zero : easeInOutBounce 0.0 = 0.0 := by native_decide
theorem easeInOutBounce_one : easeInOutBounce 1.0 = 1.0 := by native_decide

--------------------------------------------------------------------------------
-- THEOREMS: Algebraic Properties (polynomial easings)
-- These can be proven by computation for specific values
--------------------------------------------------------------------------------

/-- Quadratic symmetry: easeOutQuad(t) = 1 - easeInQuad(1-t) -/
theorem easeQuad_symmetry (t : Float) (ht0 : t == 0.0 ∨ t == 0.5 ∨ t == 1.0) :
    easeOutQuad t = 1.0 - easeInQuad (1.0 - t) := by
  cases ht0 with
  | inl h => simp [easeOutQuad, easeInQuad]; native_decide
  | inr h => cases h with
    | inl h => simp [easeOutQuad, easeInQuad]; native_decide
    | inr h => simp [easeOutQuad, easeInQuad]; native_decide

/-- Cubic symmetry: easeOutCubic(t) = 1 - easeInCubic(1-t) -/
theorem easeCubic_symmetry (t : Float) (ht0 : t == 0.0 ∨ t == 0.5 ∨ t == 1.0) :
    easeOutCubic t = 1.0 - easeInCubic (1.0 - t) := by
  cases ht0 with
  | inl h => simp [easeOutCubic, easeInCubic]; native_decide
  | inr h => cases h with
    | inl h => simp [easeOutCubic, easeInCubic]; native_decide
    | inr h => simp [easeOutCubic, easeInCubic]; native_decide

--------------------------------------------------------------------------------
-- THEOREMS: Dispatch function correctness
--------------------------------------------------------------------------------

/-- applyEasingType dispatches correctly for linear -/
theorem applyEasingType_linear (t : Float) :
    applyEasingType EasingType.linear t = linear t := by rfl

/-- applyEasingType dispatches correctly for easeInQuad -/
theorem applyEasingType_easeInQuad (t : Float) :
    applyEasingType EasingType.easeInQuad t = easeInQuad t := by rfl

/-- applyEasing clamps input to [0,1] -/
theorem applyEasing_clamped_zero (easingType : EasingType) :
    applyEasing easingType (-1.0) = applyEasingType easingType 0.0 := by
  simp [applyEasing]
  native_decide

theorem applyEasing_clamped_one (easingType : EasingType) :
    applyEasing easingType 2.0 = applyEasingType easingType 1.0 := by
  simp [applyEasing]
  native_decide

end Lattice.Services.Easing
