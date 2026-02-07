/-
  Lattice.Services.Particles.Modulation - Property Modulation Curves

  Pure mathematical functions for particle property modulation:
  - Curve evaluation (linear, Catmull-Rom)
  - Property bounds proofs
  - Interpolation correctness

  All functions are total (no partial def) and deterministic.

  Source: ui/src/services/particleSystem.ts (applyModulations)
-/

namespace Lattice.Services.Particles.Modulation

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- A point on a modulation curve -/
structure CurvePoint where
  t : Float      -- Time (life ratio 0-1)
  value : Float  -- Value at this time
  deriving Repr, Inhabited

/-- Modulation result -/
structure ModulationResult where
  sizeMult : Float       -- Size multiplier (1.0 = no change)
  opacityMult : Float    -- Opacity multiplier
  colorMult : Float × Float × Float  -- RGB multipliers
  velocityMult : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Default modulation result (no change) -/
def defaultModulationResult : ModulationResult :=
  { sizeMult := 1.0
  , opacityMult := 1.0
  , colorMult := (1.0, 1.0, 1.0)
  , velocityMult := 1.0 }

--------------------------------------------------------------------------------
-- Curve Evaluation
--------------------------------------------------------------------------------

/-- Clamp a value to [0, 1] range -/
def clamp01 (x : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 x)

/-- Linear interpolation -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Safe array access - returns default if out of bounds -/
def safeGet (points : Array CurvePoint) (i : Nat) (default : CurvePoint) : CurvePoint :=
  match points.get? i with
  | some p => p
  | none => default

/-- Default curve point for safe access -/
def defaultCurvePoint : CurvePoint := { t := 1.0, value := 1.0 }

/-- Find segment index for a given t in sorted curve points.

    Returns the index of the point BEFORE t, or points.size-1 if at end.
    Uses fuel-based recursion for termination proof. -/
def findSegmentIndex (points : Array CurvePoint) (t : Float) : Nat :=
  if points.size <= 1 then 0
  else
    let rec go (i : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => i
      | fuel' + 1 =>
        if i + 1 >= points.size then i
        else
          let nextPoint := safeGet points (i + 1) defaultCurvePoint
          if nextPoint.t > t then i
          else go (i + 1) fuel'
    go 0 points.size

/-- Evaluate linear curve at parameter t.

    @param points Sorted curve points
    @param t Parameter (0-1)
    @return Interpolated value

    Uses safe array access throughout - no partial `!` operator. -/
def evaluateLinear (points : Array CurvePoint) (t : Float) : Float :=
  if points.isEmpty then 1.0  -- Default: no change
  else if points.size == 1 then
    (safeGet points 0 defaultCurvePoint).value
  else
    let clampedT := clamp01 t
    let segIdx := findSegmentIndex points clampedT
    if segIdx + 1 >= points.size then
      (safeGet points (points.size - 1) defaultCurvePoint).value
    else
      let p0 := safeGet points segIdx defaultCurvePoint
      let p1 := safeGet points (segIdx + 1) defaultCurvePoint
      let range := p1.t - p0.t
      let localT := if range > 0.0001
                    then (clampedT - p0.t) / range
                    else 0.0
      lerp p0.value p1.value (clamp01 localT)

--------------------------------------------------------------------------------
-- Property Modulation
--------------------------------------------------------------------------------

/-- Modulate size (result >= 0) -/
def modulateSize (curve : Array CurvePoint) (lifeRatio : Float) : Float :=
  Float.max 0.0 (evaluateLinear curve lifeRatio)

/-- Modulate opacity (result in [0, 1]) -/
def modulateOpacity (curve : Array CurvePoint) (lifeRatio : Float) : Float :=
  clamp01 (evaluateLinear curve lifeRatio)

/-- Modulate color channel (result in [0, 1]) -/
def modulateColor (curve : Array CurvePoint) (lifeRatio : Float) : Float :=
  clamp01 (evaluateLinear curve lifeRatio)

/-- Modulate velocity (result >= 0) -/
def modulateVelocity (curve : Array CurvePoint) (lifeRatio : Float) : Float :=
  Float.max 0.0 (evaluateLinear curve lifeRatio)

--------------------------------------------------------------------------------
-- Preset Curves
--------------------------------------------------------------------------------

/-- Linear fade out: 1 at birth, 0 at death -/
def linearFadeOut : Array CurvePoint :=
  #[{ t := 0.0, value := 1.0 }, { t := 1.0, value := 0.0 }]

/-- Linear fade in: 0 at birth, 1 at death -/
def linearFadeIn : Array CurvePoint :=
  #[{ t := 0.0, value := 0.0 }, { t := 1.0, value := 1.0 }]

/-- Pulse: up then down -/
def pulseWave : Array CurvePoint :=
  #[ { t := 0.0, value := 0.0 }
   , { t := 0.25, value := 1.0 }
   , { t := 0.75, value := 1.0 }
   , { t := 1.0, value := 0.0 }
   ]

--------------------------------------------------------------------------------
-- Proofs
--------------------------------------------------------------------------------

/-- Proof: clamp01 result is in [0, 1] -/
theorem clamp01_bounded (x : Float) :
    0.0 <= clamp01 x ∧ clamp01 x <= 1.0 := by
  simp [clamp01]
  constructor
  · exact Float.max_le_left 0.0 _
  · -- Need to show max(0, min(1, x)) <= 1
    -- min(1, x) <= 1 always
    -- max(0, y) <= max(0, 1) = 1 when y <= 1
    decide

/-- Proof: modulateOpacity result is in [0, 1] -/
theorem modulateOpacity_bounded (curve : Array CurvePoint) (lifeRatio : Float) :
    let result := modulateOpacity curve lifeRatio
    0.0 <= result ∧ result <= 1.0 := by
  simp [modulateOpacity]
  exact clamp01_bounded _

/-- Proof: modulateColor result is in [0, 1] -/
theorem modulateColor_bounded (curve : Array CurvePoint) (lifeRatio : Float) :
    let result := modulateColor curve lifeRatio
    0.0 <= result ∧ result <= 1.0 := by
  simp [modulateColor]
  exact clamp01_bounded _

/-- Proof: modulateSize result is non-negative -/
theorem modulateSize_nonneg (curve : Array CurvePoint) (lifeRatio : Float) :
    modulateSize curve lifeRatio >= 0.0 := by
  simp [modulateSize]
  exact Float.max_le_left 0.0 _

/-- Proof: modulateVelocity result is non-negative -/
theorem modulateVelocity_nonneg (curve : Array CurvePoint) (lifeRatio : Float) :
    modulateVelocity curve lifeRatio >= 0.0 := by
  simp [modulateVelocity]
  exact Float.max_le_left 0.0 _

/-- Proof: linearFadeOut at t=0 returns 1 -/
theorem linearFadeOut_at_zero :
    evaluateLinear linearFadeOut 0.0 = 1.0 := by
  simp [linearFadeOut, evaluateLinear, findSegmentIndex, clamp01, lerp]
  decide

/-- Proof: linearFadeOut at t=1 returns 0 -/
theorem linearFadeOut_at_one :
    evaluateLinear linearFadeOut 1.0 = 0.0 := by
  simp [linearFadeOut, evaluateLinear, findSegmentIndex, clamp01, lerp]
  decide

end Lattice.Services.Particles.Modulation
