/-
  Lattice.Services.Effects.ColorCurves - Curve-based Color Adjustments

  Pure mathematical functions for curve-based color adjustments:
  - Cubic Bezier curve interpolation
  - Curve LUT (lookup table) generation
  - S-curve and lift curve presets

  All functions operate on normalized [0,1] color values.
  All functions are total and deterministic.
  NO banned constructs: no partial def, sorry, panic!, unreachable!

  Source: ui/src/services/effects/colorRenderer.ts
-/

import Lattice.Services.Effects.ColorCorrection

namespace Lattice.Services.Effects.ColorCurves

open ColorCorrection (RGB clamp01)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- A point on a curve with input/output values -/
structure CurvePoint where
  input : Float   -- Input value [0,1]
  output : Float  -- Output value [0,1]
  deriving Repr, Inhabited

/-- Curve parameters for each channel -/
structure CurveParams where
  master : Array CurvePoint  -- Master curve (affects all channels)
  red : Array CurvePoint     -- Red channel curve
  green : Array CurvePoint   -- Green channel curve
  blue : Array CurvePoint    -- Blue channel curve
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Default Values
--------------------------------------------------------------------------------

/-- Identity curve (no change) -/
def identityCurve : Array CurvePoint :=
  #[{ input := 0.0, output := 0.0 }, { input := 1.0, output := 1.0 }]

/-- Default curves (identity on all channels) -/
def defaultCurveParams : CurveParams :=
  { master := identityCurve
    red := identityCurve
    green := identityCurve
    blue := identityCurve }

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Safe array access with default -/
def safeGet (arr : Array α) (i : Nat) (default : α) : α :=
  arr.get? i |>.getD default

/-- Safe power function -/
def safePow (base exp : Float) : Float :=
  let result := Float.pow base exp
  if result.isNaN || result.isInf then 1.0
  else result

/-- Absolute value -/
def fabs (x : Float) : Float :=
  if x < 0.0 then -x else x

--------------------------------------------------------------------------------
-- Cubic Bezier
--------------------------------------------------------------------------------

/-- Cubic Bezier interpolation for curve segment -/
def cubicBezier (t p0 p1 p2 p3 : Float) : Float :=
  let t' := clamp01 t
  let mt := 1.0 - t'
  let mt2 := mt * mt
  let mt3 := mt2 * mt
  let t2 := t' * t'
  let t3 := t2 * t'
  -- mt³*p0 + 3*mt²*t*p1 + 3*mt*t²*p2 + t³*p3
  let term0 := mt3 * p0
  let term1 := 3.0 * mt2 * t' * p1
  let term2 := 3.0 * mt * t2 * p2
  let term3 := t3 * p3
  term0 + term1 + term2 + term3

/-- Find curve segment containing input value (returns index of first point) -/
def findSegmentIndex (points : Array CurvePoint) (x : Float) : Nat :=
  if points.size < 2 then 0
  else
    let rec go (i : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => i
      | fuel' + 1 =>
        if i >= points.size - 1 then i - 1
        else
          let p2 := safeGet points (i + 1) { input := 1.0, output := 1.0 }
          if x <= p2.input then i
          else go (i + 1) fuel'
    go 0 points.size

/-- Interpolate on curve at given input -/
def interpolateCurve (points : Array CurvePoint) (x : Float) : Float :=
  if points.size < 2 then x
  else
    let idx := findSegmentIndex points x
    let defaultP1 : CurvePoint := { input := 0.0, output := 0.0 }
    let defaultP2 : CurvePoint := { input := 1.0, output := 1.0 }
    let p1 := safeGet points idx defaultP1
    let p2 := safeGet points (idx + 1) defaultP2
    let inRange := p2.input - p1.input
    let t := if inRange > 0.0001 then (x - p1.input) / inRange else 0.0
    -- Control points at 1/3 and 2/3 of segment
    let delta := p2.output - p1.output
    let cp1 := p1.output + delta / 3.0
    let cp2 := p2.output - delta / 3.0
    cubicBezier t p1.output cp1 cp2 p2.output

--------------------------------------------------------------------------------
-- Lookup Table Generation
--------------------------------------------------------------------------------

/-- Build 256-entry lookup table from curve points -/
def buildCurveLUT (points : Array CurvePoint) : Array UInt8 :=
  Array.ofFn fun i : Fin 256 =>
    let normalized := Float.ofNat i.val / 255.0
    let result := interpolateCurve points normalized
    let scaled := result * 255.0
    let clamped := if scaled < 0.0 then 0.0
                   else if scaled > 255.0 then 255.0
                   else scaled
    clamped.toUInt8

/-- Apply curve using LUT (safe indexing) -/
def applyCurveLUT (lut : Array UInt8) (value : Float) : Float :=
  let idx := (clamp01 value * 255.0).toUInt64.toNat
  let safeIdx := min 255 idx
  match lut.get? safeIdx with
  | some v => Float.ofNat v.toNat / 255.0
  | none => value  -- Fallback

/-- Apply curves to RGB -/
def applyCurves (params : CurveParams) (color : RGB) : RGB :=
  let masterLUT := buildCurveLUT params.master
  let redLUT := buildCurveLUT params.red
  let greenLUT := buildCurveLUT params.green
  let blueLUT := buildCurveLUT params.blue
  let r' := applyCurveLUT redLUT (applyCurveLUT masterLUT color.r)
  let g' := applyCurveLUT greenLUT (applyCurveLUT masterLUT color.g)
  let b' := applyCurveLUT blueLUT (applyCurveLUT masterLUT color.b)
  { r := clamp01 r', g := clamp01 g', b := clamp01 b' }

--------------------------------------------------------------------------------
-- Curve Presets
--------------------------------------------------------------------------------

/-- Create S-curve for contrast enhancement -/
def createSCurve (amount : Float) : Array CurvePoint :=
  let amt := clamp01 (fabs amount) * 0.25
  let sign := if amount < 0.0 then -1.0 else 1.0
  let shadow := 0.25 - sign * amt
  let highlight := 0.75 + sign * amt
  #[ { input := 0.0, output := 0.0 }
   , { input := 0.25, output := shadow }
   , { input := 0.75, output := highlight }
   , { input := 1.0, output := 1.0 }
   ]

/-- Create lift curve (raise shadows) -/
def createLiftCurve (lift gamma : Float) : Array CurvePoint :=
  let liftAmt := clamp01 lift
  let gammaAmt := if gamma < 0.1 then 0.1 else if gamma > 10.0 then 10.0 else gamma
  let midIn := 0.5
  let invGamma := 1.0 / gammaAmt
  let midOut := safePow midIn invGamma
  #[ { input := 0.0, output := liftAmt }
   , { input := midIn, output := midOut }
   , { input := 1.0, output := 1.0 }
   ]

/-- Create gamma curve -/
def createGammaCurve (gamma : Float) : Array CurvePoint :=
  let gammaAmt := if gamma < 0.1 then 0.1 else if gamma > 10.0 then 10.0 else gamma
  let invGamma := 1.0 / gammaAmt
  let mkPoint (x : Float) : CurvePoint := { input := x, output := safePow x invGamma }
  #[ mkPoint 0.0, mkPoint 0.25, mkPoint 0.5, mkPoint 0.75, mkPoint 1.0 ]

--------------------------------------------------------------------------------
-- Proofs (Structural - No sorry, No native_decide)
--------------------------------------------------------------------------------

/-- Identity curve has exactly 2 points -/
theorem identityCurve_size : identityCurve.size = 2 := by
  simp only [identityCurve, Array.size_mk, List.length_cons, List.length_nil]

/-- Default curves use identity for master -/
theorem defaultCurveParams_identity_master :
    defaultCurveParams.master = identityCurve := by
  rfl

/-- S-curve has exactly 4 points -/
theorem createSCurve_size (amount : Float) : (createSCurve amount).size = 4 := by
  simp only [createSCurve, Array.size_mk, List.length_cons, List.length_nil]

/-- Lift curve has exactly 3 points -/
theorem createLiftCurve_size (lift gamma : Float) : (createLiftCurve lift gamma).size = 3 := by
  simp only [createLiftCurve, Array.size_mk, List.length_cons, List.length_nil]

/-- Gamma curve has exactly 5 points -/
theorem createGammaCurve_size (gamma : Float) : (createGammaCurve gamma).size = 5 := by
  simp only [createGammaCurve, Array.size_mk, List.length_cons, List.length_nil]

/-- Curve LUT has exactly 256 entries -/
theorem buildCurveLUT_size (points : Array CurvePoint) : (buildCurveLUT points).size = 256 := by
  simp only [buildCurveLUT, Array.size_ofFn]

/-- applyCurves preserves structure -/
theorem applyCurves_preserves_structure (params : CurveParams) (color : RGB) :
    ∃ r g b, applyCurves params color = { r := r, g := g, b := b } := by
  exact ⟨_, _, _, rfl⟩

/-- cubicBezier is well-defined for any inputs -/
theorem cubicBezier_defined (t p0 p1 p2 p3 : Float) :
    ∃ result, cubicBezier t p0 p1 p2 p3 = result := by
  exact ⟨_, rfl⟩

/-- findSegmentIndex returns 0 for empty or single-point curves -/
theorem findSegmentIndex_small_curves (points : Array CurvePoint) (x : Float)
    (h : points.size < 2) : findSegmentIndex points x = 0 := by
  simp only [findSegmentIndex]
  split_ifs with h'
  · rfl
  · exact absurd h h'

/-- interpolateCurve returns x for small curves -/
theorem interpolateCurve_small (points : Array CurvePoint) (x : Float)
    (h : points.size < 2) : interpolateCurve points x = x := by
  simp only [interpolateCurve]
  split_ifs with h'
  · rfl
  · exact absurd h h'

end Lattice.Services.Effects.ColorCurves
