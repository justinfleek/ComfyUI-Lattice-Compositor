/-
  Lattice.Services.ShapeOperations.Bezier - Cubic Bezier Curve Operations

  Pure cubic Bezier curve math:
  - Point evaluation at parameter t
  - Derivative (tangent) evaluation
  - De Casteljau subdivision
  - Arc length approximation
  - Bounding box calculation

  Source: ui/src/services/shapeOperations.ts (bezier utilities)
-/

import Lattice.Services.ShapeOperations.Point2D

namespace Lattice.Services.ShapeOperations.Bezier

open Lattice.Services.ShapeOperations.Point2D

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- A cubic Bezier curve defined by 4 control points:
    p0 = start point
    p1 = start control (absolute position)
    p2 = end control (absolute position)
    p3 = end point -/
structure CubicBezier where
  p0 : Point2D
  p1 : Point2D
  p2 : Point2D
  p3 : Point2D
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Point Evaluation
--------------------------------------------------------------------------------

/-- Evaluate cubic Bezier at parameter t ∈ [0, 1].

    Uses the explicit form:
    B(t) = (1-t)³·P₀ + 3(1-t)²t·P₁ + 3(1-t)t²·P₂ + t³·P₃ -/
def evalPoint (curve : CubicBezier) (t : Float) : Point2D :=
  let mt := 1 - t
  let mt2 := mt * mt
  let mt3 := mt2 * mt
  let t2 := t * t
  let t3 := t2 * t

  let x := mt3 * curve.p0.x + 3 * mt2 * t * curve.p1.x +
           3 * mt * t2 * curve.p2.x + t3 * curve.p3.x
  let y := mt3 * curve.p0.y + 3 * mt2 * t * curve.p1.y +
           3 * mt * t2 * curve.p2.y + t3 * curve.p3.y
  ⟨x, y⟩

/-- Evaluate cubic Bezier at t using 4 separate points -/
def cubicBezierPoint (p0 p1 p2 p3 : Point2D) (t : Float) : Point2D :=
  evalPoint ⟨p0, p1, p2, p3⟩ t

--------------------------------------------------------------------------------
-- Derivative (Tangent)
--------------------------------------------------------------------------------

/-- Evaluate first derivative (tangent) of cubic Bezier at t.

    B'(t) = 3(1-t)²(P₁-P₀) + 6(1-t)t(P₂-P₁) + 3t²(P₃-P₂) -/
def evalDerivative (curve : CubicBezier) (t : Float) : Point2D :=
  let mt := 1 - t
  let mt2 := mt * mt
  let t2 := t * t

  let dx := 3 * mt2 * (curve.p1.x - curve.p0.x) +
            6 * mt * t * (curve.p2.x - curve.p1.x) +
            3 * t2 * (curve.p3.x - curve.p2.x)
  let dy := 3 * mt2 * (curve.p1.y - curve.p0.y) +
            6 * mt * t * (curve.p2.y - curve.p1.y) +
            3 * t2 * (curve.p3.y - curve.p2.y)
  ⟨dx, dy⟩

/-- Get normalized tangent at t -/
def evalTangent (curve : CubicBezier) (t : Float) : Point2D :=
  normalize (evalDerivative curve t)

/-- Get normal (perpendicular to tangent) at t -/
def evalNormal (curve : CubicBezier) (t : Float) : Point2D :=
  perpendicular (evalTangent curve t)

--------------------------------------------------------------------------------
-- De Casteljau Subdivision
--------------------------------------------------------------------------------

/-- Split a cubic Bezier at t using de Casteljau's algorithm.

    Returns (leftCurve, rightCurve) where:
    - leftCurve covers [0, t]
    - rightCurve covers [t, 1] -/
def split (curve : CubicBezier) (t : Float) : CubicBezier × CubicBezier :=
  -- First level
  let q0 := lerp curve.p0 curve.p1 t
  let q1 := lerp curve.p1 curve.p2 t
  let q2 := lerp curve.p2 curve.p3 t

  -- Second level
  let r0 := lerp q0 q1 t
  let r1 := lerp q1 q2 t

  -- Split point
  let s := lerp r0 r1 t

  let left := CubicBezier.mk curve.p0 q0 r0 s
  let right := CubicBezier.mk s r1 q2 curve.p3

  (left, right)

/-- Split using 4 separate points, return as arrays of 4 points each -/
def splitCubicBezier (p0 p1 p2 p3 : Point2D) (t : Float)
    : (Array Point2D) × (Array Point2D) :=
  let (left, right) := split ⟨p0, p1, p2, p3⟩ t
  (#[left.p0, left.p1, left.p2, left.p3],
   #[right.p0, right.p1, right.p2, right.p3])

--------------------------------------------------------------------------------
-- Arc Length
--------------------------------------------------------------------------------

/-- Approximate arc length using subdivision (Gaussian quadrature approximation).

    subdivisions: number of linear segments to use -/
def arcLength (curve : CubicBezier) (subdivisions : Nat := 32) : Float :=
  let rec accumulate (i : Nat) (prev : Point2D) (len : Float) : Float :=
    if i > subdivisions then len
    else
      let t := i.toFloat / subdivisions.toFloat
      let curr := evalPoint curve t
      let segLen := distance prev curr
      accumulate (i + 1) curr (len + segLen)
  accumulate 1 (evalPoint curve 0) 0

/-- Arc length using 4 separate points -/
def cubicBezierLength (p0 p1 p2 p3 : Point2D) (subdivisions : Nat := 32) : Float :=
  arcLength ⟨p0, p1, p2, p3⟩ subdivisions

--------------------------------------------------------------------------------
-- Point at Arc Length
--------------------------------------------------------------------------------

/-- Find parameter t corresponding to a given arc length distance.

    Uses binary search to find t where arcLength(0, t) ≈ targetDistance.
    tolerance: convergence tolerance -/
def parameterAtArcLength (curve : CubicBezier) (targetDistance : Float)
    (totalLength : Float := 0) (tolerance : Float := 0.001) : Float :=
  let total := if totalLength > 0 then totalLength else arcLength curve
  if total < tolerance then 0
  else if targetDistance <= 0 then 0
  else if targetDistance >= total then 1
  else
    -- Binary search for t
    let rec search (lo hi : Float) (fuel : Nat) : Float :=
      match fuel with
      | 0 => (lo + hi) / 2
      | n + 1 =>
        if hi - lo < tolerance then (lo + hi) / 2
        else
          let mid := (lo + hi) / 2
          let (left, _) := split curve mid
          let leftLen := arcLength left 16  -- Coarse approximation
          if leftLen < targetDistance then
            search mid hi n
          else
            search lo mid n
    search 0 1 50

--------------------------------------------------------------------------------
-- Bounding Box
--------------------------------------------------------------------------------

/-- Axis-aligned bounding box -/
structure BoundingBox where
  minX : Float
  minY : Float
  maxX : Float
  maxY : Float
  deriving Repr, Inhabited

/-- Calculate tight bounding box of cubic Bezier.

    Finds extrema by solving B'(t) = 0 for x and y components. -/
def boundingBox (curve : CubicBezier) : BoundingBox :=
  -- Start with endpoints
  let minX := Float.min curve.p0.x curve.p3.x
  let maxX := Float.max curve.p0.x curve.p3.x
  let minY := Float.min curve.p0.y curve.p3.y
  let maxY := Float.max curve.p0.y curve.p3.y

  -- Solve for extrema: coefficients of B'(t) = at² + bt + c
  -- For x: ax = 3(-p0 + 3p1 - 3p2 + p3), bx = 6(p0 - 2p1 + p2), cx = 3(p1 - p0)
  let ax := 3 * (-curve.p0.x + 3 * curve.p1.x - 3 * curve.p2.x + curve.p3.x)
  let bx := 6 * (curve.p0.x - 2 * curve.p1.x + curve.p2.x)
  let cx := 3 * (curve.p1.x - curve.p0.x)

  let ay := 3 * (-curve.p0.y + 3 * curve.p1.y - 3 * curve.p2.y + curve.p3.y)
  let by := 6 * (curve.p0.y - 2 * curve.p1.y + curve.p2.y)
  let cy := 3 * (curve.p1.y - curve.p0.y)

  -- Helper to find roots of quadratic at² + bt + c = 0 in (0, 1)
  let solveQuadratic (a b c : Float) : Array Float :=
    if Float.abs a < 0.0001 then
      -- Linear: bt + c = 0
      if Float.abs b < 0.0001 then #[]
      else
        let t := -c / b
        if t > 0 && t < 1 then #[t] else #[]
    else
      let disc := b * b - 4 * a * c
      if disc < 0 then #[]
      else
        let sqrtDisc := Float.sqrt disc
        let t1 := (-b + sqrtDisc) / (2 * a)
        let t2 := (-b - sqrtDisc) / (2 * a)
        let roots := #[]
        let roots := if t1 > 0 && t1 < 1 then roots.push t1 else roots
        let roots := if t2 > 0 && t2 < 1 && t2 != t1 then roots.push t2 else roots
        roots

  -- Find extrema for x
  let xRoots := solveQuadratic ax bx cx
  let (minX, maxX) := xRoots.foldl (fun (mn, mx) t =>
    let pt := evalPoint curve t
    (Float.min mn pt.x, Float.max mx pt.x)) (minX, maxX)

  -- Find extrema for y
  let yRoots := solveQuadratic ay by cy
  let (minY, maxY) := yRoots.foldl (fun (mn, mx) t =>
    let pt := evalPoint curve t
    (Float.min mn pt.y, Float.max mx pt.y)) (minY, maxY)

  ⟨minX, minY, maxX, maxY⟩

--------------------------------------------------------------------------------
-- Flatten to Polyline
--------------------------------------------------------------------------------

/-- Convert Bezier curve to polyline with specified number of segments -/
def flatten (curve : CubicBezier) (segments : Nat := 16) : Array Point2D :=
  let n := max 2 segments
  Array.range (n + 1) |>.map fun i =>
    let t := i.toFloat / n.toFloat
    evalPoint curve t

--------------------------------------------------------------------------------
-- Curvature
--------------------------------------------------------------------------------

/-- Calculate curvature at parameter t.

    κ = |B'(t) × B''(t)| / |B'(t)|³

    Returns 0 if velocity is near zero. -/
def curvature (curve : CubicBezier) (t : Float) : Float :=
  let d1 := evalDerivative curve t
  let speed := length d1
  if speed < 0.0001 then 0
  else
    -- Second derivative: B''(t) = 6(1-t)(P2 - 2P1 + P0) + 6t(P3 - 2P2 + P1)
    let mt := 1 - t
    let d2x := 6 * mt * (curve.p2.x - 2 * curve.p1.x + curve.p0.x) +
               6 * t * (curve.p3.x - 2 * curve.p2.x + curve.p1.x)
    let d2y := 6 * mt * (curve.p2.y - 2 * curve.p1.y + curve.p0.y) +
               6 * t * (curve.p3.y - 2 * curve.p2.y + curve.p1.y)

    -- Cross product magnitude
    let crossMag := Float.abs (d1.x * d2y - d1.y * d2x)

    crossMag / (speed * speed * speed)

end Lattice.Services.ShapeOperations.Bezier
