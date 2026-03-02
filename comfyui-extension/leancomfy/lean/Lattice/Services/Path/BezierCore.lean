/-
  Lattice.Services.Path.BezierCore - Core Bezier Curve Math

  Pure mathematical functions for Bezier curve operations:
  - Point and vertex operations
  - Cubic Bezier evaluation
  - de Casteljau subdivision algorithm
  - Arc length estimation

  Source: ui/src/services/pathMorphing.ts
-/

namespace Lattice.Services.Path.BezierCore

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D point -/
structure Point2D where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

/-- Bezier vertex with point and control handles -/
structure BezierVertex where
  point : Point2D
  inHandle : Point2D   -- Relative to point
  outHandle : Point2D  -- Relative to point
  deriving Repr, Inhabited

/-- Bezier path (open or closed) -/
structure BezierPath where
  vertices : Array BezierVertex
  closed : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

/-- Create zero point -/
def Point2D.zero : Point2D := ⟨0.0, 0.0⟩

/-- Clone a point -/
def Point2D.clone (p : Point2D) : Point2D := ⟨p.x, p.y⟩

/-- Add two points -/
def Point2D.add (a b : Point2D) : Point2D :=
  ⟨a.x + b.x, a.y + b.y⟩

/-- Subtract two points -/
def Point2D.sub (a b : Point2D) : Point2D :=
  ⟨a.x - b.x, a.y - b.y⟩

/-- Scale a point -/
def Point2D.scale (p : Point2D) (s : Float) : Point2D :=
  ⟨p.x * s, p.y * s⟩

/-- Distance between two points -/
def Point2D.distance (a b : Point2D) : Float :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  Float.sqrt (dx * dx + dy * dy)

/-- Linear interpolation between two numbers -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Linear interpolation between two points -/
def Point2D.lerp (a b : Point2D) (t : Float) : Point2D :=
  ⟨lerp a.x b.x t, lerp a.y b.y t⟩

--------------------------------------------------------------------------------
-- Vertex Operations
--------------------------------------------------------------------------------

/-- Clone a vertex -/
def BezierVertex.clone (v : BezierVertex) : BezierVertex :=
  { point := v.point.clone
  , inHandle := v.inHandle.clone
  , outHandle := v.outHandle.clone }

/-- Get absolute position of in-handle -/
def BezierVertex.inHandleAbsolute (v : BezierVertex) : Point2D :=
  v.point.add v.inHandle

/-- Get absolute position of out-handle -/
def BezierVertex.outHandleAbsolute (v : BezierVertex) : Point2D :=
  v.point.add v.outHandle

/-- Interpolate between two vertices -/
def BezierVertex.lerp (a b : BezierVertex) (t : Float) : BezierVertex :=
  { point := Point2D.lerp a.point b.point t
  , inHandle := Point2D.lerp a.inHandle b.inHandle t
  , outHandle := Point2D.lerp a.outHandle b.outHandle t }

--------------------------------------------------------------------------------
-- Cubic Bezier Evaluation
--------------------------------------------------------------------------------

/-- Evaluate a cubic Bezier curve at parameter t.

    p0: Start point
    p1: First control point (absolute)
    p2: Second control point (absolute)
    p3: End point
    t: Parameter [0, 1]

    Uses the standard cubic Bezier formula:
    B(t) = (1-t)³P₀ + 3(1-t)²tP₁ + 3(1-t)t²P₂ + t³P₃ -/
def cubicBezierPoint (p0 p1 p2 p3 : Point2D) (t : Float) : Point2D :=
  let mt := 1.0 - t
  let mt2 := mt * mt
  let mt3 := mt2 * mt
  let t2 := t * t
  let t3 := t2 * t

  let x := mt3 * p0.x + 3.0 * mt2 * t * p1.x + 3.0 * mt * t2 * p2.x + t3 * p3.x
  let y := mt3 * p0.y + 3.0 * mt2 * t * p1.y + 3.0 * mt * t2 * p2.y + t3 * p3.y
  ⟨x, y⟩

/-- Cubic Bezier derivative at parameter t.

    Returns tangent vector (not normalized). -/
def cubicBezierDerivative (p0 p1 p2 p3 : Point2D) (t : Float) : Point2D :=
  let mt := 1.0 - t
  let mt2 := mt * mt
  let t2 := t * t

  -- B'(t) = 3(1-t)²(P₁-P₀) + 6(1-t)t(P₂-P₁) + 3t²(P₃-P₂)
  let d01 := p1.sub p0
  let d12 := p2.sub p1
  let d23 := p3.sub p2

  let x := 3.0 * mt2 * d01.x + 6.0 * mt * t * d12.x + 3.0 * t2 * d23.x
  let y := 3.0 * mt2 * d01.y + 6.0 * mt * t * d12.y + 3.0 * t2 * d23.y
  ⟨x, y⟩

--------------------------------------------------------------------------------
-- de Casteljau Subdivision
--------------------------------------------------------------------------------

/-- Segment of a cubic Bezier (4 control points) -/
structure BezierSegment where
  p0 : Point2D
  p1 : Point2D
  p2 : Point2D
  p3 : Point2D
  deriving Repr, Inhabited

/-- Split a cubic Bezier at parameter t using de Casteljau's algorithm.

    Returns (leftSegment, rightSegment) where:
    - leftSegment covers [0, t]
    - rightSegment covers [t, 1] -/
def splitCubicBezier (p0 p1 p2 p3 : Point2D) (t : Float) : BezierSegment × BezierSegment :=
  -- First level interpolation
  let q0 := Point2D.lerp p0 p1 t
  let q1 := Point2D.lerp p1 p2 t
  let q2 := Point2D.lerp p2 p3 t

  -- Second level interpolation
  let r0 := Point2D.lerp q0 q1 t
  let r1 := Point2D.lerp q1 q2 t

  -- Third level - the split point
  let s := Point2D.lerp r0 r1 t

  let left := { p0 := p0, p1 := q0, p2 := r0, p3 := s }
  let right := { p0 := s, p1 := r1, p2 := q2, p3 := p3 }
  (left, right)

--------------------------------------------------------------------------------
-- Arc Length Estimation
--------------------------------------------------------------------------------

/-- Estimate arc length of a cubic Bezier segment using chord approximation.

    Samples the curve at regular intervals and sums the chord lengths.
    More samples = more accurate but slower. -/
def estimateSegmentLength (p0 p1 p2 p3 : Point2D) (samples : Nat := 10) : Float :=
  if samples == 0 then 0.0
  else
    let rec go (i : Nat) (prev : Point2D) (acc : Float) : Float :=
      if i > samples then acc
      else
        let t := i.toFloat / samples.toFloat
        let curr := cubicBezierPoint p0 p1 p2 p3 t
        let dist := Point2D.distance prev curr
        go (i + 1) curr (acc + dist)
    go 1 p0 0.0

/-- Get segment control points from a path.

    segmentIndex: Index of the segment (0 to n-1 for closed, 0 to n-2 for open)
    Returns (p0, p1, p2, p3) as absolute coordinates. -/
def getSegmentControlPoints (path : BezierPath) (segmentIndex : Nat)
    : Option (Point2D × Point2D × Point2D × Point2D) :=
  if path.vertices.size == 0 then none
  else
    let n := path.vertices.size
    if segmentIndex >= n then none
    else
      let v0 := path.vertices[segmentIndex]!
      let nextIdx := (segmentIndex + 1) % n
      let v1 := path.vertices[nextIdx]!

      let p0 := v0.point
      let p1 := v0.outHandleAbsolute
      let p2 := v1.inHandleAbsolute
      let p3 := v1.point

      some (p0, p1, p2, p3)

/-- Calculate total arc length of a path. -/
def getPathLength (path : BezierPath) (samplesPerSegment : Nat := 10) : Float :=
  if path.vertices.size == 0 then 0.0
  else
    let numSegments := if path.closed then path.vertices.size else path.vertices.size - 1
    let rec go (i : Nat) (acc : Float) : Float :=
      if i >= numSegments then acc
      else
        match getSegmentControlPoints path i with
        | some (p0, p1, p2, p3) =>
          let len := estimateSegmentLength p0 p1 p2 p3 samplesPerSegment
          go (i + 1) (acc + len)
        | none => acc
    go 0 0.0

/-- Calculate arc lengths of each segment. -/
def getSegmentLengths (path : BezierPath) (samplesPerSegment : Nat := 10) : Array Float :=
  if path.vertices.size == 0 then #[]
  else
    let numSegments := if path.closed then path.vertices.size else path.vertices.size - 1
    let rec go (i : Nat) (acc : Array Float) : Array Float :=
      if i >= numSegments then acc
      else
        match getSegmentControlPoints path i with
        | some (p0, p1, p2, p3) =>
          let len := estimateSegmentLength p0 p1 p2 p3 samplesPerSegment
          go (i + 1) (acc.push len)
        | none => go (i + 1) acc
    go 0 #[]

end Lattice.Services.Path.BezierCore
