/-
  Lattice.Services.ShapeOperations.Generators - Shape Generation

  Pure shape generation algorithms:
  - Rectangle (with optional roundness)
  - Ellipse (circular Bezier approximation)
  - Regular polygon (n-gon)
  - Star (n-pointed with inner/outer radii)

  Source: ui/src/services/shapeOperations.ts (shape generators)
-/

import Lattice.Services.ShapeOperations.Point2D

namespace Lattice.Services.ShapeOperations.Generators

open Lattice.Services.ShapeOperations.Point2D

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Direction for shape winding (clockwise or counter-clockwise) -/
inductive WindingDirection
  | clockwise
  | counterClockwise
  deriving Repr, Inhabited, BEq

/-- A Bezier vertex with point and control handles -/
structure BezierVertex where
  point : Point2D
  inHandle : Point2D   -- Relative to point
  outHandle : Point2D  -- Relative to point
  deriving Repr, Inhabited

/-- A Bezier path is a list of vertices with closed flag -/
structure BezierPath where
  vertices : Array BezierVertex
  closed : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Magic number for circular Bezier approximation.
    Derived from: 4/3 * tan(π/8) ≈ 0.5522847498 -/
def kappa : Float := 0.5522847498

/-- Convert degrees to radians -/
def degToRad (deg : Float) : Float := deg * Float.pi / 180

--------------------------------------------------------------------------------
-- Vertex Helpers
--------------------------------------------------------------------------------

/-- Create a corner vertex (no handles) -/
def cornerVertex (p : Point2D) : BezierVertex :=
  ⟨p, origin, origin⟩

/-- Create a smooth vertex with symmetric handles -/
def smoothVertex (p : Point2D) (handleDir : Point2D) (handleLen : Float) : BezierVertex :=
  let h := scale (normalize handleDir) handleLen
  ⟨p, neg h, h⟩

/-- Clone a vertex -/
def cloneVertex (v : BezierVertex) : BezierVertex :=
  ⟨clone v.point, clone v.inHandle, clone v.outHandle⟩

/-- Clone a path -/
def clonePath (p : BezierPath) : BezierPath :=
  ⟨p.vertices.map cloneVertex, p.closed⟩

--------------------------------------------------------------------------------
-- Rectangle
--------------------------------------------------------------------------------

/-- Generate a rectangle path.

    position: center of rectangle
    size: width and height
    roundness: corner radius (0 for sharp corners)
    direction: winding direction -/
def generateRectangle (position : Point2D) (size : Point2D)
    (roundness : Float := 0) (direction : WindingDirection := .clockwise) : BezierPath :=
  let hw := size.x / 2
  let hh := size.y / 2
  let r := Float.min roundness (Float.min hw hh)

  -- Corner positions (clockwise from top-left)
  let tl : Point2D := ⟨position.x - hw, position.y - hh⟩
  let tr : Point2D := ⟨position.x + hw, position.y - hh⟩
  let br : Point2D := ⟨position.x + hw, position.y + hh⟩
  let bl : Point2D := ⟨position.x - hw, position.y + hh⟩

  let corners := match direction with
    | .clockwise => #[tl, tr, br, bl]
    | .counterClockwise => #[tl, bl, br, tr]

  if r < 0.01 then
    -- Sharp corners
    let vertices := corners.map cornerVertex
    ⟨vertices, true⟩
  else
    -- Rounded corners
    let k := kappa * r
    let vertices : Array BezierVertex := #[]

    -- Generate 8 vertices (2 per corner for rounded)
    let mkRoundedCorner (corner : Point2D) (prevDir nextDir : Point2D) : Array BezierVertex :=
      let startPt := add corner (scale (normalize prevDir) r)
      let endPt := add corner (scale (normalize nextDir) r)
      #[
        ⟨startPt, scale (normalize prevDir) (-k), origin⟩,
        ⟨endPt, origin, scale (normalize nextDir) (-k)⟩
      ]

    match direction with
    | .clockwise =>
      let v0 := mkRoundedCorner tl ⟨0, 1⟩ ⟨1, 0⟩   -- TL: from bottom, to right
      let v1 := mkRoundedCorner tr ⟨-1, 0⟩ ⟨0, 1⟩  -- TR: from left, to bottom
      let v2 := mkRoundedCorner br ⟨0, -1⟩ ⟨-1, 0⟩ -- BR: from top, to left
      let v3 := mkRoundedCorner bl ⟨1, 0⟩ ⟨0, -1⟩  -- BL: from right, to top
      ⟨v0 ++ v1 ++ v2 ++ v3, true⟩
    | .counterClockwise =>
      let v0 := mkRoundedCorner tl ⟨1, 0⟩ ⟨0, 1⟩   -- TL: from right, to bottom
      let v1 := mkRoundedCorner bl ⟨0, -1⟩ ⟨1, 0⟩  -- BL: from top, to right
      let v2 := mkRoundedCorner br ⟨-1, 0⟩ ⟨0, -1⟩ -- BR: from left, to top
      let v3 := mkRoundedCorner tr ⟨0, 1⟩ ⟨-1, 0⟩  -- TR: from bottom, to left
      ⟨v0 ++ v1 ++ v2 ++ v3, true⟩

--------------------------------------------------------------------------------
-- Ellipse
--------------------------------------------------------------------------------

/-- Generate an ellipse path using 4-point Bezier approximation.

    position: center of ellipse
    size: width and height (diameter, not radius)
    direction: winding direction -/
def generateEllipse (position : Point2D) (size : Point2D)
    (direction : WindingDirection := .clockwise) : BezierPath :=
  let rx := size.x / 2
  let ry := size.y / 2
  let kx := rx * kappa
  let ky := ry * kappa

  -- 4 cardinal points with circular handles
  let top : BezierVertex := ⟨
    ⟨position.x, position.y - ry⟩,
    ⟨-kx, 0⟩,
    ⟨kx, 0⟩
  ⟩
  let right : BezierVertex := ⟨
    ⟨position.x + rx, position.y⟩,
    ⟨0, -ky⟩,
    ⟨0, ky⟩
  ⟩
  let bottom : BezierVertex := ⟨
    ⟨position.x, position.y + ry⟩,
    ⟨kx, 0⟩,
    ⟨-kx, 0⟩
  ⟩
  let left : BezierVertex := ⟨
    ⟨position.x - rx, position.y⟩,
    ⟨0, ky⟩,
    ⟨0, -ky⟩
  ⟩

  let vertices := match direction with
    | .clockwise => #[top, right, bottom, left]
    | .counterClockwise =>
      -- Reverse order and swap handles
      #[
        ⟨top.point, top.outHandle, top.inHandle⟩,
        ⟨left.point, left.outHandle, left.inHandle⟩,
        ⟨bottom.point, bottom.outHandle, bottom.inHandle⟩,
        ⟨right.point, right.outHandle, right.inHandle⟩
      ]

  ⟨vertices, true⟩

--------------------------------------------------------------------------------
-- Regular Polygon
--------------------------------------------------------------------------------

/-- Generate a regular polygon (n-gon).

    position: center of polygon
    points: number of sides (minimum 3)
    radius: distance from center to vertices
    roundness: percentage of handle smoothing (0-100)
    rotation: rotation in degrees (0 = first point at top)
    direction: winding direction -/
def generatePolygon (position : Point2D) (points : Nat)
    (radius : Float) (roundness : Float := 0)
    (rotation : Float := 0) (direction : WindingDirection := .clockwise) : BezierPath :=
  let numPoints := max 3 points
  let angleStep := Float.pi * 2 / numPoints.toFloat
  let startAngle := degToRad (rotation - 90)  -- Start at top

  let vertices := Array.range numPoints |>.map fun i =>
    let idx := match direction with
      | .clockwise => i
      | .counterClockwise => numPoints - 1 - i
    let dirMult : Float := match direction with
      | .clockwise => 1
      | .counterClockwise => -1

    let angle := startAngle + angleStep * idx.toFloat * dirMult

    let pt : Point2D := ⟨
      position.x + Float.cos angle * radius,
      position.y + Float.sin angle * radius
    ⟩

    if roundness > 0 then
      let handleLength := radius * (roundness / 100) * 0.5
      let tangentAngle := angle + Float.pi / 2 * dirMult
      let tangent : Point2D := ⟨Float.cos tangentAngle, Float.sin tangentAngle⟩

      BezierVertex.mk pt
        (scale tangent handleLength)
        (scale tangent (-handleLength))
    else
      cornerVertex pt

  ⟨vertices, true⟩

--------------------------------------------------------------------------------
-- Star
--------------------------------------------------------------------------------

/-- Generate a star shape.

    position: center of star
    points: number of points (minimum 3)
    outerRadius: radius to outer tips
    innerRadius: radius to inner valleys
    outerRoundness: smoothing at outer tips (0-100)
    innerRoundness: smoothing at inner valleys (0-100)
    rotation: rotation in degrees (0 = first point at top)
    direction: winding direction -/
def generateStar (position : Point2D) (points : Nat)
    (outerRadius innerRadius : Float)
    (outerRoundness innerRoundness : Float := 0)
    (rotation : Float := 0) (direction : WindingDirection := .clockwise) : BezierPath :=
  let numPoints := max 3 points
  let angleStep := Float.pi / numPoints.toFloat  -- Half step for alternating
  let startAngle := degToRad (rotation - 90)

  let totalVertices := numPoints * 2

  let vertices := Array.range totalVertices |>.map fun i =>
    let idx := match direction with
      | .clockwise => i
      | .counterClockwise => totalVertices - 1 - i
    let dirMult : Float := match direction with
      | .clockwise => 1
      | .counterClockwise => -1

    let angle := startAngle + angleStep * idx.toFloat * dirMult
    let isOuter := idx % 2 == 0

    let radius := if isOuter then outerRadius else innerRadius
    let roundness := if isOuter then outerRoundness else innerRoundness

    let pt : Point2D := ⟨
      position.x + Float.cos angle * radius,
      position.y + Float.sin angle * radius
    ⟩

    if roundness > 0 then
      let handleLength := radius * (roundness / 100) * 0.3
      let tangentAngle := angle + Float.pi / 2 * dirMult
      let tangent : Point2D := ⟨Float.cos tangentAngle, Float.sin tangentAngle⟩

      BezierVertex.mk pt
        (scale tangent handleLength)
        (scale tangent (-handleLength))
    else
      cornerVertex pt

  ⟨vertices, true⟩

--------------------------------------------------------------------------------
-- Path from Points
--------------------------------------------------------------------------------

/-- Create a path from an array of points (sharp corners) -/
def pathFromPoints (points : Array Point2D) (closed : Bool := true) : BezierPath :=
  let vertices := points.map cornerVertex
  ⟨vertices, closed⟩

/-- Create a smooth path from points using Catmull-Rom to Bezier conversion -/
def smoothPathFromPoints (points : Array Point2D) (closed : Bool := true)
    (tension : Float := 0.5) : BezierPath :=
  if points.size < 2 then ⟨#[], closed⟩
  else
    let n := points.size
    let vertices := Array.range n |>.map fun i =>
      let curr := points[i]!
      let prev := points[(i + n - 1) % n]!
      let next := points[(i + 1) % n]!

      -- Catmull-Rom tangent
      let tangent := scale (sub next prev) (tension / 2)

      -- Handle lengths proportional to distance
      let distPrev := distance curr prev
      let distNext := distance curr next
      let avgDist := (distPrev + distNext) / 2

      -- Scale handles
      let handleIn := scale (neg (normalize tangent)) (avgDist * 0.25)
      let handleOut := scale (normalize tangent) (avgDist * 0.25)

      BezierVertex.mk curr handleIn handleOut

    ⟨vertices, closed⟩

end Lattice.Services.ShapeOperations.Generators
