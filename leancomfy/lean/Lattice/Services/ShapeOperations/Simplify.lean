/-
  Lattice.Services.ShapeOperations.Simplify - Path Simplification

  Pure path simplification algorithms:
  - Douglas-Peucker line simplification
  - Perpendicular distance calculation
  - Bezier curve fitting
  - Path smoothing

  Source: ui/src/services/shapeOperations.ts (simplification functions)
-/

import Lattice.Services.ShapeOperations.Point2D
import Lattice.Services.ShapeOperations.Generators

namespace Lattice.Services.ShapeOperations.Simplify

open Lattice.Services.ShapeOperations.Point2D
open Lattice.Services.ShapeOperations.Generators

--------------------------------------------------------------------------------
-- Perpendicular Distance
--------------------------------------------------------------------------------

/-- Calculate perpendicular distance from a point to a line segment.

    point: the point to measure from
    lineStart: start of line segment
    lineEnd: end of line segment

    Returns the shortest distance from point to the line segment. -/
def perpendicularDistance (point lineStart lineEnd : Point2D) : Float :=
  let dx := lineEnd.x - lineStart.x
  let dy := lineEnd.y - lineStart.y
  let lineLengthSq := dx * dx + dy * dy

  if lineLengthSq == 0 then
    -- Line segment is a point
    distance point lineStart
  else
    -- Project point onto line and clamp to segment
    let t := ((point.x - lineStart.x) * dx + (point.y - lineStart.y) * dy) / lineLengthSq
    let tClamped := Float.max 0 (Float.min 1 t)

    let projection : Point2D := ⟨
      lineStart.x + tClamped * dx,
      lineStart.y + tClamped * dy
    ⟩

    distance point projection

--------------------------------------------------------------------------------
-- Douglas-Peucker Algorithm
--------------------------------------------------------------------------------

/-- Douglas-Peucker line simplification algorithm.

    Recursively removes points that are within tolerance of the line
    between their neighbors.

    points: array of points to simplify
    tolerance: maximum distance threshold for point removal

    Returns simplified array of points. -/
def douglasPeuckerAux (points : Array Point2D) (tolerance : Float) (fuel : Nat) : Array Point2D :=
  if fuel == 0 || points.size <= 2 then
    if points.size <= 2 then points
    else #[points[0]!, points[points.size - 1]!]
  else
    -- Find point with maximum distance from line between first and last
    let first := points[0]!
    let last := points[points.size - 1]!

    let rec findMax (i : Nat) (maxDist : Float) (maxIdx : Nat) : (Float × Nat) :=
      if i >= points.size - 1 then (maxDist, maxIdx)
      else
        let d := perpendicularDistance points[i]! first last
        if d > maxDist then
          findMax (i + 1) d i
        else
          findMax (i + 1) maxDist maxIdx

    let (maxDist, maxIndex) := findMax 1 0 0

    -- If max distance exceeds tolerance, recursively simplify
    if maxDist > tolerance then
      let leftPoints := points.extract 0 (maxIndex + 1)
      let rightPoints := points.extract maxIndex points.size

      let leftSimplified := douglasPeuckerAux leftPoints tolerance (fuel - 1)
      let rightSimplified := douglasPeuckerAux rightPoints tolerance (fuel - 1)

      -- Combine, removing duplicate at junction
      let leftWithoutLast := leftSimplified.extract 0 (leftSimplified.size - 1)
      leftWithoutLast ++ rightSimplified
    else
      -- All points within tolerance, return just endpoints
      #[first, last]

/-- Douglas-Peucker polyline simplification algorithm.

    Reduces the number of points in a curve while preserving its shape.
    Uses a recursive divide-and-conquer approach.

    points: array of points to simplify
    tolerance: maximum distance threshold for point removal

    Returns simplified array of points. -/
def douglasPeucker (points : Array Point2D) (tolerance : Float) : Array Point2D :=
  -- Fuel bounds recursion: max depth is log2(points.size) but we use points.size for safety
  douglasPeuckerAux points tolerance points.size

--------------------------------------------------------------------------------
-- Ramer-Douglas-Peucker (Alias)
--------------------------------------------------------------------------------

/-- Ramer-Douglas-Peucker algorithm (alias for douglasPeucker) -/
def rdpSimplify (points : Array Point2D) (tolerance : Float) : Array Point2D :=
  douglasPeucker points tolerance

--------------------------------------------------------------------------------
-- Simplify Polygon
--------------------------------------------------------------------------------

/-- Simplify a closed polygon using Douglas-Peucker.

    For closed shapes, we need special handling to ensure
    the closure point is handled correctly. -/
def simplifyPolygon (points : Array Point2D) (tolerance : Float) : Array Point2D :=
  if points.size <= 3 then points
  else douglasPeucker points tolerance

--------------------------------------------------------------------------------
-- Fit Bezier to Polygon
--------------------------------------------------------------------------------

/-- Fit smooth Bezier curves to a polygon for smoother paths.

    Uses Catmull-Rom to Bezier conversion for smooth curves.
    points: simplified polygon vertices
    closed: whether the path should be closed -/
def fitBezierToPolygon (points : Array Point2D) (closed : Bool) : BezierPath :=
  if points.size < 2 then ⟨#[], closed⟩
  else if points.size == 2 then
    ⟨points.map cornerVertex, closed⟩
  else
    let n := points.size

    let vertices := Array.range n |>.map fun i =>
      let curr := points[i]!
      let prev := points[(i + n - 1) % n]!
      let next := points[(i + 1) % n]!

      -- Calculate tangent at this point (average of in and out directions)
      let toPrev := sub prev curr
      let toNext := sub next curr

      -- Handle length proportional to distance to neighbors
      let distPrev := distance curr prev
      let distNext := distance curr next
      let handleScale : Float := 0.25  -- Adjust for curve tightness

      -- Smooth handles using tangent
      if not closed && i == 0 then
        -- First point of open path - no in handle
        BezierVertex.mk curr origin (scale (normalize toNext) (distNext * handleScale))
      else if not closed && i == n - 1 then
        -- Last point of open path - no out handle
        BezierVertex.mk curr (scale (normalize toPrev) (distPrev * handleScale)) origin
      else
        -- Interior point or closed path - smooth handles
        let tangent := normalize (sub toNext toPrev)
        BezierVertex.mk curr
          (scale tangent (-distPrev * handleScale))
          (scale tangent (distNext * handleScale))

    ⟨vertices, closed⟩

--------------------------------------------------------------------------------
-- Path Simplification (High-Level)
--------------------------------------------------------------------------------

/-- Simplify a Bezier path.

    Converts to polygon, applies Douglas-Peucker, then optionally
    refits Bezier curves.

    path: input Bezier path
    tolerance: simplification tolerance
    straightLines: if true, return polygon; if false, fit curves -/
def simplifyPath (path : BezierPath) (tolerance : Float)
    (straightLines : Bool := false) : BezierPath :=
  if path.vertices.size <= 2 then path
  else
    -- Extract just the points from vertices
    let points := path.vertices.map (·.point)

    -- Apply Douglas-Peucker
    let simplified := douglasPeucker points tolerance

    if straightLines then
      -- Return as polygon with straight edges
      ⟨simplified.map cornerVertex, path.closed⟩
    else
      -- Fit Bezier curves
      fitBezierToPolygon simplified path.closed

--------------------------------------------------------------------------------
-- Path Smoothing
--------------------------------------------------------------------------------

/-- Smooth a path by adjusting handle lengths.

    Blends existing handles toward ideal smooth handles based on
    neighboring point positions.

    amount: smoothing factor (0-100, where 100 is maximum smoothing) -/
def smoothPath (path : BezierPath) (amount : Float) : BezierPath :=
  if path.vertices.size < 2 then path
  else
    let factor := amount / 100
    let n := path.vertices.size

    let vertices := Array.range n |>.map fun i =>
      let v := path.vertices[i]!
      let prev := path.vertices[(i + n - 1) % n]!
      let next := path.vertices[(i + 1) % n]!

      -- Calculate ideal smooth handles
      let toPrev := sub prev.point v.point
      let toNext := sub next.point v.point

      let avgDir := normalize (sub toNext toPrev)
      let idealHandleLength := (distance v.point prev.point + distance v.point next.point) / 6

      -- Ideal handles
      let idealIn := scale avgDir (-idealHandleLength)
      let idealOut := scale avgDir idealHandleLength

      -- Blend current handles toward ideal
      BezierVertex.mk v.point
        (lerp v.inHandle idealIn factor)
        (lerp v.outHandle idealOut factor)

    ⟨vertices, path.closed⟩

--------------------------------------------------------------------------------
-- Visvalingam-Whyatt Algorithm (Alternative)
--------------------------------------------------------------------------------

/-- Calculate area of triangle formed by three points.
    Uses shoelace formula: Area = |x1(y2-y3) + x2(y3-y1) + x3(y1-y2)| / 2 -/
def triangleArea (p1 p2 p3 : Point2D) : Float :=
  Float.abs (p1.x * (p2.y - p3.y) + p2.x * (p3.y - p1.y) + p3.x * (p1.y - p2.y)) / 2

/-- Visvalingam-Whyatt simplification algorithm.

    Removes points based on effective area contribution.
    Tends to preserve shape features better than Douglas-Peucker
    for certain applications.

    points: array of points to simplify
    minArea: minimum triangle area threshold -/
def visvalingamWhyattAux (points : Array Point2D) (minArea : Float) (fuel : Nat) : Array Point2D :=
  if fuel == 0 || points.size <= 2 then points
  else
    -- Calculate areas for all interior points
    let rec findMinArea (i : Nat) (minA : Float) (minIdx : Nat) : (Float × Nat) :=
      if i >= points.size - 1 then (minA, minIdx)
      else
        let area := triangleArea points[i - 1]! points[i]! points[i + 1]!
        if area < minA then
          findMinArea (i + 1) area i
        else
          findMinArea (i + 1) minA minIdx

    let (minAreaFound, minIdx) := findMinArea 1 Float.pi 1  -- Start with large value

    if minAreaFound < minArea then
      -- Remove the point with minimum area
      let newPoints := points.eraseIdx minIdx
      -- Recurse with decremented fuel
      visvalingamWhyattAux newPoints minArea (fuel - 1)
    else
      points

/-- Visvalingam-Whyatt simplification algorithm.

    Removes points based on effective area contribution.
    Tends to preserve shape features better than Douglas-Peucker
    for certain applications.

    points: array of points to simplify
    minArea: minimum triangle area threshold -/
def visvalingamWhyatt (points : Array Point2D) (minArea : Float) : Array Point2D :=
  -- Fuel = points.size since we remove at most one point per iteration
  visvalingamWhyattAux points minArea points.size

end Lattice.Services.ShapeOperations.Simplify
