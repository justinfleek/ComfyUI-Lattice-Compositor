/-
  Lattice.Services.Path.Morphing - Path Morphing Algorithms

  Pure mathematical functions for Bezier path morphing:
  - Subdivision for point count matching
  - Correspondence optimization (rotation, reversal)
  - Travel distance calculation
  - Vertex interpolation

  Source: ui/src/services/pathMorphing.ts
-/

import Lattice.Services.Path.BezierCore

namespace Lattice.Services.Path.Morphing

open Lattice.Services.Path.BezierCore

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Point matching strategy for paths with different vertex counts -/
inductive PointMatchingStrategy where
  | subdivideShorter  -- Add vertices to shorter path
  | subdivideBoth     -- Add vertices to both paths to match
  | resample          -- Resample both with even spacing
  deriving Repr, DecidableEq, Inhabited

/-- Correspondence method for closed paths -/
inductive CorrespondenceMethod where
  | index           -- Direct index matching
  | nearestRotation -- Find rotation that minimizes travel
  | nearestDistance -- Same as nearestRotation
  | manual          -- Use manual mapping
  deriving Repr, DecidableEq, Inhabited

/-- Morph configuration -/
structure MorphConfig where
  pointMatchingStrategy : PointMatchingStrategy := .subdivideShorter
  correspondenceMethod : CorrespondenceMethod := .nearestRotation
  resampleCount : Option Nat := none
  deriving Repr, Inhabited

/-- Result of preparing paths for morphing -/
structure PreparedMorphPaths where
  source : BezierPath
  target : BezierPath
  rotationOffset : Nat
  reversed : Bool
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Path Cloning
--------------------------------------------------------------------------------

/-- Clone a path -/
def clonePath (path : BezierPath) : BezierPath :=
  { vertices := path.vertices.map BezierVertex.clone
  , closed := path.closed }

--------------------------------------------------------------------------------
-- Correspondence / Travel Distance
--------------------------------------------------------------------------------

/-- Calculate total travel distance for a given rotation offset.

    Lower is better - vertices should move less during morphing.

    rotationOffset: How many positions to rotate target indices
    reversed: Whether to reverse target traversal order -/
def calculateTravelDistance (source target : BezierPath)
    (rotationOffset : Nat) (reversed : Bool) : Float :=
  let n := source.vertices.size
  if n == 0 || n != target.vertices.size then 0.0
  else
    let rec go (i : Nat) (acc : Float) : Float :=
      if i >= n then acc
      else
        let srcIdx := i
        let tgtIdx :=
          if reversed then
            (n - 1 - i + rotationOffset + n) % n
          else
            (i + rotationOffset) % n

        let srcPoint := source.vertices[srcIdx]!.point
        let tgtPoint := target.vertices[tgtIdx]!.point
        let dist := Point2D.distance srcPoint tgtPoint
        go (i + 1) (acc + dist)
    go 0 0.0

/-- Find optimal rotation offset to minimize travel distance.

    Tries all rotation offsets and both directions (for closed paths).
    Returns (offset, reversed) pair. -/
def findOptimalRotation (source target : BezierPath) : Nat × Bool :=
  let n := source.vertices.size
  if n == 0 then (0, false)
  else
    let rec findBest (offset : Nat) (bestOffset : Nat) (bestReversed : Bool)
        (bestDist : Float) : Nat × Bool :=
      if offset >= n then (bestOffset, bestReversed)
      else
        -- Try normal direction
        let dist := calculateTravelDistance source target offset false
        let (bestOffset', bestReversed', bestDist') :=
          if dist < bestDist then (offset, false, dist)
          else (bestOffset, bestReversed, bestDist)

        -- Try reversed direction (for closed paths)
        let (bestOffset'', bestReversed'', bestDist'') :=
          if source.closed && target.closed then
            let distRev := calculateTravelDistance source target offset true
            if distRev < bestDist' then (offset, true, distRev)
            else (bestOffset', bestReversed', bestDist')
          else (bestOffset', bestReversed', bestDist')

        findBest (offset + 1) bestOffset'' bestReversed'' bestDist''

    findBest 0 0 false (1.0 / 0.0)  -- Start with infinity

/-- Rotate and optionally reverse a path's vertices.

    offset: Number of positions to rotate
    reverse: Whether to reverse vertex order -/
def rotateVertices (path : BezierPath) (offset : Nat) (reverse : Bool) : BezierPath :=
  let n := path.vertices.size
  if n == 0 then path
  else
    let vertices := Array.ofFn fun (i : Fin n) =>
      let srcIdx :=
        if reverse then
          (n - 1 - i.val + offset + n) % n
        else
          (i.val + offset) % n

      let srcVertex := path.vertices[srcIdx]!

      if reverse then
        -- Swap in/out handles when reversing
        { point := srcVertex.point.clone
        , inHandle := srcVertex.outHandle.clone
        , outHandle := srcVertex.inHandle.clone }
      else
        srcVertex.clone

    { vertices := vertices, closed := path.closed }

--------------------------------------------------------------------------------
-- Subdivision
--------------------------------------------------------------------------------

/-- Subdivide a segment at parameter t.

    Inserts a new vertex at the split point.
    Returns new path with one additional vertex. -/
def subdivideSegmentAt (path : BezierPath) (segmentIndex : Nat) (t : Float) : BezierPath :=
  let n := path.vertices.size
  if n == 0 || segmentIndex >= n then path
  else
    let nextIdx := (segmentIndex + 1) % n
    let v0 := path.vertices[segmentIndex]!
    let v1 := path.vertices[nextIdx]!

    let p0 := v0.point
    let p1 := v0.outHandleAbsolute
    let p2 := v1.inHandleAbsolute
    let p3 := v1.point

    let (left, right) := splitCubicBezier p0 p1 p2 p3 t

    -- Update v0's out handle
    let v0' := { v0 with outHandle := left.p1.sub left.p0 }

    -- Create new vertex at split point
    let newVertex : BezierVertex :=
      { point := left.p3.clone
      , inHandle := left.p2.sub left.p3
      , outHandle := right.p1.sub right.p0 }

    -- Update v1's in handle
    let v1' := { v1 with inHandle := right.p2.sub right.p3 }

    -- Build new vertex array
    let vertices := Array.empty
      |>.append (path.vertices.extract 0 segmentIndex)
      |>.push v0'
      |>.push newVertex
      |>.push v1'
      |>.append (path.vertices.extract (nextIdx + 1) n)

    { vertices := vertices, closed := path.closed }

/-- Find index of longest segment. -/
def findLongestSegment (lengths : Array Float) : Nat :=
  if lengths.size == 0 then 0
  else
    let rec go (i : Nat) (maxIdx : Nat) (maxLen : Float) : Nat :=
      if i >= lengths.size then maxIdx
      else
        let len := lengths[i]!
        if len > maxLen then go (i + 1) i len
        else go (i + 1) maxIdx maxLen
    go 0 0 0.0

/-- Subdivide a path to have a specific number of vertices.

    Repeatedly subdivides the longest segment until target count is reached.

    Uses explicit fuel parameter to prove termination. Each subdivision adds
    exactly one vertex, so fuel = targetCount - currentSize bounds iterations. -/
def subdivideToVertexCountAux (path : BezierPath) (targetCount : Nat) (fuel : Nat) : BezierPath :=
  if fuel == 0 then path
  else if path.vertices.size >= targetCount then path
  else
    -- Find longest segment
    let lengths := getSegmentLengths path 10
    let maxIdx := findLongestSegment lengths

    -- Subdivide at midpoint
    let newPath := subdivideSegmentAt path maxIdx 0.5

    -- Recurse with decremented fuel
    subdivideToVertexCountAux newPath targetCount (fuel - 1)

/-- Subdivide a path to have a specific number of vertices.

    Wrapper that computes appropriate fuel. -/
def subdivideToVertexCount (path : BezierPath) (targetCount : Nat) : BezierPath :=
  -- Fuel = number of vertices we need to add
  let fuel := if targetCount > path.vertices.size
              then targetCount - path.vertices.size
              else 0
  subdivideToVertexCountAux path targetCount fuel

--------------------------------------------------------------------------------
-- Resampling
--------------------------------------------------------------------------------

/-- Get point at a specific arc length along the path. -/
def getPointAtArcLength (path : BezierPath) (targetLength : Float)
    (segmentLengths : Array Float) : Point2D :=
  if segmentLengths.size == 0 || path.vertices.size == 0 then
    Point2D.zero
  else
    let rec go (i : Nat) (accumulated : Float) : Point2D :=
      if i >= segmentLengths.size then
        -- Return last point
        path.vertices[path.vertices.size - 1]!.point
      else
        let segLen := segmentLengths[i]!
        if accumulated + segLen >= targetLength || i == segmentLengths.size - 1 then
          -- Found segment containing target length
          let localT := if segLen > 0.0 then (targetLength - accumulated) / segLen else 0.0
          let clampedT := Float.max 0.0 (Float.min 1.0 localT)
          match getSegmentControlPoints path i with
          | some (p0, p1, p2, p3) => cubicBezierPoint p0 p1 p2 p3 clampedT
          | none => path.vertices[i]!.point
        else
          go (i + 1) (accumulated + segLen)
    go 0 0.0

/-- Resample a path with evenly spaced vertices. -/
def resamplePath (path : BezierPath) (vertexCount : Nat) : BezierPath :=
  if vertexCount < 2 || path.vertices.size == 0 then clonePath path
  else
    let segmentLengths := getSegmentLengths path 10
    let totalLength := segmentLengths.foldl (· + ·) 0.0

    if totalLength == 0.0 then clonePath path
    else
      let spacing := totalLength / (if path.closed then vertexCount.toFloat else (vertexCount - 1).toFloat)

      let vertices := Array.ofFn fun (i : Fin vertexCount) =>
        let targetLength := i.val.toFloat * spacing
        let point := getPointAtArcLength path targetLength segmentLengths

        -- Calculate tangent for handles (simplified)
        let prevLength := Float.max 0.0 (targetLength - spacing * 0.33)
        let nextLength := Float.min totalLength (targetLength + spacing * 0.33)
        let prevPoint := getPointAtArcLength path prevLength segmentLengths
        let nextPoint := getPointAtArcLength path nextLength segmentLengths

        let tangent := Point2D.sub nextPoint prevPoint |>.scale 0.5
        let handleScale := 0.33

        { point := point
        , inHandle := tangent.scale (-handleScale)
        , outHandle := tangent.scale handleScale }

      { vertices := vertices, closed := path.closed }

--------------------------------------------------------------------------------
-- Main Morphing Functions
--------------------------------------------------------------------------------

/-- Interpolate between two prepared paths.

    Paths must have the same vertex count.
    t: Interpolation factor [0, 1] -/
def morphPaths (source target : BezierPath) (t : Float) : BezierPath :=
  let clampedT := Float.max 0.0 (Float.min 1.0 t)

  if clampedT == 0.0 then clonePath source
  else if clampedT == 1.0 then clonePath target
  else
    let n := Float.min source.vertices.size.toFloat target.vertices.size.toFloat |>.toUInt64.toNat

    let vertices := Array.ofFn fun (i : Fin n) =>
      let srcV := source.vertices[i.val]!
      let tgtV := target.vertices[i.val]!
      BezierVertex.lerp srcV tgtV clampedT

    { vertices := vertices, closed := source.closed }

/-- Prepare two paths for morphing.

    Matches vertex counts and finds optimal correspondence. -/
def prepareMorphPaths (source target : BezierPath) (config : MorphConfig := {})
    : PreparedMorphPaths :=
  if source.vertices.size == 0 || target.vertices.size == 0 then
    { source := clonePath source
    , target := clonePath target
    , rotationOffset := 0
    , reversed := false }
  else
    -- Step 1: Match vertex counts
    let (prepSource, prepTarget) :=
      if source.vertices.size == target.vertices.size then
        (clonePath source, clonePath target)
      else
        match config.pointMatchingStrategy with
        | .subdivideShorter =>
          if source.vertices.size < target.vertices.size then
            (subdivideToVertexCount source target.vertices.size, clonePath target)
          else
            (clonePath source, subdivideToVertexCount target source.vertices.size)
        | .subdivideBoth =>
          let maxCount := Nat.max source.vertices.size target.vertices.size
          (subdivideToVertexCount source maxCount, subdivideToVertexCount target maxCount)
        | .resample =>
          let count := config.resampleCount.getD (Nat.max source.vertices.size target.vertices.size)
          (resamplePath source count, resamplePath target count)

    -- Step 2: Find optimal correspondence (for closed paths)
    let (rotationOffset, reversed) :=
      if prepSource.closed && prepTarget.closed then
        match config.correspondenceMethod with
        | .nearestRotation | .nearestDistance => findOptimalRotation prepSource prepTarget
        | .index | .manual => (0, false)
      else (0, false)

    -- Apply rotation to target
    let finalTarget :=
      if rotationOffset != 0 || reversed then
        rotateVertices prepTarget rotationOffset reversed
      else prepTarget

    { source := prepSource
    , target := finalTarget
    , rotationOffset := rotationOffset
    , reversed := reversed }

/-- Convenience function: prepare and morph in one step. -/
def morphPathsAuto (source target : BezierPath) (t : Float)
    (config : MorphConfig := {}) : BezierPath :=
  let prepared := prepareMorphPaths source target config
  morphPaths prepared.source prepared.target t

end Lattice.Services.Path.Morphing
