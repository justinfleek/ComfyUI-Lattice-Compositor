/-
  Lattice.Services.SVGExtrusion.Simplify - Vertex Simplification Mathematics

  Pure mathematical functions for geometry simplification:
  - Vertex welding (merging close vertices)
  - Tolerance-based rounding
  - Index remapping

  Source: ui/src/services/svgExtrusion.ts (lines 1185-1239)
-/

namespace Lattice.Services.SVGExtrusion.Simplify

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 3D vertex position -/
structure Vertex3D where
  x : Float
  y : Float
  z : Float
deriving Repr, Inhabited, BEq

/-- Simplified geometry result -/
structure SimplifiedGeometry where
  positions : Array Float       -- Flattened x,y,z values
  indices : Array Nat           -- Triangle indices
  originalToNew : Array Nat     -- Mapping from original to new vertex index
deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Tolerance Rounding
--------------------------------------------------------------------------------

/-- Round a value to the nearest tolerance step.

    This is the key to vertex welding - vertices within tolerance
    will round to the same value.

    @param v Value to round
    @param tolerance Grid spacing
    @return Rounded value -/
def roundToTolerance (v tolerance : Float) : Float :=
  if tolerance <= 0.0 then v
  else Float.round (v / tolerance) * tolerance

/-- Round a 3D vertex to tolerance grid.

    @param vertex The vertex to round
    @param tolerance Grid spacing
    @return Rounded vertex -/
def roundVertex (vertex : Vertex3D) (tolerance : Float) : Vertex3D :=
  { x := roundToTolerance vertex.x tolerance
  , y := roundToTolerance vertex.y tolerance
  , z := roundToTolerance vertex.z tolerance }

--------------------------------------------------------------------------------
-- Vertex Key Generation
--------------------------------------------------------------------------------

/-- Create a string key for a vertex (for deduplication).

    @param vertex The vertex
    @return String key in format "x,y,z" -/
def vertexKey (vertex : Vertex3D) : String :=
  s!"{vertex.x},{vertex.y},{vertex.z}"

--------------------------------------------------------------------------------
-- Vertex Welding
--------------------------------------------------------------------------------

/-- Result of processing a single vertex during welding -/
structure WeldResult where
  newIndex : Nat
  positions : Array Float
  seenKeys : Std.HashMap String Nat
deriving Inhabited

/-- Process a single vertex for welding.

    @param vertex Original vertex
    @param tolerance Rounding tolerance
    @param currentPositions Current position array
    @param seenKeys Map of seen vertex keys to indices
    @return Updated state with new index -/
def processVertex
    (vertex : Vertex3D)
    (tolerance : Float)
    (currentPositions : Array Float)
    (seenKeys : Std.HashMap String Nat) : WeldResult :=
  let rounded := roundVertex vertex tolerance
  let key := vertexKey rounded
  match seenKeys.get? key with
  | some existingIndex =>
    { newIndex := existingIndex
    , positions := currentPositions
    , seenKeys := seenKeys }
  | none =>
    let newIndex := currentPositions.size / 3
    let newPositions := currentPositions.push rounded.x |>.push rounded.y |>.push rounded.z
    let newSeenKeys := seenKeys.insert key newIndex
    { newIndex := newIndex
    , positions := newPositions
    , seenKeys := newSeenKeys }

/-- Weld vertices by merging those within tolerance.

    This is a vertex deduplication algorithm that merges vertices
    that are closer than the tolerance threshold.

    @param vertices Array of original vertices
    @param tolerance Distance threshold for welding
    @return Simplified geometry with deduplicated vertices -/
def weldVertices (vertices : Array Vertex3D) (tolerance : Float) : SimplifiedGeometry :=
  let initialState : (Array Float × Std.HashMap String Nat × Array Nat) :=
    (#[], Std.HashMap.empty, #[])
  let (positions, _, indexMap) := vertices.foldl
    (fun (positions, seen, indices) vertex =>
      let result := processVertex vertex tolerance positions seen
      (result.positions, result.seenKeys, indices.push result.newIndex))
    initialState
  { positions := positions
  , indices := #[]  -- Indices need to be rebuilt from original geometry
  , originalToNew := indexMap }

--------------------------------------------------------------------------------
-- Index Remapping
--------------------------------------------------------------------------------

/-- Remap triangle indices using the vertex mapping.

    @param originalIndices Original triangle indices
    @param indexMap Mapping from old to new vertex indices
    @return Remapped indices -/
def remapIndices (originalIndices : Array Nat) (indexMap : Array Nat) : Array Nat :=
  originalIndices.map fun oldIdx =>
    if h : oldIdx < indexMap.size then indexMap[oldIdx]
    else oldIdx  -- Keep original if out of bounds

--------------------------------------------------------------------------------
-- Degenerate Triangle Removal
--------------------------------------------------------------------------------

/-- Check if a triangle is degenerate (all same vertices).

    @param i0 First vertex index
    @param i1 Second vertex index
    @param i2 Third vertex index
    @return True if triangle is degenerate -/
def isDegenerateTriangle (i0 i1 i2 : Nat) : Bool :=
  i0 == i1 || i1 == i2 || i0 == i2

/-- Remove degenerate triangles from index array.

    After welding, some triangles may collapse to lines or points.

    @param indices Triangle indices (groups of 3)
    @return Indices with degenerate triangles removed -/
def removeDegenerateTriangles (indices : Array Nat) : Array Nat :=
  let triCount := indices.size / 3
  let result := Array.mkEmpty (indices.size)
  let rec process (i : Nat) (acc : Array Nat) : Array Nat :=
    if h : i >= triCount then acc
    else
      let base := i * 3
      let i0 := if h0 : base < indices.size then indices[base] else 0
      let i1 := if h1 : base + 1 < indices.size then indices[base + 1] else 0
      let i2 := if h2 : base + 2 < indices.size then indices[base + 2] else 0
      if isDegenerateTriangle i0 i1 i2 then
        process (i + 1) acc
      else
        process (i + 1) (acc.push i0 |>.push i1 |>.push i2)
  termination_by triCount - i
  process 0 result

--------------------------------------------------------------------------------
-- Full Simplification Pipeline
--------------------------------------------------------------------------------

/-- Simplify geometry by welding vertices and removing degenerate triangles.

    @param vertices Original vertex positions
    @param indices Original triangle indices
    @param tolerance Welding tolerance
    @return Simplified geometry -/
def simplifyGeometry
    (vertices : Array Vertex3D)
    (indices : Array Nat)
    (tolerance : Float) : SimplifiedGeometry :=
  let welded := weldVertices vertices tolerance
  let remappedIndices := remapIndices indices welded.originalToNew
  let cleanIndices := removeDegenerateTriangles remappedIndices
  { positions := welded.positions
  , indices := cleanIndices
  , originalToNew := welded.originalToNew }

--------------------------------------------------------------------------------
-- Statistics
--------------------------------------------------------------------------------

/-- Calculate simplification statistics.

    @param originalVertexCount Original number of vertices
    @param simplified Simplified geometry result
    @return (new vertex count, reduction percentage) -/
def simplificationStats (originalVertexCount : Nat) (simplified : SimplifiedGeometry) : (Nat × Float) :=
  let newCount := simplified.positions.size / 3
  let reduction := if originalVertexCount > 0 then
    (1.0 - Float.ofNat newCount / Float.ofNat originalVertexCount) * 100.0
  else 0.0
  (newCount, reduction)

end Lattice.Services.SVGExtrusion.Simplify
