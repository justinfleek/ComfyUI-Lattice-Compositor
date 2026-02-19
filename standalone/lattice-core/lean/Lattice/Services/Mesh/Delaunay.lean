/-
  Lattice.Services.Mesh.Delaunay - Delaunay Triangulation

  Pure mathematical implementation of Bowyer-Watson algorithm for
  Delaunay triangulation. Used for mesh warp deformation.

  Features:
  - Super-triangle construction
  - Circumcircle containment test
  - Incremental point insertion
  - Bad triangle removal

  Source: ui/src/services/meshWarpDeformation.ts
-/

namespace Lattice.Services.Mesh.Delaunay

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D point for mesh operations -/
structure Point2D where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

/-- Triangle defined by indices into point array -/
structure Triangle where
  a : Nat
  b : Nat
  c : Nat
  deriving Repr, Inhabited, BEq

/-- Edge defined by two point indices -/
structure Edge where
  a : Nat
  b : Nat
  deriving Repr, Inhabited, BEq

/-- Check if two edges are equal (considering both directions) -/
def edgeEquals (e1 e2 : Edge) : Bool :=
  (e1.a == e2.a && e1.b == e2.b) || (e1.a == e2.b && e1.b == e2.a)

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

/-- Distance between two points -/
def distance (a b : Point2D) : Float :=
  let dx := b.x - a.x
  let dy := b.y - a.y
  Float.sqrt (dx * dx + dy * dy)

/-- Point subtraction -/
def sub (a b : Point2D) : Point2D :=
  ⟨a.x - b.x, a.y - b.y⟩

--------------------------------------------------------------------------------
-- Circumcircle Test
--------------------------------------------------------------------------------

/-- Check if a point is inside the circumcircle of a triangle.

    Uses the determinant method. The sign of the determinant indicates
    whether the point is inside (positive for CCW triangles) or outside.

    Mathematical formula:
    | ax-px  ay-py  (ax-px)²+(ay-py)² |
    | bx-px  by-py  (bx-px)²+(by-py)² | > 0 for inside (CCW triangle)
    | cx-px  cy-py  (cx-px)²+(cy-py)² |
-/
def isPointInCircumcircle (point a b c : Point2D) : Bool :=
  let ax := a.x - point.x
  let ay := a.y - point.y
  let bx := b.x - point.x
  let by_ := b.y - point.y  -- 'by' is reserved
  let cx := c.x - point.x
  let cy := c.y - point.y

  -- Determinant calculation
  let det :=
    (ax * ax + ay * ay) * (bx * cy - cx * by_) -
    (bx * bx + by_ * by_) * (ax * cy - cx * ay) +
    (cx * cx + cy * cy) * (ax * by_ - bx * ay)

  -- Check orientation of triangle
  let orientation := (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x)

  -- Inside if det and orientation have same sign
  if orientation > 0 then det > 0 else det < 0

--------------------------------------------------------------------------------
-- Super Triangle
--------------------------------------------------------------------------------

/-- Create a super triangle that encompasses all points.

    The super triangle is large enough that all input points
    lie strictly inside it. Used as initial state for Bowyer-Watson. -/
def createSuperTriangle (points : Array Point2D) : (Point2D × Point2D × Point2D) :=
  if points.size == 0 then
    (⟨0, 0⟩, ⟨1, 0⟩, ⟨0.5, 1⟩)
  else
    -- Find bounding box
    let minX := points.foldl (fun acc p => Float.min acc p.x) (1.0 / 0.0)
    let maxX := points.foldl (fun acc p => Float.max acc p.x) (-1.0 / 0.0)
    let minY := points.foldl (fun acc p => Float.min acc p.y) (1.0 / 0.0)
    let maxY := points.foldl (fun acc p => Float.max acc p.y) (-1.0 / 0.0)

    let dx := maxX - minX
    let dy := maxY - minY
    let deltaMax := Float.max dx dy * 2.0

    -- Super triangle vertices
    let superA : Point2D := ⟨minX - deltaMax, minY - deltaMax⟩
    let superB : Point2D := ⟨minX + deltaMax * 2.0, minY - deltaMax⟩
    let superC : Point2D := ⟨minX + deltaMax / 2.0, maxY + deltaMax * 2.0⟩

    (superA, superB, superC)

--------------------------------------------------------------------------------
-- Triangle Edge Extraction
--------------------------------------------------------------------------------

/-- Get the three edges of a triangle -/
def triangleEdges (tri : Triangle) : Array Edge :=
  #[⟨tri.a, tri.b⟩, ⟨tri.b, tri.c⟩, ⟨tri.c, tri.a⟩]

/-- Check if an edge is shared between a triangle and any in a list -/
def isEdgeShared (edge : Edge) (tri : Triangle) (others : Array Triangle) : Bool :=
  others.any fun other =>
    if other == tri then false
    else
      let otherEdges := triangleEdges other
      otherEdges.any fun otherEdge => edgeEquals edge otherEdge

--------------------------------------------------------------------------------
-- Bowyer-Watson Algorithm
--------------------------------------------------------------------------------

/-- Find all triangles whose circumcircle contains the given point -/
def findBadTriangles (point : Point2D) (triangles : Array Triangle)
    (allPoints : Array Point2D) : Array Triangle :=
  triangles.filter fun tri =>
    let pa := allPoints[tri.a]!
    let pb := allPoints[tri.b]!
    let pc := allPoints[tri.c]!
    isPointInCircumcircle point pa pb pc

/-- Find the boundary polygon of bad triangles (non-shared edges) -/
def findPolygonBoundary (badTriangles : Array Triangle) : Array Edge :=
  let allEdges := badTriangles.foldl (fun acc tri =>
    acc ++ (triangleEdges tri).toList) []

  -- Keep only edges that appear exactly once (not shared)
  allEdges.filter fun edge =>
    let count := allEdges.foldl (fun acc e =>
      if edgeEquals edge e then acc + 1 else acc) 0
    count == 1
  |>.toArray

/-- Delaunay triangulation using Bowyer-Watson algorithm.

    Incrementally inserts points and maintains Delaunay property.
    Uses explicit fuel to prove termination. -/
def delaunayTriangulateAux (points : Array Point2D) (fuel : Nat)
    (triangles : Array Triangle) (allPoints : Array Point2D)
    (currentIdx : Nat) : Array Triangle :=
  if fuel == 0 || currentIdx >= points.size then triangles
  else
    let point := points[currentIdx]!

    -- Find triangles whose circumcircle contains this point
    let badTriangles := findBadTriangles point triangles allPoints

    -- Find boundary polygon
    let polygon := findPolygonBoundary badTriangles

    -- Remove bad triangles
    let triangles' := triangles.filter fun t => !badTriangles.contains t

    -- Create new triangles from polygon edges to new point
    let newTriangles := polygon.map fun edge =>
      ⟨edge.a, edge.b, currentIdx⟩

    delaunayTriangulateAux points (fuel - 1) (triangles' ++ newTriangles)
      allPoints (currentIdx + 1)

/-- Delaunay triangulation of a point set.

    Returns array of triangles (as index triples into input array).
    Uses Bowyer-Watson algorithm. -/
def delaunayTriangulate (points : Array Point2D) : Array Triangle :=
  if points.size < 3 then #[]
  else
    -- Create super triangle
    let (superA, superB, superC) := createSuperTriangle points
    let superIndices := #[points.size, points.size + 1, points.size + 2]

    -- All points including super triangle
    let allPoints := points ++ #[superA, superB, superC]

    -- Initial triangle is the super triangle
    let initialTriangles := #[⟨superIndices[0]!, superIndices[1]!, superIndices[2]!⟩]

    -- Run Bowyer-Watson with fuel = points.size
    let triangles := delaunayTriangulateAux points points.size initialTriangles
      allPoints 0

    -- Remove triangles that include super triangle vertices
    triangles.filter fun t =>
      !superIndices.contains t.a &&
      !superIndices.contains t.b &&
      !superIndices.contains t.c

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

/-- Flatten triangles to index array (for GPU) -/
def flattenTriangles (triangles : Array Triangle) : Array Nat :=
  triangles.foldl (fun acc tri =>
    acc ++ #[tri.a, tri.b, tri.c]) #[]

/-- Get triangle count -/
def triangleCount (triangles : Array Triangle) : Nat :=
  triangles.size

end Lattice.Services.Mesh.Delaunay
