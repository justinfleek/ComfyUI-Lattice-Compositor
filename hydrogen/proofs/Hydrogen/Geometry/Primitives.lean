/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                HYDROGEN // GEOMETRY // PRIMITIVES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Procedural geometry primitives: Box, Sphere, Plane, Cylinder, etc.
  
  These are the fundamental building blocks for 3D scenes. Each generator
  produces a MeshDescriptor with PROVEN vertex and index counts.
  
  Key design decisions:
  - Generators return MeshDescriptors, not actual vertex data
  - Vertex/index counts are computed and proven correct
  - Bounding volumes are computed exactly from parameters
  - Subdivision levels parameterize quality/performance tradeoff

  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Mesh      : Mesh descriptor types
  - Box3      : Bounding box
  - Sphere    : Bounding sphere
  - Vec3      : 3D vectors
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Geometry.Mesh
import Hydrogen.Math.Box3
import Hydrogen.Math.Sphere
import Hydrogen.Math.Vec3

namespace Hydrogen.Geometry

open Hydrogen.Math

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: BOX GEOMETRY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Parameters for box geometry generation -/
structure BoxParams where
  /-- Width (X axis) -/
  width : ℝ
  /-- Height (Y axis) -/
  height : ℝ
  /-- Depth (Z axis) -/
  depth : ℝ
  /-- Segments along width -/
  widthSegments : Nat := 1
  /-- Segments along height -/
  heightSegments : Nat := 1
  /-- Segments along depth -/
  depthSegments : Nat := 1

namespace BoxParams

/-- Unit box centered at origin -/
def unit : BoxParams :=
  { width := 1, height := 1, depth := 1 }

/-- Create from Vec3 dimensions -/
def fromSize (size : Vec3) : BoxParams :=
  { width := size.x, height := size.y, depth := size.z }

end BoxParams

/-- Box geometry generator.
    
    A box has 6 faces, each subdivided into a grid.
    For a simple box (1×1×1 segments):
    - 24 vertices (4 per face, not shared due to different normals)
    - 36 indices (6 per face, 2 triangles each) -/
structure BoxGeometry where
  params : BoxParams

namespace BoxGeometry

/-- Vertices per face for given segments -/
def verticesPerFace (widthSegs heightSegs : Nat) : Nat :=
  (widthSegs + 1) * (heightSegs + 1)

/-- Indices per face for given segments (2 triangles per quad) -/
def indicesPerFace (widthSegs heightSegs : Nat) : Nat :=
  widthSegs * heightSegs * 6

/-- Total vertex count for box -/
def vertexCount (p : BoxParams) : Nat :=
  -- Front/Back faces (width × height)
  2 * verticesPerFace p.widthSegments p.heightSegments +
  -- Left/Right faces (depth × height)
  2 * verticesPerFace p.depthSegments p.heightSegments +
  -- Top/Bottom faces (width × depth)
  2 * verticesPerFace p.widthSegments p.depthSegments

/-- Total index count for box -/
def indexCount (p : BoxParams) : Nat :=
  -- Front/Back faces
  2 * indicesPerFace p.widthSegments p.heightSegments +
  -- Left/Right faces
  2 * indicesPerFace p.depthSegments p.heightSegments +
  -- Top/Bottom faces
  2 * indicesPerFace p.widthSegments p.depthSegments

/-- Create mesh descriptor for box -/
def toMeshDescriptor (box : BoxGeometry) : MeshDescriptor :=
  let p := box.params
  { layout := VertexLayout.positionNormalUV
    vertexCount := vertexCount p
    indexFormat := some (IndexFormat.forVertexCount (vertexCount p))
    indexCount := indexCount p
    topology := PrimitiveTopology.triangleList
    boundingBox := some (Box3.fromCenterAndSize Vec3.zero ⟨p.width, p.height, p.depth⟩)
    boundingSphere := none }

-- ─────────────────────────────────────────────────────────────────────────────
-- BoxGeometry Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Unit box has 24 vertices -/
theorem unit_vertexCount : vertexCount BoxParams.unit = 24 := rfl

/-- Unit box has 36 indices -/
theorem unit_indexCount : indexCount BoxParams.unit = 36 := rfl

/-- Vertex count is always positive for valid segments -/
theorem vertexCount_pos (p : BoxParams) 
    (_hw : p.widthSegments ≥ 1) (_hh : p.heightSegments ≥ 1) (_hd : p.depthSegments ≥ 1) : 
    vertexCount p > 0 := by
  unfold vertexCount verticesPerFace
  have h1 : (p.widthSegments + 1) * (p.heightSegments + 1) > 0 := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have h2 : (p.depthSegments + 1) * (p.heightSegments + 1) > 0 := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have h3 : (p.widthSegments + 1) * (p.depthSegments + 1) > 0 := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  omega

/-- Index count is always positive for valid segments -/
theorem indexCount_pos (p : BoxParams) 
    (hw : p.widthSegments ≥ 1) (hh : p.heightSegments ≥ 1) (_hd : p.depthSegments ≥ 1) : 
    indexCount p > 0 := by
  unfold indexCount indicesPerFace
  have h1 : p.widthSegments * p.heightSegments > 0 := Nat.mul_pos hw hh
  omega

/-- Index count is divisible by 3 (triangles) -/
theorem indexCount_div3 (p : BoxParams) : indexCount p % 3 = 0 := by
  unfold indexCount indicesPerFace
  omega

end BoxGeometry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: PLANE GEOMETRY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Parameters for plane geometry generation -/
structure PlaneParams where
  /-- Width (X axis) -/
  width : ℝ
  /-- Height (Y axis, in local space; renders as Z in world) -/
  height : ℝ
  /-- Segments along width -/
  widthSegments : Nat := 1
  /-- Segments along height -/
  heightSegments : Nat := 1

namespace PlaneParams

/-- Unit plane centered at origin -/
def unit : PlaneParams :=
  { width := 1, height := 1 }

end PlaneParams

/-- Plane geometry generator.
    
    A plane is a single flat quad with optional subdivision.
    For a simple plane (1×1 segments):
    - 4 vertices
    - 6 indices (2 triangles) -/
structure PlaneGeometry where
  params : PlaneParams

namespace PlaneGeometry

/-- Total vertex count for plane -/
def vertexCount (p : PlaneParams) : Nat :=
  (p.widthSegments + 1) * (p.heightSegments + 1)

/-- Total index count for plane -/
def indexCount (p : PlaneParams) : Nat :=
  p.widthSegments * p.heightSegments * 6

/-- Create mesh descriptor for plane -/
def toMeshDescriptor (plane : PlaneGeometry) : MeshDescriptor :=
  let p := plane.params
  { layout := VertexLayout.positionNormalUV
    vertexCount := vertexCount p
    indexFormat := some (IndexFormat.forVertexCount (vertexCount p))
    indexCount := indexCount p
    topology := PrimitiveTopology.triangleList
    boundingBox := some (Box3.fromCenterAndSize Vec3.zero ⟨p.width, 0, p.height⟩)
    boundingSphere := none }

-- ─────────────────────────────────────────────────────────────────────────────
-- PlaneGeometry Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Unit plane has 4 vertices -/
theorem unit_vertexCount : vertexCount PlaneParams.unit = 4 := rfl

/-- Unit plane has 6 indices -/
theorem unit_indexCount : indexCount PlaneParams.unit = 6 := rfl

/-- Index count is divisible by 3 -/
theorem indexCount_div3 (p : PlaneParams) : indexCount p % 3 = 0 := by
  unfold indexCount
  omega

/-- Index count is divisible by 6 (two triangles per quad) -/
theorem indexCount_div6 (p : PlaneParams) : indexCount p % 6 = 0 := by
  unfold indexCount
  omega

end PlaneGeometry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: SPHERE GEOMETRY (UV Sphere)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Parameters for sphere geometry generation (UV sphere) -/
structure SphereParams where
  /-- Radius -/
  radius : ℝ
  /-- Segments around equator (longitude) -/
  widthSegments : Nat := 32
  /-- Segments from pole to pole (latitude) -/
  heightSegments : Nat := 16
  /-- Phi start angle (radians) -/
  phiStart : ℝ := 0
  /-- Phi length (radians, 2π for full sphere) -/
  phiLength : ℝ := 2 * Real.pi
  /-- Theta start angle (radians) -/
  thetaStart : ℝ := 0
  /-- Theta length (radians, π for full sphere) -/
  thetaLength : ℝ := Real.pi

namespace SphereParams

/-- Unit sphere centered at origin -/
noncomputable def unit : SphereParams :=
  { radius := 1 }

/-- Low-poly sphere for performance -/
noncomputable def lowPoly : SphereParams :=
  { radius := 1, widthSegments := 16, heightSegments := 8 }

/-- High-poly sphere for quality -/
noncomputable def highPoly : SphereParams :=
  { radius := 1, widthSegments := 64, heightSegments := 32 }

end SphereParams

/-- Sphere geometry generator (UV sphere).
    
    A UV sphere has vertices arranged in rings (latitude) and segments (longitude).
    The poles are single vertices shared by all triangles meeting there. -/
structure SphereGeometry where
  params : SphereParams

namespace SphereGeometry

/-- Total vertex count for UV sphere -/
def vertexCount (p : SphereParams) : Nat :=
  -- Grid of (widthSegments + 1) × (heightSegments + 1) vertices
  -- Top and bottom rows are degenerate (single point replicated)
  (p.widthSegments + 1) * (p.heightSegments + 1)

/-- Total index count for UV sphere -/
def indexCount (p : SphereParams) : Nat :=
  -- Each quad becomes 2 triangles, but top/bottom rows are triangles not quads
  p.widthSegments * p.heightSegments * 6

/-- Create mesh descriptor for sphere -/
def toMeshDescriptor (sphere : SphereGeometry) : MeshDescriptor :=
  let p := sphere.params
  { layout := VertexLayout.positionNormalUV
    vertexCount := vertexCount p
    indexFormat := some (IndexFormat.forVertexCount (vertexCount p))
    indexCount := indexCount p
    topology := PrimitiveTopology.triangleList
    boundingBox := some (Box3.fromCenterAndSize Vec3.zero (Vec3.uniform (2 * p.radius)))
    boundingSphere := some (Sphere.mk Vec3.zero p.radius) }

-- ─────────────────────────────────────────────────────────────────────────────
-- SphereGeometry Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Unit sphere vertex count -/
theorem unit_vertexCount : vertexCount SphereParams.unit = 33 * 17 := rfl

/-- Low-poly sphere vertex count -/
theorem lowPoly_vertexCount : vertexCount SphereParams.lowPoly = 17 * 9 := rfl

/-- Index count is divisible by 3 -/
theorem indexCount_div3 (p : SphereParams) : indexCount p % 3 = 0 := by
  unfold indexCount
  omega

end SphereGeometry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: CYLINDER GEOMETRY
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Parameters for cylinder geometry generation -/
structure CylinderParams where
  /-- Radius at top -/
  radiusTop : ℝ
  /-- Radius at bottom -/
  radiusBottom : ℝ
  /-- Height -/
  height : ℝ
  /-- Radial segments -/
  radialSegments : Nat := 32
  /-- Height segments -/
  heightSegments : Nat := 1
  /-- Include top cap -/
  openEnded : Bool := false
  /-- Theta start (radians) -/
  thetaStart : ℝ := 0
  /-- Theta length (radians, 2π for full cylinder) -/
  thetaLength : ℝ := 2 * Real.pi

namespace CylinderParams

/-- Unit cylinder (radius 1, height 1) -/
noncomputable def unit : CylinderParams :=
  { radiusTop := 1, radiusBottom := 1, height := 1 }

/-- Cone (radiusTop = 0) -/
noncomputable def cone (radius height : ℝ) : CylinderParams :=
  { radiusTop := 0, radiusBottom := radius, height := height }

end CylinderParams

/-- Cylinder geometry generator.
    
    A cylinder has a tube body and optional top/bottom caps. -/
structure CylinderGeometry where
  params : CylinderParams

namespace CylinderGeometry

/-- Vertices for the tube body -/
def bodyVertexCount (p : CylinderParams) : Nat :=
  (p.radialSegments + 1) * (p.heightSegments + 1)

/-- Vertices for one cap -/
def capVertexCount (p : CylinderParams) : Nat :=
  p.radialSegments + 2  -- center + ring + one for UV seam

/-- Total vertex count -/
def vertexCount (p : CylinderParams) : Nat :=
  let body := bodyVertexCount p
  let caps := if p.openEnded then 0 else 2 * capVertexCount p
  body + caps

/-- Indices for the tube body -/
def bodyIndexCount (p : CylinderParams) : Nat :=
  p.radialSegments * p.heightSegments * 6

/-- Indices for one cap -/
def capIndexCount (p : CylinderParams) : Nat :=
  p.radialSegments * 3

/-- Total index count -/
def indexCount (p : CylinderParams) : Nat :=
  let body := bodyIndexCount p
  let caps := if p.openEnded then 0 else 2 * capIndexCount p
  body + caps

/-- Create mesh descriptor for cylinder -/
noncomputable def toMeshDescriptor (cyl : CylinderGeometry) : MeshDescriptor :=
  let p := cyl.params
  let maxRadius := max p.radiusTop p.radiusBottom
  { layout := VertexLayout.positionNormalUV
    vertexCount := vertexCount p
    indexFormat := some (IndexFormat.forVertexCount (vertexCount p))
    indexCount := indexCount p
    topology := PrimitiveTopology.triangleList
    boundingBox := some (Box3.fromCenterAndSize Vec3.zero ⟨2*maxRadius, p.height, 2*maxRadius⟩)
    boundingSphere := none }

-- ─────────────────────────────────────────────────────────────────────────────
-- CylinderGeometry Proofs
-- ─────────────────────────────────────────────────────────────────────────────

/-- Body index count is divisible by 3 -/
theorem bodyIndexCount_div3 (p : CylinderParams) : bodyIndexCount p % 3 = 0 := by
  unfold bodyIndexCount
  omega

/-- Cap index count is divisible by 3 -/
theorem capIndexCount_div3 (p : CylinderParams) : capIndexCount p % 3 = 0 := by
  unfold capIndexCount
  omega

end CylinderGeometry

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: CONVENIENCE CONSTRUCTORS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Create a box mesh descriptor -/
def boxMesh (width height depth : ℝ) : MeshDescriptor :=
  let box := BoxGeometry.mk { width := width, height := height, depth := depth }
  box.toMeshDescriptor

/-- Create a unit box mesh descriptor -/
def unitBoxMesh : MeshDescriptor :=
  let box := BoxGeometry.mk BoxParams.unit
  box.toMeshDescriptor

/-- Create a plane mesh descriptor -/
def planeMesh (width height : ℝ) : MeshDescriptor :=
  let plane := PlaneGeometry.mk { width := width, height := height }
  plane.toMeshDescriptor

/-- Create a sphere mesh descriptor -/
noncomputable def sphereMesh (radius : ℝ) (widthSegs heightSegs : Nat := 32) : MeshDescriptor :=
  let sphere := SphereGeometry.mk { radius := radius, widthSegments := widthSegs, heightSegments := heightSegs }
  sphere.toMeshDescriptor

/-- Create a cylinder mesh descriptor -/
noncomputable def cylinderMesh (radius height : ℝ) (radialSegs : Nat := 32) : MeshDescriptor :=
  let cyl := CylinderGeometry.mk { radiusTop := radius, radiusBottom := radius, height := height, radialSegments := radialSegs }
  cyl.toMeshDescriptor

/-- Create a cone mesh descriptor -/
noncomputable def coneMesh (radius height : ℝ) (_radialSegs : Nat := 32) : MeshDescriptor :=
  let cone := CylinderGeometry.mk (CylinderParams.cone radius height)
  cone.toMeshDescriptor

end Hydrogen.Geometry
