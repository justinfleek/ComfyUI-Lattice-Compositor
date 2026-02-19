/-
  TensorCore.Geometry - Type-safe 3D geometry primitives

  These types mirror what elm-3d-scene uses, but with dependent types
  ensuring correctness. The Lean side computes transformations,
  validates meshes, and the Elm side just renders.

  Key insight: mesh indices must be valid for the vertex array.
  This is easy to mess up, impossible to mess up here.
-/

import TensorCore.Basic

namespace TensorCore.Geometry

/-! ## Basic 3D types -/

/-- A 3D point with named coordinates -/
structure Point3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- A 3D vector -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- A normalized direction (unit vector) -/
structure Direction3 where
  vec : Vec3
  isUnit : vec.x^2 + vec.y^2 + vec.z^2 = 1  -- proof it's normalized!

/-- RGB color with values in [0,1] -/
structure Color where
  r : Float
  g : Float
  b : Float
  valid : 0 ≤ r ∧ r ≤ 1 ∧ 0 ≤ g ∧ g ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1

/-- Color without proof (for FFI) -/
structure ColorRGB where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited

/-! ## Mesh types with index safety -/

/--
  A vertex with position and normal.
  The normal should be a unit vector but we relax that for the demo.
-/
structure Vertex where
  position : Point3
  normal : Vec3
  deriving Repr

/--
  A triangle index - three indices into a vertex array.

  The key type safety: these indices must be valid!
  `n` is the number of vertices in the mesh.
-/
structure TriangleIndex (n : Nat) where
  i0 : Fin n
  i1 : Fin n
  i2 : Fin n

/--
  A mesh with `v` vertices and `t` triangles.

  This is the key type: you cannot construct a mesh with invalid indices.
  The indices are bounded by the vertex count at the type level.
-/
structure Mesh (v : Nat) (t : Nat) where
  vertices : Array Vertex
  triangles : Array (TriangleIndex v)
  vertexCount : vertices.size = v
  triangleCount : triangles.size = t

/-! ## Primitive constructors -/

/-- Create a unit cube centered at origin -/
-- NOTE: Takes Unit to avoid eager evaluation at module init time
-- Implementation detail: generates 8 vertices and 12 triangles (2 per face)
def unitCube (_ : Unit) : Mesh 8 12 :=
  -- 8 vertices of a unit cube centered at origin
  let vertices := Array.mk [
    ⟨⟨-0.5, -0.5, -0.5⟩, ⟨0, 0, -1⟩⟩,  -- 0: bottom-left-back
    ⟨⟨0.5, -0.5, -0.5⟩, ⟨0, 0, -1⟩⟩,   -- 1: bottom-right-back
    ⟨⟨0.5, 0.5, -0.5⟩, ⟨0, 0, -1⟩⟩,    -- 2: top-right-back
    ⟨⟨-0.5, 0.5, -0.5⟩, ⟨0, 0, -1⟩⟩,  -- 3: top-left-back
    ⟨⟨-0.5, -0.5, 0.5⟩, ⟨0, 0, 1⟩⟩,   -- 4: bottom-left-front
    ⟨⟨0.5, -0.5, 0.5⟩, ⟨0, 0, 1⟩⟩,    -- 5: bottom-right-front
    ⟨⟨0.5, 0.5, 0.5⟩, ⟨0, 0, 1⟩⟩,     -- 6: top-right-front
    ⟨⟨-0.5, 0.5, 0.5⟩, ⟨0, 0, 1⟩⟩     -- 7: top-left-front
  ]
  -- 12 triangles (2 per face, 6 faces)
  let triangles := Array.mk [
    -- Back face (z = -0.5)
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩⟩,
    -- Front face (z = 0.5)
    ⟨⟨4, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩⟩,
    ⟨⟨4, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩⟩,
    -- Right face (x = 0.5)
    ⟨⟨1, by decide⟩, ⟨6, by decide⟩, ⟨2, by decide⟩⟩,
    ⟨⟨1, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩⟩,
    -- Left face (x = -0.5)
    ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨7, by decide⟩, ⟨4, by decide⟩⟩,
    -- Top face (y = 0.5)
    ⟨⟨3, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩⟩,
    ⟨⟨3, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩⟩,
    -- Bottom face (y = -0.5)
    ⟨⟨0, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨5, by decide⟩, ⟨1, by decide⟩⟩
  ]
  ⟨vertices, triangles, by rfl, by rfl⟩

/-- Create a sphere with given subdivisions -/
-- Implementation detail: generates sphere mesh via subdivision
-- For now, returns a simple icosahedron approximation
def sphere (subdivisions : Nat) : Σ v t, Mesh v t :=
  -- Simple icosahedron (12 vertices, 20 triangles)
  -- This is a placeholder - full sphere generation with subdivisions is complex
  let vertices := Array.mk [
    -- Icosahedron vertices (simplified)
    ⟨⟨0, 0.5, 0⟩, ⟨0, 1, 0⟩⟩,
    ⟨⟨0.447, 0.223, 0⟩, ⟨0.447, 0.223, 0⟩⟩,
    ⟨⟨0.138, 0.223, 0.425⟩, ⟨0.138, 0.223, 0.425⟩⟩,
    ⟨⟨-0.361, 0.223, 0.263⟩, ⟨-0.361, 0.223, 0.263⟩⟩,
    ⟨⟨-0.361, 0.223, -0.263⟩, ⟨-0.361, 0.223, -0.263⟩⟩,
    ⟨⟨0.138, 0.223, -0.425⟩, ⟨0.138, 0.223, -0.425⟩⟩,
    ⟨⟨0.361, -0.223, 0.263⟩, ⟨0.361, -0.223, 0.263⟩⟩,
    ⟨⟨-0.138, -0.223, 0.425⟩, ⟨-0.138, -0.223, 0.425⟩⟩,
    ⟨⟨-0.447, -0.223, 0⟩, ⟨-0.447, -0.223, 0⟩⟩,
    ⟨⟨-0.138, -0.223, -0.425⟩, ⟨-0.138, -0.223, -0.425⟩⟩,
    ⟨⟨0.361, -0.223, -0.263⟩, ⟨0.361, -0.223, -0.263⟩⟩,
    ⟨⟨0, -0.5, 0⟩, ⟨0, -1, 0⟩⟩
  ]
  let triangles := Array.mk [
    -- Top cap
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨5, by decide⟩, ⟨1, by decide⟩⟩,
    -- Middle band
    ⟨⟨1, by decide⟩, ⟨6, by decide⟩, ⟨2, by decide⟩⟩,
    ⟨⟨2, by decide⟩, ⟨7, by decide⟩, ⟨3, by decide⟩⟩,
    ⟨⟨3, by decide⟩, ⟨8, by decide⟩, ⟨4, by decide⟩⟩,
    ⟨⟨4, by decide⟩, ⟨9, by decide⟩, ⟨5, by decide⟩⟩,
    ⟨⟨5, by decide⟩, ⟨10, by decide⟩, ⟨1, by decide⟩⟩,
    ⟨⟨2, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩⟩,
    ⟨⟨3, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩⟩,
    ⟨⟨4, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩⟩,
    ⟨⟨5, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩⟩,
    ⟨⟨1, by decide⟩, ⟨10, by decide⟩, ⟨6, by decide⟩⟩,
    -- Bottom cap
    ⟨⟨11, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩⟩,
    ⟨⟨11, by decide⟩, ⟨8, by decide⟩, ⟨7, by decide⟩⟩,
    ⟨⟨11, by decide⟩, ⟨9, by decide⟩, ⟨8, by decide⟩⟩,
    ⟨⟨11, by decide⟩, ⟨10, by decide⟩, ⟨9, by decide⟩⟩,
    ⟨⟨11, by decide⟩, ⟨6, by decide⟩, ⟨10, by decide⟩⟩
  ]
  ⟨12, 20, ⟨vertices, triangles, by rfl, by rfl⟩⟩

/--
  Create a box with given dimensions.
  Returns the mesh along with its computed vertex/triangle counts.
-/
-- Implementation detail: generates box mesh with given dimensions
def box (width height depth : Float) : Mesh 8 12 :=
  let w2 := width / 2
  let h2 := height / 2
  let d2 := depth / 2
  -- 8 vertices of a box centered at origin
  let vertices := Array.mk [
    ⟨⟨-w2, -h2, -d2⟩, ⟨0, 0, -1⟩⟩,  -- 0: bottom-left-back
    ⟨⟨w2, -h2, -d2⟩, ⟨0, 0, -1⟩⟩,    -- 1: bottom-right-back
    ⟨⟨w2, h2, -d2⟩, ⟨0, 0, -1⟩⟩,     -- 2: top-right-back
    ⟨⟨-w2, h2, -d2⟩, ⟨0, 0, -1⟩⟩,   -- 3: top-left-back
    ⟨⟨-w2, -h2, d2⟩, ⟨0, 0, 1⟩⟩,    -- 4: bottom-left-front
    ⟨⟨w2, -h2, d2⟩, ⟨0, 0, 1⟩⟩,     -- 5: bottom-right-front
    ⟨⟨w2, h2, d2⟩, ⟨0, 0, 1⟩⟩,      -- 6: top-right-front
    ⟨⟨-w2, h2, d2⟩, ⟨0, 0, 1⟩⟩      -- 7: top-left-front
  ]
  -- 12 triangles (2 per face, 6 faces) - same structure as unitCube
  let triangles := Array.mk [
    -- Back face
    ⟨⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩⟩,
    -- Front face
    ⟨⟨4, by decide⟩, ⟨6, by decide⟩, ⟨5, by decide⟩⟩,
    ⟨⟨4, by decide⟩, ⟨7, by decide⟩, ⟨6, by decide⟩⟩,
    -- Right face
    ⟨⟨1, by decide⟩, ⟨6, by decide⟩, ⟨2, by decide⟩⟩,
    ⟨⟨1, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩⟩,
    -- Left face
    ⟨⟨0, by decide⟩, ⟨3, by decide⟩, ⟨7, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨7, by decide⟩, ⟨4, by decide⟩⟩,
    -- Top face
    ⟨⟨3, by decide⟩, ⟨2, by decide⟩, ⟨6, by decide⟩⟩,
    ⟨⟨3, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩⟩,
    -- Bottom face
    ⟨⟨0, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩⟩,
    ⟨⟨0, by decide⟩, ⟨5, by decide⟩, ⟨1, by decide⟩⟩
  ]
  ⟨vertices, triangles, by rfl, by rfl⟩

/-! ## Transformations -/

/-- 4x4 transformation matrix -/
structure Transform where
  m : Array Float  -- 16 elements, column-major
  valid : m.size = 16

/-- Identity transform -/
def Transform.identity : Transform :=
  ⟨#[1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1], by rfl⟩

/-- Translation -/
def Transform.translate (dx dy dz : Float) : Transform :=
  ⟨#[1,0,0,0, 0,1,0,0, 0,0,1,0, dx,dy,dz,1], by rfl⟩

/-- Uniform scale -/
def Transform.scale (s : Float) : Transform :=
  ⟨#[s,0,0,0, 0,s,0,0, 0,0,s,0, 0,0,0,1], by rfl⟩

/-- Rotation around Y axis -/
def Transform.rotateY (angle : Float) : Transform :=
  let c := Float.cos angle
  let s := Float.sin angle
  ⟨#[c,0,s,0, 0,1,0,0, -s,0,c,0, 0,0,0,1], by rfl⟩

/-- Compose transforms (matrix multiply) -/
-- Column-major 4x4 matrix multiplication
-- This is a pure Lean implementation (not FFI) so should be proven
def Transform.compose (a b : Transform) : Transform :=
  -- Matrix multiplication: C[i,j] = sum_k A[i,k] * B[k,j]
  -- For column-major: data[k*4 + i] is element at row i, col k
  let resultData := (List.range 16).map fun idx =>
    let col := idx / 4
    let row := idx % 4
    (List.range 4).foldl (fun sum k =>
      let aIdx := k * 4 + row
      let bIdx := col * 4 + k
      sum + a.m[aIdx]! * b.m[bIdx]!
    ) 0.0
  have h_len : resultData.length = 16 := List.length_map ..
  ⟨Array.mk resultData, by rw [← h_len]; rfl⟩

/-! ## Scene graph types -/

/-- Material for rendering -/
inductive Material where
  | color : ColorRGB → Material
  | matte : ColorRGB → Material
  | metal : ColorRGB → Float → Material  -- color, roughness
  | pbr : ColorRGB → Float → Float → Material  -- color, metallic, roughness

/--
  A scene object: geometry + material + transform.

  The mesh dimensions are existentially quantified - the scene
  doesn't care about exact counts, just that they're valid.
-/
structure SceneObject where
  name : String
  mesh : Σ v t, Mesh v t
  material : Material
  transform : Transform

/-- A complete scene -/
structure Scene where
  objects : Array SceneObject
  ambientLight : ColorRGB
  directionalLight : Option (Vec3 × ColorRGB)  -- direction, color

/-! ## Scene building DSL -/

/-- Empty scene -/
def Scene.empty : Scene := {
  objects := #[]
  ambientLight := ⟨0.1, 0.1, 0.1⟩
  directionalLight := none
}

/-- Add an object to the scene -/
def Scene.addObject (scene : Scene) (obj : SceneObject) : Scene :=
  { scene with objects := scene.objects.push obj }

/-- Set ambient light -/
def Scene.withAmbient (scene : Scene) (color : ColorRGB) : Scene :=
  { scene with ambientLight := color }

/-- Set directional light -/
def Scene.withDirectionalLight (scene : Scene) (dir : Vec3) (color : ColorRGB) : Scene :=
  { scene with directionalLight := some (dir, color) }

end TensorCore.Geometry
