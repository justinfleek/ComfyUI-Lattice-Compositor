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
-- NOTE: Takes Unit to avoid eager evaluation at module init time (sorry is a placeholder)
def unitCube (_ : Unit) : Mesh 8 12 := sorry  -- 8 vertices, 12 triangles (2 per face)

/-- Create a sphere with given subdivisions -/
def sphere (subdivisions : Nat) : Σ v t, Mesh v t := sorry

/-- 
  Create a box with given dimensions.
  Returns the mesh along with its computed vertex/triangle counts.
-/
-- NOTE: box already takes arguments, so it won't be evaluated at init time
def box (width height depth : Float) : Mesh 8 12 := sorry

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
-- NOTE: This is a function with arguments, so it won't be evaluated at init time
-- Implementation is a placeholder (sorry)
def Transform.compose (a b : Transform) : Transform := sorry

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
