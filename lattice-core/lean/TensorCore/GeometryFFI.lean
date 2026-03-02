/-
  TensorCore.GeometryFFI - Export geometry to Elm-consumable JSON

  The Lean side does all the heavy lifting (transforms, mesh generation,
  validation). The Elm side just receives pre-validated JSON and renders.
-/

import TensorCore.Geometry

namespace TensorCore.GeometryFFI

open TensorCore.Geometry

/-! ## JSON serialization for Elm -/

/-- Serialize a Point3 to JSON array -/
def Point3.toJson (p : Point3) : String :=
  s!"[{p.x}, {p.y}, {p.z}]"

/-- Serialize a Vec3 to JSON array -/
def Vec3.toJson (v : Vec3) : String :=
  s!"[{v.x}, {v.y}, {v.z}]"

/-- Serialize a ColorRGB to JSON -/
def ColorRGB.toJson (c : ColorRGB) : String :=
  s!"\{\"r\": {c.r}, \"g\": {c.g}, \"b\": {c.b}}"

/-- Serialize a Vertex to JSON -/
def Vertex.toJson (v : Vertex) : String :=
  s!"\{\"position\": {v.position.toJson}, \"normal\": {v.normal.toJson}}"

/-- Serialize transform matrix to JSON array (for Elm's Mat4) -/
def Transform.toJson (t : Transform) : String :=
  let vals := t.m.toList.map toString |> String.intercalate ", "
  s!"[{vals}]"

/-- Serialize material to JSON -/
def Material.toJson : Material → String
  | .color c => s!"\{\"type\": \"color\", \"color\": {c.toJson}}"
  | .matte c => s!"\{\"type\": \"matte\", \"color\": {c.toJson}}"
  | .metal c r => s!"\{\"type\": \"metal\", \"color\": {c.toJson}, \"roughness\": {r}}"
  | .pbr c m r => s!"\{\"type\": \"pbr\", \"color\": {c.toJson}, \"metallic\": {m}, \"roughness\": {r}}"

/-- 
  Serialize a complete scene to JSON for Elm.
  
  This flattens the typed mesh into arrays that Elm/WebGL can consume.
-/
def Scene.toJson (scene : Scene) : String :=
  let objectsJson := scene.objects.toList.map fun obj =>
    -- Flatten mesh vertices and indices
    let ⟨v, t, mesh⟩ := obj.mesh
    let vertices := mesh.vertices.toList.map Vertex.toJson |> String.intercalate ", "
    let indices := mesh.triangles.toList.map fun tri =>
      s!"[{tri.i0.val}, {tri.i1.val}, {tri.i2.val}]"
    let indicesJson := indices.intercalate ", "
    
    s!"\{
      \"name\": \"{obj.name}\",
      \"vertices\": [{vertices}],
      \"indices\": [{indicesJson}],
      \"material\": {obj.material.toJson},
      \"transform\": {obj.transform.toJson}
    }"
  
  let objectsStr := objectsJson.intercalate ",\n    "
  let dirLightJson := match scene.directionalLight with
    | none => "null"
    | some (dir, color) => s!"\{\"direction\": {dir.toJson}, \"color\": {color.toJson}}"
  
  s!"\{
  \"objects\": [
    {objectsStr}
  ],
  \"ambientLight\": {scene.ambientLight.toJson},
  \"directionalLight\": {dirLightJson}
}"

/-! ## Example scene builder (demonstrates the API) -/

/-- Create a demo scene with a few objects -/
-- NOTE: This is a function (takes Unit) to avoid evaluating unitCube at module init time
-- unitCube is currently a sorry placeholder
def demoScene (_ : Unit) : Scene :=
  let red : ColorRGB := ⟨0.8, 0.2, 0.2⟩
  let blue : ColorRGB := ⟨0.2, 0.2, 0.8⟩
  let white : ColorRGB := ⟨0.9, 0.9, 0.9⟩
  
  Scene.empty
    |> Scene.withAmbient ⟨0.1, 0.1, 0.15⟩
    |> Scene.withDirectionalLight ⟨1, -1, -1⟩ white
    |> Scene.addObject {
        name := "RedCube"
        mesh := ⟨8, 12, unitCube ()⟩
        material := .matte red
        transform := Transform.translate (-2) 0 0
      }
    |> Scene.addObject {
        name := "BlueCube"
        mesh := ⟨8, 12, unitCube ()⟩
        material := .metal blue 0.3
        transform := Transform.translate 2 0 0
      }

/-! ## FFI exports -/

/-- Export scene creation -/
@[export geometry_create_scene]
def createScene : IO String := do
  pure (demoScene ()).toJson

/-- Export mesh generation -/
-- NOTE: This is lazy (IO) to avoid evaluating unitCube at module init time
@[export geometry_create_cube]
def createCube (x y z : Float) (r g b : Float) : IO String := do
  let obj : SceneObject := {
    name := "Cube"
    mesh := ⟨8, 12, unitCube ()⟩  -- unitCube evaluated only when this function is called
    material := .matte ⟨r, g, b⟩
    transform := Transform.translate x y z
  }
  pure $ s!"\{
    \"vertices\": [],
    \"indices\": [],
    \"material\": {obj.material.toJson},
    \"transform\": {obj.transform.toJson}
  }"

end TensorCore.GeometryFFI
