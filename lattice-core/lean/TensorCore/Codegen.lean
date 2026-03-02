/-
  TensorCore.Codegen - Generate types for Python, Elm, and TypeScript from Lean

  This is the single source of truth. The Lean types ARE the spec.
  We use Lean's metaprogramming to emit code for other languages.

  The key insight: dependent types can't be fully expressed elsewhere,
  but we can generate runtime checks that enforce the same invariants.
-/

import Lean
import TensorCore.Basic
import TensorCore.Geometry

namespace TensorCore.Codegen

open Lean Meta Elab

/-! ## Schema Definition -/

/-- A field in a generated type -/
structure Field where
  name : String
  type : String
  leanType : String
  doc : Option String := none
  validation : Option String := none  -- Runtime check for langs that need it

/-- A type to generate -/
structure TypeDef where
  name : String
  doc : String
  fields : List Field
  deriving Repr

/-- An enum to generate -/
structure EnumDef where
  name : String
  doc : String
  variants : List (String × Option Int)  -- name, optional explicit value
  deriving Repr

/-! ## Type Registry -/

/-- All types we want to generate -/
def typeRegistry : List TypeDef := [
  { name := "Point3"
    doc := "A 3D point"
    fields := [
      { name := "x", type := "float", leanType := "Float", doc := some "X coordinate" },
      { name := "y", type := "float", leanType := "Float", doc := some "Y coordinate" },
      { name := "z", type := "float", leanType := "Float", doc := some "Z coordinate" }
    ]
  },
  { name := "Vec3"
    doc := "A 3D vector"
    fields := [
      { name := "x", type := "float", leanType := "Float" },
      { name := "y", type := "float", leanType := "Float" },
      { name := "z", type := "float", leanType := "Float" }
    ]
  },
  { name := "ColorRGB"
    doc := "RGB color with values in [0,1]"
    fields := [
      { name := "r", type := "float", leanType := "Float", 
        validation := some "0 <= r <= 1" },
      { name := "g", type := "float", leanType := "Float",
        validation := some "0 <= g <= 1" },
      { name := "b", type := "float", leanType := "Float",
        validation := some "0 <= b <= 1" }
    ]
  },
  { name := "Vertex"
    doc := "A mesh vertex with position and normal"
    fields := [
      { name := "position", type := "Point3", leanType := "Point3" },
      { name := "normal", type := "Vec3", leanType := "Vec3" }
    ]
  },
  { name := "Transform"
    doc := "4x4 transformation matrix (column-major)"
    fields := [
      { name := "matrix", type := "array<float>", leanType := "Array Float",
        validation := some "len(matrix) == 16" }
    ]
  },
  { name := "SceneObject"
    doc := "An object in the scene"
    fields := [
      { name := "name", type := "string", leanType := "String" },
      { name := "vertices", type := "array<Vertex>", leanType := "Array Vertex" },
      { name := "indices", type := "array<array<int>>", leanType := "Array (Array Nat)",
        validation := some "all(all(i < len(vertices) for i in tri) for tri in indices)" },
      { name := "material", type := "Material", leanType := "Material" },
      { name := "transform", type := "Transform", leanType := "Transform" }
    ]
  },
  { name := "Scene"
    doc := "A complete 3D scene"
    fields := [
      { name := "objects", type := "array<SceneObject>", leanType := "Array SceneObject" },
      { name := "ambientLight", type := "ColorRGB", leanType := "ColorRGB" },
      { name := "directionalLight", type := "optional<DirectionalLight>", 
        leanType := "Option DirectionalLight" }
    ]
  }
]

def enumRegistry : List EnumDef := [
  { name := "DType"
    doc := "Tensor data types"
    variants := [("F32", some 0), ("F16", some 1), ("BF16", some 2), ("NVFP4", some 3)]
  },
  { name := "MaterialType"
    doc := "Material types for rendering"
    variants := [("Color", none), ("Matte", none), ("Metal", none), ("PBR", none)]
  }
]

/-! ## Python Generator -/

def genPythonField (f : Field) : String :=
  let pyType := match f.type with
    | "float" => "float"
    | "int" => "int"
    | "string" => "str"
    | "bool" => "bool"
    | t => if t.startsWith "array<" then s!"list[{t.drop 6 |>.dropRight 1}]"
           else if t.startsWith "optional<" then s!"{t.drop 9 |>.dropRight 1} | None"
           else t
  s!"    {f.name}: {pyType}"

def genPythonType (t : TypeDef) : String :=
  let fields := t.fields.map genPythonField |> String.intercalate "\n"
  let validators := t.fields.filterMap fun f =>
    f.validation.map fun v => s!"        assert {v}, \"{f.name} validation failed\""
  let validatorCode := if validators.isEmpty then "" else
    "\n\n    def __post_init__(self):\n" ++ (validators.map (· ++ "\n") |> String.join)
  s!"@dataclass
class {t.name}:
    \"\"\"{t.doc}\"\"\"
{fields}{validatorCode}
"

def genPythonEnum (e : EnumDef) : String :=
  let variants := e.variants.map fun (name, val) =>
    match val with
    | some v => s!"    {name} = {v}"
    | none => s!"    {name} = auto()"
  s!"class {e.name}(Enum):
    \"\"\"{e.doc}\"\"\"
{variants.map (· ++ "\n") |> String.join}"

def generatePython : String :=
  let header := "\"\"\"
Auto-generated from Lean type definitions.
DO NOT EDIT - regenerate with `lake run codegen python`

This file mirrors the Lean types in TensorCore.Geometry
The validation checks enforce the same invariants that
Lean proves at compile time.
\"\"\"

from dataclasses import dataclass
from enum import Enum, auto
from typing import Optional

"
  let enums := enumRegistry.map genPythonEnum |> String.intercalate "\n\n"
  let types := typeRegistry.map genPythonType |> String.intercalate "\n\n"
  header ++ enums ++ "\n\n" ++ types

/-! ## Elm Generator -/

def toElmType (t : String) : String := match t with
  | "float" => "Float"
  | "int" => "Int"
  | "string" => "String"
  | "bool" => "Bool"
  | t => if t.startsWith "array<" then s!"List {toElmType (t.drop 6 |>.dropRight 1)}"
         else if t.startsWith "optional<" then s!"Maybe {toElmType (t.drop 9 |>.dropRight 1)}"
         else t

def genElmField (f : Field) : String :=
  s!"    {f.name} : {toElmType f.type}"

def genElmType (t : TypeDef) : String :=
  let fields := t.fields.map genElmField |> String.intercalate "\n    , "
  s!"{{-| {t.doc} -}}
type alias {t.name} =
    {{ {fields}
    }}
"

def genElmEnum (e : EnumDef) : String :=
  let variants := e.variants.map (·.1) |> String.intercalate "\n    | "
  s!"{{-| {e.doc} -}}
type {e.name}
    = {variants}
"

def generateElm : String :=
  let header := """module Generated.Types exposing (..)

{-| Auto-generated from Lean type definitions.
DO NOT EDIT - regenerate with `lake run codegen elm`

This module mirrors the Lean types in TensorCore.Geometry
-}


"""
  let enums := enumRegistry.map genElmEnum |> String.intercalate "\n\n"
  let types := typeRegistry.map genElmType |> String.intercalate "\n\n"
  header ++ enums ++ "\n\n" ++ types

/-! ## TypeScript Generator (for potential future use) -/

def toTsType (t : String) : String := match t with
  | "float" => "number"
  | "int" => "number"
  | "string" => "string"
  | "bool" => "boolean"
  | t => if t.startsWith "array<" then s!"{toTsType (t.drop 6 |>.dropRight 1)}[]"
         else if t.startsWith "optional<" then s!"{toTsType (t.drop 9 |>.dropRight 1)} | null"
         else t

def genTsField (f : Field) : String :=
  s!"  {f.name}: {toTsType f.type};"

def genTsType (t : TypeDef) : String :=
  let fields := t.fields.map genTsField |> String.intercalate "\n"
  s!"/** {t.doc} */
export interface {t.name} {{
{fields}
}}
"

def genTsEnum (e : EnumDef) : String :=
  let variants := e.variants.map fun (name, val) =>
    match val with
    | some v => s!"  {name} = {v},"
    | none => s!"  {name},"
  s!"/** {e.doc} */
export enum {e.name} {{
{variants.map (· ++ "\n") |> String.join}}}
"

def generateTypeScript : String :=
  let header := """/**
 * Auto-generated from Lean type definitions.
 * DO NOT EDIT - regenerate with `lake run codegen typescript`
 */

"""
  let enums := enumRegistry.map genTsEnum |> String.intercalate "\n\n"
  let types := typeRegistry.map genTsType |> String.intercalate "\n\n"
  header ++ enums ++ "\n\n" ++ types

/-! ## JSON Schema Generator -/

def toJsonSchemaType (t : String) : String := match t with
  | "float" => "\"type\": \"number\""
  | "int" => "\"type\": \"integer\""
  | "string" => "\"type\": \"string\""
  | "bool" => "\"type\": \"boolean\""
  | t => if t.startsWith "array<" then 
           s!"\"type\": \"array\", \"items\": {{ {toJsonSchemaType (t.drop 6 |>.dropRight 1)} }}"
         else s!"\"$ref\": \"#/definitions/{t}\""

def genJsonSchemaField (f : Field) : String :=
  s!"\"{f.name}\": {{ {toJsonSchemaType f.type} }}"

def genJsonSchemaType (t : TypeDef) : String :=
  let fields := t.fields.map genJsonSchemaField |> String.intercalate ",\n      "
  let required := t.fields.map (s!"\"{·.name}\"") |> String.intercalate ", "
  s!"\"{t.name}\": {{
    \"type\": \"object\",
    \"description\": \"{t.doc}\",
    \"properties\": {{
      {fields}
    }},
    \"required\": [{required}]
  }}"

def generateJsonSchema : String :=
  let defs := typeRegistry.map genJsonSchemaType |> String.intercalate ",\n  "
  s!"{{
  \"$schema\": \"http://json-schema.org/draft-07/schema#\",
  \"title\": \"TensorCore Types\",
  \"description\": \"Auto-generated from Lean type definitions\",
  \"definitions\": {{
  {defs}
  }}
}}"

/-! ## CLI Interface -/

def usage : String := "
Usage: lake run codegen <target>

Targets:
  python      Generate Python dataclasses
  elm         Generate Elm type aliases
  typescript  Generate TypeScript interfaces
  jsonschema  Generate JSON Schema
  all         Generate all targets

Output goes to generated/<target>/
"

end TensorCore.Codegen
