/-!
  Blog post outline generation

  Maps to ultimate-cmo-feature-spec.md
-/

import Compass.Core

namespace COMPASS.Features

open Compass.Core

structure BlogPostOutlineGeneration where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def BlogPostOutlineGeneration.toJson (f : BlogPostOutlineGeneration) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def BlogPostOutlineGeneration.fromJson (j : Json) : Option BlogPostOutlineGeneration := do
  let id ← (Json.fieldN 0 j) >>= Json.asString
  let title ← (Json.fieldN 1 j) >>= Json.asString
  let description ← (Json.fieldN 2 j) >>= Json.asString
  let created_at ← (Json.fieldN 3 j) >>= Json.asString
  let updated_at ← (Json.fieldN 4 j) >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem BlogPostOutlineGeneration.roundtrip (f : BlogPostOutlineGeneration) :
    BlogPostOutlineGeneration.fromJson (BlogPostOutlineGeneration.toJson f) = some f := by
  cases f; unfold BlogPostOutlineGeneration.toJson BlogPostOutlineGeneration.fromJson; simp

instance : Extractable BlogPostOutlineGeneration where
  encode := BlogPostOutlineGeneration.toJson
  decode := BlogPostOutlineGeneration.fromJson
  roundtrip := BlogPostOutlineGeneration.roundtrip

end COMPASS.Features
