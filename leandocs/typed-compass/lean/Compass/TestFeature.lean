import Compass.Core

namespace COMPASS.Features

open Compass.Core

structure BlogPost where
  id : String
  title : String
  content : String
  author_id : String
  deriving Repr

def BlogPost.toJson (bp : BlogPost) : Json := .obj [
  ("id", .str bp.id),
  ("title", .str bp.title),
  ("content", .str bp.content),
  ("author_id", .str bp.author_id)
]

def BlogPost.fromJson (j : Json) : Option BlogPost := do
  let id ← (Json.fieldN 0 j) >>= Json.asString
  let title ← (Json.fieldN 1 j) >>= Json.asString
  let content ← (Json.fieldN 2 j) >>= Json.asString
  let author_id ← (Json.fieldN 3 j) >>= Json.asString
  pure ⟨id, title, content, author_id⟩

theorem BlogPost.roundtrip (bp : BlogPost) :
    BlogPost.fromJson (BlogPost.toJson bp) = some bp := by
  cases bp; unfold BlogPost.toJson BlogPost.fromJson; simp

instance : Extractable BlogPost where
  encode := BlogPost.toJson
  decode := BlogPost.fromJson
  roundtrip := BlogPost.roundtrip

end COMPASS.Features
