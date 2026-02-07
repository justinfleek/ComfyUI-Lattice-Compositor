import Compass.Core

/-!
  What-if analysis
  Maps to ultimate-cmo-feature-spec.md
-/

namespace Compass.Features

open Compass.Core

structure WhatIfAnalysis where
  id : String
  title : String
  description : String
  created_at : String
  updated_at : String
  deriving Repr

def WhatIfAnalysis.toJson (f : WhatIfAnalysis) : Json := .obj [
  ("id", .str f.id),
  ("title", .str f.title),
  ("description", .str f.description),
  ("created_at", .str f.created_at),
  ("updated_at", .str f.updated_at)
]

def WhatIfAnalysis.fromJson (j : Json) : Option WhatIfAnalysis := do
  let id ← Json.fieldN 0 j >>= Json.asString
  let title ← Json.fieldN 1 j >>= Json.asString
  let description ← Json.fieldN 2 j >>= Json.asString
  let created_at ← Json.fieldN 3 j >>= Json.asString
  let updated_at ← Json.fieldN 4 j >>= Json.asString
  pure ⟨id, title, description, created_at, updated_at⟩

theorem WhatIfAnalysis.roundtrip (f : WhatIfAnalysis) :
    WhatIfAnalysis.fromJson (WhatIfAnalysis.toJson f) = some f := by
  cases f; rfl

instance : Extractable WhatIfAnalysis where
  encode := WhatIfAnalysis.toJson
  decode := WhatIfAnalysis.fromJson
  roundtrip := WhatIfAnalysis.roundtrip

end Compass.Features
