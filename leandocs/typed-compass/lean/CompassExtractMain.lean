/-
  Main executable for extracting verified COMPASS types

  Usage:
    lake exe compass-extract purescript  # emit PureScript module (PRIMARY)
    lake exe compass-extract python      # emit Python module
    lake exe compass-extract elm         # emit Elm module (legacy)
    lake exe compass-extract all         # emit everything
-/

import Compass
import Compass.Emit

open Compass.Emit

def writeFile (path : String) (content : String) : IO Unit := do
  IO.FS.writeFile path content
  IO.println s!"Wrote {path}"

def main (args : List String) : IO Unit := do
  match args with
  | ["purescript"] =>
    IO.FS.createDirAll "extracted/purescript/Compass"
    writeFile "extracted/purescript/Compass/Types.purs" pureScriptModule
  | ["python"] =>
    IO.FS.createDirAll "extracted/python"
    writeFile "extracted/python/compass_types.py" pythonModule
  | ["elm"] =>
    IO.FS.createDirAll "extracted/elm/Compass"
    writeFile "extracted/elm/Compass/Types.elm" elmModule
  | ["all"] =>
    IO.FS.createDirAll "extracted/purescript/Compass"
    IO.FS.createDirAll "extracted/python"
    IO.FS.createDirAll "extracted/elm/Compass"
    writeFile "extracted/purescript/Compass/Types.purs" pureScriptModule
    writeFile "extracted/python/compass_types.py" pythonModule
    writeFile "extracted/elm/Compass/Types.elm" elmModule
    IO.println "Done. All COMPASS types extracted from proofs."
  | _ => do
    IO.println "Usage: lake exe compass-extract <target>"
    IO.println ""
    IO.println "Targets:"
    IO.println "  purescript  Extract verified PureScript types + codecs (PRIMARY)"
    IO.println "  python      Extract verified Python dataclasses"
    IO.println "  elm         Extract verified Elm types + codecs (legacy)"
    IO.println "  all         Extract everything"
    IO.println ""
    IO.println "Every extracted type has a proven roundtrip theorem in Lean."
    IO.println "The proofs guarantee the extraction is correct."
    IO.println ""
    IO.println "Types extracted:"
    IO.println "  - Permission (21 variants)"
    IO.println "  - Role (4 variants)"
    IO.println "  - User"
    IO.println "  - Session"
    IO.println "  - JobStatus (7 variants)"
