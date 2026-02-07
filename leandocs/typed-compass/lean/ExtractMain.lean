/-
  Main executable for extracting verified code

  Usage:
    lake exe extract elm      # emit Elm module
    lake exe extract python   # emit Python module  
    lake exe extract c        # emit C header
    lake exe extract all      # emit everything
-/

import TensorCore.Extract

open TensorCore.Extract

def writeFile (path : String) (content : String) : IO Unit := do
  IO.FS.writeFile path content
  IO.println s!"Wrote {path}"

def main (args : List String) : IO Unit := do
  match args with
  | ["elm"] =>
    IO.FS.createDirAll "extracted/elm/TensorCore"
    writeFile "extracted/elm/TensorCore/Types.elm" elmModule
  | ["python"] =>
    IO.FS.createDirAll "extracted/python"
    writeFile "extracted/python/types.py" pythonModule
  | ["c"] =>
    IO.FS.createDirAll "extracted/c"
    writeFile "extracted/c/tensor_core_types.h" cHeader
  | ["all"] =>
    IO.FS.createDirAll "extracted/elm/TensorCore"
    IO.FS.createDirAll "extracted/python"
    IO.FS.createDirAll "extracted/c"
    writeFile "extracted/elm/TensorCore/Types.elm" elmModule
    writeFile "extracted/python/types.py" pythonModule
    writeFile "extracted/c/tensor_core_types.h" cHeader
    IO.println "Done. All types extracted from proofs."
  | _ => do
    IO.println "Usage: lake exe extract <target>"
    IO.println ""
    IO.println "Targets:"
    IO.println "  elm     Extract verified Elm types + codecs"
    IO.println "  python  Extract verified Python dataclasses"
    IO.println "  c       Extract verified C structs"
    IO.println "  all     Extract everything"
    IO.println ""
    IO.println "Every extracted type has a proven roundtrip theorem in Lean."
    IO.println "The proofs guarantee the extraction is correct."
