/-
  Main executable for extracting verified code

  Usage:
    lake exe extract elm              # emit Elm module
    lake exe extract python           # emit Python module  
    lake exe extract c                # emit C header
    lake exe extract cpp23             # emit C++23 header
    lake exe extract typescript       # emit TypeScript types
    lake exe extract ffi-typescript   # emit TypeScript FFI bridge
    lake exe extract ffi-python      # emit Python FFI bridge
    lake exe extract all              # emit everything
-/

import TensorCore.Extract
import Color.Extract
import Color.FFICodegen
import Lattice.Codegen
import Lattice.CodegenCpp23
import Lattice.Extract

open TensorCore.Extract
open Color.Extract
open Color.FFICodegen
open Lattice.Codegen
open Lattice.CodegenCpp23
open Lattice.Extract

def writeFile (path : String) (content : String) : IO Unit := do
  IO.FS.createDirAll (System.FilePath.parent path)
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
  | ["cpp23"] =>
    IO.FS.createDirAll "extracted/cpp23"
    writeFile "extracted/cpp23/lattice_primitives.hpp" cpp23Header
    IO.println "Generated C++23 types from Lean proofs."
  | ["typescript"] =>
    IO.FS.createDirAll "extracted/typescript"
    writeFile "extracted/typescript/types.ts" typescriptTypesModule
    IO.println "Generated TypeScript types from Lean proofs."
  | ["haskell"] =>
    IO.FS.createDirAll "extracted/haskell/Lattice/Types"
    writeFile "extracted/haskell/Lattice/Types/Primitives.hs" haskellModule
    IO.println "Generated Haskell types from Lean proofs."
  | ["purescript"] =>
    IO.FS.createDirAll "extracted/purescript/Lattice/Types"
    writeFile "extracted/purescript/Lattice/Types/Primitives.purs" purescriptModule
    IO.println "Generated PureScript types from Lean proofs."
  | ["ffi-typescript"] =>
    IO.FS.createDirAll "extracted/typescript"
    writeFile "extracted/typescript/ffiBridge.ts" generateFFIBridge
    IO.println "Generated TypeScript FFI bridge from Lean definitions."
  | ["ffi-python"] =>
    IO.FS.createDirAll "extracted/python"
    writeFile "extracted/python/theme_generator_ffi.py" generatePythonBridge
    IO.println "Generated Python FFI bridge from Lean definitions."
  | ["theme"] =>
    -- Generate all theme-related code
    IO.FS.createDirAll "extracted/typescript"
    IO.FS.createDirAll "extracted/python"
    writeFile "extracted/typescript/types.ts" typescriptTypesModule
    writeFile "extracted/typescript/ffiBridge.ts" generateFFIBridge
    writeFile "extracted/python/theme_generator_ffi.py" generatePythonBridge
    IO.println "Generated all theme generation code from Lean."
  | ["all"] =>
    IO.FS.createDirAll "extracted/elm/TensorCore"
    IO.FS.createDirAll "extracted/python"
    IO.FS.createDirAll "extracted/c"
    IO.FS.createDirAll "extracted/typescript"
    writeFile "extracted/elm/TensorCore/Types.elm" elmModule
    writeFile "extracted/python/types.py" pythonModule
    writeFile "extracted/c/tensor_core_types.h" cHeader
    writeFile "extracted/typescript/types.ts" typescriptTypesModule
    writeFile "extracted/typescript/ffiBridge.ts" generateFFIBridge
    writeFile "extracted/python/theme_generator_ffi.py" generatePythonBridge
    IO.println "Done. All types extracted from proofs."
  | _ => do
    IO.println "Usage: lake exe extract <target>"
    IO.println ""
    IO.println "Targets:"
    IO.println "  elm              Extract verified Elm types + codecs"
    IO.println "  python           Extract verified Python dataclasses"
    IO.println "  c                Extract verified C structs"
    IO.println "  cpp23            Extract verified C++23 headers"
    IO.println "  typescript       Extract TypeScript type definitions"
    IO.println "  haskell          Extract Haskell types + JSON instances"
    IO.println "  purescript       Extract PureScript types + JSON instances"
    IO.println "  ffi-typescript   Generate TypeScript FFI bridge"
    IO.println "  ffi-python        Generate Python FFI bridge"
    IO.println "  theme            Generate all theme-related code"
    IO.println "  all              Extract everything"
    IO.println ""
    IO.println "Every extracted type has a proven roundtrip theorem in Lean."
    IO.println "The proofs guarantee the extraction is correct."
