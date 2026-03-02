import TensorCore.Basic
import TensorCore.Tensor
import TensorCore.Ops
import TensorCore.Graph
import TensorCore.FFI

def main : IO Unit := do
  IO.println "TensorCore - Type-safe tensors for the discerning droid"
  IO.println ""
  IO.println "This library provides:"
  IO.println "  • Dependent types for tensor shapes"
  IO.println "  • Compile-time shape checking"
  IO.println "  • Type-safe computation graphs"
  IO.println "  • FFI boundary with runtime validation"
  IO.println ""
  IO.println "The droids can't cheat here."
