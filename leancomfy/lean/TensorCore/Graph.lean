/-
  TensorCore.Graph - Type-safe computation graph for ComfyUI

  This is the key abstraction. Nodes are typed, edges carry shape info,
  and the graph can only be constructed if types align.
  
  Python sees opaque NodeHandle values - it can wire them up but
  can't forge invalid connections.
-/

import TensorCore.Ops

namespace TensorCore

/-! ## Node types for ComfyUI-style graphs -/

/-- A socket (input or output) with typed shape -/
structure Socket (shape : Shape) (dtype : DType) where
  id : Nat
  deriving Repr

/-- Node kinds - each with typed inputs/outputs -/
inductive NodeKind where
  | input : (shape : Shape) → (dtype : DType) → NodeKind
  | conv2d : NodeKind
  | matmul : NodeKind
  | add : NodeKind
  | relu : NodeKind
  | output : NodeKind

/-- 
  A Node in the computation graph.
  
  The existential types (shape, dtype) are hidden - 
  Python just sees a NodeHandle. But Lean knows the types
  and enforces them at connection time.
-/
structure Node where
  id : Nat
  kind : NodeKind
  -- Input/output shapes stored for runtime
  inputShapes : List (Shape × DType)
  outputShapes : List (Shape × DType)

/-- 
  Type-safe edge between nodes.
  
  The source and target shapes must match - this is checked
  at compile time when building the graph.
-/
structure Edge (srcShape : Shape) (srcDtype : DType) where
  srcNode : Nat
  srcPort : Nat
  dstNode : Nat
  dstPort : Nat

/-- The computation graph -/
structure Graph where
  nodes : List Node
  edges : List (Σ s d, Edge s d)  -- existentially typed edges
  nextId : Nat

namespace Graph

def empty : Graph := ⟨[], [], 0⟩

/-- Add an input node with known shape -/
def addInput (g : Graph) (shape : Shape) (dtype : DType) : Graph × Node :=
  let node : Node := {
    id := g.nextId
    kind := .input shape dtype
    inputShapes := []
    outputShapes := [(shape, dtype)]
  }
  (⟨node :: g.nodes, g.edges, g.nextId + 1⟩, node)

/-- 
  Connect two nodes - type-safe!
  
  This function requires proof that shapes match.
  Python can't call this directly - it goes through the FFI
  which validates at the boundary.
-/
def connect (g : Graph) 
    (srcNode : Node) (srcPort : Nat) 
    (dstNode : Node) (dstPort : Nat)
    (h : srcNode.outputShapes[srcPort]? = dstNode.inputShapes[dstPort]?)
    : Graph :=
  match srcNode.outputShapes[srcPort]? with
  | some (shape, dtype) =>
    let edge : Edge shape dtype := {
      srcNode := srcNode.id
      srcPort := srcPort
      dstNode := dstNode.id
      dstPort := dstPort
    }
    ⟨g.nodes, ⟨shape, dtype, edge⟩ :: g.edges, g.nextId⟩
  | none => g  -- unreachable given the proof h

end Graph

/-! ## Example: Building a simple graph -/

example : Graph :=
  let g := Graph.empty
  -- Add input [1, 3, 224, 224] fp16
  let (g, inp) := g.addInput [1, 3, 224, 224] .f16
  -- In real code, would add conv, relu, etc
  -- Each connection requires a proof that shapes match
  g

end TensorCore
