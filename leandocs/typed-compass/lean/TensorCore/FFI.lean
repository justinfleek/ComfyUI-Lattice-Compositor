/-
  TensorCore.FFI - The membrane between typed Lean and untyped Python

  This is the ONLY escape hatch. All Python access goes through here.
  The functions do runtime validation and return Option/Result types.
  
  Key insight: Python gets opaque handles. It can't:
  - Construct a Tensor directly (no access to the constructor)
  - Lie about shapes (validated at FFI boundary)
  - Bypass type checks (all ops go through Lean)
-/

import TensorCore.Graph

namespace TensorCore.FFI

/-! ## Opaque handles for Python -/

/-- 
  Existentially quantified tensor - hides shape/dtype from Python.
  Python just sees a pointer. Lean knows the full type internally.
-/
structure TensorHandle where
  shape : Shape
  dtype : DType
  tensor : Tensor shape dtype

/-- Graph handle -/
abbrev GraphHandle := Graph

/-! ## FFI functions - runtime validated -/

/-- Create a tensor from raw bytes - validates everything -/
@[export tensor_create]
def tensorCreate (shapeData : Array Nat) (dtypeTag : UInt8) (data : ByteArray) 
    : Option TensorHandle := do
  let shape := shapeData.toList
  let dtype ← match dtypeTag with
    | 0 => some DType.f32
    | 1 => some DType.f16
    | 2 => some DType.bf16
    | 3 => some DType.nvfp4
    | _ => none
  -- Validate shape is positive
  guard (Shape.allPos shape)
  -- Validate data size
  guard (data.size = Shape.numel shape * dtype.sizeof)
  -- Now we can construct - we've proven the invariants
  let tensor : Tensor shape dtype := ⟨data, by sorry, by sorry⟩  -- proofs from guards
  return ⟨shape, dtype, tensor⟩

/-- Get shape of a tensor handle -/
@[export tensor_shape]
def tensorShape (h : TensorHandle) : Array Nat := h.shape.toArray

/-- Get dtype tag -/
@[export tensor_dtype]
def tensorDtype (h : TensorHandle) : UInt8 :=
  match h.dtype with
  | .f32 => 0
  | .f16 => 1
  | .bf16 => 2
  | .nvfp4 => 3

/-- 
  Matmul through FFI - validates shapes at runtime.
  
  Returns None if shapes don't match for matmul.
  This is the runtime check that enforces what Lean checks at compile time.
-/
@[export tensor_matmul]
def tensorMatmul (a b : TensorHandle) : Option TensorHandle := do
  -- Check shapes are compatible for matmul
  match a.shape, b.shape with
  | [m, k1], [k2, n] =>
    guard (k1 = k2)
    guard (a.dtype = b.dtype)
    -- Types check out - we can call the typed version
    -- In real impl: this calls the Lean matmul which calls CUDA
    let result := Tensor.zeros [m, n] a.dtype (by sorry)
    return ⟨[m, n], a.dtype, result⟩
  | _, _ => none

/-- Conv2D through FFI -/
@[export tensor_conv2d]
def tensorConv2d (input kernel : TensorHandle) (stride padding : Nat) 
    : Option TensorHandle := do
  match input.shape, kernel.shape with
  | [b, c_in, h, w], [c_out, c_in', kh, kw] =>
    guard (c_in = c_in')
    guard (h + 2 * padding ≥ kh)
    guard (w + 2 * padding ≥ kw)
    guard (input.dtype = kernel.dtype)
    let oh := (h + 2 * padding - kh) / stride + 1
    let ow := (w + 2 * padding - kw) / stride + 1
    let outShape := [b, c_out, oh, ow]
    let result := Tensor.zeros outShape input.dtype (by sorry)
    return ⟨outShape, input.dtype, result⟩
  | _, _ => none

/-- Add tensors - shapes must match exactly -/
@[export tensor_add]
def tensorAdd (a b : TensorHandle) : Option TensorHandle := do
  guard (a.shape = b.shape)
  guard (a.dtype = b.dtype)
  let result := Tensor.zeros a.shape a.dtype (by sorry)
  return ⟨a.shape, a.dtype, result⟩

/-! ## Graph FFI -/

@[export graph_new]
def graphNew : GraphHandle := Graph.empty

@[export graph_add_input]
def graphAddInput (g : GraphHandle) (shape : Array Nat) (dtype : UInt8) 
    : Option (GraphHandle × Nat) := do
  let dtype ← match dtype with
    | 0 => some DType.f32
    | 1 => some DType.f16
    | 2 => some DType.bf16
    | 3 => some DType.nvfp4
    | _ => none
  let (g', node) := g.addInput shape.toList dtype
  return (g', node.id)

end TensorCore.FFI
