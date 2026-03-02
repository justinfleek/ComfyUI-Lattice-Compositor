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
import TensorCore.Basic

namespace TensorCore.FFI

open TensorCore

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

/-! ## Helper lemmas for shape positivity -/

/-- Extract proof that shape is positive from tensor handle -/
def TensorHandle.posShape (h : TensorHandle) : Shape.allPos h.shape := h.tensor.posShape

/-- If [m, k] is positive, then m > 0 -/
theorem shape2d_pos_head (m k : Nat) (h : Shape.allPos [m, k]) : m > 0 := by
  unfold Shape.allPos at h
  exact And.left h

/-- If [m, k] is positive, then [m, n] is positive if n > 0 -/
theorem shape2d_pos_preserve (m k n : Nat) (h : Shape.allPos [m, k]) (hn : n > 0) : Shape.allPos [m, n] := by
  unfold Shape.allPos
  exact ⟨shape2d_pos_head m k h, ⟨hn, True.intro⟩⟩

/-- If [b, c_in, h, w] is positive, then [b, c_out, oh, ow] is positive if c_out > 0, oh > 0, ow > 0 -/
theorem shape4d_pos_preserve (b c_in h w c_out oh ow : Nat) 
    (h_shape : Shape.allPos [b, c_in, h, w]) 
    (hc : c_out > 0) (hoh : oh > 0) (how : ow > 0) : Shape.allPos [b, c_out, oh, ow] := by
  unfold Shape.allPos at h_shape
  unfold Shape.allPos
  -- h_shape is (b > 0) ∧ ((c_in > 0) ∧ ((h > 0) ∧ ((w > 0) ∧ True)))
  -- We need (b > 0) ∧ ((c_out > 0) ∧ ((oh > 0) ∧ ((ow > 0) ∧ True)))
  exact ⟨And.left h_shape, ⟨hc, ⟨hoh, ⟨how, True.intro⟩⟩⟩⟩

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
  -- Validate shape is positive using decidability instance
  match instDecidableAllPos shape with
  | isTrue hpos =>
    -- Validate data size
    if hsize : data.size = Shape.numel shape * dtype.sizeof then
      -- Now we can construct - we've proven the invariants
      let tensor : Tensor shape dtype := ⟨data, hsize, hpos⟩
      return ⟨shape, dtype, tensor⟩
    else
      none
  | isFalse _ => none

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
  match h_a_shape : a.shape, h_b_shape : b.shape with
  | [m, k1], [k2, n] =>
    guard (k1 = k2)
    guard (a.dtype = b.dtype)
    -- Convert a.tensor.posShape from a.shape.allPos to Shape.allPos [m, k1]
    -- Use the equality from pattern match: h_a_shape : a.shape = [m, k1]
    have h_a_pos : Shape.allPos [m, k1] := h_a_shape ▸ a.tensor.posShape
    -- Extract n > 0 from b.tensor.posShape: Shape.allPos [k2, n]
    have hn : n > 0 := by
      -- Convert b.tensor.posShape from b.shape.allPos to Shape.allPos [k2, n]
      -- Use the equality from pattern match: h_b_shape : b.shape = [k2, n]
      have h_b_pos : Shape.allPos [k2, n] := h_b_shape ▸ b.tensor.posShape
      -- By definition: Shape.allPos [k2, n] = (k2 > 0) ∧ Shape.allPos [n]
      -- Extract Shape.allPos [n] first
      have h_n_allpos : Shape.allPos [n] := And.right h_b_pos
      -- Shape.allPos [n] = (n > 0) ∧ True by definition
      -- Use dsimp to reduce Shape.allPos [n] to (n > 0) ∧ True
      dsimp [Shape.allPos] at h_n_allpos
      exact And.left h_n_allpos
    -- Now prove [m, n] is positive using lemma
    -- Use lemma to prove Shape.allPos [m, n]
    have hpos : Shape.allPos [m, n] := shape2d_pos_preserve m k1 n h_a_pos hn
    let result := Tensor.zeros [m, n] a.dtype hpos
    return ⟨[m, n], a.dtype, result⟩
  | _, _ => none

/-- Conv2D through FFI -/
@[export tensor_conv2d]
def tensorConv2d (input kernel : TensorHandle) (stride padding : Nat) 
    : Option TensorHandle := do
  match h_input_shape : input.shape, h_kernel_shape : kernel.shape with
  | [b, c_in, h, w], [c_out, c_in', kh, kw] =>
    guard (c_in = c_in')
    guard (h + 2 * padding ≥ kh)
    guard (w + 2 * padding ≥ kw)
    guard (input.dtype = kernel.dtype)
    let oh := (h + 2 * padding - kh) / stride + 1
    let ow := (w + 2 * padding - kw) / stride + 1
    let outShape := [b, c_out, oh, ow]
    -- Prove output shape is positive
    -- We have Shape.allPos [b, c_in, h, w] from input.tensor.posShape
    -- We need c_out > 0, oh > 0, ow > 0
    -- Extract c_out > 0 from kernel.tensor.posShape
    have hc_out : c_out > 0 := by
      -- Convert kernel.tensor.posShape from kernel.shape.allPos to Shape.allPos [c_out, c_in', kh, kw]
      have h_kernel_pos : Shape.allPos [c_out, c_in', kh, kw] := h_kernel_shape ▸ kernel.tensor.posShape
      -- Extract c_out > 0 from Shape.allPos [c_out, c_in', kh, kw]
      unfold Shape.allPos at h_kernel_pos
      exact h_kernel_pos.1
    -- Prove oh > 0: (h + 2 * padding - kh) / stride + 1
    -- Since guard ensures h + 2 * padding ≥ kh, the subtraction is safe
    -- Division by stride (≥ 1) gives ≥ 0, then + 1 gives ≥ 1 > 0
    have h_oh : oh > 0 := by
      simp only [oh]
      -- Nat division is always ≥ 0, so adding 1 gives ≥ 1 > 0
      have h_div_nonneg : (h + 2 * padding - kh) / stride ≥ 0 := Nat.zero_le _
      omega
    -- Prove ow > 0: same reasoning
    have h_ow : ow > 0 := by
      simp only [ow]
      have h_div_nonneg : (w + 2 * padding - kw) / stride ≥ 0 := Nat.zero_le _
      omega
    -- Convert input.tensor.posShape from input.shape.allPos to Shape.allPos [b, c_in, h, w]
    -- Use the equality from pattern match: h_input_shape : input.shape = [b, c_in, h, w]
    have h_input_pos : Shape.allPos [b, c_in, h, w] := h_input_shape ▸ input.tensor.posShape
    let hpos := shape4d_pos_preserve b c_in h w c_out oh ow h_input_pos hc_out h_oh h_ow
    let result := Tensor.zeros outShape input.dtype hpos
    return ⟨outShape, input.dtype, result⟩
  | _, _ => none

/-- Add tensors - shapes must match exactly -/
@[export tensor_add]
def tensorAdd (a b : TensorHandle) : Option TensorHandle := do
  guard (a.shape = b.shape)
  guard (a.dtype = b.dtype)
  -- Shape is positive because it matches a.shape which is positive
  -- Extract proof directly from handle
  let hpos := a.tensor.posShape
  let result := Tensor.zeros a.shape a.dtype hpos
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
