/-
  TensorCore.Basic - The typed foundation

  This is System F2 for tensor operations. The droids can't cheat here because:
  1. Tensor dimensions are in the type (dependent types)
  2. No runtime casts - shapes are proven at compile time
  3. The only escape to Python is through blessed FFI functions
-/

namespace TensorCore

/-- Data types for tensors - mirrors CUDA/PyTorch -/
inductive DType where
  | f32 : DType
  | f16 : DType
  | bf16 : DType
  | nvfp4 : DType  -- Blackwell native
  deriving Repr, DecidableEq

/-- Size of dtype in bytes -/
def DType.sizeof : DType → Nat
  | .f32 => 4
  | .f16 => 2
  | .bf16 => 2
  | .nvfp4 => 1  -- simplified, actually 4 bits

/-- A shape is a list of positive naturals -/
abbrev Shape := List Nat

/-- Product of shape dimensions -/
def Shape.numel : Shape → Nat
  | [] => 1
  | d :: ds => d * Shape.numel ds

/-- Proof that all dimensions are positive -/
def Shape.allPos : Shape → Prop
  | [] => True
  | d :: ds => d > 0 ∧ Shape.allPos ds

/-- Decidable instance for Shape.allPos -/
instance instDecidableAllPos : (s : Shape) → Decidable (Shape.allPos s)
  | [] => isTrue trivial
  | d :: ds =>
    match instDecidableAllPos ds with
    | isTrue hds =>
      if hd : d > 0 then
        isTrue ⟨hd, hds⟩
      else
        isFalse (fun ⟨h1, _⟩ => hd h1)
    | isFalse hds =>
      isFalse (fun ⟨_, h2⟩ => hds h2)

end TensorCore
