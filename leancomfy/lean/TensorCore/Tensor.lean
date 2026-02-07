/-
  TensorCore.Tensor - The actual tensor type

  Key insight: the shape is a *type parameter*, not a runtime value.
  Python can't lie about shapes because it can't construct the proof.
-/

import TensorCore.Basic

namespace TensorCore

/-- 
  A tensor with shape and dtype encoded in the type.
  
  The 'valid' field is the key - it's a *proof* that the data
  has the right size. No proof, no tensor. Can't forge it from Python.
-/
structure Tensor (shape : Shape) (dtype : DType) where
  /-- Raw bytes - opaque to the outside world -/
  data : ByteArray
  /-- Proof that data size matches shape * dtype size -/
  valid : data.size = Shape.numel shape * dtype.sizeof
  /-- Proof that all dimensions are positive -/
  posShape : Shape.allPos shape

/-- Smart constructor - the only way to make a Tensor -/
def Tensor.mk? (shape : Shape) (dtype : DType) (data : ByteArray) 
    : Option (Tensor shape dtype) :=
  if h1 : data.size = Shape.numel shape * dtype.sizeof then
    if h2 : Shape.allPos shape then
      some ⟨data, h1, h2⟩
    else
      none
  else
    none

/-- Zero tensor - always valid -/
def Tensor.zeros (shape : Shape) (dtype : DType) (hpos : Shape.allPos shape) 
    : Tensor shape dtype :=
  let size := Shape.numel shape * dtype.sizeof
  let lst := List.replicate size (0 : UInt8)
  have h_lst_len : lst.length = size := List.length_replicate ..
  let arr := Array.mk lst
  have h_arr_size : arr.size = size := by
    rw [← h_lst_len]
    rfl
  let data := ByteArray.mk arr
  have h : data.size = size := by
    rw [ByteArray.size]
    exact h_arr_size
  ⟨data, h, hpos⟩

/-- Get the shape (compile-time known) -/
def Tensor.shape (_ : Tensor s d) : Shape := s

/-- Get the dtype (compile-time known) -/
def Tensor.dtype (_ : Tensor s d) : DType := d

/-- Number of elements -/
def Tensor.numel (_ : Tensor s d) : Nat := Shape.numel s

end TensorCore
