/-
  Lattice.Primitives - Layer 0: Primitives with proofs
  
  Single source of truth for all primitive types.
  Every type has proofs of its invariants.
  No type escapes, no lazy code, all functions total.
  
  CRITICAL: This is Layer 0 - NO IMPORTS except Lean standard library.
  All other layers depend on this.
  
  Uses Float (IEEE 754) for runtime values to match C++23/Haskell/TypeScript/PureScript.
-/

import Batteries.Data.Nat.Basic
import Batteries.Data.String.Basic
import Batteries.Lean.Float

namespace Lattice.Primitives

/-! ## String Primitives -/

/-- Non-empty string with proof that length > 0 -/
structure NonEmptyString where
  value : String
  length_gt_zero : value.length > 0
  deriving Repr

/-- Smart constructor for NonEmptyString -/
def NonEmptyString.ofString (s : String) : Option NonEmptyString :=
  if h : s.length > 0 then
    some ⟨s, h⟩
  else
    none

/-- Proof that NonEmptyString is non-empty -/
theorem NonEmptyString.length_pos (nes : NonEmptyString) : nes.value.length > 0 :=
  nes.length_gt_zero

/-! ## Integer Primitives -/

/-- Positive integer with proof that value > 0 -/
structure PositiveInt where
  value : Nat
  value_gt_zero : value > 0
  deriving Repr

/-- Smart constructor for PositiveInt -/
def PositiveInt.ofNat (n : Nat) : Option PositiveInt :=
  if h : n > 0 then
    some ⟨n, h⟩
  else
    none

/-- Proof that PositiveInt is positive -/
theorem PositiveInt.pos (pi : PositiveInt) : pi.value > 0 :=
  pi.value_gt_zero

/-! ## Float Primitives -/

/-- Positive float with proof that value > 0 and is finite -/
structure PositiveFloat where
  value : Float
  value_gt_zero : value > 0
  is_finite : value.isFinite
  deriving Repr

/-- Smart constructor for PositiveFloat -/
def PositiveFloat.ofFloat (f : Float) : Option PositiveFloat :=
  if h1 : f > 0 then
    if h2 : f.isFinite then
      some ⟨f, h1, h2⟩
    else
      none
  else
    none

/-- Proof that PositiveFloat is positive -/
theorem PositiveFloat.pos (pf : PositiveFloat) : pf.value > 0 :=
  pf.value_gt_zero

/-- Proof that PositiveFloat is finite -/
theorem PositiveFloat.finite (pf : PositiveFloat) : pf.value.isFinite :=
  pf.is_finite

/-- Non-negative float with proof that value ≥ 0 and is finite -/
structure NonNegativeFloat where
  value : Float
  value_ge_zero : value ≥ 0
  is_finite : value.isFinite
  deriving Repr

/-- Smart constructor for NonNegativeFloat -/
def NonNegativeFloat.ofFloat (f : Float) : Option NonNegativeFloat :=
  if h1 : f ≥ 0 then
    if h2 : f.isFinite then
      some ⟨f, h1, h2⟩
    else
      none
  else
    none

/-- Proof that NonNegativeFloat is non-negative -/
theorem NonNegativeFloat.nonneg (nnf : NonNegativeFloat) : nnf.value ≥ 0 :=
  nnf.value_ge_zero

/-- Proof that NonNegativeFloat is finite -/
theorem NonNegativeFloat.finite (nnf : NonNegativeFloat) : nnf.value.isFinite :=
  nnf.is_finite

/-- Percentage with proof that 0 ≤ value ≤ 100 -/
structure Percentage where
  value : Float
  value_ge_zero : value ≥ 0
  value_le_hundred : value ≤ 100
  is_finite : value.isFinite
  deriving Repr

/-- Smart constructor for Percentage -/
def Percentage.ofFloat (f : Float) : Option Percentage :=
  if h1 : f ≥ 0 then
    if h2 : f ≤ 100 then
      if h3 : f.isFinite then
        some ⟨f, h1, h2, h3⟩
      else
        none
    else
      none
  else
    none

/-- Proof that Percentage is in valid range -/
theorem Percentage.in_range (p : Percentage) : 0 ≤ p.value ∧ p.value ≤ 100 :=
  ⟨p.value_ge_zero, p.value_le_hundred⟩

/-- Proof that Percentage is finite -/
theorem Percentage.finite (p : Percentage) : p.value.isFinite :=
  p.is_finite

/-- Normalized value with proof that 0 ≤ value ≤ 1 -/
structure NormalizedValue where
  value : Float
  value_ge_zero : value ≥ 0
  value_le_one : value ≤ 1
  is_finite : value.isFinite
  deriving Repr

/-- Smart constructor for NormalizedValue -/
def NormalizedValue.ofFloat (f : Float) : Option NormalizedValue :=
  if h1 : f ≥ 0 then
    if h2 : f ≤ 1 then
      if h3 : f.isFinite then
        some ⟨f, h1, h2, h3⟩
      else
        none
    else
      none
  else
    none

/-- Proof that NormalizedValue is in valid range -/
theorem NormalizedValue.in_range (nv : NormalizedValue) : 0 ≤ nv.value ∧ nv.value ≤ 1 :=
  ⟨nv.value_ge_zero, nv.value_le_one⟩

/-- Proof that NormalizedValue is finite -/
theorem NormalizedValue.finite (nv : NormalizedValue) : nv.value.isFinite :=
  nv.is_finite

/-- Frame number with proof that value ≥ 0 -/
structure FrameNumber where
  value : Nat
  deriving Repr

/-- Proof that FrameNumber is non-negative (always true for ℕ) -/
theorem FrameNumber.nonneg (fn : FrameNumber) : fn.value ≥ 0 :=
  Nat.zero_le fn.value

/-! ## Vector Primitives -/

/-- 2D vector with proof that all components are finite -/
structure Vec2 where
  x : Float
  y : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  deriving Repr

/-- Smart constructor for Vec2 -/
def Vec2.ofFloats (x_val : Float) (y_val : Float) : Option Vec2 :=
  if hx : x_val.isFinite then
    if hy : y_val.isFinite then
      some ⟨x_val, y_val, hx, hy⟩
    else
      none
  else
    none

/-- Proof that Vec2 components are finite -/
theorem Vec2.finite (v : Vec2) : v.x.isFinite ∧ v.y.isFinite :=
  ⟨v.x_finite, v.y_finite⟩

/-- 3D vector with proof that all components are finite -/
structure Vec3 where
  x : Float
  y : Float
  z : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite

/-- Smart constructor for Vec3 -/
def Vec3.ofFloats (x_val : Float) (y_val : Float) (z_val : Float) : Option Vec3 :=
  if hx : x_val.isFinite then
    if hy : y_val.isFinite then
      if hz : z_val.isFinite then
        some ⟨x_val, y_val, z_val, hx, hy, hz⟩
      else
        none
    else
      none
  else
    none

/-- Proof that Vec3 components are finite -/
theorem Vec3.finite (v : Vec3) : v.x.isFinite ∧ v.y.isFinite ∧ v.z.isFinite :=
  ⟨v.x_finite, v.y_finite, v.z_finite⟩

/-- 4D vector with proof that all components are finite -/
structure Vec4 where
  x : Float
  y : Float
  z : Float
  w : Float
  x_finite : x.isFinite
  y_finite : y.isFinite
  z_finite : z.isFinite
  w_finite : w.isFinite

/-- Smart constructor for Vec4 -/
def Vec4.ofFloats (x_val : Float) (y_val : Float) (z_val : Float) (w_val : Float) : Option Vec4 :=
  if hx : x_val.isFinite then
    if hy : y_val.isFinite then
      if hz : z_val.isFinite then
        if hw : w_val.isFinite then
          some ⟨x_val, y_val, z_val, w_val, hx, hy, hz, hw⟩
        else
          none
      else
        none
    else
      none
  else
    none

/-- Proof that Vec4 components are finite -/
theorem Vec4.finite (v : Vec4) : v.x.isFinite ∧ v.y.isFinite ∧ v.z.isFinite ∧ v.w.isFinite :=
  ⟨v.x_finite, v.y_finite, v.z_finite, v.w_finite⟩

/-! ## Matrix Primitives -/

/-- 3x3 matrix with proof that all entries are finite -/
structure Matrix3x3 where
  m00 : Float
  m01 : Float
  m02 : Float
  m10 : Float
  m11 : Float
  m12 : Float
  m20 : Float
  m21 : Float
  m22 : Float
  all_finite : m00.isFinite ∧ m01.isFinite ∧ m02.isFinite ∧
               m10.isFinite ∧ m11.isFinite ∧ m12.isFinite ∧
               m20.isFinite ∧ m21.isFinite ∧ m22.isFinite

/-- Smart constructor for Matrix3x3 -/
def Matrix3x3.ofFloats (m00_val m01_val m02_val m10_val m11_val m12_val m20_val m21_val m22_val : Float) :
    Option Matrix3x3 :=
  if h : m00_val.isFinite ∧ m01_val.isFinite ∧ m02_val.isFinite ∧
        m10_val.isFinite ∧ m11_val.isFinite ∧ m12_val.isFinite ∧
        m20_val.isFinite ∧ m21_val.isFinite ∧ m22_val.isFinite then
    some ⟨m00_val, m01_val, m02_val, m10_val, m11_val, m12_val, m20_val, m21_val, m22_val, h⟩
  else
    none

/-- 4x4 matrix with proof that all entries are finite -/
structure Matrix4x4 where
  m00 : Float
  m01 : Float
  m02 : Float
  m03 : Float
  m10 : Float
  m11 : Float
  m12 : Float
  m13 : Float
  m20 : Float
  m21 : Float
  m22 : Float
  m23 : Float
  m30 : Float
  m31 : Float
  m32 : Float
  m33 : Float
  all_finite : m00.isFinite ∧ m01.isFinite ∧ m02.isFinite ∧ m03.isFinite ∧
               m10.isFinite ∧ m11.isFinite ∧ m12.isFinite ∧ m13.isFinite ∧
               m20.isFinite ∧ m21.isFinite ∧ m22.isFinite ∧ m23.isFinite ∧
               m30.isFinite ∧ m31.isFinite ∧ m32.isFinite ∧ m33.isFinite

/-- Smart constructor for Matrix4x4 -/
def Matrix4x4.ofFloats (m00_val m01_val m02_val m03_val m10_val m11_val m12_val m13_val
                  m20_val m21_val m22_val m23_val m30_val m31_val m32_val m33_val : Float) :
    Option Matrix4x4 :=
  if h : m00_val.isFinite ∧ m01_val.isFinite ∧ m02_val.isFinite ∧ m03_val.isFinite ∧
        m10_val.isFinite ∧ m11_val.isFinite ∧ m12_val.isFinite ∧ m13_val.isFinite ∧
        m20_val.isFinite ∧ m21_val.isFinite ∧ m22_val.isFinite ∧ m23_val.isFinite ∧
        m30_val.isFinite ∧ m31_val.isFinite ∧ m32_val.isFinite ∧ m33_val.isFinite then
    some ⟨m00_val, m01_val, m02_val, m03_val, m10_val, m11_val, m12_val, m13_val,
          m20_val, m21_val, m22_val, m23_val, m30_val, m31_val, m32_val, m33_val, h⟩
  else
    none

/-! ## Protocols (Type Classes) -/

/-- Identifiable protocol: has an id field of type NonEmptyString -/
class Identifiable (α : Type _) where
  id : α → NonEmptyString

/-- Timestamped protocol: has createdAt and updatedAt fields -/
class Timestamped (α : Type _) where
  createdAt : α → ℕ  -- Unix timestamp in seconds
  updatedAt : α → ℕ  -- Unix timestamp in seconds

/-- Named protocol: has a name field of type NonEmptyString -/
class Named (α : Type _) where
  name : α → NonEmptyString

/-- Versioned protocol: has a version field of type PositiveInt -/
class Versioned (α : Type _) where
  version : α → PositiveInt

/-- FrameScoped protocol: has startFrame and endFrame fields of type FrameNumber -/
class FrameScoped (α : Type _) where
  startFrame : α → FrameNumber
  endFrame : α → FrameNumber

/-! ## Constants -/

/-- Minimum frame number (always 0) -/
def MIN_FRAME_NUMBER : FrameNumber := ⟨(0 : Nat)⟩

/-- Maximum frame number (practical limit: 2^31 - 1) -/
def MAX_FRAME_NUMBER : FrameNumber := ⟨(2147483647 : Nat)⟩

/-- Proof that MIN_FRAME_NUMBER ≤ MAX_FRAME_NUMBER -/
theorem MIN_FRAME_LE_MAX_FRAME : MIN_FRAME_NUMBER.value ≤ MAX_FRAME_NUMBER.value :=
  by decide

/-- Standard FPS value: 24 -/
def FPS_24 : PositiveInt := ⟨24, by decide⟩

/-- Standard FPS value: 25 -/
def FPS_25 : PositiveInt := ⟨25, by decide⟩

/-- Standard FPS value: 30 -/
def FPS_30 : PositiveInt := ⟨30, by decide⟩

/-- Standard FPS value: 60 -/
def FPS_60 : PositiveInt := ⟨60, by decide⟩

/-- Proof that all standard FPS values are positive -/
theorem all_fps_positive :
  FPS_24.value > 0 ∧ FPS_25.value > 0 ∧ FPS_30.value > 0 ∧ FPS_60.value > 0 :=
  ⟨FPS_24.value_gt_zero, FPS_25.value_gt_zero, FPS_30.value_gt_zero, FPS_60.value_gt_zero⟩

/-- Standard resolution: 720p width -/
def RES_720P_WIDTH : PositiveInt := ⟨1280, by decide⟩

/-- Standard resolution: 720p height -/
def RES_720P_HEIGHT : PositiveInt := ⟨720, by decide⟩

/-- Standard resolution: 1080p width -/
def RES_1080P_WIDTH : PositiveInt := ⟨1920, by decide⟩

/-- Standard resolution: 1080p height -/
def RES_1080P_HEIGHT : PositiveInt := ⟨1080, by decide⟩

/-- Standard resolution: 4K width -/
def RES_4K_WIDTH : PositiveInt := ⟨3840, by decide⟩

/-- Standard resolution: 4K height -/
def RES_4K_HEIGHT : PositiveInt := ⟨2160, by decide⟩

/-- Proof that all standard resolutions are positive -/
theorem all_resolutions_positive :
  RES_720P_WIDTH.value > 0 ∧ RES_720P_HEIGHT.value > 0 ∧
  RES_1080P_WIDTH.value > 0 ∧ RES_1080P_HEIGHT.value > 0 ∧
  RES_4K_WIDTH.value > 0 ∧ RES_4K_HEIGHT.value > 0 :=
  ⟨RES_720P_WIDTH.value_gt_zero, RES_720P_HEIGHT.value_gt_zero,
   RES_1080P_WIDTH.value_gt_zero, RES_1080P_HEIGHT.value_gt_zero,
   RES_4K_WIDTH.value_gt_zero, RES_4K_HEIGHT.value_gt_zero⟩

/-! ## Color Primitives -/

/-- RGB color with components in [0, 1] -/
structure RGB where
  r : Float
  g : Float
  b : Float
  r_ge_0 : r ≥ 0
  r_le_1 : r ≤ 1
  r_finite : r.isFinite
  g_ge_0 : g ≥ 0
  g_le_1 : g ≤ 1
  g_finite : g.isFinite
  b_ge_0 : b ≥ 0
  b_le_1 : b ≤ 1
  b_finite : b.isFinite
  deriving Repr

/-- RGBA color with components in [0, 1] -/
structure RGBA where
  r : Float
  g : Float
  b : Float
  a : Float
  r_ge_0 : r ≥ 0
  r_le_1 : r ≤ 1
  r_finite : r.isFinite
  g_ge_0 : g ≥ 0
  g_le_1 : g ≤ 1
  g_finite : g.isFinite
  b_ge_0 : b ≥ 0
  b_le_1 : b ≤ 1
  b_finite : b.isFinite
  a_ge_0 : a ≥ 0
  a_le_1 : a ≤ 1
  a_finite : a.isFinite
  deriving Repr

/-- Hex color string (e.g., "#ff0000" or "#ff0000ff") -/
structure HexColor where
  value : String
  starts_with_hash : value.length > 0 ∧ value.get! 0 = '#'
  valid_length : value.length = 7 ∨ value.length = 9
  deriving Repr

/-- Smart constructor for HexColor -/
def HexColor.ofString (s : String) : Option HexColor :=
  if h1 : s.length > 0 ∧ s.get! 0 = '#' then
    if h2 : s.length = 7 ∨ s.length = 9 then
      some ⟨s, h1, h2⟩
    else
      none
  else
    none

end Lattice.Primitives
