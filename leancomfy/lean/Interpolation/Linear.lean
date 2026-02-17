/-
  Linear Interpolation Proofs
  CRITICAL: All proofs must verify without `sorry`
-/

import Interpolation.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Interpolation.Linear

/-- Linear interpolation function -/
def lerp (a b : Float) (t : UnitInterval) : Float :=
  a + (b - a) * t.val

/-- CRITICAL PROOF: lerp at t=0 returns a -/
theorem lerp_zero (a b : Float) :
    lerp a b ⟨0, le_refl 0, by norm_num⟩ = a := by
  simp [lerp]
  ring

/-- CRITICAL PROOF: lerp at t=1 returns b -/
theorem lerp_one (a b : Float) :
    lerp a b ⟨1, by norm_num, le_refl 1⟩ = b := by
  simp [lerp]
  ring

/-- CRITICAL PROOF: lerp is idempotent when a = b -/
theorem lerp_identity (a : Float) (t : UnitInterval) :
    lerp a a t = a := by
  simp [lerp]
  ring

/-- CRITICAL PROOF: lerp is monotonic when a ≤ b -/
theorem lerp_monotonic (a b : Float) (t₁ t₂ : UnitInterval)
    (h_ab : a ≤ b) (h_t : t₁.val ≤ t₂.val) :
    lerp a b t₁ ≤ lerp a b t₂ := by
  simp [lerp]
  have h : (b - a) * t₁.val ≤ (b - a) * t₂.val := by
    apply mul_le_mul_of_nonneg_left h_t
    linarith
  linarith

/-- CRITICAL PROOF: lerp is continuous (Lipschitz with constant |b - a|) -/
theorem lerp_lipschitz (a b : Float) (t₁ t₂ : UnitInterval) :
    |lerp a b t₁ - lerp a b t₂| ≤ |b - a| * |t₁.val - t₂.val| := by
  simp [lerp]
  ring_nf
  rw [abs_mul]
  exact le_refl _

/-- Vector linear interpolation -/
def lerpVec2 (a b : Vec2) (t : UnitInterval) : Vec2 :=
  ⟨lerp a.x b.x t, lerp a.y b.y t⟩

def lerpVec3 (a b : Vec3) (t : UnitInterval) : Vec3 :=
  ⟨lerp a.x b.x t, lerp a.y b.y t, lerp a.z b.z t⟩

/-- Vector lerp inherits endpoint properties -/
theorem lerpVec3_zero (a b : Vec3) :
    lerpVec3 a b ⟨0, le_refl 0, by norm_num⟩ = a := by
  simp [lerpVec3, lerp_zero]

theorem lerpVec3_one (a b : Vec3) :
    lerpVec3 a b ⟨1, by norm_num, le_refl 1⟩ = b := by
  simp [lerpVec3, lerp_one]

/-- EXPORT: C-compatible function for FFI -/
@[export lattice_lerp]
def lerp_c (a b t : Float) : Float :=
  if h1 : 0 ≤ t then
    if h2 : t ≤ 1 then lerp a b ⟨t, h1, h2⟩
    else b  -- clamp high
  else a    -- clamp low

end Interpolation.Linear
