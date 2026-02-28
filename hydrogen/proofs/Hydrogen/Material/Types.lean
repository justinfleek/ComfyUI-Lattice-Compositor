/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      HYDROGEN // MATERIAL // TYPES
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Core material types with proven bounds.
  
  This module defines the foundational types for material properties.
  Unlike Three.js's inheritance hierarchy, Hydrogen uses a STACKED
  architecture where materials are composed from independent layers.
  
  KEY INVARIANTS:
    - All bounded values (roughness, metalness, etc.) in [0, 1]
    - Opacity in [0, 1]
    - IOR > 1 (physically valid)
    - Alpha test threshold in [0, 1]
  
  STACKED ARCHITECTURE:
    Materials are not monolithic classes but compositions of layers:
    - Each layer contributes one aspect (albedo, roughness, normal, etc.)
    - Layers can be combined, masked, blended
    - This enables agent-composable materials
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Light.Types : ColorRGB (shared color representation)
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Light.Types
import Mathlib.Data.Real.Basic

namespace Hydrogen.Material

open Hydrogen.Light

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: BOUNDED UNIT VALUES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- A value bounded in [0, 1]. Used for roughness, metalness, opacity, etc. -/
structure UnitValue where
  value : ℝ
  ge_0 : value ≥ 0
  le_1 : value ≤ 1

namespace UnitValue

def zero : UnitValue where
  value := 0
  ge_0 := by norm_num
  le_1 := by norm_num

def one : UnitValue where
  value := 1
  ge_0 := by norm_num
  le_1 := by norm_num

def half : UnitValue where
  value := 0.5
  ge_0 := by norm_num
  le_1 := by norm_num

/-- Create from a value, clamping to [0, 1] -/
noncomputable def clamp (v : ℝ) : UnitValue where
  value := max 0 (min v 1)
  ge_0 := le_max_left 0 _
  le_1 := by
    apply max_le
    · norm_num
    · exact min_le_right v 1

/-- Linear interpolation between two unit values -/
noncomputable def lerp (a b : UnitValue) (t : UnitValue) : UnitValue where
  value := a.value * (1 - t.value) + b.value * t.value
  ge_0 := by
    have ha := a.ge_0
    have hb := b.ge_0
    have ht := t.ge_0
    have ht1 := t.le_1
    have h1 : 1 - t.value ≥ 0 := by linarith
    have h2 : a.value * (1 - t.value) ≥ 0 := mul_nonneg ha h1
    have h3 : b.value * t.value ≥ 0 := mul_nonneg hb ht
    linarith
  le_1 := by
    have ha := a.le_1
    have hb := b.le_1
    have ht := t.ge_0
    have ht1 := t.le_1
    have h1 : 1 - t.value ≥ 0 := by linarith
    have h2 : 1 - t.value ≤ 1 := by linarith
    calc a.value * (1 - t.value) + b.value * t.value 
        ≤ 1 * (1 - t.value) + 1 * t.value := by nlinarith
      _ = 1 := by ring

/-- Complement (1 - value) -/
def complement (u : UnitValue) : UnitValue where
  value := 1 - u.value
  ge_0 := by linarith [u.le_1]
  le_1 := by linarith [u.ge_0]

/-- Multiply two unit values (stays in [0, 1]) -/
def mul (a b : UnitValue) : UnitValue where
  value := a.value * b.value
  ge_0 := mul_nonneg a.ge_0 b.ge_0
  le_1 := by
    have ha := a.le_1
    have hb := b.le_1
    have ha0 := a.ge_0
    have hb0 := b.ge_0
    calc a.value * b.value ≤ 1 * b.value := by nlinarith
      _ = b.value := one_mul _
      _ ≤ 1 := hb

end UnitValue

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: RENDERING SIDE
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Which side of geometry to render -/
inductive Side where
  | front      -- Front-facing triangles only (default)
  | back       -- Back-facing triangles only
  | double     -- Both sides
  deriving Repr, BEq, DecidableEq

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: BLENDING
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Blending modes -/
inductive BlendMode where
  | none           -- No blending (opaque)
  | normal         -- Standard alpha blending
  | additive       -- Add source to destination
  | subtractive    -- Subtract source from destination
  | multiply       -- Multiply source and destination
  deriving Repr, BEq, DecidableEq

/-- Blend factors for custom blending -/
inductive BlendFactor where
  | zero
  | one
  | srcColor
  | oneMinusSrcColor
  | dstColor
  | oneMinusDstColor
  | srcAlpha
  | oneMinusSrcAlpha
  | dstAlpha
  | oneMinusDstAlpha
  deriving Repr, BEq, DecidableEq

/-- Blend equation -/
inductive BlendEquation where
  | add
  | subtract
  | reverseSubtract
  | min
  | max
  deriving Repr, BEq, DecidableEq

/-- Complete blend state -/
structure BlendState where
  enabled : Bool
  srcFactor : BlendFactor
  dstFactor : BlendFactor
  equation : BlendEquation

namespace BlendState

def solid : BlendState where
  enabled := false
  srcFactor := .one
  dstFactor := .zero
  equation := .add

def transparent : BlendState where
  enabled := true
  srcFactor := .srcAlpha
  dstFactor := .oneMinusSrcAlpha
  equation := .add

def additive : BlendState where
  enabled := true
  srcFactor := .srcAlpha
  dstFactor := .one
  equation := .add

def multiply : BlendState where
  enabled := true
  srcFactor := .dstColor
  dstFactor := .zero
  equation := .add

end BlendState

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: DEPTH AND STENCIL
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Depth comparison function -/
inductive DepthFunc where
  | never
  | less
  | equal
  | lessEqual
  | greater
  | notEqual
  | greaterEqual
  | always
  deriving Repr, BEq, DecidableEq

/-- Depth state -/
structure DepthState where
  test : Bool
  write : Bool
  func : DepthFunc

namespace DepthState

def default : DepthState where
  test := true
  write := true
  func := .less

def readOnly : DepthState where
  test := true
  write := false
  func := .less

def disabled : DepthState where
  test := false
  write := false
  func := .always

end DepthState

/-- Stencil operation -/
inductive StencilOp where
  | keep
  | zero
  | replace
  | increment
  | incrementWrap
  | decrement
  | decrementWrap
  | invert
  deriving Repr, BEq, DecidableEq

/-- Stencil state -/
structure StencilState where
  enabled : Bool
  func : DepthFunc
  ref : UInt8
  mask : UInt8
  failOp : StencilOp
  zFailOp : StencilOp
  passOp : StencilOp

namespace StencilState

def disabled : StencilState where
  enabled := false
  func := .always
  ref := 0
  mask := 0xFF
  failOp := .keep
  zFailOp := .keep
  passOp := .keep

end StencilState

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: INDEX OF REFRACTION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Index of refraction (IOR). Must be ≥ 1 (vacuum = 1). -/
structure IOR where
  value : ℝ
  ge_1 : value ≥ 1

namespace IOR

def vacuum : IOR where value := 1; ge_1 := by norm_num
def air : IOR where value := 1.0003; ge_1 := by norm_num
def water : IOR where value := 1.333; ge_1 := by norm_num
def glass : IOR where value := 1.5; ge_1 := by norm_num
def diamond : IOR where value := 2.42; ge_1 := by norm_num

/-- F0 reflectance from IOR (Fresnel at normal incidence).
    Formula: F0 = ((n - 1) / (n + 1))² -/
noncomputable def toF0 (ior : IOR) : UnitValue where
  value := ((ior.value - 1) / (ior.value + 1))^2
  ge_0 := sq_nonneg _
  le_1 := by
    have h := ior.ge_1
    have hpos : ior.value + 1 > 0 := by linarith
    -- For n ≥ 1: 0 ≤ (n-1)/(n+1) < 1
    have hnum_ge0 : ior.value - 1 ≥ 0 := by linarith
    have hle1 : (ior.value - 1) / (ior.value + 1) < 1 := by
      rw [div_lt_one hpos]
      linarith
    have hge0 : (ior.value - 1) / (ior.value + 1) ≥ 0 := div_nonneg hnum_ge0 (le_of_lt hpos)
    -- x in [0, 1) implies x² ≤ 1
    have hlt1 : (ior.value - 1) / (ior.value + 1) ≤ 1 := le_of_lt hle1
    calc ((ior.value - 1) / (ior.value + 1))^2 
        ≤ 1^2 := sq_le_sq' (by linarith) hlt1
      _ = 1 := by ring

/-- IOR from F0 reflectance.
    Formula: n = (1 + √F0) / (1 - √F0) -/
noncomputable def fromF0 (f0 : UnitValue) (hne1 : f0.value < 1) : IOR where
  value := (1 + Real.sqrt f0.value) / (1 - Real.sqrt f0.value)
  ge_1 := by
    have hf0ge := f0.ge_0
    have hsqrt_ge : Real.sqrt f0.value ≥ 0 := Real.sqrt_nonneg _
    have hsqrt_lt1 : Real.sqrt f0.value < 1 := by
      have h : Real.sqrt f0.value < Real.sqrt 1 := Real.sqrt_lt_sqrt hf0ge hne1
      simp at h
      exact h
    have hdenom_pos : 1 - Real.sqrt f0.value > 0 := by linarith
    have hdenom_nonneg : 1 - Real.sqrt f0.value ≥ 0 := le_of_lt hdenom_pos
    -- (1 + s) / (1 - s) ≥ 1 ⟺ 1 + s ≥ 1 - s ⟺ 2s ≥ 0
    have key : 1 + Real.sqrt f0.value ≥ 1 - Real.sqrt f0.value := by linarith
    have hdiv : (1 + Real.sqrt f0.value) / (1 - Real.sqrt f0.value) ≥ 
                (1 - Real.sqrt f0.value) / (1 - Real.sqrt f0.value) := 
      div_le_div_of_nonneg_right key hdenom_nonneg
    have hone : (1 - Real.sqrt f0.value) / (1 - Real.sqrt f0.value) = 1 := 
      div_self (ne_of_gt hdenom_pos)
    rw [hone] at hdiv
    exact hdiv

end IOR

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: MATERIAL BASE PROPERTIES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Alpha test mode -/
inductive AlphaMode where
  | solid        -- Fully opaque
  | mask         -- Alpha test (cutout)
  | blend        -- Alpha blending
  deriving Repr, BEq, DecidableEq

/-- Base material properties (render state, not appearance) -/
structure MaterialBase where
  side : Side
  alphaMode : AlphaMode
  alphaCutoff : UnitValue      -- For mask mode
  opacity : UnitValue
  blend : BlendState
  depth : DepthState
  stencil : StencilState
  visible : Bool

namespace MaterialBase

def default : MaterialBase where
  side := .front
  alphaMode := .solid
  alphaCutoff := { value := 0.5, ge_0 := by norm_num, le_1 := by norm_num }
  opacity := UnitValue.one
  blend := BlendState.solid
  depth := DepthState.default
  stencil := StencilState.disabled
  visible := true

def transparent : MaterialBase where
  side := .double
  alphaMode := .blend
  alphaCutoff := UnitValue.half
  opacity := UnitValue.one
  blend := BlendState.transparent
  depth := DepthState.readOnly
  stencil := StencilState.disabled
  visible := true

def masked : MaterialBase where
  side := .double
  alphaMode := .mask
  alphaCutoff := UnitValue.half
  opacity := UnitValue.one
  blend := BlendState.solid
  depth := DepthState.default
  stencil := StencilState.disabled
  visible := true

end MaterialBase

end Hydrogen.Material
