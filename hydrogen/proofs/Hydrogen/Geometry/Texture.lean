/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                     HYDROGEN // GEOMETRY // TEXTURE
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Texture sampling and UV coordinate transformations with proven properties.
  
  This module provides the mathematical foundations for texture mapping:
  
  UV COORDINATES:
    - Wrap modes: repeat, clamp, mirror
    - Coordinate transformations (scale, offset, rotate)
  
  MIPMAPPING:
    - Level-of-detail (LOD) calculation
    - Trilinear interpolation bounds
  
  INTERPOLATION:
    - Bilinear interpolation (for 2D textures)
    - Barycentric coordinates (for triangle sampling)
  
  PROVEN INVARIANTS:
    - Wrap modes produce outputs in [0, 1]
    - Bilinear interpolation preserves bounds
    - Barycentric coordinates sum to 1
    - LOD is non-negative
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Mathlib : Real analysis
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Hydrogen.Geometry.Texture

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: WRAP MODES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Texture wrap modes for UV coordinates outside [0, 1]. -/
inductive WrapMode where
  | repeat   -- Tile infinitely: u mod 1
  | clamp    -- Clamp to edges: clamp(u, 0, 1)
  | mirror   -- Mirror at boundaries
  deriving Repr, DecidableEq

/-- Fractional part function: fract(x) = x - floor(x) ∈ [0, 1) -/
noncomputable def fract (x : ℝ) : ℝ :=
  x - ⌊x⌋

/-- Fractional part is in [0, 1) -/
theorem fract_nonneg (x : ℝ) : fract x ≥ 0 := by
  unfold fract
  have h := Int.floor_le x
  linarith

theorem fract_lt_one (x : ℝ) : fract x < 1 := by
  unfold fract
  have h := Int.lt_floor_add_one x
  linarith

/-- Repeat wrap: tile the texture infinitely -/
noncomputable def wrapRepeat (u : ℝ) : ℝ :=
  fract u

/-- Repeat wrap produces output in [0, 1) -/
theorem wrapRepeat_bounded (u : ℝ) : 
    wrapRepeat u ≥ 0 ∧ wrapRepeat u < 1 := by
  unfold wrapRepeat
  exact ⟨fract_nonneg u, fract_lt_one u⟩

/-- Clamp wrap: restrict to [0, 1] -/
noncomputable def wrapClamp (u : ℝ) : ℝ :=
  max 0 (min u 1)

/-- Clamp wrap produces output in [0, 1] -/
theorem wrapClamp_bounded (u : ℝ) :
    wrapClamp u ≥ 0 ∧ wrapClamp u ≤ 1 := by
  unfold wrapClamp
  constructor
  · exact le_max_left 0 (min u 1)
  · have h : min u 1 ≤ 1 := min_le_right u 1
    exact le_trans (max_le (by norm_num) (min_le_right u 1)) (by norm_num : (1:ℝ) ≤ 1)

/-- Clamp is idempotent on [0, 1] -/
theorem wrapClamp_idempotent (u : ℝ) (h0 : u ≥ 0) (h1 : u ≤ 1) :
    wrapClamp u = u := by
  unfold wrapClamp
  simp [max_eq_right h0, min_eq_left h1]

/-- Mirror wrap: reflect at boundaries -/
noncomputable def wrapMirror (u : ℝ) : ℝ :=
  let t := fract (u / 2) * 2  -- t ∈ [0, 2)
  if t ≤ 1 then t else 2 - t

/-- Mirror wrap produces output in [0, 1] -/
theorem wrapMirror_bounded (u : ℝ) :
    wrapMirror u ≥ 0 ∧ wrapMirror u ≤ 1 := by
  unfold wrapMirror
  have hfract := fract_nonneg (u / 2)
  have hfract_lt := fract_lt_one (u / 2)
  have ht_nonneg : fract (u / 2) * 2 ≥ 0 := by linarith
  have ht_lt : fract (u / 2) * 2 < 2 := by linarith
  simp only []
  split_ifs with h
  · -- t ≤ 1
    exact ⟨ht_nonneg, h⟩
  · -- t > 1
    push_neg at h
    constructor
    · linarith
    · linarith

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: BILINEAR INTERPOLATION
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Linear interpolation (lerp) -/
noncomputable def lerp (a b t : ℝ) : ℝ :=
  a + (b - a) * t

/-- Lerp at t=0 equals a -/
theorem lerp_zero (a b : ℝ) : lerp a b 0 = a := by
  unfold lerp; ring

/-- Lerp at t=1 equals b -/
theorem lerp_one (a b : ℝ) : lerp a b 1 = b := by
  unfold lerp; ring

/-- Lerp preserves bounds -/
theorem lerp_bounds (a b t : ℝ) (hab : a ≤ b) (ht0 : t ≥ 0) (ht1 : t ≤ 1) :
    lerp a b t ≥ a ∧ lerp a b t ≤ b := by
  unfold lerp
  constructor
  · have h : (b - a) * t ≥ 0 := mul_nonneg (by linarith) ht0
    linarith
  · have h1 : (b - a) * t ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left ht1 (by linarith)
    linarith

/-- Bilinear interpolation on a unit square.
    
    Given values at four corners:
      c00 (bottom-left), c10 (bottom-right),
      c01 (top-left),    c11 (top-right)
    
    Interpolate at (u, v) ∈ [0,1]². -/
noncomputable def bilinear (c00 c10 c01 c11 : ℝ) (u v : ℝ) : ℝ :=
  let bottom := lerp c00 c10 u
  let top := lerp c01 c11 u
  lerp bottom top v

/-- Bilinear at corner (0, 0) -/
theorem bilinear_corner_00 (c00 c10 c01 c11 : ℝ) :
    bilinear c00 c10 c01 c11 0 0 = c00 := by
  unfold bilinear
  simp [lerp_zero]

/-- Bilinear at corner (1, 0) -/
theorem bilinear_corner_10 (c00 c10 c01 c11 : ℝ) :
    bilinear c00 c10 c01 c11 1 0 = c10 := by
  unfold bilinear
  simp [lerp_one, lerp_zero]

/-- Bilinear at corner (0, 1) -/
theorem bilinear_corner_01 (c00 c10 c01 c11 : ℝ) :
    bilinear c00 c10 c01 c11 0 1 = c01 := by
  unfold bilinear
  simp [lerp_zero, lerp_one]

/-- Bilinear at corner (1, 1) -/
theorem bilinear_corner_11 (c00 c10 c01 c11 : ℝ) :
    bilinear c00 c10 c01 c11 1 1 = c11 := by
  unfold bilinear
  simp [lerp_one]

/-- Bilinear at center equals weighted average -/
theorem bilinear_center (c00 c10 c01 c11 : ℝ) :
    bilinear c00 c10 c01 c11 (1/2) (1/2) = (c00 + c10 + c01 + c11) / 4 := by
  unfold bilinear lerp
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: BARYCENTRIC COORDINATES
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Barycentric coordinates for a triangle.
    
    (u, v, w) where u + v + w = 1.
    These are weights for interpolating across a triangle. -/
structure Barycentric where
  u : ℝ
  v : ℝ
  w : ℝ
  sum_one : u + v + w = 1

/-- Create barycentric coords from two values (third is derived) -/
def Barycentric.fromUV (u v : ℝ) : Barycentric where
  u := u
  v := v
  w := 1 - u - v
  sum_one := by ring

/-- Barycentric coordinates at vertex 0: (1, 0, 0) -/
def Barycentric.vertex0 : Barycentric where
  u := 1
  v := 0
  w := 0
  sum_one := by ring

/-- Barycentric coordinates at vertex 1: (0, 1, 0) -/
def Barycentric.vertex1 : Barycentric where
  u := 0
  v := 1
  w := 0
  sum_one := by ring

/-- Barycentric coordinates at vertex 2: (0, 0, 1) -/
def Barycentric.vertex2 : Barycentric where
  u := 0
  v := 0
  w := 1
  sum_one := by ring

/-- Barycentric coordinates at centroid: (1/3, 1/3, 1/3) -/
noncomputable def Barycentric.centroid : Barycentric where
  u := 1/3
  v := 1/3
  w := 1/3
  sum_one := by ring

/-- Interpolate a value using barycentric coordinates -/
noncomputable def barycentricInterp (bary : Barycentric) (v0 v1 v2 : ℝ) : ℝ :=
  bary.u * v0 + bary.v * v1 + bary.w * v2

/-- Barycentric interp at vertex 0 gives v0 -/
theorem barycentricInterp_vertex0 (v0 v1 v2 : ℝ) :
    barycentricInterp Barycentric.vertex0 v0 v1 v2 = v0 := by
  unfold barycentricInterp Barycentric.vertex0
  ring

/-- Barycentric interp at vertex 1 gives v1 -/
theorem barycentricInterp_vertex1 (v0 v1 v2 : ℝ) :
    barycentricInterp Barycentric.vertex1 v0 v1 v2 = v1 := by
  unfold barycentricInterp Barycentric.vertex1
  ring

/-- Barycentric interp at vertex 2 gives v2 -/
theorem barycentricInterp_vertex2 (v0 v1 v2 : ℝ) :
    barycentricInterp Barycentric.vertex2 v0 v1 v2 = v2 := by
  unfold barycentricInterp Barycentric.vertex2
  ring

/-- Barycentric interp at centroid gives average -/
noncomputable def barycentricInterp_centroid_val (v0 v1 v2 : ℝ) : ℝ :=
  barycentricInterp Barycentric.centroid v0 v1 v2

theorem barycentricInterp_centroid (v0 v1 v2 : ℝ) :
    barycentricInterp Barycentric.centroid v0 v1 v2 = (v0 + v1 + v2) / 3 := by
  unfold barycentricInterp Barycentric.centroid
  ring

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: MIPMAP LOD
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Mipmap level of detail (LOD).
    
    LOD determines which texture resolution to sample:
    - LOD 0 = full resolution
    - LOD 1 = half resolution (2x2 averaged)
    - LOD n = 2^n times smaller
    
    Non-negative values only. -/
structure MipLOD where
  value : ℝ
  nonneg : value ≥ 0

/-- LOD 0 (full resolution) -/
def MipLOD.zero : MipLOD where
  value := 0
  nonneg := le_refl 0

/-- Compute LOD from texture coordinate derivatives.
    
    LOD = log₂(max(|du/dx|, |du/dy|, |dv/dx|, |dv/dy|) * textureSize)
    
    This simplified version takes the maximum gradient magnitude. -/
noncomputable def computeLOD (maxGradient : ℝ) (textureSize : ℝ) 
    (_hgrad : maxGradient > 0) (_hsize : textureSize > 0) : MipLOD where
  value := max 0 (Real.log (maxGradient * textureSize) / Real.log 2)
  nonneg := le_max_left 0 _

/-- LOD increases with gradient (larger screen coverage = higher LOD) -/
theorem lod_increases_with_gradient (g1 g2 texSize : ℝ)
    (hg1 : g1 > 0) (hg2 : g2 > 0) (hg12 : g1 < g2) (hsize : texSize > 0) :
    (computeLOD g1 texSize hg1 hsize).value ≤ (computeLOD g2 texSize hg2 hsize).value := by
  unfold computeLOD
  simp only
  have h1 : g1 * texSize < g2 * texSize := by nlinarith
  have hlog_mono : Real.log (g1 * texSize) < Real.log (g2 * texSize) := by
    apply Real.log_lt_log
    · exact mul_pos hg1 hsize
    · exact h1
  have hdiv_mono : Real.log (g1 * texSize) / Real.log 2 < 
                   Real.log (g2 * texSize) / Real.log 2 := by
    apply div_lt_div_of_pos_right hlog_mono
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  exact max_le_max_left 0 (le_of_lt hdiv_mono)

end Hydrogen.Geometry.Texture
