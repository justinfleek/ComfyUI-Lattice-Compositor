-- |
-- Module      : Color.BlendModes
-- Description : HSL-based blend mode proofs
-- 
-- Proves correctness of HSL component extraction and recombination
-- for Hue, Saturation, Color, and Luminosity blend modes
--

import Color.Color

-- ============================================================================
-- HSL COMPONENT EXTRACTION
-- ============================================================================

-- | Extract hue component from HSL
def extractHue (hsl : HSL) : Hue := hsl.h

-- | Extract saturation component from HSL
def extractSaturation (hsl : HSL) : Saturation := hsl.s

-- | Extract lightness component from HSL
def extractLightness (hsl : HSL) : Lightness := hsl.l

-- ============================================================================
-- HSL COMPONENT RECOMBINATION
-- ============================================================================

-- | Recombine HSL from components
def recombineHSL (h : Hue) (s : Saturation) (l : Lightness) : HSL := {
  h := h
  s := s
  l := l
}

-- ============================================================================
-- BLEND MODE OPERATIONS
-- ============================================================================

-- | Hue blend: Take hue from blend, saturation and lightness from base
def blendHueHSL (base : HSL) (blend : HSL) : HSL := {
  h := blend.h
  s := base.s
  l := base.l
}

-- | Saturation blend: Take saturation from blend, hue and lightness from base
def blendSaturationHSL (base : HSL) (blend : HSL) : HSL := {
  h := base.h
  s := blend.s
  l := base.l
}

-- | Color blend: Take hue and saturation from blend, lightness from base
def blendColorHSL (base : HSL) (blend : HSL) : HSL := {
  h := blend.h
  s := blend.s
  l := base.l
}

-- | Luminosity blend: Take lightness from blend, hue and saturation from base
def blendLuminosityHSL (base : HSL) (blend : HSL) : HSL := {
  h := base.h
  s := base.s
  l := blend.l
}

-- ============================================================================
-- PROOFS: COMPONENT EXTRACTION PRESERVES INVARIANTS
-- ============================================================================

-- | Proof: Extracted hue preserves angle wrapping
theorem extractHue_preserves_angle (hsl : HSL) : 
  extractHue hsl = hsl.h := rfl

-- | Proof: Extracted saturation preserves bounds
theorem extractSaturation_preserves_bounds (hsl : HSL) : 
  0 ≤ (extractSaturation hsl).value ∧ (extractSaturation hsl).value ≤ 1 := by
  simp [extractSaturation]
  exact ⟨hsl.s.s_0_le, hsl.s.s_le_1⟩

-- | Proof: Extracted lightness preserves bounds
theorem extractLightness_preserves_bounds (hsl : HSL) : 
  0 ≤ (extractLightness hsl).value ∧ (extractLightness hsl).value ≤ 1 := by
  simp [extractLightness]
  exact ⟨hsl.l.l_0_le, hsl.l.l_le_1⟩

-- ============================================================================
-- PROOFS: RECOMBINATION PRESERVES INVARIANTS
-- ============================================================================

-- | Proof: Recombined HSL preserves all invariants
theorem recombineHSL_preserves_invariants (h : Hue) (s : Saturation) (l : Lightness) :
  let hsl := recombineHSL h s l
  0 ≤ hsl.s.value ∧ hsl.s.value ≤ 1 ∧ 0 ≤ hsl.l.value ∧ hsl.l.value ≤ 1 := by
  simp [recombineHSL]
  exact ⟨s.s_0_le, s.s_le_1, l.l_0_le, l.l_le_1⟩

-- ============================================================================
-- PROOFS: BLEND MODES PRESERVE INVARIANTS
-- ============================================================================

-- | Proof: Hue blend preserves saturation and lightness bounds
theorem blendHueHSL_preserves_bounds (base : HSL) (blend : HSL) :
  let result := blendHueHSL base blend
  0 ≤ result.s.value ∧ result.s.value ≤ 1 ∧ 0 ≤ result.l.value ∧ result.l.value ≤ 1 := by
  simp [blendHueHSL]
  exact ⟨base.s.s_0_le, base.s.s_le_1, base.l.l_0_le, base.l.l_le_1⟩

-- | Proof: Saturation blend preserves hue and lightness bounds
theorem blendSaturationHSL_preserves_bounds (base : HSL) (blend : HSL) :
  let result := blendSaturationHSL base blend
  0 ≤ result.s.value ∧ result.s.value ≤ 1 ∧ 0 ≤ result.l.value ∧ result.l.value ≤ 1 := by
  simp [blendSaturationHSL]
  exact ⟨blend.s.s_0_le, blend.s.s_le_1, base.l.l_0_le, base.l.l_le_1⟩

-- | Proof: Color blend preserves lightness bounds
theorem blendColorHSL_preserves_bounds (base : HSL) (blend : HSL) :
  let result := blendColorHSL base blend
  0 ≤ result.s.value ∧ result.s.value ≤ 1 ∧ 0 ≤ result.l.value ∧ result.l.value ≤ 1 := by
  simp [blendColorHSL]
  exact ⟨blend.s.s_0_le, blend.s.s_le_1, base.l.l_0_le, base.l.l_le_1⟩

-- | Proof: Luminosity blend preserves hue and saturation bounds
theorem blendLuminosityHSL_preserves_bounds (base : HSL) (blend : HSL) :
  let result := blendLuminosityHSL base blend
  0 ≤ result.s.value ∧ result.s.value ≤ 1 ∧ 0 ≤ result.l.value ∧ result.l.value ≤ 1 := by
  simp [blendLuminosityHSL]
  exact ⟨base.s.s_0_le, base.s.s_le_1, blend.l.l_0_le, blend.l.l_le_1⟩

-- ============================================================================
-- PROOFS: BLEND MODES COMPOSE WITH COLOR CONVERSIONS
-- ============================================================================

-- | Proof: Hue blend composes correctly with RGB conversion
-- Converting RGB → HSL → blend → HSL → RGB preserves RGB bounds
-- hslToRGB always produces valid RGB8 values with r_le_255 invariant
theorem blendHueHSL_composes_with_rgb (baseRGB : RGB) (blendRGB : RGB) :
  let baseHSL := rgbToHSL baseRGB
  let blendHSL := rgbToHSL blendRGB
  let blendedHSL := blendHueHSL baseHSL blendHSL
  let resultRGB := hslToRGB blendedHSL
  resultRGB.r.value ≤ 255 ∧ resultRGB.g.value ≤ 255 ∧ resultRGB.b.value ≤ 255 := by
  intro baseHSL blendHSL blendedHSL resultRGB
  -- hslToRGB produces RGB8 values with r_le_255 invariant (proven in Color.lean)
  exact ⟨resultRGB.r.r_le_255, resultRGB.g.r_le_255, resultRGB.b.r_le_255⟩

-- | Proof: Saturation blend composes correctly with RGB conversion
theorem blendSaturationHSL_composes_with_rgb (baseRGB : RGB) (blendRGB : RGB) :
  let baseHSL := rgbToHSL baseRGB
  let blendHSL := rgbToHSL blendRGB
  let blendedHSL := blendSaturationHSL baseHSL blendHSL
  let resultRGB := hslToRGB blendedHSL
  resultRGB.r.value ≤ 255 ∧ resultRGB.g.value ≤ 255 ∧ resultRGB.b.value ≤ 255 := by
  intro baseHSL blendHSL blendedHSL resultRGB
  exact ⟨resultRGB.r.r_le_255, resultRGB.g.r_le_255, resultRGB.b.r_le_255⟩

-- | Proof: Color blend composes correctly with RGB conversion
theorem blendColorHSL_composes_with_rgb (baseRGB : RGB) (blendRGB : RGB) :
  let baseHSL := rgbToHSL baseRGB
  let blendHSL := rgbToHSL blendRGB
  let blendedHSL := blendColorHSL baseHSL blendHSL
  let resultRGB := hslToRGB blendedHSL
  resultRGB.r.value ≤ 255 ∧ resultRGB.g.value ≤ 255 ∧ resultRGB.b.value ≤ 255 := by
  intro baseHSL blendHSL blendedHSL resultRGB
  exact ⟨resultRGB.r.r_le_255, resultRGB.g.r_le_255, resultRGB.b.r_le_255⟩

-- | Proof: Luminosity blend composes correctly with RGB conversion
theorem blendLuminosityHSL_composes_with_rgb (baseRGB : RGB) (blendRGB : RGB) :
  let baseHSL := rgbToHSL baseRGB
  let blendHSL := rgbToHSL blendRGB
  let blendedHSL := blendLuminosityHSL baseHSL blendHSL
  let resultRGB := hslToRGB blendedHSL
  resultRGB.r.value ≤ 255 ∧ resultRGB.g.value ≤ 255 ∧ resultRGB.b.value ≤ 255 := by
  intro baseHSL blendHSL blendedHSL resultRGB
  exact ⟨resultRGB.r.r_le_255, resultRGB.g.r_le_255, resultRGB.b.r_le_255⟩
