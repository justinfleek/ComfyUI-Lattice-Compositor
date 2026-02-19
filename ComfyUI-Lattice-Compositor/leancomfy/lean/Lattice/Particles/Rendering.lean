/-
  Lattice.Particles.Rendering - Particle rendering configurations

  Part of Particles module. Max 500 lines.

  Source: ui/src/types/particles.ts (rendering options)
-/

import Lattice.Primitives
import Lattice.Particles.Enums

namespace Lattice.Particles.Rendering

open Lattice.Primitives
open Lattice.Particles.Enums

/-! ## Connection Render Config -/

/-- Connection rendering configuration -/
structure ConnectionRenderConfig where
  enabled : Bool
  maxDistance : Float                -- Pixels, connect if closer
  maxConnections : Nat               -- Per particle, 1-5 (HARD LIMIT)
  lineWidth : Float                  -- 0.5-3
  lineOpacity : Float                -- 0-1
  fadeByDistance : Bool              -- Opacity decreases with distance
  color : Option RGB                 -- Optional RGB color override (0-1 range)
  maxDistance_positive : maxDistance > 0
  maxDistance_finite : maxDistance.isFinite
  maxConnections_positive : maxConnections > 0
  maxConnections_le_5 : maxConnections ≤ 5
  lineWidth_ge_05 : lineWidth ≥ 0.5
  lineWidth_le_3 : lineWidth ≤ 3.0
  lineWidth_finite : lineWidth.isFinite
  lineOpacity_ge_0 : lineOpacity ≥ 0
  lineOpacity_le_1 : lineOpacity ≤ 1
  lineOpacity_finite : lineOpacity.isFinite
  deriving Repr

/-! ## Particle Render Options -/

/-- Particle render options -/
structure ParticleRenderOptions where
  blendMode : ParticleBlendMode
  renderTrails : Bool
  trailLength : Nat
  trailOpacityFalloff : Float        -- 0-1
  particleShape : ParticleShape
  glowEnabled : Bool
  glowRadius : Float
  glowIntensity : Float              -- 0-1
  -- Motion blur
  motionBlur : Bool
  motionBlurStrength : Float         -- 0-1
  motionBlurSamples : Nat            -- 1-16
  -- Connections
  connections : ConnectionRenderConfig
  -- Sprite sheet
  spriteEnabled : Bool
  spriteImageUrl : Option String
  spriteColumns : Nat
  spriteRows : Nat
  spriteAnimate : Bool
  spriteFrameRate : Float
  spriteRandomStart : Bool
  -- LOD (Level of Detail)
  lodEnabled : Bool
  lodDistances : Array Float         -- [near, mid, far]
  lodSizeMultipliers : Array Float   -- Size multipliers
  -- Depth of Field
  dofEnabled : Bool
  dofFocusDistance : Float
  dofFocusRange : Float
  dofMaxBlur : Float                 -- 0-1
  -- Shadows
  shadowsEnabled : Bool
  castShadows : Bool
  receiveShadows : Bool
  shadowSoftness : Float             -- 0-1
  -- 3D mesh particles
  meshMode : MeshMode
  meshGeometry : MeshGeometry
  -- Proofs
  trailOpacityFalloff_ge_0 : trailOpacityFalloff ≥ 0
  trailOpacityFalloff_le_1 : trailOpacityFalloff ≤ 1
  trailOpacityFalloff_finite : trailOpacityFalloff.isFinite
  glowRadius_ge_0 : glowRadius ≥ 0
  glowRadius_finite : glowRadius.isFinite
  glowIntensity_ge_0 : glowIntensity ≥ 0
  glowIntensity_le_1 : glowIntensity ≤ 1
  glowIntensity_finite : glowIntensity.isFinite
  motionBlurStrength_ge_0 : motionBlurStrength ≥ 0
  motionBlurStrength_le_1 : motionBlurStrength ≤ 1
  motionBlurStrength_finite : motionBlurStrength.isFinite
  motionBlurSamples_positive : motionBlurSamples > 0
  motionBlurSamples_le_16 : motionBlurSamples ≤ 16
  spriteColumns_positive : spriteColumns > 0
  spriteRows_positive : spriteRows > 0
  spriteFrameRate_positive : spriteFrameRate > 0
  spriteFrameRate_finite : spriteFrameRate.isFinite
  dofFocusDistance_ge_0 : dofFocusDistance ≥ 0
  dofFocusDistance_finite : dofFocusDistance.isFinite
  dofFocusRange_ge_0 : dofFocusRange ≥ 0
  dofFocusRange_finite : dofFocusRange.isFinite
  dofMaxBlur_ge_0 : dofMaxBlur ≥ 0
  dofMaxBlur_le_1 : dofMaxBlur ≤ 1
  dofMaxBlur_finite : dofMaxBlur.isFinite
  shadowSoftness_ge_0 : shadowSoftness ≥ 0
  shadowSoftness_le_1 : shadowSoftness ≤ 1
  shadowSoftness_finite : shadowSoftness.isFinite
  deriving Repr

/-! ## Modulation Config -/

/-- Particle modulation configuration -/
structure ParticleModulationConfig where
  id : NonEmptyString
  emitterId : NonEmptyString
  property : ModulationProperty
  startValue : Float
  endValue : Float
  easing : NonEmptyString            -- Easing function name
  startValue_finite : startValue.isFinite
  endValue_finite : endValue.isFinite
  deriving Repr

end Lattice.Particles.Rendering
