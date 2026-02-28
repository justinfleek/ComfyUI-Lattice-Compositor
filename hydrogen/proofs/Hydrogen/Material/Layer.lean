/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                      HYDROGEN // MATERIAL // LAYER
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Composable material layers for stacked material architecture.
  
  STACKED ARCHITECTURE:
    Instead of monolithic material classes (MeshStandardMaterial, etc.),
    Hydrogen uses independent layers that can be combined:
    
    - AlbedoLayer     : Base color
    - RoughnessLayer  : Surface roughness
    - MetalnessLayer  : Metallic vs dielectric
    - NormalLayer     : Surface detail via normal perturbation
    - EmissiveLayer   : Self-illumination
    - OcclusionLayer  : Ambient occlusion
    - ClearcoatLayer  : Additional specular layer
    - TransmissionLayer : Glass/translucency
  
  WHY STACKED:
    - Agents can reason about individual layers independently
    - Layers can be mixed/matched without inheritance hierarchies
    - Each layer has proven bounds
    - Composition is algebraic, not ad-hoc
  
  ─────────────────────────────────────────────────────────────────────────────
  DEPENDENCIES
  ─────────────────────────────────────────────────────────────────────────────
  
  - Types : UnitValue, IOR, ColorRGB
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Material.Types
import Hydrogen.Light.Types

namespace Hydrogen.Material

open Hydrogen.Light

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 1: LAYER TYPE CLASS
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Layer identifier for type-safe layer addressing -/
inductive LayerKind where
  | albedo
  | roughness
  | metalness
  | normal
  | emissive
  | occlusion
  | clearcoat
  | transmission
  | sheen
  | anisotropy
  deriving Repr, BEq, DecidableEq

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 2: ALBEDO LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Albedo (base color) layer.
    
    For dielectrics: diffuse reflectance color
    For metals: F0 (specular reflectance at normal incidence)
    
    In PBR, albedo should generally be in [0.04, 0.9] for realistic materials.
    Pure black absorbs all light; pure white is unrealistically bright. -/
structure AlbedoLayer where
  color : ColorRGB
  
namespace AlbedoLayer

def white : AlbedoLayer where color := ColorRGB.white
def black : AlbedoLayer where color := ColorRGB.black

/-- Neutral gray (50% reflectance) -/
def gray : AlbedoLayer where
  color := {
    r := 0.5, g := 0.5, b := 0.5
    r_ge_0 := by norm_num, r_le_1 := by norm_num
    g_ge_0 := by norm_num, g_le_1 := by norm_num
    b_ge_0 := by norm_num, b_le_1 := by norm_num
  }

/-- Create from RGB values -/
def fromRGB (r g b : UnitValue) : AlbedoLayer where
  color := {
    r := r.value, g := g.value, b := b.value
    r_ge_0 := r.ge_0, r_le_1 := r.le_1
    g_ge_0 := g.ge_0, g_le_1 := g.le_1
    b_ge_0 := b.ge_0, b_le_1 := b.le_1
  }

end AlbedoLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 3: ROUGHNESS LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Roughness layer.
    
    - 0: Perfect mirror (physically impossible, use ~0.01)
    - 0.5: Typical plastic
    - 1: Completely diffuse
    
    In BRDF equations, roughness is often squared (α = roughness²). -/
structure RoughnessLayer where
  roughness : UnitValue

namespace RoughnessLayer

def mirror : RoughnessLayer where roughness := { value := 0.01, ge_0 := by norm_num, le_1 := by norm_num }
def smooth : RoughnessLayer where roughness := { value := 0.1, ge_0 := by norm_num, le_1 := by norm_num }
def plastic : RoughnessLayer where roughness := UnitValue.half
def rough : RoughnessLayer where roughness := { value := 0.8, ge_0 := by norm_num, le_1 := by norm_num }
def diffuse : RoughnessLayer where roughness := UnitValue.one

/-- Alpha value for BRDF (roughness squared) -/
def alpha (layer : RoughnessLayer) : UnitValue := UnitValue.mul layer.roughness layer.roughness

end RoughnessLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 4: METALNESS LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Metalness layer.
    
    - 0: Dielectric (plastic, stone, wood, skin)
    - 1: Metal (gold, silver, copper)
    
    In practice, use 0 or 1; intermediate values represent mixed surfaces
    (e.g., dusty metal) but are less physically accurate. -/
structure MetalnessLayer where
  metalness : UnitValue

namespace MetalnessLayer

def dielectric : MetalnessLayer where metalness := UnitValue.zero
def metal : MetalnessLayer where metalness := UnitValue.one

/-- Is this a pure dielectric? -/
noncomputable def isDielectric (layer : MetalnessLayer) : Bool := layer.metalness.value == 0

/-- Is this a pure metal? -/
noncomputable def isMetal (layer : MetalnessLayer) : Bool := layer.metalness.value == 1

end MetalnessLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 5: NORMAL LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Normal map type -/
inductive NormalMapType where
  | tangentSpace   -- Most common: normals relative to surface tangent space
  | objectSpace    -- Normals in object space (useful for static objects)
  deriving Repr, BEq, DecidableEq

/-- Normal perturbation layer.
    
    Stores intensity for procedural use or texture reference.
    Actual normal vectors come from textures at render time. -/
structure NormalLayer where
  mapType : NormalMapType
  intensity : UnitValue  -- Scale factor for normal perturbation

namespace NormalLayer

def none : NormalLayer where
  mapType := .tangentSpace
  intensity := UnitValue.zero

def subtle : NormalLayer where
  mapType := .tangentSpace
  intensity := { value := 0.3, ge_0 := by norm_num, le_1 := by norm_num }

def full : NormalLayer where
  mapType := .tangentSpace
  intensity := UnitValue.one

end NormalLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 6: EMISSIVE LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Emissive (self-illumination) layer.
    
    Emissive surfaces add light to the scene without being affected by
    external lighting. Useful for screens, neon signs, lava, etc.
    
    The intensity can exceed 1 for HDR/bloom effects. -/
structure EmissiveLayer where
  color : ColorRGB
  intensity : ℝ
  intensity_nonneg : intensity ≥ 0

namespace EmissiveLayer

def none : EmissiveLayer where
  color := ColorRGB.black
  intensity := 0
  intensity_nonneg := by norm_num

def subtle (color : ColorRGB) : EmissiveLayer where
  color := color
  intensity := 0.5
  intensity_nonneg := by norm_num

def bright (color : ColorRGB) : EmissiveLayer where
  color := color
  intensity := 2
  intensity_nonneg := by norm_num

/-- Is emission disabled? -/
noncomputable def isOff (layer : EmissiveLayer) : Bool := layer.intensity == 0

end EmissiveLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 7: OCCLUSION LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Ambient occlusion layer.
    
    Simulates soft shadows in crevices where ambient light is occluded.
    - 0: Fully occluded (black)
    - 1: No occlusion (full ambient) -/
structure OcclusionLayer where
  intensity : UnitValue  -- How strongly AO affects the result

namespace OcclusionLayer

def none : OcclusionLayer where intensity := UnitValue.zero
def subtle : OcclusionLayer where intensity := UnitValue.half
def full : OcclusionLayer where intensity := UnitValue.one

end OcclusionLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 8: CLEARCOAT LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Clearcoat layer (car paint, lacquered wood).
    
    An additional specular layer on top of the base material.
    Has its own roughness and intensity. -/
structure ClearcoatLayer where
  intensity : UnitValue    -- How much clearcoat (0 = none)
  roughness : UnitValue    -- Clearcoat roughness (usually low)

namespace ClearcoatLayer

def none : ClearcoatLayer where
  intensity := UnitValue.zero
  roughness := UnitValue.zero

def carPaint : ClearcoatLayer where
  intensity := UnitValue.one
  roughness := { value := 0.1, ge_0 := by norm_num, le_1 := by norm_num }

def lacquer : ClearcoatLayer where
  intensity := { value := 0.5, ge_0 := by norm_num, le_1 := by norm_num }
  roughness := { value := 0.2, ge_0 := by norm_num, le_1 := by norm_num }

end ClearcoatLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 9: TRANSMISSION LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Transmission (glass, translucency) layer.
    
    Allows light to pass through the material.
    - transmission: 0 = opaque, 1 = fully transmissive
    - ior: index of refraction for Snell's law
    - thickness: for volumetric effects -/
structure TransmissionLayer where
  transmission : UnitValue
  ior : IOR
  thickness : ℝ
  thickness_nonneg : thickness ≥ 0

namespace TransmissionLayer

def opaqueMaterial : TransmissionLayer where
  transmission := UnitValue.zero
  ior := IOR.glass
  thickness := 0
  thickness_nonneg := by norm_num

def glass : TransmissionLayer where
  transmission := UnitValue.one
  ior := IOR.glass
  thickness := 0.1
  thickness_nonneg := by norm_num

def thinGlass : TransmissionLayer where
  transmission := UnitValue.one
  ior := IOR.glass
  thickness := 0.01
  thickness_nonneg := by norm_num

def water : TransmissionLayer where
  transmission := UnitValue.one
  ior := IOR.water
  thickness := 1
  thickness_nonneg := by norm_num

def diamond : TransmissionLayer where
  transmission := UnitValue.one
  ior := IOR.diamond
  thickness := 0.05
  thickness_nonneg := by norm_num

end TransmissionLayer

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- SECTION 10: SHEEN LAYER
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/-- Sheen layer (fabric, velvet).
    
    Adds soft highlight at grazing angles, typical of cloth materials. -/
structure SheenLayer where
  intensity : UnitValue
  color : ColorRGB
  roughness : UnitValue

namespace SheenLayer

def none : SheenLayer where
  intensity := UnitValue.zero
  color := ColorRGB.white
  roughness := UnitValue.half

def fabric : SheenLayer where
  intensity := UnitValue.one
  color := ColorRGB.white
  roughness := { value := 0.3, ge_0 := by norm_num, le_1 := by norm_num }

def velvet : SheenLayer where
  intensity := UnitValue.one
  color := ColorRGB.white
  roughness := { value := 0.8, ge_0 := by norm_num, le_1 := by norm_num }

end SheenLayer

end Hydrogen.Material
