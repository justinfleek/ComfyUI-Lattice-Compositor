/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                               HYDROGEN // MATERIAL
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Complete PBR material system for Hydrogen 3D rendering.
  
  This module re-exports all material types and functions:
  
  CORE TYPES:
    - UnitValue        : Values bounded to [0, 1] with algebraic proofs
    - IOR              : Index of refraction with F0 conversion
    - BlendState       : Alpha blending configuration
    - DepthState       : Depth testing and writing
    - StencilState     : Stencil operations
    - MaterialBase     : Common material properties
  
  MATERIAL LAYERS:
    - AlbedoLayer      : Base color/diffuse
    - RoughnessLayer   : Surface roughness (α = roughness²)
    - MetalnessLayer   : Metallic workflow
    - NormalLayer      : Normal mapping
    - EmissiveLayer    : Self-illumination
    - OcclusionLayer   : Ambient occlusion
    - ClearcoatLayer   : Clear coat for car paint, etc.
    - TransmissionLayer: Glass/liquid transmission
    - SheenLayer       : Fabric sheen
  
  BRDF MODELS:
    - lambertianFactor : Ideal diffuse (1/π)
    - fresnelSchlick   : Angle-dependent reflectance
    - ggxDistribution  : GGX/Trowbridge-Reitz NDF
    - smithGeometry    : Smith-GGX shadowing/masking
    - cookTorranceSpecular : Full specular BRDF
  
  SPARKLE/GLITTER:
    - lambertProject   : Equal-area hemisphere-to-disk projection
    - ggxJacobian      : GGX stretch transformation Jacobian
    - gaussian2D       : 2D Gaussian for particle antialiasing
    - particleContribution : Per-particle energy (1/N)
    - lodResolution    : Level-of-detail for particle selection
  
  IMAGE SIGNAL PROCESSING (ISP):
    - exposureFactor   : Exposure compensation via exp2
    - vignettingFalloff: Radial light falloff polynomial
    - softplus/sigmoid : Activation functions for parameter transforms
    - CRF parameters   : Camera response function toe/shoulder/gamma
    - lerp             : Linear interpolation
  
  PROVEN INVARIANTS:
    - UnitValue operations preserve bounds
    - Fresnel reflectance in [0, 1]
    - GGX distribution is non-negative
    - Smith geometry term in [0, 1]
    - Fresnel + diffuse = 1 (energy conservation)
    - Cook-Torrance is symmetric (Helmholtz reciprocity)
    - Fresnel is monotonically decreasing in cosTheta
    - Lambert projection bounded to disk
    - GGX Jacobian is strictly positive
    - Gaussian PDF is non-negative
    - N particles × (1/N) contribution = 1 (sparkle energy conservation)
    - Higher LOD means lower resolution (exponential decay)
    - Exposure factor is strictly positive for any parameter
    - Vignetting bounded to [0, 1] with proper coefficients
    - Softplus is strictly positive
    - Sigmoid is bounded to (0, 1)
    - Gamma correction preserves [0, 1]
  
  ─────────────────────────────────────────────────────────────────────────────
  MODULE STRUCTURE
  ─────────────────────────────────────────────────────────────────────────────
  
  Material/
  ├── Types.lean   — Core types: UnitValue, IOR, BlendState, MaterialBase
  ├── Layer.lean   — Material layers: albedo, roughness, metalness, etc.
  ├── BRDF.lean    — Bidirectional reflectance: Fresnel, GGX, Smith, Cook-Torrance
  ├── Sparkle.lean — Stochastic glitter: Lambert projection, Gaussian, LOD
  └── ISP.lean     — Image signal processing: exposure, vignetting, CRF
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Material.Types
import Hydrogen.Material.Layer
import Hydrogen.Material.BRDF
import Hydrogen.Material.Sparkle
import Hydrogen.Material.ISP
