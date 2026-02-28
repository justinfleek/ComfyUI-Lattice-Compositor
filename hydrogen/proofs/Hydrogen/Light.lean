/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                                 HYDROGEN // LIGHT
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

  Complete light system for Hydrogen 3D rendering.
  
  This module re-exports all light types and functions:
  
  LIGHT TYPES:
    - DirectionalLight : Parallel rays (sun, distant light)
    - PointLight       : Omnidirectional point source (bulb)
    - SpotLight        : Cone of light (flashlight, stage light)
  
  ATTENUATION:
    - distanceAttenuation : Intensity falloff with distance
    - cutoffFactor        : Hard/soft distance cutoff
    - spotFactor          : Angular falloff for spotlights
    - inverseSquareAttenuation : Physically correct 1/d² law
  
  SHADOWS:
    - ShadowValue      : In-shadow percentage [0, 1]
    - shadowComparison : Depth-based shadow test
    - adaptiveBias     : Angle-dependent bias to prevent acne
    - pcfCombine       : Percentage closer filtering
    - CascadeSplits    : Cascaded shadow map configuration
  
  PROVEN INVARIANTS:
    - Attenuation is always in [0, 1]
    - Intensity decreases with distance
    - Shadow values are bounded
    - Unit directions have length 1
    - Irradiance is non-negative
  
  ─────────────────────────────────────────────────────────────────────────────
  MODULE STRUCTURE
  ─────────────────────────────────────────────────────────────────────────────
  
  Light/
  ├── Types.lean       — Core types: ColorRGB, Intensity, Decay, ConeAngle
  ├── Attenuation.lean — Distance falloff and cutoff functions
  ├── Directional.lean — DirectionalLight, UnitDirection, irradiance
  ├── Point.lean       — PointLight, position-based lighting
  ├── Spot.lean        — SpotLight, cone angles, penumbra
  └── Shadow.lean      — Shadow mapping, bias, PCF, cascades
  
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Hydrogen.Light.Types
import Hydrogen.Light.Attenuation
import Hydrogen.Light.Directional
import Hydrogen.Light.Point
import Hydrogen.Light.Spot
import Hydrogen.Light.Shadow
