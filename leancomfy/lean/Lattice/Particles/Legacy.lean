/-
  Lattice.Particles.Legacy - Legacy particle types for backwards compatibility

  Part of Particles module. Max 500 lines.

  Source: ui/src/types/particles.ts (lines 14-100)
-/

import Lattice.Primitives
import Lattice.Particles.Enums

namespace Lattice.Particles.Legacy

open Lattice.Primitives
open Lattice.Particles.Enums

/-! ## Legacy Particle Emitter -/

/-- Legacy particle emitter configuration -/
structure LegacyParticleEmitter where
  emitterType : LegacyEmitterType
  positionPropertyId : NonEmptyString   -- AnimatableProperty ID for position
  pathLayerId : Option NonEmptyString   -- For path emitter
  ratePropertyId : NonEmptyString       -- AnimatableProperty ID for rate
  lifetimePropertyId : NonEmptyString   -- AnimatableProperty ID for lifetime
  lifetimeVariance : Float              -- 0-1 randomness
  speedPropertyId : NonEmptyString
  speedVariance : Float
  directionPropertyId : NonEmptyString  -- Degrees
  spreadPropertyId : NonEmptyString     -- Cone angle
  radiusPropertyId : Option NonEmptyString  -- For circle
  widthPropertyId : Option NonEmptyString   -- For box
  heightPropertyId : Option NonEmptyString  -- For box
  lifetimeVariance_ge_0 : lifetimeVariance ≥ 0
  lifetimeVariance_le_1 : lifetimeVariance ≤ 1
  lifetimeVariance_finite : lifetimeVariance.isFinite
  speedVariance_ge_0 : speedVariance ≥ 0
  speedVariance_le_1 : speedVariance ≤ 1
  speedVariance_finite : speedVariance.isFinite
  deriving Repr

/-! ## Legacy Particle Texture -/

/-- Extracted region bounds -/
structure ExtractedRegion where
  x : Float
  y : Float
  width : Float
  height : Float
  x_ge_0 : x ≥ 0
  x_finite : x.isFinite
  y_ge_0 : y ≥ 0
  y_finite : y.isFinite
  width_positive : width > 0
  width_finite : width.isFinite
  height_positive : height > 0
  height_finite : height.isFinite
  deriving Repr

/-- Legacy particle texture configuration -/
structure LegacyParticleTexture where
  textureType : ParticleTextureType
  builtinShape : Option BuiltinShape
  imageAssetId : Option NonEmptyString
  generatedPrompt : Option String       -- AI-generated (SDXL)
  extractedFromAssetId : Option NonEmptyString
  extractedRegion : Option ExtractedRegion
  -- PBR maps (optional, for 3D-like rendering)
  albedo : Option String                -- Base64
  normal : Option String
  roughness : Option String
  deriving Repr

/-! ## Legacy Particle Physics -/

/-- Legacy particle physics configuration -/
structure LegacyParticlePhysics where
  gravityPropertyId : NonEmptyString    -- AnimatableProperty ID for gravity vector
  windPropertyId : NonEmptyString       -- AnimatableProperty ID for wind vector
  dragPropertyId : NonEmptyString       -- AnimatableProperty ID for drag
  turbulencePropertyId : NonEmptyString -- AnimatableProperty ID for turbulence
  turbulenceScale : Float               -- Noise scale
  depthCollision : Bool
  depthLayerId : Option NonEmptyString
  bounciness : Float                    -- 0-1
  turbulenceScale_positive : turbulenceScale > 0
  turbulenceScale_finite : turbulenceScale.isFinite
  bounciness_ge_0 : bounciness ≥ 0
  bounciness_le_1 : bounciness ≤ 1
  bounciness_finite : bounciness.isFinite
  deriving Repr

/-! ## Legacy Particle Rendering -/

/-- Legacy particle rendering configuration -/
structure LegacyParticleRendering where
  startSizePropertyId : NonEmptyString
  endSizePropertyId : NonEmptyString
  sizeVariance : Float
  startColorPropertyId : NonEmptyString -- Hex color AnimatableProperty
  endColorPropertyId : NonEmptyString
  colorVariance : Float
  startOpacityPropertyId : NonEmptyString
  endOpacityPropertyId : NonEmptyString
  rotationPropertyId : NonEmptyString
  rotationSpeedPropertyId : NonEmptyString
  blendMode : NonEmptyString            -- BlendMode name
  stretchToVelocity : Bool
  stretchFactor : Float
  sizeVariance_ge_0 : sizeVariance ≥ 0
  sizeVariance_le_1 : sizeVariance ≤ 1
  sizeVariance_finite : sizeVariance.isFinite
  colorVariance_ge_0 : colorVariance ≥ 0
  colorVariance_le_1 : colorVariance ≤ 1
  colorVariance_finite : colorVariance.isFinite
  stretchFactor_ge_0 : stretchFactor ≥ 0
  stretchFactor_finite : stretchFactor.isFinite
  deriving Repr

/-! ## Legacy Particle Data -/

/-- Legacy particle data (for backwards compatibility) -/
structure LegacyParticleData where
  emitter : LegacyParticleEmitter
  texture : LegacyParticleTexture
  physics : LegacyParticlePhysics
  rendering : LegacyParticleRendering
  deriving Repr

end Lattice.Particles.Legacy
