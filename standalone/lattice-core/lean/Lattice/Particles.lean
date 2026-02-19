/-
  Lattice.Particles - Particle system types

  Main re-export module for particle types.

  Source: ui/src/types/particles.ts (644 lines)

  Module structure (to stay under 500 lines each):
  - Enums.lean: Shape, behavior, blend mode enumerations
  - Physics.lean: Collision, flocking, spring, SPH configs
  - Emitter.lean: Emitter configurations
  - Rendering.lean: Render options, connections
  - Audio.lean: Audio bindings and mappings
  - Legacy.lean: Legacy particle types for backwards compatibility
-/

import Lattice.Primitives
import Lattice.Particles.Enums
import Lattice.Particles.Physics
import Lattice.Particles.Emitter
import Lattice.Particles.Rendering
import Lattice.Particles.Audio
import Lattice.Particles.Legacy

namespace Lattice.Particles

open Lattice.Primitives

/-! ## Particle Layer Data -/

/-- Complete particle layer data -/
structure ParticleLayerData where
  systemConfig : Emitter.ParticleSystemLayerConfig
  emitters : Array Emitter.ParticleEmitterConfig
  gravityWells : Array Physics.GravityWellConfig
  vortices : Array Physics.VortexConfig
  modulations : Array Rendering.ParticleModulationConfig
  renderOptions : Rendering.ParticleRenderOptions
  turbulenceFields : Array Physics.TurbulenceFieldConfig
  subEmitters : Array Emitter.SubEmitterConfig
  flocking : Option Physics.FlockingConfig
  collision : Option Physics.CollisionConfig
  audioBindings : Array Audio.AudioBindingConfig
  audioMappings : Array Audio.AudioParticleMapping
  exportEnabled : Bool
  exportFormat : Option NonEmptyString
  -- Time remapping support
  speedMapEnabled : Bool
  speedMapPropertyId : Option NonEmptyString  -- AnimatableProperty ID
  -- CC Particle World style visualization
  visualization : Option Emitter.ParticleVisualizationConfig
  -- Particle groups for selective interactions
  groups : Array Physics.ParticleGroupConfig
  -- Spring system for cloth/soft body
  springConfig : Option Physics.SpringSystemConfig
  -- SPH fluid simulation
  sphConfig : Option Physics.SPHFluidConfig
  -- LOD (Level of Detail)
  lodConfig : Option Physics.ParticleLODConfig
  -- DOF (Depth of Field)
  dofConfig : Option Physics.ParticleDOFConfig
  -- Custom collision planes
  collisionPlanes : Array Physics.CollisionPlaneConfig
  deriving Repr

-- Re-export all submodules
export Enums (
  EmitterShape
  BoundaryBehavior
  ParticleShape
  ParticleBlendMode
  BuiltinShape
  ParticleTextureType
  LegacyEmitterType
  ParticleFalloff
  SPHPreset
  SpringStructureType
  SpritePlayMode
  SplineEmitMode
  DepthMode
  MaskChannel
  SubEmitterTrigger
  AudioFeatureName
  AudioTargetType
  AudioCurveType
  AudioTriggerMode
  ModulationProperty
  AudioMappingParameter
  MeshMode
  MeshGeometry
  FloorBehavior
)

export Physics (
  ParticleVec3
  CollisionPlaneConfig
  CollisionConfig
  FlockingConfig
  SpringStructure
  SpringSystemConfig
  SPHFluidConfig
  TurbulenceFieldConfig
  GravityWellConfig
  VortexConfig
  ParticleLODConfig
  ParticleDOFConfig
  ParticleGroupConfig
)

export Emitter (
  DepthMapEmission
  MaskEmission
  SplinePathEmission
  SpriteConfig
  ParticleEmitterConfig
  SubEmitterConfig
  ParticleSystemLayerConfig
  ParticleVisualizationConfig
)

export Rendering (
  ConnectionRenderConfig
  ParticleRenderOptions
  ParticleModulationConfig
)

export Audio (
  AudioBindingConfig
  AudioParticleMapping
)

export Legacy (
  LegacyParticleEmitter
  ExtractedRegion
  LegacyParticleTexture
  LegacyParticlePhysics
  LegacyParticleRendering
  LegacyParticleData
)

end Lattice.Particles
