/-
  Lattice.Particles.Enums - Particle system enumerations

  Part of Particles module. Max 500 lines.

  Source: ui/src/types/particles.ts
-/

import Lattice.Primitives

namespace Lattice.Particles.Enums

open Lattice.Primitives

/-! ## Emitter Shapes -/

/-- Particle emitter shape types -/
inductive EmitterShape where
  | point
  | line
  | circle
  | box
  | sphere
  | ring
  | spline
  | depthMap
  | mask
  | cone
  | image       -- Emit from non-transparent pixels
  | depthEdge   -- Emit from depth discontinuities
  | mesh        -- Emit from mesh vertices
  deriving Repr, BEq, DecidableEq

/-! ## Boundary Behaviors -/

/-- Boundary behavior for particles -/
inductive BoundaryBehavior where
  | bounce
  | kill
  | wrap
  | stick
  | none
  deriving Repr, BEq, DecidableEq

/-! ## Particle Shape -/

/-- Renderable particle shape -/
inductive ParticleShape where
  | circle
  | square
  | triangle
  | star
  deriving Repr, BEq, DecidableEq

/-! ## Blend Mode -/

/-- Particle blend mode -/
inductive ParticleBlendMode where
  | normal
  | additive
  | multiply
  | screen
  deriving Repr, BEq, DecidableEq

/-! ## Builtin Shapes -/

/-- Built-in particle texture shapes -/
inductive BuiltinShape where
  | circle
  | square
  | star
  | spark
  | smoke
  deriving Repr, BEq, DecidableEq

/-! ## Texture Types -/

/-- Particle texture type -/
inductive ParticleTextureType where
  | builtin
  | image
  | generated
  | extracted
  deriving Repr, BEq, DecidableEq

/-! ## Emitter Types (Legacy) -/

/-- Legacy emitter type -/
inductive LegacyEmitterType where
  | point
  | line
  | circle
  | box
  | path
  deriving Repr, BEq, DecidableEq

/-! ## Force Falloff -/

/-- Force falloff type -/
inductive ParticleFalloff where
  | linear
  | quadratic
  | constant
  deriving Repr, BEq, DecidableEq

/-! ## SPH Preset -/

/-- SPH fluid preset -/
inductive SPHPreset where
  | water
  | honey
  | lava
  | gas
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Spring Structure Type -/

/-- Spring structure type -/
inductive SpringStructureType where
  | cloth
  | rope
  | softbody
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Sprite Play Mode -/

/-- Sprite animation play mode -/
inductive SpritePlayMode where
  | loop
  | once
  | pingpong
  | random
  deriving Repr, BEq, DecidableEq

/-! ## Spline Emit Mode -/

/-- Spline path emission mode -/
inductive SplineEmitMode where
  | uniform
  | random
  | start
  | end
  | sequential
  deriving Repr, BEq, DecidableEq

/-! ## Depth Mode -/

/-- Depth value interpretation -/
inductive DepthMode where
  | nearWhite
  | nearBlack
  deriving Repr, BEq, DecidableEq

/-! ## Mask Channel -/

/-- Channel to use for mask emission -/
inductive MaskChannel where
  | luminance
  | alpha
  | red
  | green
  | blue
  deriving Repr, BEq, DecidableEq

/-! ## Sub Emitter Trigger -/

/-- Sub-emitter trigger event -/
inductive SubEmitterTrigger where
  | death
  deriving Repr, BEq, DecidableEq

/-! ## Audio Features -/

/-- Audio feature for particle binding -/
inductive AudioFeatureName where
  | amplitude
  | bass
  | mid
  | high
  | beat
  | spectralCentroid
  | rms
  | onsets
  deriving Repr, BEq, DecidableEq

/-! ## Audio Target -/

/-- Audio binding target type -/
inductive AudioTargetType where
  | emitter
  | system
  | forceField
  deriving Repr, BEq, DecidableEq

/-! ## Audio Curve -/

/-- Audio response curve type -/
inductive AudioCurveType where
  | linear
  | exponential
  | logarithmic
  | step
  deriving Repr, BEq, DecidableEq

/-! ## Audio Trigger Mode -/

/-- Audio trigger mode -/
inductive AudioTriggerMode where
  | continuous
  | onThreshold
  | onBeat
  deriving Repr, BEq, DecidableEq

/-! ## Modulation Property -/

/-- Modulation target property -/
inductive ModulationProperty where
  | size
  | speed
  | opacity
  | colorR
  | colorG
  | colorB
  deriving Repr, BEq, DecidableEq

/-! ## Audio Mapping Parameter -/

/-- Audio mapping target parameter -/
inductive AudioMappingParameter where
  | emissionRate
  | speed
  | size
  | gravity
  | windStrength
  deriving Repr, BEq, DecidableEq

/-! ## Mesh Mode -/

/-- Particle mesh rendering mode -/
inductive MeshMode where
  | billboard
  | mesh
  deriving Repr, BEq, DecidableEq

/-! ## Mesh Geometry -/

/-- Particle mesh geometry type -/
inductive MeshGeometry where
  | cube
  | sphere
  | cylinder
  | cone
  | torus
  | custom
  deriving Repr, BEq, DecidableEq

/-! ## Floor Behavior -/

/-- Floor collision behavior -/
inductive FloorBehavior where
  | none
  | bounce
  | stick
  | kill
  deriving Repr, BEq, DecidableEq

end Lattice.Particles.Enums
