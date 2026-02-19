/-
  Lattice.Schemas.Exports.ParticleSchema

  Particle trajectory export format types.

  Source: ui/src/schemas/exports/particle-schema.ts
-/

namespace Lattice.Schemas.Exports.ParticleSchema

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_FRAMES : Nat := 100000
def MAX_PARTICLES : Nat := 10000000
def MAX_VELOCITY : Float := 100000.0
def MAX_PARTICLE_RATE : Nat := 1000000
def MAX_COORDINATE : Float := 16384.0

--------------------------------------------------------------------------------
-- Structures
--------------------------------------------------------------------------------

/-- Particle position at a frame -/
structure ParticlePosition where
  frame : Nat
  x : Float
  y : Float
  z : Option Float := Option.none
  deriving Repr, Inhabited

/-- Particle velocity at a frame -/
structure ParticleVelocity where
  frame : Nat
  vx : Float
  vy : Float
  vz : Float
  deriving Repr, Inhabited

/-- Particle color (normalized 0-1) -/
structure ParticleColor where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited

/-- Particle data with full lifecycle -/
structure ParticleData where
  id : Nat
  birthFrame : Nat
  deathFrame : Nat
  positions : Array ParticlePosition
  velocities : Option (Array ParticleVelocity) := Option.none
  size : Option (Array Float) := Option.none
  opacity : Option (Array Float) := Option.none
  color : Option (Array ParticleColor) := Option.none
  deriving Repr, Inhabited

/-- 3D position -/
structure Position3D where
  x : Float
  y : Float
  z : Float
  deriving Repr, Inhabited

/-- Emitter configuration -/
structure EmitterConfig where
  emitterType : String
  position : Position3D
  rate : Nat
  lifetime : Nat
  deriving Repr, Inhabited

/-- Particle trajectory export metadata -/
structure ParticleTrajectoryMetadata where
  totalParticles : Nat
  frameCount : Nat
  maxActiveParticles : Nat
  deriving Repr, Inhabited

/-- Particle trajectory export -/
structure ParticleTrajectoryExport where
  particles : Array ParticleData
  emitterConfig : EmitterConfig
  metadata : ParticleTrajectoryMetadata
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

/-- Check if particle position is valid -/
def ParticlePosition.isValid (p : ParticlePosition) : Bool :=
  p.frame <= MAX_FRAMES

/-- Check if particle velocity is valid -/
def ParticleVelocity.isValid (v : ParticleVelocity) : Bool :=
  v.frame <= MAX_FRAMES &&
  v.vx >= -MAX_VELOCITY && v.vx <= MAX_VELOCITY &&
  v.vy >= -MAX_VELOCITY && v.vy <= MAX_VELOCITY &&
  v.vz >= -MAX_VELOCITY && v.vz <= MAX_VELOCITY

/-- Check if particle color is normalized -/
def ParticleColor.isValid (c : ParticleColor) : Bool :=
  c.r >= 0 && c.r <= 1 &&
  c.g >= 0 && c.g <= 1 &&
  c.b >= 0 && c.b <= 1

/-- Check if particle data is valid -/
def ParticleData.isValid (d : ParticleData) : Bool :=
  d.id <= MAX_PARTICLES &&
  d.birthFrame <= MAX_FRAMES &&
  d.deathFrame <= MAX_FRAMES &&
  d.deathFrame >= d.birthFrame &&
  d.positions.size == (d.deathFrame - d.birthFrame + 1)

/-- Check if emitter config is valid -/
def EmitterConfig.isValid (c : EmitterConfig) : Bool :=
  c.rate <= MAX_PARTICLE_RATE &&
  c.lifetime <= MAX_FRAMES

/-- Check if metadata is valid -/
def ParticleTrajectoryMetadata.isValid (m : ParticleTrajectoryMetadata) : Bool :=
  m.totalParticles <= MAX_PARTICLES &&
  m.frameCount <= MAX_FRAMES &&
  m.maxActiveParticles <= MAX_PARTICLES

/-- Check if trajectory export is valid -/
def ParticleTrajectoryExport.isValid (e : ParticleTrajectoryExport) : Bool :=
  e.metadata.isValid &&
  e.emitterConfig.isValid &&
  e.particles.size == e.metadata.totalParticles

end Lattice.Schemas.Exports.ParticleSchema
