/-
  Lattice.Schemas.Settings.ParticlePreferencesSchema

  Particle preferences validation for localStorage settings.

  Source: ui/src/schemas/settings/particle-preferences-schema.ts
-/

import Lattice.Schemas.SharedValidation

namespace Lattice.Schemas.Settings.ParticlePreferencesSchema

--------------------------------------------------------------------------------
-- Enums
--------------------------------------------------------------------------------

/-- Rendering backend options -/
inductive RenderingBackend where
  | auto
  | webgpu
  | webgl2
  | cpu
  deriving Repr, DecidableEq, Inhabited

def renderingBackendFromString : String → Option RenderingBackend
  | "auto" => some .auto
  | "webgpu" => some .webgpu
  | "webgl2" => some .webgl2
  | "cpu" => some .cpu
  | _ => none

def renderingBackendToString : RenderingBackend → String
  | .auto => "auto"
  | .webgpu => "webgpu"
  | .webgl2 => "webgl2"
  | .cpu => "cpu"

/-- Simulation mode options -/
inductive SimulationMode where
  | realtime
  | cached
  | baked
  deriving Repr, DecidableEq, Inhabited

def simulationModeFromString : String → Option SimulationMode
  | "realtime" => some .realtime
  | "cached" => some .cached
  | "baked" => some .baked
  | _ => none

def simulationModeToString : SimulationMode → String
  | .realtime => "realtime"
  | .cached => "cached"
  | .baked => "baked"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

def MAX_CHECKPOINT_INTERVAL : Nat := 10000
def MAX_CACHE_MEMORY_MB : Nat := 100000
def MAX_PARTICLES_PER_LAYER : Nat := 100000000
def MAX_TARGET_FPS : Nat := 120
def MIN_TARGET_FPS : Nat := 1

--------------------------------------------------------------------------------
-- Particle Preferences
--------------------------------------------------------------------------------

/-- Particle preferences structure -/
structure ParticlePreferences where
  renderingBackend : RenderingBackend
  simulationMode : SimulationMode
  cacheCheckpointInterval : Nat
  maxCacheMemoryMB : Nat
  maxParticlesPerLayer : Nat
  enableGPUCompute : Bool
  targetFPS : Nat
  enableMotionBlur : Bool
  enableSoftParticles : Bool
  enableShadows : Bool
  lodEnabled : Bool
  deriving Repr, Inhabited

/-- Default particle preferences -/
def defaultParticlePreferences : ParticlePreferences :=
  { renderingBackend := .auto
  , simulationMode := .realtime
  , cacheCheckpointInterval := 100
  , maxCacheMemoryMB := 4096
  , maxParticlesPerLayer := 1000000
  , enableGPUCompute := true
  , targetFPS := 60
  , enableMotionBlur := false
  , enableSoftParticles := true
  , enableShadows := false
  , lodEnabled := true
  }

--------------------------------------------------------------------------------
-- Validation
--------------------------------------------------------------------------------

open SharedValidation in
/-- Validate ParticlePreferences -/
def validateParticlePreferences (pp : ParticlePreferences) : Except ValidationError ParticlePreferences := do
  _ ← validatePositiveInt "cacheCheckpointInterval" MAX_CHECKPOINT_INTERVAL pp.cacheCheckpointInterval.toInt
  _ ← validatePositiveInt "maxCacheMemoryMB" MAX_CACHE_MEMORY_MB pp.maxCacheMemoryMB.toInt
  _ ← validatePositiveInt "maxParticlesPerLayer" MAX_PARTICLES_PER_LAYER pp.maxParticlesPerLayer.toInt
  if pp.targetFPS < MIN_TARGET_FPS || pp.targetFPS > MAX_TARGET_FPS then
    throw (mkError "targetFPS" s!"must be between {MIN_TARGET_FPS} and {MAX_TARGET_FPS}")
  pure pp

/-- Safe validation -/
def safeValidateParticlePreferences (pp : ParticlePreferences) : Option ParticlePreferences :=
  match validateParticlePreferences pp with
  | .ok p => some p
  | .error _ => none

end Lattice.Schemas.Settings.ParticlePreferencesSchema
