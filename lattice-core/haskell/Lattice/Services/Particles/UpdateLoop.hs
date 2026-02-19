{-|
Module      : Lattice.Services.Particles.UpdateLoop
Description : Main Particle System Update Orchestration
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure functions for the main particle system update loop:
- Step orchestration (emission, forces, position, death)
- Global configuration
- Frame state management
- System-level operations

This module composes the other particle modules into a
coherent update pipeline. All state is explicit - no hidden
mutation.

Source: ui/src/services/particleSystem.ts (step method, lines 481-718)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.UpdateLoop
  ( -- * Types
    SystemConfig(..)
  , SystemState(..)
  , StepInput(..)
  , StepResult(..)
    -- * Update Functions
  , stepParticle
  , stepSystem
    -- * Force Application
  , applyAllForces
  , calculateTotalForce
    -- * Global Properties
  , calculateWindForce
  , applyGlobalGravity
  , applyGlobalFriction
    -- * Lifecycle
  , processDeaths
  , filterExpired
  ) where

import Lattice.Services.Particles.Forces
import Lattice.Services.Particles.Lifecycle
import Lattice.Services.Particles.Modulation
import Lattice.Services.Particles.Collision (CollisionConfig)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Global particle system configuration
data SystemConfig = SystemConfig
  { scMaxParticles :: Int        -- ^ Maximum particles allowed
  , scGravity :: Double          -- ^ Global gravity (positive = down)
  , scWindDirection :: Double    -- ^ Wind direction in degrees
  , scWindStrength :: Double     -- ^ Wind force strength
  , scFriction :: Double         -- ^ Global friction (0-1)
  , scCollision :: CollisionConfig
  , scRespectMaskBoundary :: Bool
  } deriving (Show, Eq)

-- | Mutable system state (carried between frames)
data SystemState = SystemState
  { ssFrameCount :: Int          -- ^ Current frame number
  , ssNoiseTime :: Double        -- ^ Turbulence noise evolution time
  , ssNextParticleId :: Int      -- ^ Next particle ID to assign
  } deriving (Show, Eq)

-- | Input data for a single update step
data StepInput = StepInput
  { siDeltaTime :: Double
  , siGravityWells :: [GravityWell]
  , siVortices :: [Vortex]
  , siLorenzAttractors :: [LorenzAttractor]
  , siModulations :: [ParticleModulation]
  , siAudioGravity :: Maybe Double     -- ^ Audio-reactive gravity override
  , siAudioWindStrength :: Maybe Double
  , siTurbulenceNoise :: [(Double, Double)]  -- ^ Pre-computed noise per particle
  } deriving (Show, Eq)

-- | Result of a single update step
data StepResult = StepResult
  { srParticles :: [Particle]        -- ^ Updated particles
  , srNewState :: SystemState        -- ^ Updated system state
  , srDeadParticles :: [Particle]    -- ^ Particles that died (for sub-emitters)
  , srNewParticleCount :: Int        -- ^ Count of new particles spawned
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Main Update
--------------------------------------------------------------------------------

-- | Step a single particle through one frame.
--
-- Applies: gravity, wind, forces, position update, modulation, age
stepParticle
  :: SystemConfig
  -> StepInput
  -> (Double, Double)  -- ^ Pre-computed turbulence noise (nx, ny)
  -> Particle
  -> Particle
stepParticle config input (noiseX, noiseY) particle =
  let dt = siDeltaTime input

      -- 1. Store previous position for trails
      p1 = storePreviousPosition particle

      -- 2. Apply global gravity
      p2 = applyGlobalGravity p1 (effectiveGravity config (siAudioGravity input)) dt

      -- 3. Apply wind
      p3 = applyWind p2 (scWindDirection config) (effectiveWind config (siAudioWindStrength input)) dt

      -- 4. Apply force fields
      p4 = applyAllForces p3 (siGravityWells input) (siVortices input) (siLorenzAttractors input) dt

      -- 5. Apply turbulence (pre-computed noise)
      p5 = applyTurbulenceForce p4 noiseX noiseY dt

      -- 6. Apply friction
      p6 = applyGlobalFriction p5 (scFriction config)

      -- 7. Update position
      p7 = updatePosition p6 dt

      -- 8. Apply modulations
      modResult = applyModulations (siModulations input) (pEmitterId p7) (lifeRatio p7)
      p8 = applyModulationResult p7 modResult

      -- 9. Increment age
      p9 = incrementAge p8 dt

  in p9

-- | Step the entire system for one frame.
stepSystem
  :: SystemConfig
  -> SystemState
  -> StepInput
  -> [Particle]
  -> StepResult
stepSystem config state input particles =
  let -- Update all particles
      noiseList = siTurbulenceNoise input ++ repeat (0, 0)  -- Pad with zeros
      updatedParticles = zipWith (stepParticle config input) noiseList particles

      -- Separate dead and alive
      (alive, dead) = filterExpired updatedParticles

      -- Update state
      newState = state
        { ssFrameCount = ssFrameCount state + 1
        , ssNoiseTime = ssNoiseTime state + siDeltaTime input
        }

  in StepResult
       { srParticles = alive
       , srNewState = newState
       , srDeadParticles = dead
       , srNewParticleCount = 0  -- Emission handled separately
       }

--------------------------------------------------------------------------------
-- Force Application
--------------------------------------------------------------------------------

-- | Apply all force fields to a particle.
applyAllForces
  :: Particle
  -> [GravityWell]
  -> [Vortex]
  -> [LorenzAttractor]
  -> Double
  -> Particle
applyAllForces p wells vortices attractors dt =
  let -- Gravity wells
      wellForce = applyGravityWells (pX p) (pY p) wells dt

      -- Vortices
      vortexForce' = applyVortices (pX p) (pY p) vortices dt

      -- Lorenz attractors
      lorenzForce' = applyLorenzAttractors (pX p) (pY p) attractors dt

      -- Sum forces
      totalVx = vx wellForce + vx vortexForce' + vx lorenzForce'
      totalVy = vy wellForce + vy vortexForce' + vy lorenzForce'

  in p { pVx = pVx p + totalVx, pVy = pVy p + totalVy }

-- | Calculate total force from all fields (for visualization).
calculateTotalForce
  :: Double -> Double
  -> [GravityWell] -> [Vortex] -> [LorenzAttractor]
  -> Double
  -> Vec2
calculateTotalForce x y wells vortices attractors dt =
  let well = applyGravityWells x y wells dt
      vort = applyVortices x y vortices dt
      lor = applyLorenzAttractors x y attractors dt
  in Vec2 (vx well + vx vort + vx lor) (vy well + vy vort + vy lor)

--------------------------------------------------------------------------------
-- Global Properties
--------------------------------------------------------------------------------

-- | Get effective gravity (with audio override).
effectiveGravity :: SystemConfig -> Maybe Double -> Double
effectiveGravity config audioVal =
  case audioVal of
    Just v | not (isNaN v) && not (isInfinite v) -> v
    _ -> scGravity config

-- | Get effective wind strength (with audio override).
effectiveWind :: SystemConfig -> Maybe Double -> Double
effectiveWind config audioVal =
  case audioVal of
    Just v | not (isNaN v) && not (isInfinite v) && v >= 0 -> v
    _ -> scWindStrength config

-- | Apply global gravity to particle.
applyGlobalGravity :: Particle -> Double -> Double -> Particle
applyGlobalGravity p gravity dt =
  p { pVy = pVy p + gravity * 0.001 * dt }

-- | Calculate wind force vector.
calculateWindForce :: Double -> Double -> Double -> Vec2
calculateWindForce direction strength dt =
  windForce direction strength dt

-- | Apply wind force to particle.
applyWind :: Particle -> Double -> Double -> Double -> Particle
applyWind p direction strength dt =
  let wind = windForce direction strength dt
  in p { pVx = pVx p + vx wind, pVy = pVy p + vy wind }

-- | Apply global friction to particle velocity.
applyGlobalFriction :: Particle -> Double -> Particle
applyGlobalFriction p friction =
  let factor = 1 - max 0 (min 1 friction)
  in p { pVx = pVx p * factor, pVy = pVy p * factor }

-- | Apply turbulence noise force.
applyTurbulenceForce :: Particle -> Double -> Double -> Double -> Particle
applyTurbulenceForce p noiseX noiseY dt =
  p { pVx = pVx p + noiseX * 0.001 * dt
    , pVy = pVy p + noiseY * 0.001 * dt
    }

--------------------------------------------------------------------------------
-- Lifecycle
--------------------------------------------------------------------------------

-- | Separate particles into alive and dead.
filterExpired :: [Particle] -> ([Particle], [Particle])
filterExpired = foldr separate ([], [])
  where
    separate p (alive, dead) =
      if isExpired p
      then (alive, p : dead)
      else (p : alive, dead)

-- | Process dead particles for sub-emitter triggers.
processDeaths :: [Particle] -> [Particle]
processDeaths = filter isExpired

-- | Apply modulation result to particle.
applyModulationResult :: Particle -> ModulationResult -> Particle
applyModulationResult p mr =
  let (rMod, gMod, bMod) = mrColorMult mr
      newColor = baseToCurrentColor (pBaseColor p) (rMod, gMod, bMod, mrOpacityMult mr)
      newSize = baseToCurrentSize (pBaseSize p) (mrSizeMult mr)
  in p { pColor = newColor, pSize = newSize }
