-- | Lattice.Services.Flow.Patterns - Flow Field Pattern Math
-- |
-- | Pure mathematical functions for Anadol-style generative flow patterns.
-- | These compute positions based on flow field equations without
-- | managing trajectories or state.
-- |
-- | Source: ui/src/services/export/wanMoveFlowGenerators.ts

module Lattice.Services.Flow.Patterns
  ( -- * Types
    Point2D, FlowParams
    -- * Spiral Flow
  , SpiralParams, spiralPosition
    -- * Wave Flow
  , WaveParams, wavePosition
    -- * Explosion Flow
  , ExplosionParams, ExplosionState
  , initExplosionParticle, stepExplosionParticle
    -- * Vortex Flow
  , VortexParams, VortexState
  , initVortexParticle, stepVortexParticle
    -- * River Flow
  , RiverParams, riverPath, riverPosition
    -- * Morph Flow
  , MorphShape(..), MorphEasing(..)
  , MorphParams
  , applyMorphEasing, gridPosition, circlePosition, morphPosition
    -- * Swarm Flow
  , SwarmParams, SwarmParticle
  , cohesionForce, separationForce, boundaryForce
  , clampVelocity, updateSwarmParticle
  ) where

import Prelude
import Data.Int (floor, toNumber, ceil)
import Math (abs, cos, min, max, pi, sin, sqrt) as Math

import Lattice.Services.Noise.SimplexNoise (simplexNoise2D)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D point for flow calculations
type Point2D =
  { x :: Number
  , y :: Number
  }

-- | Flow field parameters common to most patterns
type FlowParams =
  { width :: Number
  , height :: Number
  , seed :: Int
  , noiseStrength :: Number
  }

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

origin :: Point2D
origin = { x: 0.0, y: 0.0 }

clampPoint :: Point2D -> Number -> Number -> Number -> Number -> Point2D
clampPoint p minX minY maxX maxY =
  { x: Math.max minX (Math.min maxX p.x)
  , y: Math.max minY (Math.min maxY p.y)
  }

--------------------------------------------------------------------------------
-- Spiral Flow
--------------------------------------------------------------------------------

-- | Parameters for spiral galaxy flow
type SpiralParams =
  { base :: FlowParams
  , turns :: Number      -- Number of spiral rotations
  , expansion :: Number  -- How much spiral expands over time
  }

-- | Calculate spiral position at time t.
spiralPosition :: SpiralParams -> Number -> Number -> Number -> Number
              -> Point2D -> Number -> Int -> Int -> Point2D
spiralPosition params t armOffset radiusOffset phaseOffset center maxRadius pointIndex frameIndex =
  let fp = params.base
      effectiveT = t + phaseOffset
      angle = armOffset + effectiveT * Math.pi * 2.0 * params.turns
      radius = (radiusOffset + effectiveT * params.expansion) * maxRadius

      noise = simplexNoise2D (toNumber pointIndex * 0.1) (toNumber frameIndex * 0.05) fp.seed
      noisedRadius = radius * (1.0 + (noise - 0.5) * fp.noiseStrength * 2.0)

      x = center.x + Math.cos angle * noisedRadius
      y = center.y + Math.sin angle * noisedRadius

  in clampPoint { x, y } 0.0 0.0 fp.width fp.height

--------------------------------------------------------------------------------
-- Wave Flow
--------------------------------------------------------------------------------

-- | Parameters for wave/ocean flow
type WaveParams =
  { base :: FlowParams
  , amplitude :: Number  -- Wave height (0 = height * 0.15)
  , frequency :: Number  -- Wave oscillations across width
  , speed :: Number      -- Horizontal movement speed
  , layers :: Int        -- Number of wave layers
  }

-- | Calculate wave position at time t.
wavePosition :: WaveParams -> Number -> Number -> Number -> Number -> Number
            -> Int -> Int -> Int -> { pos :: Point2D, visible :: Boolean }
wavePosition params t startX layerY phaseOffset amplitudeVar layer pointIndex frameIndex =
  let fp = params.base
      amplitude = if params.amplitude == 0.0
                  then fp.height * 0.15
                  else params.amplitude

      rawX = startX + t * fp.width * params.speed * 10.0
      x = fmod rawX (fp.width * 1.2) - fp.width * 0.1

      waveAngle = (x / fp.width) * Math.pi * 2.0 * params.frequency +
                  phaseOffset + t * Math.pi * 4.0
      wave = Math.sin waveAngle
      y = layerY + wave * amplitude * amplitudeVar

      noise = simplexNoise2D (x * 0.01) (toNumber frameIndex * 0.05 + toNumber layer) fp.seed
      noisedY = y + (noise - 0.5) * amplitude * fp.noiseStrength * 4.0

      pos = clampPoint { x, y: noisedY } 0.0 0.0 fp.width fp.height
      visible = x >= 0.0 && x <= fp.width
  in { pos, visible }
  where
    fmod a b = a - toNumber (floor (a / b)) * b

--------------------------------------------------------------------------------
-- Explosion Flow
--------------------------------------------------------------------------------

-- | Parameters for explosion/big bang flow
type ExplosionParams =
  { base :: FlowParams
  , speed :: Number       -- Explosion velocity multiplier
  , decay :: Number       -- Velocity decay per frame [0, 1]
  , center :: Point2D     -- Explosion center (origin = canvas center)
  }

-- | Explosion particle state
type ExplosionState =
  { x :: Number
  , y :: Number
  , vx :: Number
  , vy :: Number
  }

-- | Initialize explosion particle.
initExplosionParticle :: ExplosionParams -> Number -> Number -> ExplosionState
initExplosionParticle params angle speed =
  let fp = params.base
      center = if params.center.x == 0.0 && params.center.y == 0.0
               then { x: fp.width / 2.0, y: fp.height / 2.0 }
               else params.center
  in { x: center.x
     , y: center.y
     , vx: Math.cos angle * speed * 20.0
     , vy: Math.sin angle * speed * 20.0
     }

-- | Step explosion particle forward one frame.
stepExplosionParticle :: ExplosionParams -> ExplosionState -> Int -> Int
                     -> { state :: ExplosionState, pos :: Point2D, visible :: Boolean }
stepExplosionParticle params state pointIndex frameIndex =
  let fp = params.base
      noiseX = (simplexNoise2D (toNumber pointIndex * 0.1) (toNumber frameIndex * 0.1) fp.seed - 0.5) *
               fp.noiseStrength * 50.0
      noiseY = (simplexNoise2D (toNumber pointIndex * 0.1 + 100.0) (toNumber frameIndex * 0.1) fp.seed - 0.5) *
               fp.noiseStrength * 50.0

      newX = state.x + state.vx + noiseX
      newY = state.y + state.vy + noiseY
      newVx = state.vx * params.decay
      newVy = state.vy * params.decay

      newState = { x: newX, y: newY, vx: newVx, vy: newVy }
      pos = clampPoint { x: newX, y: newY } 0.0 0.0 fp.width fp.height
      visible = newX >= 0.0 && newX <= fp.width && newY >= 0.0 && newY <= fp.height
  in { state: newState, pos, visible }

--------------------------------------------------------------------------------
-- Vortex Flow
--------------------------------------------------------------------------------

-- | Parameters for vortex/whirlpool flow
type VortexParams =
  { base :: FlowParams
  , strength :: Number    -- Angular velocity multiplier
  , maxRadius :: Number   -- 0 = min(width,height)*0.4
  , center :: Point2D
  }

-- | Vortex particle state
type VortexState =
  { angle :: Number
  , radius :: Number
  }

-- | Initialize vortex particle.
initVortexParticle :: Number -> Number -> VortexState
initVortexParticle startAngle startRadius = { angle: startAngle, radius: startRadius }

-- | Step vortex particle forward one frame.
stepVortexParticle :: VortexParams -> VortexState -> { state :: VortexState, pos :: Point2D }
stepVortexParticle params state =
  let fp = params.base
      maxRadius = if params.maxRadius == 0.0
                  then Math.min fp.width fp.height * 0.4
                  else params.maxRadius
      center = if params.center.x == 0.0 && params.center.y == 0.0
               then { x: fp.width / 2.0, y: fp.height / 2.0 }
               else params.center

      angularSpeed = params.strength * (1.0 + (maxRadius - state.radius) / maxRadius * 2.0)
      newAngle = state.angle + angularSpeed
      newRadius = Math.max 10.0 (state.radius - state.radius * 0.01 * params.strength)

      noise = simplexNoise2D state.angle (state.radius * 0.01) fp.seed
      noisedRadius = newRadius * (1.0 + (noise - 0.5) * fp.noiseStrength)

      x = center.x + Math.cos newAngle * noisedRadius
      y = center.y + Math.sin newAngle * noisedRadius

      newState = { angle: newAngle, radius: newRadius }
      pos = clampPoint { x, y } 0.0 0.0 fp.width fp.height
  in { state: newState, pos }

--------------------------------------------------------------------------------
-- Data River Flow
--------------------------------------------------------------------------------

-- | Parameters for data river flow
type RiverParams =
  { base :: FlowParams
  , riverWidth :: Number  -- 0 = height * 0.3
  , curve :: Number       -- S-curve intensity
  , turbulence :: Number  -- Lane turbulence
  }

-- | Calculate river centerline y-position at x.
riverPath :: RiverParams -> Number -> Number
riverPath params x =
  let fp = params.base
      t = x / fp.width
  in fp.height / 2.0 + Math.sin (t * Math.pi * 2.0 * params.curve) * fp.height * 0.25

-- | Calculate river position at time t.
riverPosition :: RiverParams -> Number -> Number -> Number -> Number
             -> Int -> Int -> { pos :: Point2D, visible :: Boolean }
riverPosition params t startX laneOffset speed pointIndex frameIndex =
  let fp = params.base
      riverWidth = if params.riverWidth == 0.0
                   then fp.height * 0.3
                   else params.riverWidth

      x = startX + t * fp.width * speed * 1.3
      baseY = riverPath params x

      noise = simplexNoise2D (x * 0.01) (toNumber frameIndex * 0.05 + toNumber pointIndex * 0.1) fp.seed
      y = baseY + laneOffset + (noise - 0.5) * riverWidth * params.turbulence * 2.0

      pos = clampPoint { x, y } 0.0 0.0 fp.width fp.height
      visible = x >= 0.0 && x <= fp.width
  in { pos, visible }

--------------------------------------------------------------------------------
-- Morph Flow
--------------------------------------------------------------------------------

-- | Shape type for morph source/target
data MorphShape = Grid | Circle | Random

derive instance eqMorphShape :: Eq MorphShape

-- | Easing type for morph transition
data MorphEasing = EaseIn | EaseOut | EaseInOut

derive instance eqMorphEasing :: Eq MorphEasing

-- | Parameters for morph flow
type MorphParams =
  { base :: FlowParams
  , sourceShape :: MorphShape
  , targetShape :: MorphShape
  , easing :: MorphEasing
  }

-- | Apply morph easing function
applyMorphEasing :: MorphEasing -> Number -> Number
applyMorphEasing easing t = case easing of
  EaseIn -> t * t
  EaseOut -> 1.0 - (1.0 - t) * (1.0 - t)
  EaseInOut ->
    if t < 0.5 then 2.0 * t * t
    else 1.0 - ((-2.0 * t + 2.0) * (-2.0 * t + 2.0)) / 2.0

-- | Generate grid position for point index
gridPosition :: FlowParams -> Int -> Int -> Point2D
gridPosition fp index numPoints =
  let cols = ceil (Math.sqrt (toNumber numPoints))
      row = index / cols
      col = index `mod` cols
      x = ((toNumber col + 0.5) / toNumber cols) * fp.width * 0.8 + fp.width * 0.1
      y = ((toNumber row + 0.5) / toNumber cols) * fp.height * 0.8 + fp.height * 0.1
  in { x, y }

-- | Generate circle position for point index
circlePosition :: FlowParams -> Int -> Int -> Point2D
circlePosition fp index numPoints =
  let angle = (toNumber index / toNumber numPoints) * Math.pi * 2.0
      radius = Math.min fp.width fp.height * 0.35
      x = fp.width / 2.0 + Math.cos angle * radius
      y = fp.height / 2.0 + Math.sin angle * radius
  in { x, y }

-- | Calculate morph position at time t.
morphPosition :: MorphParams -> Number -> Point2D -> Point2D
             -> Int -> Int -> Point2D
morphPosition params t source target pointIndex frameIndex =
  let fp = params.base
      easedT = applyMorphEasing params.easing t

      noise = simplexNoise2D (toNumber pointIndex * 0.1) (toNumber frameIndex * 0.02) fp.seed
      noiseOffset = (noise - 0.5) * 20.0 * (1.0 - Math.abs (t - 0.5) * 2.0)

      x = source.x + (target.x - source.x) * easedT + noiseOffset
      y = source.y + (target.y - source.y) * easedT + noiseOffset

  in clampPoint { x, y } 0.0 0.0 fp.width fp.height

--------------------------------------------------------------------------------
-- Swarm/Flocking Flow
--------------------------------------------------------------------------------

-- | Parameters for swarm/flocking behavior
type SwarmParams =
  { base :: FlowParams
  , cohesion :: Number    -- Attraction to center of mass
  , separation :: Number  -- Minimum distance between particles
  , alignment :: Number   -- Velocity matching strength
  , maxSpeed :: Number    -- Maximum particle velocity
  }

-- | Swarm particle state
type SwarmParticle =
  { x :: Number
  , y :: Number
  , vx :: Number
  , vy :: Number
  }

-- | Calculate cohesion force toward center of mass
cohesionForce :: SwarmParams -> SwarmParticle -> Number -> Number -> { fx :: Number, fy :: Number }
cohesionForce params particle cx cy =
  let fx = (cx - particle.x) * params.cohesion
      fy = (cy - particle.y) * params.cohesion
  in { fx, fy }

-- | Calculate separation force from another particle
separationForce :: SwarmParams -> SwarmParticle -> SwarmParticle -> { fx :: Number, fy :: Number }
separationForce params p1 p2 =
  let dx = p1.x - p2.x
      dy = p1.y - p2.y
      dist = Math.sqrt (dx * dx + dy * dy)
  in if dist < params.separation && dist > 0.0
     then let factor = (params.separation - dist) * 0.1
          in { fx: dx / dist * factor, fy: dy / dist * factor }
     else { fx: 0.0, fy: 0.0 }

-- | Calculate boundary avoidance force
boundaryForce :: SwarmParams -> SwarmParticle -> { fx :: Number, fy :: Number }
boundaryForce params particle =
  let fp = params.base
      margin = 50.0
      fx1 = if particle.x < margin then (margin - particle.x) * 0.1 else 0.0
      fx2 = if particle.x > fp.width - margin then -(particle.x - (fp.width - margin)) * 0.1 else 0.0
      fy1 = if particle.y < margin then (margin - particle.y) * 0.1 else 0.0
      fy2 = if particle.y > fp.height - margin then -(particle.y - (fp.height - margin)) * 0.1 else 0.0
  in { fx: fx1 + fx2, fy: fy1 + fy2 }

-- | Clamp velocity to max speed
clampVelocity :: Number -> Number -> Number -> { vx :: Number, vy :: Number }
clampVelocity vx vy maxSpeed =
  let speed = Math.sqrt (vx * vx + vy * vy)
  in if speed > maxSpeed
     then { vx: vx / speed * maxSpeed, vy: vy / speed * maxSpeed }
     else { vx, vy }

-- | Update swarm particle with forces
updateSwarmParticle :: SwarmParams -> SwarmParticle -> Number -> Number
                   -> { particle :: SwarmParticle, pos :: Point2D }
updateSwarmParticle params particle fx fy =
  let fp = params.base
      newVx = particle.vx + fx
      newVy = particle.vy + fy
      clamped = clampVelocity newVx newVy params.maxSpeed
      newX = particle.x + clamped.vx
      newY = particle.y + clamped.vy

      newParticle = { x: newX, y: newY, vx: clamped.vx, vy: clamped.vy }
      pos = clampPoint { x: newX, y: newY } 0.0 0.0 fp.width fp.height
  in { particle: newParticle, pos }
