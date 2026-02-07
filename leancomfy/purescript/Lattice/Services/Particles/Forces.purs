-- | Lattice.Services.Particles.Forces - Particle Force Field Calculations
-- |
-- | Pure mathematical functions for particle force fields:
-- | - Gravity wells with falloff (linear, quadratic, constant)
-- | - Vortex fields with tangential force and inward pull
-- | - Lorenz strange attractor (2D approximation)
-- | - Wind force from direction/strength
-- | - Friction damping
-- |
-- | All functions operate on normalized coordinates (0-1) and return
-- | velocity deltas to be applied to particles.
-- |
-- | Source: ui/src/services/particleSystem.ts

module Lattice.Services.Particles.Forces
  ( FalloffType(..)
  , Vec2
  , GravityWell
  , Vortex
  , LorenzAttractor
  , distance
  , normalize
  , vecAdd
  , vecScale
  , applyFalloff
  , gravityWellForce
  , vortexForce
  , lorenzForce
  , windForce
  , gravityForce
  , applyFriction
  , applyGravityWells
  , applyVortices
  , applyLorenzAttractors
  ) where

import Prelude

import Data.Array (foldl)
import Math (cos, max, min, pi, sin, sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Falloff function type for force fields
data FalloffType
  = FalloffConstant   -- ^ No falloff
  | FalloffLinear     -- ^ Linear falloff with distance
  | FalloffQuadratic  -- ^ Quadratic falloff (inverse square-ish)

derive instance eqFalloffType :: Eq FalloffType

-- | 2D velocity vector
type Vec2 =
  { x :: Number
  , y :: Number
  }

-- | Gravity well configuration
type GravityWell =
  { x :: Number        -- ^ Center X (normalized 0-1)
  , y :: Number        -- ^ Center Y (normalized 0-1)
  , strength :: Number -- ^ Force strength
  , radius :: Number   -- ^ Effect radius
  , falloff :: FalloffType
  }

-- | Vortex configuration
type Vortex =
  { x :: Number          -- ^ Center X
  , y :: Number          -- ^ Center Y
  , strength :: Number   -- ^ Tangential force strength
  , inwardPull :: Number -- ^ Radial inward force
  , radius :: Number     -- ^ Effect radius
  }

-- | Lorenz attractor configuration
type LorenzAttractor =
  { x :: Number        -- ^ Center X
  , y :: Number        -- ^ Center Y
  , sigma :: Number    -- ^ Lorenz σ parameter (default 10)
  , rho :: Number      -- ^ Lorenz ρ parameter (default 28)
  , beta :: Number     -- ^ Lorenz β parameter (default 8/3)
  , strength :: Number -- ^ Overall force multiplier
  , radius :: Number   -- ^ Effect radius
  }

--------------------------------------------------------------------------------
-- Vector Operations
--------------------------------------------------------------------------------

-- | Calculate distance between two points
distance :: Number -> Number -> Number -> Number -> Number
distance x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in sqrt (dx * dx + dy * dy)

-- | Normalize a vector, returns zero vector if magnitude is too small
normalize :: Number -> Number -> Vec2
normalize dx dy =
  let mag = sqrt (dx * dx + dy * dy)
  in if mag > 0.0001
     then { x: dx / mag, y: dy / mag }
     else { x: 0.0, y: 0.0 }

-- | Add two vectors
vecAdd :: Vec2 -> Vec2 -> Vec2
vecAdd a b = { x: a.x + b.x, y: a.y + b.y }

-- | Scale a vector
vecScale :: Vec2 -> Number -> Vec2
vecScale v s = { x: v.x * s, y: v.y * s }

--------------------------------------------------------------------------------
-- Falloff Functions
--------------------------------------------------------------------------------

-- | Apply falloff based on distance ratio (0 at center, 1 at edge)
applyFalloff :: Number -> FalloffType -> Number
applyFalloff distRatio falloff = case falloff of
  FalloffConstant  -> 1.0
  FalloffLinear    -> 1.0 - distRatio
  FalloffQuadratic -> (1.0 - distRatio) * (1.0 - distRatio)

--------------------------------------------------------------------------------
-- Gravity Well Force
--------------------------------------------------------------------------------

-- | Calculate force from a gravity well on a particle.
-- |
-- | Returns velocity delta (vx, vy) to add to particle.
-- | Force points toward well center, scaled by strength and falloff.
gravityWellForce :: Number -> Number -> GravityWell -> Number -> Vec2
gravityWellForce px py well deltaTime =
  let dx = well.x - px
      dy = well.y - py
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= well.radius || dist <= 0.001
     then { x: 0.0, y: 0.0 }
     else
       let distRatio = dist / well.radius
           falloffFactor = applyFalloff distRatio well.falloff
           force = well.strength * 0.0001 * falloffFactor
           nx = dx / dist
           ny = dy / dist
       in { x: nx * force * deltaTime, y: ny * force * deltaTime }

--------------------------------------------------------------------------------
-- Vortex Force
--------------------------------------------------------------------------------

-- | Calculate force from a vortex field on a particle.
-- |
-- | Returns velocity delta with:
-- | - Tangential component (perpendicular to radius, creates spin)
-- | - Radial component (inward pull, creates spiral)
vortexForce :: Number -> Number -> Vortex -> Number -> Vec2
vortexForce px py vortex deltaTime =
  let dx = vortex.x - px
      dy = vortex.y - py
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= vortex.radius || dist <= 0.001
     then { x: 0.0, y: 0.0 }
     else
       let influence = 1.0 - dist / vortex.radius
           tangentialStrength = vortex.strength * 0.0001 * influence
           -- Normalize direction
           nx = dx / dist
           ny = dy / dist
           -- Perpendicular direction (tangent)
           perpX = -ny
           perpY = nx
           -- Tangential force
           tangentForce = { x: perpX * tangentialStrength * deltaTime
                         , y: perpY * tangentialStrength * deltaTime }
           -- Inward pull force
           inwardStrength = vortex.inwardPull * 0.0001 * influence
           inwardForce = { x: nx * inwardStrength * deltaTime
                        , y: ny * inwardStrength * deltaTime }
       in vecAdd tangentForce inwardForce

--------------------------------------------------------------------------------
-- Lorenz Attractor Force
--------------------------------------------------------------------------------

-- | Calculate force from a Lorenz strange attractor.
-- |
-- | Creates chaotic, butterfly-like motion. Uses 2D approximation where
-- | the Z coordinate is simulated from distance to center.
-- |
-- | Lorenz equations:
-- | dx/dt = σ(y - x)
-- | dy/dt = x(ρ - z) - y
lorenzForce :: Number -> Number -> LorenzAttractor -> Number -> Vec2
lorenzForce px py attractor deltaTime =
  let dx = px - attractor.x
      dy = py - attractor.y
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= attractor.radius || dist <= 0.001
     then { x: 0.0, y: 0.0 }
     else
       let influence = 1.0 - dist / attractor.radius
           -- Simulate Z coordinate from distance
           pseudoZ = dist * 0.1
           -- Lorenz equations (adapted for 2D)
           ldx = attractor.sigma * (dy - dx)
           ldy = dx * (attractor.rho - pseudoZ) - dy
           -- Apply force
           forceStrength = attractor.strength * 0.001 * influence
       in { x: ldx * forceStrength * deltaTime, y: ldy * forceStrength * deltaTime }

--------------------------------------------------------------------------------
-- Wind Force
--------------------------------------------------------------------------------

-- | Calculate wind force from direction and strength.
windForce :: Number -> Number -> Number -> Vec2
windForce direction strength deltaTime =
  let radians = direction * pi / 180.0
      windX = cos radians * strength * 0.001
      windY = sin radians * strength * 0.001
  in { x: windX * deltaTime, y: windY * deltaTime }

--------------------------------------------------------------------------------
-- Gravity Force
--------------------------------------------------------------------------------

-- | Calculate global gravity force.
gravityForce :: Number -> Number -> Vec2
gravityForce gravity deltaTime =
  { x: 0.0, y: gravity * 0.001 * deltaTime }

--------------------------------------------------------------------------------
-- Friction
--------------------------------------------------------------------------------

-- | Apply friction to velocity.
-- |
-- | Returns scaled velocity after friction.
-- | friction = 0 means no friction (full speed preserved)
-- | friction = 1 means complete stop
applyFriction :: Number -> Number -> Number -> Vec2
applyFriction vxIn vyIn friction =
  let factor = 1.0 - max 0.0 (min 1.0 friction)
  in { x: vxIn * factor, y: vyIn * factor }

--------------------------------------------------------------------------------
-- Combined Force Application
--------------------------------------------------------------------------------

-- | Apply multiple gravity wells to a particle.
applyGravityWells :: Number -> Number -> Array GravityWell -> Number -> Vec2
applyGravityWells px py wells deltaTime =
  foldl (\acc w -> vecAdd acc (gravityWellForce px py w deltaTime)) { x: 0.0, y: 0.0 } wells

-- | Apply multiple vortices to a particle.
applyVortices :: Number -> Number -> Array Vortex -> Number -> Vec2
applyVortices px py vortices deltaTime =
  foldl (\acc v -> vecAdd acc (vortexForce px py v deltaTime)) { x: 0.0, y: 0.0 } vortices

-- | Apply multiple Lorenz attractors to a particle.
applyLorenzAttractors :: Number -> Number -> Array LorenzAttractor -> Number -> Vec2
applyLorenzAttractors px py attractors deltaTime =
  foldl (\acc a -> vecAdd acc (lorenzForce px py a deltaTime)) { x: 0.0, y: 0.0 } attractors
