{-|
Module      : Lattice.Services.Particles.Forces
Description : Particle Force Field Calculations
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for particle force fields:
- Gravity wells with falloff (linear, quadratic, constant)
- Vortex fields with tangential force and inward pull
- Lorenz strange attractor (2D approximation)
- Wind force from direction/strength
- Friction damping

All functions operate on normalized coordinates (0-1) and return
velocity deltas to be applied to particles.

Source: ui/src/services/particleSystem.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.Forces
  ( -- * Types
    FalloffType(..)
  , Vec2(..)
  , GravityWell(..)
  , Vortex(..)
  , LorenzAttractor(..)
    -- * Vector Operations
  , distance
  , normalize
  , vecAdd
  , vecScale
    -- * Falloff
  , applyFalloff
    -- * Force Calculations
  , gravityWellForce
  , vortexForce
  , lorenzForce
  , windForce
  , gravityForce
  , applyFriction
    -- * Combined Forces
  , applyGravityWells
  , applyVortices
  , applyLorenzAttractors
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Falloff function type for force fields
data FalloffType
  = FalloffConstant   -- ^ No falloff
  | FalloffLinear     -- ^ Linear falloff with distance
  | FalloffQuadratic  -- ^ Quadratic falloff (inverse square-ish)
  deriving (Show, Eq)

-- | 2D velocity vector
data Vec2 = Vec2
  { vx :: Double
  , vy :: Double
  } deriving (Show, Eq)

-- | Gravity well configuration
data GravityWell = GravityWell
  { gwX :: Double        -- ^ Center X (normalized 0-1)
  , gwY :: Double        -- ^ Center Y (normalized 0-1)
  , gwStrength :: Double -- ^ Force strength
  , gwRadius :: Double   -- ^ Effect radius
  , gwFalloff :: FalloffType
  } deriving (Show, Eq)

-- | Vortex configuration
data Vortex = Vortex
  { vortexX :: Double          -- ^ Center X
  , vortexY :: Double          -- ^ Center Y
  , vortexStrength :: Double   -- ^ Tangential force strength
  , vortexInwardPull :: Double -- ^ Radial inward force
  , vortexRadius :: Double     -- ^ Effect radius
  } deriving (Show, Eq)

-- | Lorenz attractor configuration
data LorenzAttractor = LorenzAttractor
  { laX :: Double        -- ^ Center X
  , laY :: Double        -- ^ Center Y
  , laSigma :: Double    -- ^ Lorenz σ parameter (default 10)
  , laRho :: Double      -- ^ Lorenz ρ parameter (default 28)
  , laBeta :: Double     -- ^ Lorenz β parameter (default 8/3)
  , laStrength :: Double -- ^ Overall force multiplier
  , laRadius :: Double   -- ^ Effect radius
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Vector Operations
--------------------------------------------------------------------------------

-- | Calculate distance between two points
distance :: Double -> Double -> Double -> Double -> Double
distance x1 y1 x2 y2 =
  let dx = x2 - x1
      dy = y2 - y1
  in sqrt (dx * dx + dy * dy)

-- | Normalize a vector, returns zero vector if magnitude is too small
normalize :: Double -> Double -> Vec2
normalize dx dy =
  let mag = sqrt (dx * dx + dy * dy)
  in if mag > 0.0001
     then Vec2 (dx / mag) (dy / mag)
     else Vec2 0 0

-- | Add two vectors
vecAdd :: Vec2 -> Vec2 -> Vec2
vecAdd a b = Vec2 (vx a + vx b) (vy a + vy b)

-- | Scale a vector
vecScale :: Vec2 -> Double -> Vec2
vecScale v s = Vec2 (vx v * s) (vy v * s)

--------------------------------------------------------------------------------
-- Falloff Functions
--------------------------------------------------------------------------------

-- | Apply falloff based on distance ratio (0 at center, 1 at edge)
applyFalloff :: Double -> FalloffType -> Double
applyFalloff distRatio falloff = case falloff of
  FalloffConstant  -> 1
  FalloffLinear    -> 1 - distRatio
  FalloffQuadratic -> (1 - distRatio) * (1 - distRatio)

--------------------------------------------------------------------------------
-- Gravity Well Force
--------------------------------------------------------------------------------

-- | Calculate force from a gravity well on a particle.
--
-- Returns velocity delta (vx, vy) to add to particle.
-- Force points toward well center, scaled by strength and falloff.
gravityWellForce :: Double -> Double -> GravityWell -> Double -> Vec2
gravityWellForce px py well deltaTime =
  let dx = gwX well - px
      dy = gwY well - py
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= gwRadius well || dist <= 0.001
     then Vec2 0 0
     else
       let distRatio = dist / gwRadius well
           falloffFactor = applyFalloff distRatio (gwFalloff well)
           force = gwStrength well * 0.0001 * falloffFactor
           nx = dx / dist
           ny = dy / dist
       in Vec2 (nx * force * deltaTime) (ny * force * deltaTime)

--------------------------------------------------------------------------------
-- Vortex Force
--------------------------------------------------------------------------------

-- | Calculate force from a vortex field on a particle.
--
-- Returns velocity delta with:
-- - Tangential component (perpendicular to radius, creates spin)
-- - Radial component (inward pull, creates spiral)
vortexForce :: Double -> Double -> Vortex -> Double -> Vec2
vortexForce px py vortex deltaTime =
  let dx = vortexX vortex - px
      dy = vortexY vortex - py
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= vortexRadius vortex || dist <= 0.001
     then Vec2 0 0
     else
       let influence = 1 - dist / vortexRadius vortex
           tangentialStrength = vortexStrength vortex * 0.0001 * influence
           -- Normalize direction
           nx = dx / dist
           ny = dy / dist
           -- Perpendicular direction (tangent)
           perpX = -ny
           perpY = nx
           -- Tangential force
           tangentForce = Vec2 (perpX * tangentialStrength * deltaTime)
                               (perpY * tangentialStrength * deltaTime)
           -- Inward pull force
           inwardStrength = vortexInwardPull vortex * 0.0001 * influence
           inwardForce = Vec2 (nx * inwardStrength * deltaTime)
                              (ny * inwardStrength * deltaTime)
       in vecAdd tangentForce inwardForce

--------------------------------------------------------------------------------
-- Lorenz Attractor Force
--------------------------------------------------------------------------------

-- | Calculate force from a Lorenz strange attractor.
--
-- Creates chaotic, butterfly-like motion. Uses 2D approximation where
-- the Z coordinate is simulated from distance to center.
--
-- Lorenz equations:
-- dx/dt = σ(y - x)
-- dy/dt = x(ρ - z) - y
lorenzForce :: Double -> Double -> LorenzAttractor -> Double -> Vec2
lorenzForce px py attractor deltaTime =
  let dx = px - laX attractor
      dy = py - laY attractor
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= laRadius attractor || dist <= 0.001
     then Vec2 0 0
     else
       let influence = 1 - dist / laRadius attractor
           -- Simulate Z coordinate from distance
           pseudoZ = dist * 0.1
           -- Lorenz equations (adapted for 2D)
           ldx = laSigma attractor * (dy - dx)
           ldy = dx * (laRho attractor - pseudoZ) - dy
           -- Apply force
           strength = laStrength attractor * 0.001 * influence
       in Vec2 (ldx * strength * deltaTime) (ldy * strength * deltaTime)

--------------------------------------------------------------------------------
-- Wind Force
--------------------------------------------------------------------------------

-- | Calculate wind force from direction and strength.
windForce :: Double -> Double -> Double -> Vec2
windForce direction strength deltaTime =
  let radians = direction * pi / 180
      windX = cos radians * strength * 0.001
      windY = sin radians * strength * 0.001
  in Vec2 (windX * deltaTime) (windY * deltaTime)

--------------------------------------------------------------------------------
-- Gravity Force
--------------------------------------------------------------------------------

-- | Calculate global gravity force.
gravityForce :: Double -> Double -> Vec2
gravityForce gravity deltaTime =
  Vec2 0 (gravity * 0.001 * deltaTime)

--------------------------------------------------------------------------------
-- Friction
--------------------------------------------------------------------------------

-- | Apply friction to velocity.
--
-- Returns scaled velocity after friction.
-- friction = 0 means no friction (full speed preserved)
-- friction = 1 means complete stop
applyFriction :: Double -> Double -> Double -> Vec2
applyFriction vxIn vyIn friction =
  let factor = 1 - max 0 (min 1 friction)
  in Vec2 (vxIn * factor) (vyIn * factor)

--------------------------------------------------------------------------------
-- Combined Force Application
--------------------------------------------------------------------------------

-- | Apply multiple gravity wells to a particle.
applyGravityWells :: Double -> Double -> [GravityWell] -> Double -> Vec2
applyGravityWells px py wells deltaTime =
  foldl vecAdd (Vec2 0 0) (map (\w -> gravityWellForce px py w deltaTime) wells)

-- | Apply multiple vortices to a particle.
applyVortices :: Double -> Double -> [Vortex] -> Double -> Vec2
applyVortices px py vortices deltaTime =
  foldl vecAdd (Vec2 0 0) (map (\v -> vortexForce px py v deltaTime) vortices)

-- | Apply multiple Lorenz attractors to a particle.
applyLorenzAttractors :: Double -> Double -> [LorenzAttractor] -> Double -> Vec2
applyLorenzAttractors px py attractors deltaTime =
  foldl vecAdd (Vec2 0 0) (map (\a -> lorenzForce px py a deltaTime) attractors)
