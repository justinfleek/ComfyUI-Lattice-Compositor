{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Physics.ForceFields
Description : Force Field Calculations for Physics Simulation
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for force field calculations:
- Gravity (constant direction)
- Wind (with turbulence noise)
- Attraction/Repulsion (point forces with falloff)
- Explosion (instantaneous radial impulse)
- Buoyancy (submerged depth-based)
- Vortex (tangential + inward)
- Drag (linear and quadratic)

All functions are total and deterministic.

Source: ui/src/services/physics/PhysicsEngine.ts (ForceFieldProcessor class)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.ForceFields
  ( -- * Types
    ForceFieldType(..)
  , ForceResult(..)
  , ForceConfig(..)
    -- * Force Calculations
  , calculateGravity
  , calculateWind
  , calculateAttraction
  , calculateExplosion
  , calculateBuoyancy
  , calculateVortex
  , calculateDrag
    -- * Utility
  , falloffLinear
  , falloffQuadratic
  , inBoundsRadius
  ) where

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Types of force fields
data ForceFieldType
  = FieldGravity
  | FieldWind
  | FieldAttraction
  | FieldExplosion
  | FieldBuoyancy
  | FieldVortex
  | FieldDrag
  deriving (Show, Eq)

-- | Force calculation result
data ForceResult
  = ForceApplied Double Double  -- ^ Force to apply (fx, fy)
  | ImpulseApplied Double Double  -- ^ Impulse (direct velocity change)
  | NoForce  -- ^ Force doesn't apply (out of range, etc.)
  deriving (Show, Eq)

-- | Generic force configuration
data ForceConfig = ForceConfig
  { fcCenterX :: Double
  , fcCenterY :: Double
  , fcStrength :: Double
  , fcRadius :: Double
  , fcFalloff :: String  -- "none", "linear", "quadratic"
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Gravity
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate gravity force.
-- Simple constant force in a direction.
calculateGravity :: Double -> Double  -- gravity direction x, y
                 -> Double            -- body mass
                 -> (Double, Double)  -- force x, y
calculateGravity gx gy mass = (gx * mass, gy * mass)

-- ────────────────────────────────────────────────────────────────────────────
-- Wind
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate wind force with turbulence.
--
-- @param baseX, baseY Base wind direction
-- @param noiseX, noiseY Pre-computed noise values for turbulence
-- @param turbulence Turbulence strength (0-1)
calculateWind :: Double -> Double  -- base direction
              -> Double -> Double  -- noise values
              -> Double            -- turbulence strength
              -> (Double, Double)  -- force
calculateWind baseX baseY noiseX noiseY turbulence =
  (baseX + noiseX * turbulence, baseY + noiseY * turbulence)

-- ────────────────────────────────────────────────────────────────────────────
-- Attraction/Repulsion
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate attraction force toward a point.
--
-- Returns Nothing if body is outside radius or too close.
-- Minimum distance of 1.0 prevents division by zero.
calculateAttraction :: Double -> Double  -- field center
                    -> Double -> Double  -- body position
                    -> Double            -- strength (positive = attract, negative = repel)
                    -> Double            -- radius (0 = infinite range)
                    -> Double            -- mass
                    -> String            -- falloff: "none", "linear", "quadratic"
                    -> Maybe (Double, Double)
calculateAttraction cx cy px py strength radius mass falloff =
  let dx = cx - px
      dy = cy - py
      distSq = dx * dx + dy * dy
      dist = sqrt distSq
  in if radius > 0 && dist > radius
     then Nothing  -- Out of range
     else if dist < 1
          then Nothing  -- Too close
          else
            let dir = (dx / dist, dy / dist)
                forceMag = case falloff of
                  "linear" -> if radius > 0
                              then strength * (radius - dist) / radius
                              else strength
                  "quadratic" -> strength / distSq
                  _ -> strength
                (dirX, dirY) = dir
            in Just (dirX * forceMag * mass, dirY * forceMag * mass)

-- ────────────────────────────────────────────────────────────────────────────
-- Explosion
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate explosion impulse (one-time radial force).
--
-- Only applies at the trigger frame. Returns impulse, not force.
calculateExplosion :: Double -> Double  -- explosion center
                   -> Double -> Double  -- body position
                   -> Double            -- strength
                   -> Double            -- radius
                   -> Maybe (Double, Double)
calculateExplosion ex ey px py strength radius =
  let dx = px - ex
      dy = py - ey
      dist = sqrt (dx * dx + dy * dy)
  in if dist > radius || dist < 1
     then Nothing
     else let falloff = 1 - dist / radius
              (nx, ny) = if dist > 0.0001
                         then (dx / dist, dy / dist)
                         else (1, 0)
          in Just (nx * strength * falloff, ny * strength * falloff)

-- ────────────────────────────────────────────────────────────────────────────
-- Buoyancy
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate buoyancy force.
--
-- @param surfaceLevel Y coordinate of water surface
-- @param bodyY Body Y position
-- @param density Fluid density
-- @param mass Body mass
-- @param radius Approximate body radius (for volume)
-- @param velX, velY Body velocity (for drag)
-- @param linearDrag Linear drag coefficient
calculateBuoyancy :: Double  -- surface level
                  -> Double  -- body Y
                  -> Double  -- density
                  -> Double  -- mass
                  -> Double  -- radius
                  -> Double  -- velX
                  -> Double  -- velY
                  -> Double  -- linearDrag
                  -> Maybe (Double, Double)
calculateBuoyancy surfaceLevel bodyY density mass radius velX velY linearDrag =
  let submergedDepth = bodyY - surfaceLevel
  in if submergedDepth <= 0
     then Nothing  -- Above water
     else
       let submergedRatio = min 1 (submergedDepth / (radius * 2))
           buoyancyForce = negate density * submergedRatio * mass * 980
           dragX = negate linearDrag * velX * submergedRatio
           dragY = negate linearDrag * velY * submergedRatio
       in Just (dragX, buoyancyForce + dragY)

-- ────────────────────────────────────────────────────────────────────────────
-- Vortex
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate vortex force (swirling motion).
--
-- Creates tangential force (swirl) and optional inward force.
calculateVortex :: Double -> Double  -- center
                -> Double -> Double  -- body position
                -> Double            -- tangential strength
                -> Double            -- inward strength
                -> Double            -- radius
                -> Double            -- mass
                -> Maybe (Double, Double)
calculateVortex cx cy px py tangentialStrength inwardStrength radius mass =
  let dx = px - cx
      dy = py - cy
      dist = sqrt (dx * dx + dy * dy)
  in if dist > radius || dist < 1
     then Nothing
     else
       let falloff = 1 - dist / radius
           (nx, ny) = (dx / dist, dy / dist)
           -- Tangent is perpendicular to normal
           (tx, ty) = (negate ny, nx)
           tangentialX = tx * tangentialStrength * falloff * mass
           tangentialY = ty * tangentialStrength * falloff * mass
           inwardX = negate nx * inwardStrength * falloff * mass
           inwardY = negate ny * inwardStrength * falloff * mass
       in Just (tangentialX + inwardX, tangentialY + inwardY)

-- ────────────────────────────────────────────────────────────────────────────
-- Drag
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate drag force opposing motion.
--
-- Linear drag: F = -c1 * v
-- Quadratic drag: F = -c2 * v²
calculateDrag :: Double -> Double  -- velocity
              -> Double            -- linear coefficient
              -> Double            -- quadratic coefficient
              -> Maybe (Double, Double)
calculateDrag velX velY linear quadratic =
  let speed = sqrt (velX * velX + velY * velY)
  in if speed < 0.01
     then Nothing  -- Too slow
     else
       let (nx, ny) = (velX / speed, velY / speed)
           dragMag = linear * speed + quadratic * speed * speed
       in Just (negate nx * dragMag, negate ny * dragMag)

-- ────────────────────────────────────────────────────────────────────────────
-- Utility Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Linear falloff from 1 at center to 0 at radius
falloffLinear :: Double -> Double -> Double
falloffLinear dist radius
  | radius <= 0 = 1
  | dist >= radius = 0
  | otherwise = 1 - dist / radius

-- | Quadratic falloff (inverse square law)
falloffQuadratic :: Double -> Double
falloffQuadratic dist
  | dist < 1 = 1  -- Clamp at minimum distance
  | otherwise = 1 / (dist * dist)

-- | Check if position is within radius of center
inBoundsRadius :: Double -> Double -> Double -> Double -> Double -> Bool
inBoundsRadius cx cy px py radius =
  let dx = px - cx
      dy = py - cy
  in dx * dx + dy * dy <= radius * radius
