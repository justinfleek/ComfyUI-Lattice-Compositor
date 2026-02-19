-- |
-- Module      : Lattice.Services.PhysicsForces
-- Description : Pure force calculation functions for physics simulation
-- 
-- Migrated from ui/src/services/physics/PhysicsEngine.ts (calculateForce method)
-- Pure force calculations for deterministic physics
-- All functions return Either Text Vec2 (error or force vector)
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Services.PhysicsForces
  ( -- Force calculations
    calculateGravityForce
  , calculateWindForce
  , calculateAttractionForce
  , calculateVortexForce
  , calculateDragForce
  , calculateBuoyancyForce
  -- Types
  , AttractionFalloff(..)
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Utils.NumericSafety (isFinite)
import Data.Either (Either(..))
import Lattice.Types.Primitives (Vec2(..))
import Lattice.Services.PhysicsVectorMath
  ( vec2Add
  , vec2Sub
  , vec2Scale
  , vec2Length
  , vec2LengthSq
  , vec2Normalize
  , vec2Perpendicular
  )
import Lattice.Utils.NumericSafety (ensureFiniteD, safeSqrtD)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Attraction force falloff type
data AttractionFalloff
  = FalloffLinear
  | FalloffQuadratic
  | FalloffConstant
  deriving (Eq, Show)

-- ============================================================================
-- GRAVITY FORCE
-- ============================================================================

-- | Calculate gravity force
-- Pure function: same inputs → same outputs
-- F = m * g (mass times gravity vector)
calculateGravityForce :: Vec2 -> Double -> Either Text Vec2
calculateGravityForce gravity mass =
  let finiteMass = ensureFiniteD mass 1.0
      finiteGravityX = ensureFiniteD (vec2X gravity) 0.0
      finiteGravityY = ensureFiniteD (vec2Y gravity) 0.0
      forceX = finiteGravityX * finiteMass
      forceY = finiteGravityY * finiteMass
  in Right (Vec2 (ensureFiniteD forceX 0.0) (ensureFiniteD forceY 0.0))

-- ============================================================================
-- WIND FORCE
-- ============================================================================

-- | Calculate wind force with turbulence
-- Pure function: same inputs → same outputs
-- Wind direction + turbulence noise based on position and frame
calculateWindForce ::
  Vec2 ->           -- Wind direction
  Double ->         -- Turbulence strength
  Double ->         -- Turbulence frequency
  Double ->         -- Noise seed
  Vec2 ->           -- Body position
  Int ->            -- Frame number
  Either Text Vec2
calculateWindForce direction turbulence frequency seed bodyPos frame =
  let finiteTurbulence = ensureFiniteD turbulence 0.0
      finiteFreq = ensureFiniteD frequency 1.0
      finiteSeed = ensureFiniteD seed 0.0
      finiteFrame = fromIntegral frame
      posX = vec2X bodyPos
      posY = vec2Y bodyPos
      -- Turbulence noise: sin/cos based (simplified simplex-like noise)
      noiseX = sin (posX * finiteFreq + finiteFrame * 0.1 + finiteSeed) * finiteTurbulence
      noiseY = cos (posY * finiteFreq + finiteFrame * 0.1 + finiteSeed * 2) * finiteTurbulence
      dirX = ensureFiniteD (vec2X direction) 0.0
      dirY = ensureFiniteD (vec2Y direction) 0.0
      forceX = dirX + noiseX
      forceY = dirY + noiseY
  in Right (Vec2 (ensureFiniteD forceX 0.0) (ensureFiniteD forceY 0.0))

-- ============================================================================
-- ATTRACTION FORCE
-- ============================================================================

-- | Calculate attraction/repulsion force
-- Pure function: same inputs → same outputs
-- Returns Left if body is out of range or too close
calculateAttractionForce ::
  Vec2 ->              -- Field center position
  Vec2 ->              -- Body position
  Double ->            -- Strength (negative = repel)
  Double ->            -- Mass
  Double ->            -- Radius (0 = infinite range)
  AttractionFalloff -> -- Falloff type
  Either Text Vec2
calculateAttractionForce center bodyPos strength mass radius falloff =
  let diff = vec2Sub center bodyPos
      distSq = vec2LengthSq diff
      dist = safeSqrtD distSq
      
      -- Validate distance
      finiteDist = ensureFiniteD dist 0.0
      finiteRadius = ensureFiniteD radius 0.0
      
  in if not (isFinite distSq) || distSq < 0
     then Left "Invalid distance squared calculation"
     else if not (isFinite finiteDist) || finiteDist < 0
          then Left "Invalid distance calculation"
          else if finiteRadius > 0 && finiteDist > finiteRadius
               then Left "Body is outside field range"
               else if finiteDist < 1.0
                    then Left "Body is too close to field center (minimum distance: 1)"
                    else
                      let -- Calculate force magnitude based on falloff
                          forceMag = case falloff of
                            FalloffLinear ->
                              let finiteStrength = ensureFiniteD strength 0.0
                                  falloffFactor = if finiteRadius > 0
                                                  then (finiteRadius - finiteDist) / finiteRadius
                                                  else 1.0
                              in finiteStrength * falloffFactor
                            FalloffQuadratic ->
                              let finiteStrength = ensureFiniteD strength 0.0
                              in finiteStrength / distSq
                            FalloffConstant ->
                              ensureFiniteD strength 0.0
                          
                          -- Normalize direction and scale by force magnitude and mass
                          normalizedDiff = vec2Normalize diff
                          finiteMass = ensureFiniteD mass 1.0
                          scaledForce = vec2Scale normalizedDiff (forceMag * finiteMass)
                      in Right scaledForce

-- ============================================================================
-- VORTEX FORCE
-- ============================================================================

-- | Calculate vortex force (rotational + inward pull)
-- Pure function: same inputs → same outputs
-- Returns Left if body is out of range or too close
calculateVortexForce ::
  Vec2 ->    -- Field center position
  Vec2 ->    -- Body position
  Double ->  -- Tangential strength
  Double ->  -- Inward force strength
  Double ->  -- Mass
  Double ->  -- Radius
  Either Text Vec2
calculateVortexForce center bodyPos strength inwardForce mass radius =
  let diff = vec2Sub bodyPos center  -- Note: reversed from attraction
      dist = vec2Length diff
      finiteDist = ensureFiniteD dist 0.0
      finiteRadius = ensureFiniteD radius 0.0
      
  in if not (isFinite finiteDist) || finiteDist < 0
     then Left "Invalid distance calculation"
     else if finiteDist > finiteRadius || finiteDist < 1.0
          then Left "Body is outside vortex range"
          else
            let -- Falloff factor
                falloff = 1.0 - (finiteDist / finiteRadius)
                
                -- Tangential force (perpendicular to radius)
                normalizedDiff = vec2Normalize diff
                tangent = vec2Perpendicular normalizedDiff
                finiteStrength = ensureFiniteD strength 0.0
                finiteMass = ensureFiniteD mass 1.0
                tangentialForce = vec2Scale tangent (finiteStrength * falloff * finiteMass)
                
                -- Inward force (toward center)
                inwardDir = vec2Scale normalizedDiff (-1.0)
                finiteInward = ensureFiniteD inwardForce 0.0
                inward = vec2Scale inwardDir (finiteInward * falloff * finiteMass)
                
                -- Combined force
                combined = vec2Add tangentialForce inward
            in Right combined

-- ============================================================================
-- DRAG FORCE
-- ============================================================================

-- | Calculate drag force (air/fluid resistance)
-- Pure function: same inputs → same outputs
-- Returns Left if speed is too low
calculateDragForce ::
  Vec2 ->    -- Body velocity
  Double ->  -- Linear drag coefficient
  Double ->  -- Quadratic drag coefficient
  Either Text Vec2
calculateDragForce velocity linear quadratic =
  let speed = vec2Length velocity
      finiteSpeed = ensureFiniteD speed 0.0
      
  in if not (isFinite finiteSpeed) || finiteSpeed < 0
     then Left "Invalid speed calculation"
     else if finiteSpeed < 0.01
          then Left "Body speed is too low (threshold: 0.01)"
          else
            let -- Drag magnitude: linear * speed + quadratic * speed^2
                finiteLinear = ensureFiniteD linear 0.0
                finiteQuadratic = ensureFiniteD quadratic 0.0
                dragMag = finiteLinear * finiteSpeed + finiteQuadratic * finiteSpeed * finiteSpeed
                
                -- Drag opposes velocity direction
                normalizedVel = vec2Normalize velocity
                dragForce = vec2Scale normalizedVel (-dragMag)
            in Right dragForce

-- ============================================================================
-- BUOYANCY FORCE
-- ============================================================================

-- | Calculate buoyancy force (fluid simulation)
-- Pure function: same inputs → same outputs
-- Returns Left if body is above water surface
calculateBuoyancyForce ::
  Vec2 ->    -- Body position
  Vec2 ->    -- Body velocity
  Double ->  -- Surface level (Y coordinate)
  Double ->  -- Fluid density
  Double ->  -- Linear drag coefficient
  Double ->  -- Angular drag coefficient (not used in force, but for completeness)
  Double ->  -- Body mass
  Double ->  -- Body radius (for submerged volume calculation)
  Either Text Vec2
calculateBuoyancyForce bodyPos bodyVel surfaceLevel density linearDrag _angularDrag mass radius =
  let bodyY = vec2Y bodyPos
      finiteBodyY = ensureFiniteD bodyY 0.0
      finiteSurface = ensureFiniteD surfaceLevel 0.0
      submergedDepth = finiteBodyY - finiteSurface
      finiteDepth = ensureFiniteD submergedDepth 0.0
      
  in if not (isFinite finiteDepth)
     then Left "Invalid submerged depth calculation"
     else if finiteDepth <= 0
          then Left "Body is above water surface"
          else
            let -- Calculate submerged ratio (approximate based on radius)
                finiteRadius = ensureFiniteD radius 10.0
                submergedRatio = min 1.0 (finiteDepth / (finiteRadius * 2))
                
                -- Buoyancy force (upward, negative Y)
                finiteDensity = ensureFiniteD density 1.0
                finiteMass = ensureFiniteD mass 1.0
                gravityConstant = 980.0  -- pixels/s²
                buoyancyForceY = -finiteDensity * submergedRatio * finiteMass * gravityConstant
                
                -- Drag forces (oppose velocity)
                finiteLinearDrag = ensureFiniteD linearDrag 0.0
                velX = vec2X bodyVel
                velY = vec2Y bodyVel
                dragX = -finiteLinearDrag * velX * submergedRatio
                dragY = -finiteLinearDrag * velY * submergedRatio
                
                -- Combined force
                forceX = ensureFiniteD dragX 0.0
                forceY = ensureFiniteD (buoyancyForceY + dragY) 0.0
            in Right (Vec2 forceX forceY)
