{-# LANGUAGE StrictData #-}

{-|
Module      : Lattice.Services.Flow.Patterns
Description : Flow Field Pattern Math
Copyright   : (c) Lattice, 2026
License     : MIT

Pure mathematical functions for Anadol-style generative flow patterns.
These compute positions based on flow field equations without
managing trajectories or state.

Source: ui/src/services/export/wanMoveFlowGenerators.ts
-}

module Lattice.Services.Flow.Patterns
  ( -- * Types
    Point2D(..), FlowParams(..)
    -- * Spiral Flow
  , SpiralParams(..), spiralPosition
    -- * Wave Flow
  , WaveParams(..), wavePosition
    -- * Explosion Flow
  , ExplosionParams(..), ExplosionState(..)
  , initExplosionParticle, stepExplosionParticle
    -- * Vortex Flow
  , VortexParams(..), VortexState(..)
  , initVortexParticle, stepVortexParticle
    -- * River Flow
  , RiverParams(..), riverPath, riverPosition
    -- * Morph Flow
  , MorphShape(..), MorphEasing(..), MorphParams(..)
  , applyMorphEasing, gridPosition, circlePosition, morphPosition
    -- * Swarm Flow
  , SwarmParams(..), SwarmParticle(..)
  , cohesionForce, separationForce, boundaryForce
  , clampVelocity, updateSwarmParticle
  ) where

import Data.Word (Word32)
import Lattice.Services.Noise.SimplexNoise (simplexNoise2D)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | 2D point for flow calculations
data Point2D = Point2D
  { px :: Double
  , py :: Double
  } deriving (Eq, Show)

-- | Flow field parameters common to most patterns
data FlowParams = FlowParams
  { fpWidth :: Double
  , fpHeight :: Double
  , fpSeed :: Word32
  , fpNoiseStrength :: Double
  } deriving (Eq, Show)

defaultFlowParams :: Double -> Double -> FlowParams
defaultFlowParams w h = FlowParams w h 42 0.1

--------------------------------------------------------------------------------
-- Point Operations
--------------------------------------------------------------------------------

origin :: Point2D
origin = Point2D 0 0

add :: Point2D -> Point2D -> Point2D
add a b = Point2D (px a + px b) (py a + py b)

scale :: Point2D -> Double -> Point2D
scale p s = Point2D (px p * s) (py p * s)

distance :: Point2D -> Point2D -> Double
distance a b =
  let dx = px b - px a
      dy = py b - py a
  in sqrt (dx * dx + dy * dy)

clampPoint :: Point2D -> Double -> Double -> Double -> Double -> Point2D
clampPoint p minX minY maxX maxY = Point2D
  (max minX (min maxX (px p)))
  (max minY (min maxY (py p)))

--------------------------------------------------------------------------------
-- Spiral Flow
--------------------------------------------------------------------------------

-- | Parameters for spiral galaxy flow
data SpiralParams = SpiralParams
  { spBase :: FlowParams
  , spTurns :: Double      -- Number of spiral rotations
  , spExpansion :: Double  -- How much spiral expands over time
  } deriving (Eq, Show)

-- | Calculate spiral position at time t.
spiralPosition :: SpiralParams -> Double -> Double -> Double -> Double
              -> Point2D -> Double -> Int -> Int -> Point2D
spiralPosition params t armOffset radiusOffset phaseOffset center maxRadius pointIndex frameIndex =
  let fp = spBase params
      effectiveT = t + phaseOffset
      angle = armOffset + effectiveT * pi * 2 * spTurns params
      radius = (radiusOffset + effectiveT * spExpansion params) * maxRadius

      noise = simplexNoise2D (fromIntegral pointIndex * 0.1) (fromIntegral frameIndex * 0.05) (fpSeed fp)
      noisedRadius = radius * (1 + (noise - 0.5) * fpNoiseStrength fp * 2)

      x = px center + cos angle * noisedRadius
      y = py center + sin angle * noisedRadius

  in clampPoint (Point2D x y) 0 0 (fpWidth fp) (fpHeight fp)

--------------------------------------------------------------------------------
-- Wave Flow
--------------------------------------------------------------------------------

-- | Parameters for wave/ocean flow
data WaveParams = WaveParams
  { wpBase :: FlowParams
  , wpAmplitude :: Double  -- Wave height (0 = height * 0.15)
  , wpFrequency :: Double  -- Wave oscillations across width
  , wpSpeed :: Double      -- Horizontal movement speed
  , wpLayers :: Int        -- Number of wave layers
  } deriving (Eq, Show)

-- | Calculate wave position at time t.
wavePosition :: WaveParams -> Double -> Double -> Double -> Double -> Double
            -> Int -> Int -> Int -> (Point2D, Bool)
wavePosition params t startX layerY phaseOffset amplitudeVar layer pointIndex frameIndex =
  let fp = wpBase params
      amplitude = if wpAmplitude params == 0
                  then fpHeight fp * 0.15
                  else wpAmplitude params

      rawX = startX + t * fpWidth fp * wpSpeed params * 10
      x = (rawX `fmod` (fpWidth fp * 1.2)) - fpWidth fp * 0.1

      waveAngle = (x / fpWidth fp) * pi * 2 * wpFrequency params +
                  phaseOffset + t * pi * 4
      wave = sin waveAngle
      y = layerY + wave * amplitude * amplitudeVar

      noise = simplexNoise2D (x * 0.01) (fromIntegral frameIndex * 0.05 + fromIntegral layer) (fpSeed fp)
      noisedY = y + (noise - 0.5) * amplitude * fpNoiseStrength fp * 4

      pos = clampPoint (Point2D x noisedY) 0 0 (fpWidth fp) (fpHeight fp)
      visible = x >= 0 && x <= fpWidth fp
  in (pos, visible)
  where
    fmod a b = a - fromIntegral (floor (a / b) :: Int) * b

--------------------------------------------------------------------------------
-- Explosion Flow
--------------------------------------------------------------------------------

-- | Parameters for explosion/big bang flow
data ExplosionParams = ExplosionParams
  { epBase :: FlowParams
  , epSpeed :: Double       -- Explosion velocity multiplier
  , epDecay :: Double       -- Velocity decay per frame [0, 1]
  , epCenter :: Point2D     -- Explosion center (origin = canvas center)
  } deriving (Eq, Show)

-- | Explosion particle state
data ExplosionState = ExplosionState
  { esX :: Double
  , esY :: Double
  , esVx :: Double
  , esVy :: Double
  } deriving (Eq, Show)

-- | Initialize explosion particle.
initExplosionParticle :: ExplosionParams -> Double -> Double -> ExplosionState
initExplosionParticle params angle speed =
  let fp = epBase params
      center = if px (epCenter params) == 0 && py (epCenter params) == 0
               then Point2D (fpWidth fp / 2) (fpHeight fp / 2)
               else epCenter params
  in ExplosionState
       { esX = px center
       , esY = py center
       , esVx = cos angle * speed * 20
       , esVy = sin angle * speed * 20
       }

-- | Step explosion particle forward one frame.
stepExplosionParticle :: ExplosionParams -> ExplosionState -> Int -> Int
                     -> (ExplosionState, Point2D, Bool)
stepExplosionParticle params state pointIndex frameIndex =
  let fp = epBase params
      noiseX = (simplexNoise2D (fromIntegral pointIndex * 0.1) (fromIntegral frameIndex * 0.1) (fpSeed fp) - 0.5) *
               fpNoiseStrength fp * 50
      noiseY = (simplexNoise2D (fromIntegral pointIndex * 0.1 + 100) (fromIntegral frameIndex * 0.1) (fpSeed fp) - 0.5) *
               fpNoiseStrength fp * 50

      newX = esX state + esVx state + noiseX
      newY = esY state + esVy state + noiseY
      newVx = esVx state * epDecay params
      newVy = esVy state * epDecay params

      newState = ExplosionState newX newY newVx newVy
      pos = clampPoint (Point2D newX newY) 0 0 (fpWidth fp) (fpHeight fp)
      visible = newX >= 0 && newX <= fpWidth fp && newY >= 0 && newY <= fpHeight fp
  in (newState, pos, visible)

--------------------------------------------------------------------------------
-- Vortex Flow
--------------------------------------------------------------------------------

-- | Parameters for vortex/whirlpool flow
data VortexParams = VortexParams
  { vpBase :: FlowParams
  , vpStrength :: Double    -- Angular velocity multiplier
  , vpMaxRadius :: Double   -- 0 = min(width,height)*0.4
  , vpCenter :: Point2D
  } deriving (Eq, Show)

-- | Vortex particle state
data VortexState = VortexState
  { vsAngle :: Double
  , vsRadius :: Double
  } deriving (Eq, Show)

-- | Initialize vortex particle.
initVortexParticle :: Double -> Double -> VortexState
initVortexParticle startAngle startRadius = VortexState startAngle startRadius

-- | Step vortex particle forward one frame.
stepVortexParticle :: VortexParams -> VortexState -> (VortexState, Point2D)
stepVortexParticle params state =
  let fp = vpBase params
      maxRadius = if vpMaxRadius params == 0
                  then min (fpWidth fp) (fpHeight fp) * 0.4
                  else vpMaxRadius params
      center = if px (vpCenter params) == 0 && py (vpCenter params) == 0
               then Point2D (fpWidth fp / 2) (fpHeight fp / 2)
               else vpCenter params

      angularSpeed = vpStrength params * (1 + (maxRadius - vsRadius state) / maxRadius * 2)
      newAngle = vsAngle state + angularSpeed
      newRadius = max 10 (vsRadius state - vsRadius state * 0.01 * vpStrength params)

      noise = simplexNoise2D (vsAngle state) (vsRadius state * 0.01) (fpSeed fp)
      noisedRadius = newRadius * (1 + (noise - 0.5) * fpNoiseStrength fp)

      x = px center + cos newAngle * noisedRadius
      y = py center + sin newAngle * noisedRadius

      newState = VortexState newAngle newRadius
      pos = clampPoint (Point2D x y) 0 0 (fpWidth fp) (fpHeight fp)
  in (newState, pos)

--------------------------------------------------------------------------------
-- Data River Flow
--------------------------------------------------------------------------------

-- | Parameters for data river flow
data RiverParams = RiverParams
  { rpBase :: FlowParams
  , rpRiverWidth :: Double  -- 0 = height * 0.3
  , rpCurve :: Double       -- S-curve intensity
  , rpTurbulence :: Double  -- Lane turbulence
  } deriving (Eq, Show)

-- | Calculate river centerline y-position at x.
riverPath :: RiverParams -> Double -> Double
riverPath params x =
  let fp = rpBase params
      t = x / fpWidth fp
  in fpHeight fp / 2 + sin (t * pi * 2 * rpCurve params) * fpHeight fp * 0.25

-- | Calculate river position at time t.
riverPosition :: RiverParams -> Double -> Double -> Double -> Double
             -> Int -> Int -> (Point2D, Bool)
riverPosition params t startX laneOffset speed pointIndex frameIndex =
  let fp = rpBase params
      riverWidth = if rpRiverWidth params == 0
                   then fpHeight fp * 0.3
                   else rpRiverWidth params

      x = startX + t * fpWidth fp * speed * 1.3
      baseY = riverPath params x

      noise = simplexNoise2D (x * 0.01) (fromIntegral frameIndex * 0.05 + fromIntegral pointIndex * 0.1) (fpSeed fp)
      y = baseY + laneOffset + (noise - 0.5) * riverWidth * rpTurbulence params * 2

      pos = clampPoint (Point2D x y) 0 0 (fpWidth fp) (fpHeight fp)
      visible = x >= 0 && x <= fpWidth fp
  in (pos, visible)

--------------------------------------------------------------------------------
-- Morph Flow
--------------------------------------------------------------------------------

-- | Shape type for morph source/target
data MorphShape = Grid | Circle | Random
  deriving (Eq, Show)

-- | Easing type for morph transition
data MorphEasing = EaseIn | EaseOut | EaseInOut
  deriving (Eq, Show)

-- | Parameters for morph flow
data MorphParams = MorphParams
  { mpBase :: FlowParams
  , mpSourceShape :: MorphShape
  , mpTargetShape :: MorphShape
  , mpEasing :: MorphEasing
  } deriving (Eq, Show)

-- | Apply morph easing function
applyMorphEasing :: MorphEasing -> Double -> Double
applyMorphEasing easing t = case easing of
  EaseIn -> t * t
  EaseOut -> 1 - (1 - t) * (1 - t)
  EaseInOut ->
    if t < 0.5 then 2 * t * t
    else 1 - ((-2 * t + 2) * (-2 * t + 2)) / 2

-- | Generate grid position for point index
gridPosition :: FlowParams -> Int -> Int -> Point2D
gridPosition fp index numPoints =
  let cols = ceiling (sqrt (fromIntegral numPoints :: Double))
      row = index `div` cols
      col = index `mod` cols
      x = ((fromIntegral col + 0.5) / fromIntegral cols) * fpWidth fp * 0.8 + fpWidth fp * 0.1
      y = ((fromIntegral row + 0.5) / fromIntegral cols) * fpHeight fp * 0.8 + fpHeight fp * 0.1
  in Point2D x y

-- | Generate circle position for point index
circlePosition :: FlowParams -> Int -> Int -> Point2D
circlePosition fp index numPoints =
  let angle = (fromIntegral index / fromIntegral numPoints) * pi * 2
      radius = min (fpWidth fp) (fpHeight fp) * 0.35
      x = fpWidth fp / 2 + cos angle * radius
      y = fpHeight fp / 2 + sin angle * radius
  in Point2D x y

-- | Calculate morph position at time t.
morphPosition :: MorphParams -> Double -> Point2D -> Point2D
             -> Int -> Int -> Point2D
morphPosition params t source target pointIndex frameIndex =
  let fp = mpBase params
      easedT = applyMorphEasing (mpEasing params) t

      noise = simplexNoise2D (fromIntegral pointIndex * 0.1) (fromIntegral frameIndex * 0.02) (fpSeed fp)
      noiseOffset = (noise - 0.5) * 20 * (1 - abs (t - 0.5) * 2)

      x = px source + (px target - px source) * easedT + noiseOffset
      y = py source + (py target - py source) * easedT + noiseOffset

  in clampPoint (Point2D x y) 0 0 (fpWidth fp) (fpHeight fp)

--------------------------------------------------------------------------------
-- Swarm/Flocking Flow
--------------------------------------------------------------------------------

-- | Parameters for swarm/flocking behavior
data SwarmParams = SwarmParams
  { swBase :: FlowParams
  , swCohesion :: Double    -- Attraction to center of mass
  , swSeparation :: Double  -- Minimum distance between particles
  , swAlignment :: Double   -- Velocity matching strength
  , swMaxSpeed :: Double    -- Maximum particle velocity
  } deriving (Eq, Show)

-- | Swarm particle state
data SwarmParticle = SwarmParticle
  { spX :: Double
  , spY :: Double
  , spVx :: Double
  , spVy :: Double
  } deriving (Eq, Show)

-- | Calculate cohesion force toward center of mass
cohesionForce :: SwarmParams -> SwarmParticle -> Double -> Double -> (Double, Double)
cohesionForce params particle cx cy =
  let fx = (cx - spX particle) * swCohesion params
      fy = (cy - spY particle) * swCohesion params
  in (fx, fy)

-- | Calculate separation force from another particle
separationForce :: SwarmParams -> SwarmParticle -> SwarmParticle -> (Double, Double)
separationForce params p1 p2 =
  let dx = spX p1 - spX p2
      dy = spY p1 - spY p2
      dist = sqrt (dx * dx + dy * dy)
  in if dist < swSeparation params && dist > 0
     then let factor = (swSeparation params - dist) * 0.1
          in (dx / dist * factor, dy / dist * factor)
     else (0, 0)

-- | Calculate boundary avoidance force
boundaryForce :: SwarmParams -> SwarmParticle -> (Double, Double)
boundaryForce params particle =
  let fp = swBase params
      margin = 50
      fx1 = if spX particle < margin then (margin - spX particle) * 0.1 else 0
      fx2 = if spX particle > fpWidth fp - margin then -(spX particle - (fpWidth fp - margin)) * 0.1 else 0
      fy1 = if spY particle < margin then (margin - spY particle) * 0.1 else 0
      fy2 = if spY particle > fpHeight fp - margin then -(spY particle - (fpHeight fp - margin)) * 0.1 else 0
  in (fx1 + fx2, fy1 + fy2)

-- | Clamp velocity to max speed
clampVelocity :: Double -> Double -> Double -> (Double, Double)
clampVelocity vx vy maxSpeed =
  let speed = sqrt (vx * vx + vy * vy)
  in if speed > maxSpeed
     then (vx / speed * maxSpeed, vy / speed * maxSpeed)
     else (vx, vy)

-- | Update swarm particle with forces
updateSwarmParticle :: SwarmParams -> SwarmParticle -> Double -> Double
                   -> (SwarmParticle, Point2D)
updateSwarmParticle params particle fx fy =
  let fp = swBase params
      newVx = spVx particle + fx
      newVy = spVy particle + fy
      (clampedVx, clampedVy) = clampVelocity newVx newVy (swMaxSpeed params)
      newX = spX particle + clampedVx
      newY = spY particle + clampedVy

      newParticle = SwarmParticle newX newY clampedVx clampedVy
      pos = clampPoint (Point2D newX newY) 0 0 (fpWidth fp) (fpHeight fp)
  in (newParticle, pos)
