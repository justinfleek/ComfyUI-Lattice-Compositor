{-|
Module      : Lattice.Services.Physics.Verlet
Description : Verlet Integration for Soft Bodies
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for position-based dynamics using Verlet
integration. Used for soft body and cloth simulation.

Features:
- Verlet integration (position-based)
- Distance constraint solving
- Constraint breaking (tearing)
- Damping

Verlet integration formula:
  x_new = x_curr + (x_curr - x_prev) * damping + a * dt²

Source: ui/src/services/physics/PhysicsEngine.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.Verlet
  ( -- * Types
    ParticleState(..)
  , Constraint(..)
  , ConstraintResult(..)
    -- * Verlet Integration
  , integrateParticle
  , getVelocity
  , setVelocity
    -- * Constraint Solving
  , solveConstraint
    -- * Cloth Grid Helpers
  , structuralRestLength
  , shearRestLength
  , bendRestLength
  , gridIndex
  , gridRowCol
    -- * Collision
  , collideWithGround
  , constrainToBounds
  ) where

import Data.Maybe (Maybe(..))

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Verlet particle state
data ParticleState = ParticleState
  { psPosX :: Double
  , psPosY :: Double
  , psPrevX :: Double
  , psPrevY :: Double
  , psAccelX :: Double
  , psAccelY :: Double
  , psInvMass :: Double  -- ^ 0 for pinned particles
  } deriving (Show, Eq)

-- | Distance constraint between two particles
data Constraint = Constraint
  { cRestLength :: Double
  , cStiffness :: Double       -- ^ 0-1, how rigidly constraint is enforced
  , cBreakThreshold :: Maybe Double  -- ^ If set, constraint breaks when stretched beyond this ratio
  } deriving (Show, Eq)

-- | Result of constraint solving
data ConstraintResult = ConstraintResult
  { crParticle1PosX :: Double
  , crParticle1PosY :: Double
  , crParticle2PosX :: Double
  , crParticle2PosY :: Double
  , crBroken :: Bool
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Verlet Integration
-- ────────────────────────────────────────────────────────────────────────────

-- | Perform Verlet integration step for a single particle.
--
-- Verlet formula: x_new = x + (x - x_prev) * damping + a * dt²
integrateParticle :: ParticleState
                  -> Double  -- ^ Damping (0-1, typically 0.98)
                  -> Double  -- ^ Time step
                  -> ParticleState
integrateParticle state damping dt
  | psInvMass state == 0 = state  -- Pinned particle
  | otherwise =
      let dtSq = dt * dt
          velX = psPosX state - psPrevX state
          velY = psPosY state - psPrevY state
          dampedVelX = velX * damping
          dampedVelY = velY * damping
          newPosX = psPosX state + dampedVelX + psAccelX state * dtSq
          newPosY = psPosY state + dampedVelY + psAccelY state * dtSq
      in state { psPosX = newPosX
               , psPosY = newPosY
               , psPrevX = psPosX state
               , psPrevY = psPosY state
               , psAccelX = 0
               , psAccelY = 0
               }

-- | Extract velocity from particle state.
--
-- Verlet velocity is implicit: v = (x_curr - x_prev) / dt
getVelocity :: ParticleState -> (Double, Double)
getVelocity state = (psPosX state - psPrevX state, psPosY state - psPrevY state)

-- | Set velocity by adjusting previous position.
setVelocity :: ParticleState -> Double -> Double -> ParticleState
setVelocity state velX velY =
  state { psPrevX = psPosX state - velX
        , psPrevY = psPosY state - velY
        }

-- ────────────────────────────────────────────────────────────────────────────
-- Distance Constraint Solving
-- ────────────────────────────────────────────────────────────────────────────

-- | Solve a distance constraint between two particles.
--
-- Moves both particles to satisfy the rest length constraint.
-- Mass-weighted: lighter particles move more.
solveConstraint :: ParticleState -> ParticleState -> Constraint -> ConstraintResult
solveConstraint p1 p2 constraint =
  let dx = psPosX p2 - psPosX p1
      dy = psPosY p2 - psPosY p1
      distance = sqrt (dx * dx + dy * dy)
  in case cBreakThreshold constraint of
       Just threshold | distance > cRestLength constraint * threshold ->
         ConstraintResult (psPosX p1) (psPosY p1) (psPosX p2) (psPosY p2) True
       _ -> solveConstraintInner p1 p2 (cRestLength constraint) (cStiffness constraint) dx dy distance

solveConstraintInner :: ParticleState -> ParticleState -> Double -> Double -> Double -> Double -> Double -> ConstraintResult
solveConstraintInner p1 p2 restLength stiffness dx dy distance
  | distance < 0.0001 =
      ConstraintResult (psPosX p1) (psPosY p1) (psPosX p2) (psPosY p2) False
  | totalInvMass < 0.0001 =
      ConstraintResult (psPosX p1) (psPosY p1) (psPosX p2) (psPosY p2) False
  | otherwise =
      let err = (distance - restLength) / distance
          corrX = dx * err * stiffness * 0.5
          corrY = dy * err * stiffness * 0.5
          ratio1 = psInvMass p1 / totalInvMass
          ratio2 = psInvMass p2 / totalInvMass
      in ConstraintResult
           (psPosX p1 + corrX * ratio1)
           (psPosY p1 + corrY * ratio1)
           (psPosX p2 - corrX * ratio2)
           (psPosY p2 - corrY * ratio2)
           False
  where
    totalInvMass = psInvMass p1 + psInvMass p2

-- ────────────────────────────────────────────────────────────────────────────
-- Cloth Grid Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Rest length for structural constraints (horizontal/vertical).
structuralRestLength :: Double -> Double
structuralRestLength = id

-- | Rest length for shear constraints (diagonal).
shearRestLength :: Double -> Double
shearRestLength spacing = spacing * sqrt 2

-- | Rest length for bend constraints (skip one).
bendRestLength :: Double -> Double
bendRestLength spacing = spacing * 2

-- | Calculate grid index from row and column.
gridIndex :: Int -> Int -> Int -> Int
gridIndex row col width = row * width + col

-- | Calculate row and column from grid index.
gridRowCol :: Int -> Int -> (Int, Int)
gridRowCol index width = (index `div` width, index `mod` width)

-- ────────────────────────────────────────────────────────────────────────────
-- Collision
-- ────────────────────────────────────────────────────────────────────────────

-- | Handle collision with a ground plane.
collideWithGround :: Double  -- ^ posX
                  -> Double  -- ^ posY
                  -> Double  -- ^ prevX
                  -> Double  -- ^ prevY
                  -> Double  -- ^ groundY
                  -> Double  -- ^ restitution
                  -> Double  -- ^ friction
                  -> (Double, Double, Double, Double)
collideWithGround posX posY prevX prevY groundY restitution friction
  | posY >= groundY = (posX, posY, prevX, prevY)
  | otherwise =
      let penetration = groundY - posY
          newPosY = groundY + penetration * restitution
          velY = posY - prevY
          newPrevY = newPosY + velY * restitution
          velX = posX - prevX
          newPrevX = posX - velX * (1 - friction)
      in (posX, newPosY, newPrevX, newPrevY)

-- | Keep particle within a bounding box.
constrainToBounds :: Double -> Double -> Double -> Double
                  -> Double -> Double -> Double -> Double
                  -> Double
                  -> (Double, Double, Double, Double)
constrainToBounds posX posY prevX prevY minX minY maxX maxY restitution =
  let (newPosX, newPrevX)
        | posX < minX =
            let pen = minX - posX
            in (minX + pen * restitution, posX + (posX - prevX) * restitution)
        | posX > maxX =
            let pen = posX - maxX
            in (maxX - pen * restitution, posX + (posX - prevX) * restitution)
        | otherwise = (posX, prevX)

      (newPosY, newPrevY)
        | posY < minY =
            let pen = minY - posY
            in (minY + pen * restitution, posY + (posY - prevY) * restitution)
        | posY > maxY =
            let pen = posY - maxY
            in (maxY - pen * restitution, posY + (posY - prevY) * restitution)
        | otherwise = (posY, prevY)

  in (newPosX, newPosY, newPrevX, newPrevY)
