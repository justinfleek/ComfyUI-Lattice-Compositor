-- | Lattice.Services.Physics.Verlet - Verlet Integration for Soft Bodies
-- |
-- | Pure mathematical functions for position-based dynamics using Verlet
-- | integration. Used for soft body and cloth simulation.
-- |
-- | Features:
-- | - Verlet integration (position-based)
-- | - Distance constraint solving
-- | - Constraint breaking (tearing)
-- | - Damping
-- |
-- | Verlet integration formula:
-- |   x_new = x_curr + (x_curr - x_prev) * damping + a * dt²
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts

module Lattice.Services.Physics.Verlet
  ( ParticleState
  , Constraint
  , ConstraintResult
  , integrateParticle
  , getVelocity
  , setVelocity
  , solveConstraint
  , structuralRestLength
  , shearRestLength
  , bendRestLength
  , gridIndex
  , gridRowCol
  , collideWithGround
  , constrainToBounds
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (sqrt)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Verlet particle state
type ParticleState =
  { posX :: Number
  , posY :: Number
  , prevX :: Number
  , prevY :: Number
  , accelX :: Number
  , accelY :: Number
  , invMass :: Number  -- ^ 0 for pinned particles
  }

-- | Distance constraint between two particles
type Constraint =
  { restLength :: Number
  , stiffness :: Number         -- ^ 0-1, how rigidly constraint is enforced
  , breakThreshold :: Maybe Number  -- ^ If set, constraint breaks when stretched beyond this ratio
  }

-- | Result of constraint solving
type ConstraintResult =
  { particle1PosX :: Number
  , particle1PosY :: Number
  , particle2PosX :: Number
  , particle2PosY :: Number
  , broken :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Verlet Integration
-- ────────────────────────────────────────────────────────────────────────────

-- | Perform Verlet integration step for a single particle.
-- |
-- | Verlet formula: x_new = x + (x - x_prev) * damping + a * dt²
integrateParticle :: ParticleState -> Number -> Number -> ParticleState
integrateParticle state damping dt =
  if state.invMass == 0.0
  then state  -- Pinned particle
  else
    let dtSq = dt * dt
        velX = state.posX - state.prevX
        velY = state.posY - state.prevY
        dampedVelX = velX * damping
        dampedVelY = velY * damping
        newPosX = state.posX + dampedVelX + state.accelX * dtSq
        newPosY = state.posY + dampedVelY + state.accelY * dtSq
    in state { posX = newPosX
             , posY = newPosY
             , prevX = state.posX
             , prevY = state.posY
             , accelX = 0.0
             , accelY = 0.0
             }

-- | Extract velocity from particle state.
-- |
-- | Verlet velocity is implicit: v = (x_curr - x_prev) / dt
getVelocity :: ParticleState -> Tuple Number Number
getVelocity state = Tuple (state.posX - state.prevX) (state.posY - state.prevY)

-- | Set velocity by adjusting previous position.
setVelocity :: ParticleState -> Number -> Number -> ParticleState
setVelocity state velX velY =
  state { prevX = state.posX - velX
        , prevY = state.posY - velY
        }

-- ────────────────────────────────────────────────────────────────────────────
-- Distance Constraint Solving
-- ────────────────────────────────────────────────────────────────────────────

-- | Solve a distance constraint between two particles.
-- |
-- | Moves both particles to satisfy the rest length constraint.
-- | Mass-weighted: lighter particles move more.
solveConstraint :: ParticleState -> ParticleState -> Constraint -> ConstraintResult
solveConstraint p1 p2 constraint =
  let dx = p2.posX - p1.posX
      dy = p2.posY - p1.posY
      distance = sqrt (dx * dx + dy * dy)
  in case constraint.breakThreshold of
       Just threshold | distance > constraint.restLength * threshold ->
         { particle1PosX: p1.posX, particle1PosY: p1.posY
         , particle2PosX: p2.posX, particle2PosY: p2.posY
         , broken: true }
       _ -> solveConstraintInner p1 p2 constraint.restLength constraint.stiffness dx dy distance

solveConstraintInner :: ParticleState -> ParticleState -> Number -> Number -> Number -> Number -> Number -> ConstraintResult
solveConstraintInner p1 p2 restLength stiffness dx dy distance =
  let totalInvMass = p1.invMass + p2.invMass
  in if distance < 0.0001 || totalInvMass < 0.0001
     then { particle1PosX: p1.posX, particle1PosY: p1.posY
          , particle2PosX: p2.posX, particle2PosY: p2.posY
          , broken: false }
     else
       let err = (distance - restLength) / distance
           corrX = dx * err * stiffness * 0.5
           corrY = dy * err * stiffness * 0.5
           ratio1 = p1.invMass / totalInvMass
           ratio2 = p2.invMass / totalInvMass
       in { particle1PosX: p1.posX + corrX * ratio1
          , particle1PosY: p1.posY + corrY * ratio1
          , particle2PosX: p2.posX - corrX * ratio2
          , particle2PosY: p2.posY - corrY * ratio2
          , broken: false }

-- ────────────────────────────────────────────────────────────────────────────
-- Cloth Grid Helpers
-- ────────────────────────────────────────────────────────────────────────────

-- | Rest length for structural constraints (horizontal/vertical).
structuralRestLength :: Number -> Number
structuralRestLength spacing = spacing

-- | Rest length for shear constraints (diagonal).
shearRestLength :: Number -> Number
shearRestLength spacing = spacing * sqrt 2.0

-- | Rest length for bend constraints (skip one).
bendRestLength :: Number -> Number
bendRestLength spacing = spacing * 2.0

-- | Calculate grid index from row and column.
gridIndex :: Int -> Int -> Int -> Int
gridIndex row col width = row * width + col

-- | Calculate row and column from grid index.
gridRowCol :: Int -> Int -> Tuple Int Int
gridRowCol index width = Tuple (index / width) (index `mod` width)

-- ────────────────────────────────────────────────────────────────────────────
-- Collision
-- ────────────────────────────────────────────────────────────────────────────

-- | Handle collision with a ground plane.
collideWithGround :: Number -> Number -> Number -> Number
                  -> Number -> Number -> Number
                  -> { posX :: Number, posY :: Number, prevX :: Number, prevY :: Number }
collideWithGround posX posY prevX prevY groundY restitution friction =
  if posY >= groundY
  then { posX, posY, prevX, prevY }
  else
    let penetration = groundY - posY
        newPosY = groundY + penetration * restitution
        velY = posY - prevY
        newPrevY = newPosY + velY * restitution
        velX = posX - prevX
        newPrevX = posX - velX * (1.0 - friction)
    in { posX, posY: newPosY, prevX: newPrevX, prevY: newPrevY }

-- | Keep particle within a bounding box.
constrainToBounds :: Number -> Number -> Number -> Number
                  -> Number -> Number -> Number -> Number
                  -> Number
                  -> { posX :: Number, posY :: Number, prevX :: Number, prevY :: Number }
constrainToBounds posX posY prevX prevY minX minY maxX maxY restitution =
  let { newPosX, newPrevX } =
        if posX < minX then
          let pen = minX - posX
          in { newPosX: minX + pen * restitution, newPrevX: posX + (posX - prevX) * restitution }
        else if posX > maxX then
          let pen = posX - maxX
          in { newPosX: maxX - pen * restitution, newPrevX: posX + (posX - prevX) * restitution }
        else { newPosX: posX, newPrevX: prevX }

      { newPosY, newPrevY } =
        if posY < minY then
          let pen = minY - posY
          in { newPosY: minY + pen * restitution, newPrevY: posY + (posY - prevY) * restitution }
        else if posY > maxY then
          let pen = posY - maxY
          in { newPosY: maxY - pen * restitution, newPrevY: posY + (posY - prevY) * restitution }
        else { newPosY: posY, newPrevY: prevY }

  in { posX: newPosX, posY: newPosY, prevX: newPrevX, prevY: newPrevY }
