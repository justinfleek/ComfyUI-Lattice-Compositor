-- | Lattice.Services.Physics.RigidBody - Rigid Body Physics Calculations
-- |
-- | Pure mathematical functions for rigid body dynamics:
-- | - Moment of inertia for various shapes
-- | - Impulse-based collision response
-- | - Friction calculation (Coulomb's law)
-- | - Position correction
-- | - Semi-implicit Euler integration
-- |
-- | All functions are deterministic and side-effect free.
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts

module Lattice.Services.Physics.RigidBody
  ( ShapeType(..)
  , BodyState
  , momentOfInertiaCircle
  , momentOfInertiaBox
  , momentOfInertiaCapsule
  , momentOfInertia
  , integrateVelocity
  , integratePosition
  , integrateBody
  , calculateImpulseMagnitude
  , angularImpulseTerm
  , calculateFrictionImpulse
  , positionCorrection
  , applyImpulse
  ) where

import Prelude

import Data.Tuple (Tuple(..))
import Math (max, min, pi, sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Shape type for moment of inertia calculation
data ShapeType = CircleShape | BoxShape | CapsuleShape

derive instance eqShapeType :: Eq ShapeType

-- | Rigid body state
type BodyState =
  { posX :: Number
  , posY :: Number
  , velX :: Number
  , velY :: Number
  , angle :: Number
  , angularVelocity :: Number
  , inverseMass :: Number
  , inverseInertia :: Number
  }

--------------------------------------------------------------------------------
-- Moment of Inertia
--------------------------------------------------------------------------------

-- | Calculate moment of inertia for a circle.
-- |
-- | Formula: I = (m * r²) / 2
momentOfInertiaCircle :: Number -> Number -> Number
momentOfInertiaCircle mass radius =
  (mass * radius * radius) / 2.0

-- | Calculate moment of inertia for a box (rectangle).
-- |
-- | Formula: I = (m * (w² + h²)) / 12
momentOfInertiaBox :: Number -> Number -> Number -> Number
momentOfInertiaBox mass width height =
  (mass * (width * width + height * height)) / 12.0

-- | Calculate moment of inertia for a capsule (stadium shape).
-- |
-- | Approximates as rectangle + two semicircles.
momentOfInertiaCapsule :: Number -> Number -> Number -> Number
momentOfInertiaCapsule mass radius len =
  let totalLength = len + pi * radius
      rectMass = (mass * len) / totalLength
      circleMass = mass - rectMass
      rectI = (rectMass * (len * len + 4.0 * radius * radius)) / 12.0
      circleI = (circleMass * radius * radius) / 2.0
  in rectI + circleI

-- | Calculate moment of inertia based on shape type.
momentOfInertia :: ShapeType -> Number -> Number -> Number -> Number
momentOfInertia shapeType mass param1 param2 = case shapeType of
  CircleShape  -> momentOfInertiaCircle mass param1
  BoxShape     -> momentOfInertiaBox mass param1 param2
  CapsuleShape -> momentOfInertiaCapsule mass param1 param2

--------------------------------------------------------------------------------
-- Semi-Implicit Euler Integration
--------------------------------------------------------------------------------

-- | Integrate velocity with acceleration and damping.
-- |
-- | Semi-implicit Euler: v_new = v + a * dt, then apply damping
integrateVelocity :: Number -> Number -> Number -> Number -> Number
integrateVelocity vel accel damping dt =
  let newVel = vel + accel * dt
  in newVel * (1.0 - damping * dt)

-- | Integrate position with velocity.
integratePosition :: Number -> Number -> Number -> Number
integratePosition pos vel dt = pos + vel * dt

-- | Integrate a full body state.
integrateBody :: BodyState -> Number -> Number -> Number -> Number -> Number -> Number -> BodyState
integrateBody state forceX forceY torque linearDamping angularDamping dt =
  let accelX = forceX * state.inverseMass
      accelY = forceY * state.inverseMass
      angAccel = torque * state.inverseInertia

      newVelX = integrateVelocity state.velX accelX linearDamping dt
      newVelY = integrateVelocity state.velY accelY linearDamping dt
      newAngVel = integrateVelocity state.angularVelocity angAccel angularDamping dt

      newPosX = integratePosition state.posX newVelX dt
      newPosY = integratePosition state.posY newVelY dt
      newAngle = integratePosition state.angle newAngVel dt

  in state { posX = newPosX
           , posY = newPosY
           , velX = newVelX
           , velY = newVelY
           , angle = newAngle
           , angularVelocity = newAngVel
           }

--------------------------------------------------------------------------------
-- Collision Response
--------------------------------------------------------------------------------

-- | Calculate impulse magnitude for collision response.
-- |
-- | Uses: j = -(1 + e) * v_rel · n / (1/m1 + 1/m2 + angular terms)
calculateImpulseMagnitude :: Number -> Number -> Number -> Number -> Number
calculateImpulseMagnitude normalVelocity restitution invMassSum angularTerm =
  let denominator = invMassSum + angularTerm
  in if denominator < 0.0001
     then 0.0
     else -(1.0 + restitution) * normalVelocity / denominator

-- | Calculate angular contribution to impulse denominator.
-- |
-- | Term: (r × n)² * invInertia
angularImpulseTerm :: Number -> Number -> Number -> Number -> Number -> Number
angularImpulseTerm rx ry nx ny inverseInertia =
  let rCrossN = rx * ny - ry * nx
  in rCrossN * rCrossN * inverseInertia

-- | Calculate friction impulse using Coulomb's law.
-- |
-- | Friction impulse is clamped to: |jt| ≤ μ * |jn|
calculateFrictionImpulse :: Number -> Number -> Number -> Number -> Number
calculateFrictionImpulse tangentVelocity invMassSum normalImpulse friction =
  if invMassSum < 0.0001
  then 0.0
  else let jt = -tangentVelocity / invMassSum
           maxFriction = normalImpulse * friction
       in max (-maxFriction) (min maxFriction jt)

-- | Calculate position correction to resolve penetration.
-- |
-- | Uses Baumgarte stabilization with slop and bias.
positionCorrection :: Number -> Number -> Number -> Number -> Number
positionCorrection depth slop bias invMassSum =
  if invMassSum < 0.0001
  then 0.0
  else let correctionDepth = max 0.0 (depth - slop)
       in correctionDepth * bias / invMassSum

-- | Apply impulse to a body.
-- |
-- | Returns (new velX, new velY, new angVel)
applyImpulse :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number
             -> Tuple (Tuple Number Number) Number
applyImpulse velX velY angVel impulseX impulseY rx ry inverseMass inverseInertia sign =
  let newVelX = velX + sign * impulseX * inverseMass
      newVelY = velY + sign * impulseY * inverseMass
      rCrossI = rx * impulseY - ry * impulseX
      newAngVel = angVel + sign * rCrossI * inverseInertia
  in Tuple (Tuple newVelX newVelY) newAngVel
