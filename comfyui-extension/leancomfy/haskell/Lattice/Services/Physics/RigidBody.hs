{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Physics.RigidBody
Description : Rigid Body Physics Calculations
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for rigid body dynamics:
- Moment of inertia for various shapes
- Impulse-based collision response
- Friction calculation (Coulomb's law)
- Position correction
- Semi-implicit Euler integration

All functions are deterministic and side-effect free.

Source: ui/src/services/physics/PhysicsEngine.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.RigidBody
  ( -- * Types
    ShapeType(..)
  , BodyState(..)
    -- * Moment of Inertia
  , momentOfInertiaCircle
  , momentOfInertiaBox
  , momentOfInertiaCapsule
  , momentOfInertia
    -- * Integration
  , integrateVelocity
  , integratePosition
  , integrateBody
    -- * Collision Response
  , calculateImpulseMagnitude
  , angularImpulseTerm
  , calculateFrictionImpulse
  , positionCorrection
  , applyImpulse
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Shape type for moment of inertia calculation
data ShapeType = CircleShape | BoxShape | CapsuleShape
  deriving (Show, Eq)

-- | Rigid body state
data BodyState = BodyState
  { bsPosX :: Double
  , bsPosY :: Double
  , bsVelX :: Double
  , bsVelY :: Double
  , bsAngle :: Double
  , bsAngularVelocity :: Double
  , bsInverseMass :: Double
  , bsInverseInertia :: Double
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Moment of Inertia
--------------------------------------------------------------------------------

-- | Calculate moment of inertia for a circle.
--
-- Formula: I = (m * r²) / 2
momentOfInertiaCircle :: Double  -- ^ Mass
                      -> Double  -- ^ Radius
                      -> Double  -- ^ Moment of inertia
momentOfInertiaCircle mass radius =
  (mass * radius * radius) / 2

-- | Calculate moment of inertia for a box (rectangle).
--
-- Formula: I = (m * (w² + h²)) / 12
--
-- This is the moment about the center of mass.
momentOfInertiaBox :: Double  -- ^ Mass
                   -> Double  -- ^ Width
                   -> Double  -- ^ Height
                   -> Double  -- ^ Moment of inertia
momentOfInertiaBox mass width height =
  (mass * (width * width + height * height)) / 12

-- | Calculate moment of inertia for a capsule (stadium shape).
--
-- Approximates as rectangle + two semicircles.
momentOfInertiaCapsule :: Double  -- ^ Mass
                       -> Double  -- ^ Radius
                       -> Double  -- ^ Length
                       -> Double  -- ^ Moment of inertia
momentOfInertiaCapsule mass radius len =
  let totalLength = len + pi * radius
      rectMass = (mass * len) / totalLength
      circleMass = mass - rectMass
      rectI = (rectMass * (len * len + 4 * radius * radius)) / 12
      circleI = (circleMass * radius * radius) / 2
  in rectI + circleI

-- | Calculate moment of inertia based on shape type.
momentOfInertia :: ShapeType
                -> Double  -- ^ Mass
                -> Double  -- ^ Param1 (radius for circle/capsule, width for box)
                -> Double  -- ^ Param2 (length for capsule, height for box)
                -> Double  -- ^ Moment of inertia
momentOfInertia shapeType mass param1 param2 =
  case shapeType of
    CircleShape  -> momentOfInertiaCircle mass param1
    BoxShape     -> momentOfInertiaBox mass param1 param2
    CapsuleShape -> momentOfInertiaCapsule mass param1 param2

--------------------------------------------------------------------------------
-- Semi-Implicit Euler Integration
--------------------------------------------------------------------------------

-- | Integrate velocity with acceleration and damping.
--
-- Semi-implicit Euler: v_new = v + a * dt, then apply damping
integrateVelocity :: Double  -- ^ Current velocity
                  -> Double  -- ^ Acceleration
                  -> Double  -- ^ Damping coefficient
                  -> Double  -- ^ Time step
                  -> Double  -- ^ New velocity
integrateVelocity vel accel damping dt =
  let newVel = vel + accel * dt
  in newVel * (1 - damping * dt)

-- | Integrate position with velocity.
integratePosition :: Double  -- ^ Current position
                  -> Double  -- ^ Velocity
                  -> Double  -- ^ Time step
                  -> Double  -- ^ New position
integratePosition pos vel dt = pos + vel * dt

-- | Integrate a full body state.
integrateBody :: BodyState
              -> Double  -- ^ Force X
              -> Double  -- ^ Force Y
              -> Double  -- ^ Torque
              -> Double  -- ^ Linear damping
              -> Double  -- ^ Angular damping
              -> Double  -- ^ Time step
              -> BodyState
integrateBody state forceX forceY torque linearDamping angularDamping dt =
  let accelX = forceX * bsInverseMass state
      accelY = forceY * bsInverseMass state
      angAccel = torque * bsInverseInertia state

      newVelX = integrateVelocity (bsVelX state) accelX linearDamping dt
      newVelY = integrateVelocity (bsVelY state) accelY linearDamping dt
      newAngVel = integrateVelocity (bsAngularVelocity state) angAccel angularDamping dt

      newPosX = integratePosition (bsPosX state) newVelX dt
      newPosY = integratePosition (bsPosY state) newVelY dt
      newAngle = integratePosition (bsAngle state) newAngVel dt

  in state { bsPosX = newPosX
           , bsPosY = newPosY
           , bsVelX = newVelX
           , bsVelY = newVelY
           , bsAngle = newAngle
           , bsAngularVelocity = newAngVel
           }

--------------------------------------------------------------------------------
-- Collision Response
--------------------------------------------------------------------------------

-- | Calculate impulse magnitude for collision response.
--
-- Uses: j = -(1 + e) * v_rel · n / (1/m1 + 1/m2 + angular terms)
calculateImpulseMagnitude :: Double  -- ^ Normal velocity (negative = approaching)
                          -> Double  -- ^ Restitution
                          -> Double  -- ^ Sum of inverse masses
                          -> Double  -- ^ Angular contribution term
                          -> Double  -- ^ Impulse magnitude
calculateImpulseMagnitude normalVelocity restitution invMassSum angularTerm =
  let denominator = invMassSum + angularTerm
  in if denominator < 0.0001
     then 0
     else -(1 + restitution) * normalVelocity / denominator

-- | Calculate angular contribution to impulse denominator.
--
-- Term: (r × n)² * invInertia
angularImpulseTerm :: Double  -- ^ Contact offset X
                   -> Double  -- ^ Contact offset Y
                   -> Double  -- ^ Normal X
                   -> Double  -- ^ Normal Y
                   -> Double  -- ^ Inverse inertia
                   -> Double  -- ^ Angular contribution
angularImpulseTerm rx ry nx ny inverseInertia =
  let rCrossN = rx * ny - ry * nx
  in rCrossN * rCrossN * inverseInertia

-- | Calculate friction impulse using Coulomb's law.
--
-- Friction impulse is clamped to: |jt| ≤ μ * |jn|
calculateFrictionImpulse :: Double  -- ^ Tangent velocity
                         -> Double  -- ^ Sum of inverse masses
                         -> Double  -- ^ Normal impulse magnitude
                         -> Double  -- ^ Friction coefficient
                         -> Double  -- ^ Friction impulse magnitude
calculateFrictionImpulse tangentVelocity invMassSum normalImpulse friction
  | invMassSum < 0.0001 = 0
  | otherwise =
      let jt = -tangentVelocity / invMassSum
          maxFriction = normalImpulse * friction
      in max (-maxFriction) (min maxFriction jt)

-- | Calculate position correction to resolve penetration.
--
-- Uses Baumgarte stabilization with slop and bias.
positionCorrection :: Double  -- ^ Penetration depth
                   -> Double  -- ^ Allowed slop
                   -> Double  -- ^ Correction bias
                   -> Double  -- ^ Sum of inverse masses
                   -> Double  -- ^ Correction magnitude
positionCorrection depth slop bias invMassSum
  | invMassSum < 0.0001 = 0
  | otherwise =
      let correctionDepth = max 0 (depth - slop)
      in correctionDepth * bias / invMassSum

-- | Apply impulse to a body.
--
-- Returns (new velX, new velY, new angVel)
applyImpulse :: Double  -- ^ Current X velocity
             -> Double  -- ^ Current Y velocity
             -> Double  -- ^ Current angular velocity
             -> Double  -- ^ Impulse X
             -> Double  -- ^ Impulse Y
             -> Double  -- ^ Contact offset X
             -> Double  -- ^ Contact offset Y
             -> Double  -- ^ Inverse mass
             -> Double  -- ^ Inverse inertia
             -> Double  -- ^ Sign (+1 or -1)
             -> (Double, Double, Double)
applyImpulse velX velY angVel impulseX impulseY rx ry inverseMass inverseInertia sign =
  let newVelX = velX + sign * impulseX * inverseMass
      newVelY = velY + sign * impulseY * inverseMass
      rCrossI = rx * impulseY - ry * impulseX
      newAngVel = angVel + sign * rCrossI * inverseInertia
  in (newVelX, newVelY, newAngVel)
