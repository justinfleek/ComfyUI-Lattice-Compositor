{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Physics.PhysicsSchema
Description : Physics simulation types
Copyright   : (c) Lattice, 2026
License     : MIT

Physics simulation type enums and core types.

Source: ui/src/schemas/physics/physics-schema.ts
-}

module Lattice.Schemas.Physics.PhysicsSchema
  ( -- * Body Type
    BodyType(..)
  , bodyTypeFromText
  , bodyTypeToText
    -- * Joint Type
  , JointType(..)
  , jointTypeFromText
  , jointTypeToText
    -- * Force Type
  , ForceType(..)
  , forceTypeFromText
  , forceTypeToText
    -- * Shape Type
  , ShapeType(..)
  , shapeTypeFromText
  , shapeTypeToText
    -- * Collision Response
  , CollisionResponse(..)
  , collisionResponseFromText
  , collisionResponseToText
    -- * Physics Vec2
  , PhysicsVec2(..)
    -- * Physics Material
  , PhysicsMaterial(..)
    -- * Collision Filter
  , CollisionFilter(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Body Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Physics body type options
data BodyType
  = BodyStatic
  | BodyDynamic
  | BodyKinematic
  | BodyDormant
  | BodyAEmatic
  | BodyDead
  deriving stock (Eq, Show, Generic, Enum, Bounded)

bodyTypeFromText :: Text -> Maybe BodyType
bodyTypeFromText "static" = Just BodyStatic
bodyTypeFromText "dynamic" = Just BodyDynamic
bodyTypeFromText "kinematic" = Just BodyKinematic
bodyTypeFromText "dormant" = Just BodyDormant
bodyTypeFromText "AEmatic" = Just BodyAEmatic
bodyTypeFromText "dead" = Just BodyDead
bodyTypeFromText _ = Nothing

bodyTypeToText :: BodyType -> Text
bodyTypeToText BodyStatic = "static"
bodyTypeToText BodyDynamic = "dynamic"
bodyTypeToText BodyKinematic = "kinematic"
bodyTypeToText BodyDormant = "dormant"
bodyTypeToText BodyAEmatic = "AEmatic"
bodyTypeToText BodyDead = "dead"

-- ────────────────────────────────────────────────────────────────────────────
-- Joint Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Physics joint type options
data JointType
  = JointPivot
  | JointSpring
  | JointDistance
  | JointPiston
  | JointWheel
  | JointWeld
  | JointBlob
  | JointRope
  deriving stock (Eq, Show, Generic, Enum, Bounded)

jointTypeFromText :: Text -> Maybe JointType
jointTypeFromText "pivot" = Just JointPivot
jointTypeFromText "spring" = Just JointSpring
jointTypeFromText "distance" = Just JointDistance
jointTypeFromText "piston" = Just JointPiston
jointTypeFromText "wheel" = Just JointWheel
jointTypeFromText "weld" = Just JointWeld
jointTypeFromText "blob" = Just JointBlob
jointTypeFromText "rope" = Just JointRope
jointTypeFromText _ = Nothing

jointTypeToText :: JointType -> Text
jointTypeToText JointPivot = "pivot"
jointTypeToText JointSpring = "spring"
jointTypeToText JointDistance = "distance"
jointTypeToText JointPiston = "piston"
jointTypeToText JointWheel = "wheel"
jointTypeToText JointWeld = "weld"
jointTypeToText JointBlob = "blob"
jointTypeToText JointRope = "rope"

-- ────────────────────────────────────────────────────────────────────────────
-- Force Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Physics force type options
data ForceType
  = ForceGravity
  | ForceWind
  | ForceAttraction
  | ForceExplosion
  | ForceBuoyancy
  | ForceVortex
  | ForceDrag
  deriving stock (Eq, Show, Generic, Enum, Bounded)

forceTypeFromText :: Text -> Maybe ForceType
forceTypeFromText "gravity" = Just ForceGravity
forceTypeFromText "wind" = Just ForceWind
forceTypeFromText "attraction" = Just ForceAttraction
forceTypeFromText "explosion" = Just ForceExplosion
forceTypeFromText "buoyancy" = Just ForceBuoyancy
forceTypeFromText "vortex" = Just ForceVortex
forceTypeFromText "drag" = Just ForceDrag
forceTypeFromText _ = Nothing

forceTypeToText :: ForceType -> Text
forceTypeToText ForceGravity = "gravity"
forceTypeToText ForceWind = "wind"
forceTypeToText ForceAttraction = "attraction"
forceTypeToText ForceExplosion = "explosion"
forceTypeToText ForceBuoyancy = "buoyancy"
forceTypeToText ForceVortex = "vortex"
forceTypeToText ForceDrag = "drag"

-- ────────────────────────────────────────────────────────────────────────────
-- Shape Type
-- ────────────────────────────────────────────────────────────────────────────

-- | Collision shape type options
data ShapeType
  = ShapeCircle
  | ShapeBox
  | ShapePolygon
  | ShapeCapsule
  | ShapeConvex
  | ShapeCompound
  deriving stock (Eq, Show, Generic, Enum, Bounded)

shapeTypeFromText :: Text -> Maybe ShapeType
shapeTypeFromText "circle" = Just ShapeCircle
shapeTypeFromText "box" = Just ShapeBox
shapeTypeFromText "polygon" = Just ShapePolygon
shapeTypeFromText "capsule" = Just ShapeCapsule
shapeTypeFromText "convex" = Just ShapeConvex
shapeTypeFromText "compound" = Just ShapeCompound
shapeTypeFromText _ = Nothing

shapeTypeToText :: ShapeType -> Text
shapeTypeToText ShapeCircle = "circle"
shapeTypeToText ShapeBox = "box"
shapeTypeToText ShapePolygon = "polygon"
shapeTypeToText ShapeCapsule = "capsule"
shapeTypeToText ShapeConvex = "convex"
shapeTypeToText ShapeCompound = "compound"

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Response
-- ────────────────────────────────────────────────────────────────────────────

-- | Collision response options
data CollisionResponse
  = ResponseCollide
  | ResponseSensor
  | ResponseNone
  deriving stock (Eq, Show, Generic, Enum, Bounded)

collisionResponseFromText :: Text -> Maybe CollisionResponse
collisionResponseFromText "collide" = Just ResponseCollide
collisionResponseFromText "sensor" = Just ResponseSensor
collisionResponseFromText "none" = Just ResponseNone
collisionResponseFromText _ = Nothing

collisionResponseToText :: CollisionResponse -> Text
collisionResponseToText ResponseCollide = "collide"
collisionResponseToText ResponseSensor = "sensor"
collisionResponseToText ResponseNone = "none"

-- ────────────────────────────────────────────────────────────────────────────
-- Physics Vec2
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D vector for physics
data PhysicsVec2 = PhysicsVec2
  { pv2X :: !Double
  , pv2Y :: !Double
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Physics Material
-- ────────────────────────────────────────────────────────────────────────────

-- | Physics material properties
data PhysicsMaterial = PhysicsMaterial
  { pmRestitution :: !Double      -- 0-1
  , pmFriction :: !Double         -- >= 0
  , pmSurfaceVelocity :: !(Maybe PhysicsVec2)
  }
  deriving stock (Eq, Show, Generic)

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Filter
-- ────────────────────────────────────────────────────────────────────────────

-- | Collision filtering
data CollisionFilter = CollisionFilter
  { cfCategory :: !Int       -- Max 32 categories
  , cfMask :: !Int           -- Bitmask
  , cfGroup :: !Int          -- 16-bit signed range
  }
  deriving stock (Eq, Show, Generic)
