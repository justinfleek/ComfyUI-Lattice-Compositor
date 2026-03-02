-- | Lattice.Schemas.Physics.PhysicsSchema - Physics simulation types
-- |
-- | Physics simulation type enums and core types.
-- |
-- | Source: ui/src/schemas/physics/physics-schema.ts

module Lattice.Schemas.Physics.PhysicsSchema
  ( -- Body Type
    BodyType(..)
  , bodyTypeFromString
  , bodyTypeToString
    -- Joint Type
  , JointType(..)
  , jointTypeFromString
  , jointTypeToString
    -- Force Type
  , ForceType(..)
  , forceTypeFromString
  , forceTypeToString
    -- Shape Type
  , ShapeType(..)
  , shapeTypeFromString
  , shapeTypeToString
    -- Collision Response
  , CollisionResponse(..)
  , collisionResponseFromString
  , collisionResponseToString
    -- Physics Vec2
  , PhysicsVec2
    -- Physics Material
  , PhysicsMaterial
    -- Collision Filter
  , CollisionFilter
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

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

derive instance Eq BodyType
derive instance Generic BodyType _

instance Show BodyType where
  show = genericShow

bodyTypeFromString :: String -> Maybe BodyType
bodyTypeFromString = case _ of
  "static" -> Just BodyStatic
  "dynamic" -> Just BodyDynamic
  "kinematic" -> Just BodyKinematic
  "dormant" -> Just BodyDormant
  "AEmatic" -> Just BodyAEmatic
  "dead" -> Just BodyDead
  _ -> Nothing

bodyTypeToString :: BodyType -> String
bodyTypeToString = case _ of
  BodyStatic -> "static"
  BodyDynamic -> "dynamic"
  BodyKinematic -> "kinematic"
  BodyDormant -> "dormant"
  BodyAEmatic -> "AEmatic"
  BodyDead -> "dead"

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

derive instance Eq JointType
derive instance Generic JointType _

instance Show JointType where
  show = genericShow

jointTypeFromString :: String -> Maybe JointType
jointTypeFromString = case _ of
  "pivot" -> Just JointPivot
  "spring" -> Just JointSpring
  "distance" -> Just JointDistance
  "piston" -> Just JointPiston
  "wheel" -> Just JointWheel
  "weld" -> Just JointWeld
  "blob" -> Just JointBlob
  "rope" -> Just JointRope
  _ -> Nothing

jointTypeToString :: JointType -> String
jointTypeToString = case _ of
  JointPivot -> "pivot"
  JointSpring -> "spring"
  JointDistance -> "distance"
  JointPiston -> "piston"
  JointWheel -> "wheel"
  JointWeld -> "weld"
  JointBlob -> "blob"
  JointRope -> "rope"

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

derive instance Eq ForceType
derive instance Generic ForceType _

instance Show ForceType where
  show = genericShow

forceTypeFromString :: String -> Maybe ForceType
forceTypeFromString = case _ of
  "gravity" -> Just ForceGravity
  "wind" -> Just ForceWind
  "attraction" -> Just ForceAttraction
  "explosion" -> Just ForceExplosion
  "buoyancy" -> Just ForceBuoyancy
  "vortex" -> Just ForceVortex
  "drag" -> Just ForceDrag
  _ -> Nothing

forceTypeToString :: ForceType -> String
forceTypeToString = case _ of
  ForceGravity -> "gravity"
  ForceWind -> "wind"
  ForceAttraction -> "attraction"
  ForceExplosion -> "explosion"
  ForceBuoyancy -> "buoyancy"
  ForceVortex -> "vortex"
  ForceDrag -> "drag"

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

derive instance Eq ShapeType
derive instance Generic ShapeType _

instance Show ShapeType where
  show = genericShow

shapeTypeFromString :: String -> Maybe ShapeType
shapeTypeFromString = case _ of
  "circle" -> Just ShapeCircle
  "box" -> Just ShapeBox
  "polygon" -> Just ShapePolygon
  "capsule" -> Just ShapeCapsule
  "convex" -> Just ShapeConvex
  "compound" -> Just ShapeCompound
  _ -> Nothing

shapeTypeToString :: ShapeType -> String
shapeTypeToString = case _ of
  ShapeCircle -> "circle"
  ShapeBox -> "box"
  ShapePolygon -> "polygon"
  ShapeCapsule -> "capsule"
  ShapeConvex -> "convex"
  ShapeCompound -> "compound"

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Response
-- ────────────────────────────────────────────────────────────────────────────

-- | Collision response options
data CollisionResponse
  = ResponseCollide
  | ResponseSensor
  | ResponseNone

derive instance Eq CollisionResponse
derive instance Generic CollisionResponse _

instance Show CollisionResponse where
  show = genericShow

collisionResponseFromString :: String -> Maybe CollisionResponse
collisionResponseFromString = case _ of
  "collide" -> Just ResponseCollide
  "sensor" -> Just ResponseSensor
  "none" -> Just ResponseNone
  _ -> Nothing

collisionResponseToString :: CollisionResponse -> String
collisionResponseToString = case _ of
  ResponseCollide -> "collide"
  ResponseSensor -> "sensor"
  ResponseNone -> "none"

-- ────────────────────────────────────────────────────────────────────────────
-- Physics Vec2
-- ────────────────────────────────────────────────────────────────────────────

-- | 2D vector for physics
type PhysicsVec2 =
  { x :: Number
  , y :: Number
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Physics Material
-- ────────────────────────────────────────────────────────────────────────────

-- | Physics material properties
type PhysicsMaterial =
  { restitution :: Number       -- 0-1
  , friction :: Number          -- >= 0
  , surfaceVelocity :: Maybe PhysicsVec2
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Filter
-- ────────────────────────────────────────────────────────────────────────────

-- | Collision filtering
type CollisionFilter =
  { category :: Int       -- Max 32 categories
  , mask :: Int           -- Bitmask
  , group :: Int          -- 16-bit signed range
  }
