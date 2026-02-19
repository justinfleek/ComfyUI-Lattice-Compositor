{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Physics
Description : Physics system types
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Physics.lean
Consolidated from Physics/* submodules.
-}

module Lattice.Physics
  ( -- * Enumerations
    BodyType(..)
  , JointType(..)
  , ForceType(..)
  , ShapeType(..)
  , CollisionResponse(..)
  , ForceFalloff(..)
  , ConstraintTornType(..)
    -- * Core Types
  , PhysicsVec2(..)
  , PhysicsMaterial(..)
  , CollisionShape(..)
  , CollisionFilter(..)
  , RigidBodyConfig(..)
  , RigidBodyState(..)
    -- * Joint Types
  , JointConfigBase(..)
  , MotorSettings(..)
  , AngleLimits(..)
  , TranslationLimits(..)
    -- * Force Types
  , ForceFieldBase(..)
  , GravityForce(..)
  , WindForce(..)
  , AttractionForce(..)
    -- * Soft Body
  , VerletParticle(..)
  , VerletConstraint(..)
  , SoftBodyConfig(..)
    -- * Space Config
  , PhysicsSpaceConfig(..)
  , PhysicsLayerData(..)
  ) where

import GHC.Generics (Generic)
import Data.Vector (Vector)
import Lattice.Primitives

--------------------------------------------------------------------------------
-- Enumerations
--------------------------------------------------------------------------------

-- | Body type determines physics behavior
data BodyType
  = BTStatic     -- ^ Immovable, participates in collision
  | BTDynamic    -- ^ Fully simulated with mass, velocity, forces
  | BTKinematic  -- ^ User-controlled position, no forces
  | BTDormant    -- ^ Dynamic that's asleep
  | BTAematic    -- ^ Follows AE keyframes when present, dynamic otherwise
  | BTDead       -- ^ Removed from simulation
  deriving stock (Eq, Show, Generic)

-- | Joint types for connecting bodies
data JointType
  = JTPivot    -- ^ Rotation around single point
  | JTSpring   -- ^ Springy connection
  | JTDistance -- ^ Fixed distance constraint
  | JTPiston   -- ^ Slide along axis
  | JTWheel    -- ^ Motor-driven rotation
  | JTWeld     -- ^ Rigid connection
  | JTBlob     -- ^ Soft blob-like connection
  | JTRope     -- ^ One-way constraint
  deriving stock (Eq, Show, Generic)

-- | Force field types
data ForceType
  = FTGravity    -- ^ Directional constant force
  | FTWind       -- ^ Directional force with turbulence
  | FTAttraction -- ^ Point attractor/repeller
  | FTExplosion  -- ^ Radial impulse
  | FTBuoyancy   -- ^ Fluid buoyancy
  | FTVortex     -- ^ Rotational force
  | FTDrag       -- ^ Air/fluid resistance
  deriving stock (Eq, Show, Generic)

-- | Collision shape types
data ShapeType
  = STCircle | STBox | STPolygon | STCapsule | STConvex | STCompound
  deriving stock (Eq, Show, Generic)

-- | Collision response types
data CollisionResponse
  = CRCollide -- ^ Normal collision
  | CRSensor  -- ^ Detect but don't respond
  | CRNone    -- ^ No collision detection
  deriving stock (Eq, Show, Generic)

-- | Force falloff types
data ForceFalloff = FFLinear | FFQuadratic | FFConstant
  deriving stock (Eq, Show, Generic)

-- | Constraint torn types for cloth
data ConstraintTornType = CTTStructural | CTTShear | CTTBend
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Core Types
--------------------------------------------------------------------------------

data PhysicsVec2 = PhysicsVec2
  { pv2X :: !FiniteFloat
  , pv2Y :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data PhysicsMaterial = PhysicsMaterial
  { pmFriction    :: !NonNegativeFloat  -- 0-1
  , pmRestitution :: !UnitFloat         -- 0-1 (bounciness)
  , pmDensity     :: !PositiveFloat
  } deriving stock (Eq, Show, Generic)

data CollisionShape = CollisionShape
  { csShapeType :: !ShapeType
  , csRadius    :: !(Maybe PositiveFloat)  -- For circle/capsule
  , csWidth     :: !(Maybe PositiveFloat)  -- For box
  , csHeight    :: !(Maybe PositiveFloat)  -- For box/capsule
  , csVertices  :: !(Maybe (Vector PhysicsVec2))  -- For polygon/convex
  , csOffset    :: !PhysicsVec2
  , csRotation  :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data CollisionFilter = CollisionFilter
  { cfCategory :: !Int  -- Bit mask
  , cfMask     :: !Int  -- What to collide with
  , cfGroup    :: !Int  -- Group index
  } deriving stock (Eq, Show, Generic)

data RigidBodyConfig = RigidBodyConfig
  { rbcId               :: !NonEmptyString
  , rbcBodyType         :: !BodyType
  , rbcMass             :: !PositiveFloat
  , rbcMoment           :: !(Maybe PositiveFloat)  -- Auto-calc if None
  , rbcShape            :: !CollisionShape
  , rbcMaterial         :: !PhysicsMaterial
  , rbcCollisionFilter  :: !CollisionFilter
  , rbcCollisionResponse :: !CollisionResponse
  , rbcLinearDamping    :: !NonNegativeFloat
  , rbcAngularDamping   :: !NonNegativeFloat
  , rbcGravityScale     :: !FiniteFloat
  , rbcFixedRotation    :: !Bool
  , rbcInitialPosition  :: !PhysicsVec2
  , rbcInitialVelocity  :: !PhysicsVec2
  , rbcInitialAngle     :: !FiniteFloat
  , rbcInitialAngularVelocity :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

data RigidBodyState = RigidBodyState
  { rbsId              :: !NonEmptyString
  , rbsPosition        :: !PhysicsVec2
  , rbsVelocity        :: !PhysicsVec2
  , rbsAngle           :: !FiniteFloat
  , rbsAngularVelocity :: !FiniteFloat
  , rbsAsleep          :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Joint Types
--------------------------------------------------------------------------------

data JointConfigBase = JointConfigBase
  { jcbId          :: !NonEmptyString
  , jcbJointType   :: !JointType
  , jcbBodyAId     :: !NonEmptyString
  , jcbBodyBId     :: !(Maybe NonEmptyString)  -- None = world
  , jcbAnchorA     :: !PhysicsVec2
  , jcbAnchorB     :: !PhysicsVec2
  , jcbCollideConnected :: !Bool
  } deriving stock (Eq, Show, Generic)

data MotorSettings = MotorSettings
  { msEnabled  :: !Bool
  , msSpeed    :: !FiniteFloat
  , msMaxForce :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

data AngleLimits = AngleLimits
  { alEnabled :: !Bool
  , alMin     :: !FiniteFloat  -- Radians
  , alMax     :: !FiniteFloat  -- Radians
  } deriving stock (Eq, Show, Generic)

data TranslationLimits = TranslationLimits
  { tlEnabled :: !Bool
  , tlMin     :: !FiniteFloat
  , tlMax     :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Force Types
--------------------------------------------------------------------------------

data ForceFieldBase = ForceFieldBase
  { ffbId       :: !NonEmptyString
  , ffbForceType :: !ForceType
  , ffbEnabled  :: !Bool
  , ffbStrength :: !FiniteFloat
  , ffbFalloff  :: !ForceFalloff
  , ffbRadius   :: !(Maybe PositiveFloat)
  } deriving stock (Eq, Show, Generic)

data GravityForce = GravityForce
  { gfBase      :: !ForceFieldBase
  , gfDirection :: !PhysicsVec2
  } deriving stock (Eq, Show, Generic)

data WindForce = WindForce
  { wfBase        :: !ForceFieldBase
  , wfDirection   :: !PhysicsVec2
  , wfTurbulence  :: !NonNegativeFloat
  , wfGustiness   :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

data AttractionForce = AttractionForce
  { afBase     :: !ForceFieldBase
  , afPosition :: !PhysicsVec2
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Soft Body
--------------------------------------------------------------------------------

data VerletParticle = VerletParticle
  { vpId          :: !NonEmptyString
  , vpPosition    :: !PhysicsVec2
  , vpPrevPosition :: !PhysicsVec2
  , vpMass        :: !PositiveFloat
  , vpPinned      :: !Bool
  } deriving stock (Eq, Show, Generic)

data VerletConstraint = VerletConstraint
  { vcId          :: !NonEmptyString
  , vcParticleAId :: !NonEmptyString
  , vcParticleBId :: !NonEmptyString
  , vcRestLength  :: !PositiveFloat
  , vcStiffness   :: !UnitFloat
  , vcTearable    :: !Bool
  , vcTornType    :: !(Maybe ConstraintTornType)
  } deriving stock (Eq, Show, Generic)

data SoftBodyConfig = SoftBodyConfig
  { sbcId          :: !NonEmptyString
  , sbcParticles   :: !(Vector VerletParticle)
  , sbcConstraints :: !(Vector VerletConstraint)
  , sbcIterations  :: !Int
  , sbcGravity     :: !PhysicsVec2
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Space Config
--------------------------------------------------------------------------------

data PhysicsSpaceConfig = PhysicsSpaceConfig
  { pscGravity           :: !PhysicsVec2
  , pscIterations        :: !Int
  , pscSubSteps          :: !Int
  , pscSleepTimeThreshold :: !NonNegativeFloat
  , pscSleepIdleThreshold :: !NonNegativeFloat
  , pscCollisionBias     :: !NonNegativeFloat
  , pscContactPersistence :: !Int
  } deriving stock (Eq, Show, Generic)

data PhysicsLayerData = PhysicsLayerData
  { pldSpaceConfig :: !PhysicsSpaceConfig
  , pldBodies      :: !(Vector RigidBodyConfig)
  , pldForces      :: !(Vector ForceFieldBase)
  , pldEnabled     :: !Bool
  } deriving stock (Eq, Show, Generic)
