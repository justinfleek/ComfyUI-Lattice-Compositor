-- | Lattice.Physics - Physics system types
-- |
-- | Source: lattice-core/lean/Lattice/Physics.lean
-- | Consolidated from Physics/* submodules.

module Lattice.Physics
  ( BodyType(..)
  , JointType(..)
  , ForceType(..)
  , ShapeType(..)
  , CollisionResponse(..)
  , ForceFalloff(..)
  , ConstraintTornType(..)
  , PhysicsVec2
  , PhysicsMaterial
  , CollisionShape
  , CollisionFilter
  , RigidBodyConfig
  , RigidBodyState
  , JointConfigBase
  , MotorSettings
  , AngleLimits
  , TranslationLimits
  , ForceFieldBase
  , GravityForce
  , WindForce
  , AttractionForce
  , VerletParticle
  , VerletConstraint
  , SoftBodyConfig
  , PhysicsSpaceConfig
  , PhysicsLayerData
  ) where

import Prelude
import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

-- ────────────────────────────────────────────────────────────────────────────
-- Enumerations
-- ────────────────────────────────────────────────────────────────────────────

data BodyType
  = BTStatic | BTDynamic | BTKinematic | BTDormant | BTAematic | BTDead

derive instance Eq BodyType
derive instance Generic BodyType _
instance Show BodyType where show = genericShow

data JointType
  = JTPivot | JTSpring | JTDistance | JTPiston | JTWheel | JTWeld | JTBlob | JTRope

derive instance Eq JointType
derive instance Generic JointType _
instance Show JointType where show = genericShow

data ForceType
  = FTGravity | FTWind | FTAttraction | FTExplosion | FTBuoyancy | FTVortex | FTDrag

derive instance Eq ForceType
derive instance Generic ForceType _
instance Show ForceType where show = genericShow

data ShapeType
  = STCircle | STBox | STPolygon | STCapsule | STConvex | STCompound

derive instance Eq ShapeType
derive instance Generic ShapeType _
instance Show ShapeType where show = genericShow

data CollisionResponse = CRCollide | CRSensor | CRNone

derive instance Eq CollisionResponse
derive instance Generic CollisionResponse _
instance Show CollisionResponse where show = genericShow

data ForceFalloff = FFLinear | FFQuadratic | FFConstant

derive instance Eq ForceFalloff
derive instance Generic ForceFalloff _
instance Show ForceFalloff where show = genericShow

data ConstraintTornType = CTTStructural | CTTShear | CTTBend

derive instance Eq ConstraintTornType
derive instance Generic ConstraintTornType _
instance Show ConstraintTornType where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Core Types
-- ────────────────────────────────────────────────────────────────────────────

type PhysicsVec2 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

type PhysicsMaterial =
  { friction    :: NonNegativeFloat
  , restitution :: UnitFloat
  , density     :: PositiveFloat
  }

type CollisionShape =
  { shapeType :: ShapeType
  , radius    :: Maybe PositiveFloat
  , width     :: Maybe PositiveFloat
  , height    :: Maybe PositiveFloat
  , vertices  :: Maybe (Array PhysicsVec2)
  , offset    :: PhysicsVec2
  , rotation  :: FiniteFloat
  }

type CollisionFilter =
  { category :: Int
  , mask     :: Int
  , group    :: Int
  }

type RigidBodyConfig =
  { id               :: NonEmptyString
  , bodyType         :: BodyType
  , mass             :: PositiveFloat
  , moment           :: Maybe PositiveFloat
  , shape            :: CollisionShape
  , material         :: PhysicsMaterial
  , collisionFilter  :: CollisionFilter
  , collisionResponse :: CollisionResponse
  , linearDamping    :: NonNegativeFloat
  , angularDamping   :: NonNegativeFloat
  , gravityScale     :: FiniteFloat
  , fixedRotation    :: Boolean
  , initialPosition  :: PhysicsVec2
  , initialVelocity  :: PhysicsVec2
  , initialAngle     :: FiniteFloat
  , initialAngularVelocity :: FiniteFloat
  }

type RigidBodyState =
  { id              :: NonEmptyString
  , position        :: PhysicsVec2
  , velocity        :: PhysicsVec2
  , angle           :: FiniteFloat
  , angularVelocity :: FiniteFloat
  , asleep          :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Joint Types
-- ────────────────────────────────────────────────────────────────────────────

type JointConfigBase =
  { id          :: NonEmptyString
  , jointType   :: JointType
  , bodyAId     :: NonEmptyString
  , bodyBId     :: Maybe NonEmptyString
  , anchorA     :: PhysicsVec2
  , anchorB     :: PhysicsVec2
  , collideConnected :: Boolean
  }

type MotorSettings =
  { enabled  :: Boolean
  , speed    :: FiniteFloat
  , maxForce :: NonNegativeFloat
  }

type AngleLimits =
  { enabled :: Boolean
  , min     :: FiniteFloat
  , max     :: FiniteFloat
  }

type TranslationLimits =
  { enabled :: Boolean
  , min     :: FiniteFloat
  , max     :: FiniteFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Force Types
-- ────────────────────────────────────────────────────────────────────────────

type ForceFieldBase =
  { id       :: NonEmptyString
  , forceType :: ForceType
  , enabled  :: Boolean
  , strength :: FiniteFloat
  , falloff  :: ForceFalloff
  , radius   :: Maybe PositiveFloat
  }

type GravityForce =
  { base      :: ForceFieldBase
  , direction :: PhysicsVec2
  }

type WindForce =
  { base        :: ForceFieldBase
  , direction   :: PhysicsVec2
  , turbulence  :: NonNegativeFloat
  , gustiness   :: NonNegativeFloat
  }

type AttractionForce =
  { base     :: ForceFieldBase
  , position :: PhysicsVec2
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Soft Body
-- ────────────────────────────────────────────────────────────────────────────

type VerletParticle =
  { id          :: NonEmptyString
  , position    :: PhysicsVec2
  , prevPosition :: PhysicsVec2
  , mass        :: PositiveFloat
  , pinned      :: Boolean
  }

type VerletConstraint =
  { id          :: NonEmptyString
  , particleAId :: NonEmptyString
  , particleBId :: NonEmptyString
  , restLength  :: PositiveFloat
  , stiffness   :: UnitFloat
  , tearable    :: Boolean
  , tornType    :: Maybe ConstraintTornType
  }

type SoftBodyConfig =
  { id          :: NonEmptyString
  , particles   :: Array VerletParticle
  , constraints :: Array VerletConstraint
  , iterations  :: Int
  , gravity     :: PhysicsVec2
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Space Config
-- ────────────────────────────────────────────────────────────────────────────

type PhysicsSpaceConfig =
  { gravity           :: PhysicsVec2
  , iterations        :: Int
  , subSteps          :: Int
  , sleepTimeThreshold :: NonNegativeFloat
  , sleepIdleThreshold :: NonNegativeFloat
  , collisionBias     :: NonNegativeFloat
  , contactPersistence :: Int
  }

type PhysicsLayerData =
  { spaceConfig :: PhysicsSpaceConfig
  , bodies      :: Array RigidBodyConfig
  , forces      :: Array ForceFieldBase
  , enabled     :: Boolean
  }
