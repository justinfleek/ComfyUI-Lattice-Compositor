-- | Lattice.Entities - Layer 5: Domain Entities with proofs
-- |
-- | Core domain entity types. Each entity implements Identifiable (id),
-- | Timestamped (createdAt, updatedAt), Named (name).
-- |
-- | Source: lattice-core/lean/Lattice/Entities.lean (split for 500 line limit)

module Lattice.Entities
  ( Identifiable
  , Timestamped
  , Named
  , Vec2
  , mkVec2
  , Vec3
  , mkVec3
  , CompositionSettings
  , RenderSettings
  , BezierHandle
  , ControlMode(..)
  , Keyframe
  , PropertyValueType(..)
  , PropertyExpression
  , AnimatableProperty
  , LayerTransform
  , LayerMask
  , EffectParameter
  , EffectInstance
  , AssetType(..)
  , AssetSource(..)
  , AssetMetadata
  , AssetReference
  , CameraControlType(..)
  , AutoOrientMode(..)
  , DepthOfField
  , CameraKeyframe
  , ForceType(..)
  , BodyType(..)
  , JointType(..)
  , PhysicsMaterial
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives
import Lattice.Enums

-- ────────────────────────────────────────────────────────────────────────────
-- Common Traits
-- ────────────────────────────────────────────────────────────────────────────

type Identifiable = { id :: NonEmptyString }

type Timestamped =
  { createdAt :: NonNegativeFloat
  , updatedAt :: NonNegativeFloat
  }

type Named = { name :: NonEmptyString }

-- ────────────────────────────────────────────────────────────────────────────
-- Vectors
-- ────────────────────────────────────────────────────────────────────────────

type Vec2 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  }

mkVec2 :: Number -> Number -> Maybe Vec2
mkVec2 x y = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  pure { x: fx, y: fy }

type Vec3 =
  { x :: FiniteFloat
  , y :: FiniteFloat
  , z :: FiniteFloat
  }

mkVec3 :: Number -> Number -> Number -> Maybe Vec3
mkVec3 x y z = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  fz <- mkFiniteFloat z
  pure { x: fx, y: fy, z: fz }

-- ────────────────────────────────────────────────────────────────────────────
-- Composition
-- ────────────────────────────────────────────────────────────────────────────

type CompositionSettings =
  { width           :: PositiveInt
  , height          :: PositiveInt
  , fps             :: PositiveFloat
  , duration        :: NonNegativeFloat
  , backgroundColor :: NonEmptyString
  }

type RenderSettings =
  { quality              :: QualityMode
  , motionBlur           :: Boolean
  , motionBlurSamples    :: PositiveInt
  , motionBlurShutterAngle :: UnitFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Keyframe
-- ────────────────────────────────────────────────────────────────────────────

type BezierHandle =
  { frame   :: FiniteFloat
  , value   :: FiniteFloat
  , enabled :: Boolean
  }

data ControlMode = CMSymmetric | CMSmooth | CMCorner

derive instance Eq ControlMode
derive instance Generic ControlMode _
instance Show ControlMode where show = genericShow

type Keyframe =
  { id            :: NonEmptyString
  , frame         :: FrameNumber
  , value         :: String  -- JSON-encoded
  , interpolation :: InterpolationType
  , inHandle      :: BezierHandle
  , outHandle     :: BezierHandle
  , controlMode   :: ControlMode
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Property
-- ────────────────────────────────────────────────────────────────────────────

data PropertyValueType
  = PVTNumber | PVTPosition | PVTColor | PVTEnum | PVTVector3

derive instance Eq PropertyValueType
derive instance Generic PropertyValueType _
instance Show PropertyValueType where show = genericShow

type PropertyExpression =
  { enabled        :: Boolean
  , expressionType :: ExpressionType
  , name           :: NonEmptyString
  , params         :: String  -- JSON-encoded
  }

type AnimatableProperty =
  { id           :: NonEmptyString
  , name         :: NonEmptyString
  , propertyType :: PropertyValueType
  , value        :: String  -- JSON-encoded
  , animated     :: Boolean
  , keyframes    :: Array NonEmptyString  -- Keyframe IDs
  , group        :: Maybe NonEmptyString
  , expression   :: Maybe PropertyExpression
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Transform
-- ────────────────────────────────────────────────────────────────────────────

type LayerTransform =
  { position :: Vec2
  , rotation :: FiniteFloat
  , scale    :: Vec2
  , anchor   :: Vec2
  , opacity  :: UnitFloat
  }

type LayerMask =
  { id       :: NonEmptyString
  , path     :: String  -- JSON-encoded path
  , mode     :: MaskMode
  , inverted :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Effect
-- ────────────────────────────────────────────────────────────────────────────

type EffectParameter =
  { id            :: NonEmptyString
  , name          :: NonEmptyString
  , parameterType :: PropertyValueType
  , value         :: String  -- JSON-encoded
  }

type EffectInstance =
  { id         :: NonEmptyString
  , createdAt  :: NonNegativeFloat
  , updatedAt  :: NonNegativeFloat
  , effectType :: EffectType
  , enabled    :: Boolean
  , parameters :: Array NonEmptyString
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Asset
-- ────────────────────────────────────────────────────────────────────────────

data AssetType
  = ATDepthMap | ATImage | ATVideo | ATAudio | ATModel
  | ATPointcloud | ATTexture | ATMaterial | ATHDRI | ATSVG
  | ATSprite | ATSpritesheet | ATLUT

derive instance Eq AssetType
derive instance Generic AssetType _
instance Show AssetType where show = genericShow

data AssetSource = ASComfyuiNode | ASFile | ASGenerated | ASURL

derive instance Eq AssetSource
derive instance Generic AssetSource _
instance Show AssetSource where show = genericShow

type AssetMetadata =
  { width            :: PositiveInt
  , height           :: PositiveInt
  , filename         :: Maybe NonEmptyString
  , frameCount       :: Maybe FrameNumber
  , duration         :: Maybe NonNegativeFloat
  , fps              :: Maybe PositiveFloat
  , hasAudio         :: Maybe Boolean
  , audioChannels    :: Maybe PositiveInt
  , sampleRate       :: Maybe PositiveInt
  , modelFormat      :: Maybe NonEmptyString
  , modelMeshCount   :: Maybe FrameNumber
  , modelVertexCount :: Maybe FrameNumber
  , pointCloudFormat :: Maybe NonEmptyString
  , pointCount       :: Maybe FrameNumber
  }

type AssetReference =
  { id        :: NonEmptyString
  , assetType :: AssetType
  , source    :: AssetSource
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Camera
-- ────────────────────────────────────────────────────────────────────────────

data CameraControlType = CCTOneNode | CCTTwoNode

derive instance Eq CameraControlType
derive instance Generic CameraControlType _
instance Show CameraControlType where show = genericShow

data AutoOrientMode = AOMOff | AOMOrientAlongPath | AOMOrientTowardsPoi

derive instance Eq AutoOrientMode
derive instance Generic AutoOrientMode _
instance Show AutoOrientMode where show = genericShow

type DepthOfField =
  { enabled       :: Boolean
  , focusDistance :: FiniteFloat
  , aperture      :: FiniteFloat
  , fStop         :: FiniteFloat
  , blurLevel     :: UnitFloat
  , lockToZoom    :: Boolean
  }

type CameraKeyframe =
  { frame           :: FrameNumber
  , position        :: Maybe Vec3
  , pointOfInterest :: Maybe Vec3
  , orientation     :: Maybe Vec3
  , xRotation       :: Maybe FiniteFloat
  , yRotation       :: Maybe FiniteFloat
  , zRotation       :: Maybe FiniteFloat
  , zoom            :: Maybe PositiveFloat
  , focalLength     :: Maybe PositiveFloat
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Force
-- ────────────────────────────────────────────────────────────────────────────

data ForceType
  = FTGravity | FTWind | FTAttraction | FTExplosion
  | FTBuoyancy | FTVortex | FTDrag

derive instance Eq ForceType
derive instance Generic ForceType _
instance Show ForceType where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Physics
-- ────────────────────────────────────────────────────────────────────────────

data BodyType = BTStatic | BTDynamic | BTKinematic | BTDormant

derive instance Eq BodyType
derive instance Generic BodyType _
instance Show BodyType where show = genericShow

data JointType
  = JTPivot | JTSpring | JTDistance | JTPiston
  | JTWheel | JTWeld | JTBlob | JTRope

derive instance Eq JointType
derive instance Generic JointType _
instance Show JointType where show = genericShow

type PhysicsMaterial =
  { restitution :: UnitFloat
  , friction    :: UnitFloat
  }
