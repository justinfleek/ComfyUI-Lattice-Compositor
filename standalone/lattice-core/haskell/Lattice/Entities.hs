{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Entities
Description : Layer 5 - Domain Entities with proofs
Copyright   : (c) Lattice, 2026
License     : MIT

Core domain entity types. Each entity implements Identifiable (id),
Timestamped (createdAt, updatedAt), Named (name).

Source: lattice-core/lean/Lattice/Entities.lean (split for 500 line limit)
-}

module Lattice.Entities
  ( -- * Common Traits
    Identifiable(..)
  , Timestamped(..)
  , Named(..)
    -- * Vectors
  , Vec2(..)
  , mkVec2
  , Vec3(..)
  , mkVec3
    -- * Composition
  , CompositionSettings(..)
  , RenderSettings(..)
    -- * Keyframe
  , BezierHandle(..)
  , ControlMode(..)
  , Keyframe(..)
    -- * Property
  , PropertyValueType(..)
  , PropertyExpression(..)
  , AnimatableProperty(..)
    -- * Layer Transform
  , LayerTransform(..)
  , LayerMask(..)
    -- * Effect
  , EffectParameter(..)
  , EffectInstance(..)
    -- * Asset
  , AssetType(..)
  , AssetSource(..)
  , AssetMetadata(..)
  , AssetReference(..)
    -- * Camera
  , CameraControlType(..)
  , AutoOrientMode(..)
  , DepthOfField(..)
  , CameraKeyframe(..)
    -- * Force
  , ForceType(..)
    -- * Physics
  , BodyType(..)
  , JointType(..)
  , PhysicsMaterial(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Data.Vector (Vector)
import Lattice.Primitives hiding (Vec2(..), Vec3(..))
import Lattice.Enums

--------------------------------------------------------------------------------
-- Common Traits
--------------------------------------------------------------------------------

newtype Identifiable = Identifiable
  { idValue :: NonEmptyString
  } deriving stock (Eq, Show, Generic)

data Timestamped = Timestamped
  { createdAt :: !NonNegativeFloat
  , updatedAt :: !NonNegativeFloat
  } deriving stock (Eq, Show, Generic)

newtype Named = Named
  { nameValue :: NonEmptyString
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Vectors
--------------------------------------------------------------------------------

data Vec2 = Vec2
  { v2x :: !FiniteFloat
  , v2y :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

mkVec2 :: Double -> Double -> Maybe Vec2
mkVec2 x y = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  pure $ Vec2 fx fy

data Vec3 = Vec3
  { v3x :: !FiniteFloat
  , v3y :: !FiniteFloat
  , v3z :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

mkVec3 :: Double -> Double -> Double -> Maybe Vec3
mkVec3 x y z = do
  fx <- mkFiniteFloat x
  fy <- mkFiniteFloat y
  fz <- mkFiniteFloat z
  pure $ Vec3 fx fy fz

--------------------------------------------------------------------------------
-- Composition
--------------------------------------------------------------------------------

data CompositionSettings = CompositionSettings
  { csWidth           :: !PositiveInt
  , csHeight          :: !PositiveInt
  , csFps             :: !PositiveFloat
  , csDuration        :: !NonNegativeFloat
  , csBackgroundColor :: !NonEmptyString
  } deriving stock (Eq, Show, Generic)

data RenderSettings = RenderSettings
  { rsQuality              :: !QualityMode
  , rsMotionBlur           :: !Bool
  , rsMotionBlurSamples    :: !PositiveInt
  , rsMotionBlurShutterAngle :: !UnitFloat
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Keyframe
--------------------------------------------------------------------------------

data BezierHandle = BezierHandle
  { bhFrame   :: !FiniteFloat
  , bhValue   :: !FiniteFloat
  , bhEnabled :: !Bool
  } deriving stock (Eq, Show, Generic)

data ControlMode = CMSymmetric | CMSmooth | CMCorner
  deriving stock (Eq, Show, Generic)

data Keyframe = Keyframe
  { kfId            :: !NonEmptyString
  , kfFrame         :: !FrameNumber
  , kfValue         :: !Text  -- JSON-encoded
  , kfInterpolation :: !InterpolationType
  , kfInHandle      :: !BezierHandle
  , kfOutHandle     :: !BezierHandle
  , kfControlMode   :: !ControlMode
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Property
--------------------------------------------------------------------------------

data PropertyValueType
  = PVTNumber | PVTPosition | PVTColor | PVTEnum | PVTVector3
  deriving stock (Eq, Show, Generic)

data PropertyExpression = PropertyExpression
  { peEnabled        :: !Bool
  , peExpressionType :: !ExpressionType
  , peName           :: !NonEmptyString
  , peParams         :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data AnimatableProperty = AnimatableProperty
  { apId           :: !NonEmptyString
  , apName         :: !NonEmptyString
  , apPropertyType :: !PropertyValueType
  , apValue        :: !Text  -- JSON-encoded
  , apAnimated     :: !Bool
  , apKeyframes    :: !(Vector NonEmptyString)  -- Keyframe IDs
  , apGroup        :: !(Maybe NonEmptyString)
  , apExpression   :: !(Maybe PropertyExpression)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Layer Transform
--------------------------------------------------------------------------------

data LayerTransform = LayerTransform
  { ltPosition :: !Vec2
  , ltRotation :: !FiniteFloat
  , ltScale    :: !Vec2
  , ltAnchor   :: !Vec2
  , ltOpacity  :: !UnitFloat
  } deriving stock (Eq, Show, Generic)

data LayerMask = LayerMask
  { lmId       :: !NonEmptyString
  , lmPath     :: !Text  -- JSON-encoded path
  , lmMode     :: !MaskMode
  , lmInverted :: !Bool
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Effect
--------------------------------------------------------------------------------

data EffectParameter = EffectParameter
  { epId            :: !NonEmptyString
  , epName          :: !NonEmptyString
  , epParameterType :: !PropertyValueType
  , epValue         :: !Text  -- JSON-encoded
  } deriving stock (Eq, Show, Generic)

data EffectInstance = EffectInstance
  { eiId         :: !NonEmptyString
  , eiCreatedAt  :: !NonNegativeFloat
  , eiUpdatedAt  :: !NonNegativeFloat
  , eiEffectType :: !EffectType
  , eiEnabled    :: !Bool
  , eiParameters :: !(Vector NonEmptyString)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Asset
--------------------------------------------------------------------------------

data AssetType
  = ATDepthMap | ATImage | ATVideo | ATAudio | ATModel
  | ATPointcloud | ATTexture | ATMaterial | ATHDRI | ATSVG
  | ATSprite | ATSpritesheet | ATLUT
  deriving stock (Eq, Show, Generic)

data AssetSource = ASComfyuiNode | ASFile | ASGenerated | ASURL
  deriving stock (Eq, Show, Generic)

data AssetMetadata = AssetMetadata
  { amWidth            :: !PositiveInt
  , amHeight           :: !PositiveInt
  , amFilename         :: !(Maybe NonEmptyString)
  , amFrameCount       :: !(Maybe FrameNumber)
  , amDuration         :: !(Maybe NonNegativeFloat)
  , amFps              :: !(Maybe PositiveFloat)
  , amHasAudio         :: !(Maybe Bool)
  , amAudioChannels    :: !(Maybe PositiveInt)
  , amSampleRate       :: !(Maybe PositiveInt)
  , amModelFormat      :: !(Maybe NonEmptyString)
  , amModelMeshCount   :: !(Maybe FrameNumber)
  , amModelVertexCount :: !(Maybe FrameNumber)
  , amPointCloudFormat :: !(Maybe NonEmptyString)
  , amPointCount       :: !(Maybe FrameNumber)
  } deriving stock (Eq, Show, Generic)

data AssetReference = AssetReference
  { arId        :: !NonEmptyString
  , arAssetType :: !AssetType
  , arSource    :: !AssetSource
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Camera
--------------------------------------------------------------------------------

data CameraControlType = CCTOneNode | CCTTwoNode
  deriving stock (Eq, Show, Generic)

data AutoOrientMode = AOMOff | AOMOrientAlongPath | AOMOrientTowardsPoi
  deriving stock (Eq, Show, Generic)

data DepthOfField = DepthOfField
  { dofEnabled       :: !Bool
  , dofFocusDistance :: !FiniteFloat
  , dofAperture      :: !FiniteFloat
  , dofFStop         :: !FiniteFloat
  , dofBlurLevel     :: !UnitFloat
  , dofLockToZoom    :: !Bool
  } deriving stock (Eq, Show, Generic)

data CameraKeyframe = CameraKeyframe
  { ckFrame           :: !FrameNumber
  , ckPosition        :: !(Maybe Vec3)
  , ckPointOfInterest :: !(Maybe Vec3)
  , ckOrientation     :: !(Maybe Vec3)
  , ckXRotation       :: !(Maybe FiniteFloat)
  , ckYRotation       :: !(Maybe FiniteFloat)
  , ckZRotation       :: !(Maybe FiniteFloat)
  , ckZoom            :: !(Maybe PositiveFloat)
  , ckFocalLength     :: !(Maybe PositiveFloat)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Force
--------------------------------------------------------------------------------

data ForceType
  = FTGravity | FTWind | FTAttraction | FTExplosion
  | FTBuoyancy | FTVortex | FTDrag
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Physics
--------------------------------------------------------------------------------

data BodyType = BTStatic | BTDynamic | BTKinematic | BTDormant
  deriving stock (Eq, Show, Generic)

data JointType
  = JTPivot | JTSpring | JTDistance | JTPiston
  | JTWheel | JTWeld | JTBlob | JTRope
  deriving stock (Eq, Show, Generic)

data PhysicsMaterial = PhysicsMaterial
  { pmRestitution :: !UnitFloat
  , pmFriction    :: !UnitFloat
  } deriving stock (Eq, Show, Generic)
