{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}

{-|
Module      : Lattice.Transform
Description : Layer transforms and motion blur
Copyright   : (c) Lattice, 2026
License     : MIT

Source: leancomfy/lean/Lattice/Transform.lean
-}

module Lattice.Transform
  ( -- * Vectors
    Vec2(..)
  , mkVec2
  , vec2Zero
  , Vec3(..)
  , mkVec3
  , vec3Zero
    -- * Separate Dimensions
  , SeparateDimensions(..)
  , defaultSeparateDimensions
    -- * Layer Transform
  , LayerTransform(..)
    -- * Motion Blur
  , MotionBlurType(..)
  , RadialMode(..)
  , LayerMotionBlurSettings(..)
    -- * Material Options
  , CastsShadows(..)
  , LayerMaterialOptions(..)
    -- * Auto-Orient
  , AutoOrientMode(..)
    -- * Follow Path
  , LoopMode(..)
  , FollowPathConstraint(..)
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)
import Lattice.Primitives hiding (Vec2(..), Vec3(..))

--------------------------------------------------------------------------------
-- Vectors
--------------------------------------------------------------------------------

data Vec2 = Vec2
  { v2x :: !FiniteFloat
  , v2y :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

mkVec2 :: Double -> Double -> Maybe Vec2
mkVec2 x y = Vec2 <$> mkFiniteFloat x <*> mkFiniteFloat y

-- | Zero vector. Uses Num instance for FiniteFloat (safe for literals).
vec2Zero :: Vec2
vec2Zero = Vec2 0 0

data Vec3 = Vec3
  { v3x :: !FiniteFloat
  , v3y :: !FiniteFloat
  , v3z :: !FiniteFloat
  } deriving stock (Eq, Show, Generic)

mkVec3 :: Double -> Double -> Double -> Maybe Vec3
mkVec3 x y z = Vec3 <$> mkFiniteFloat x <*> mkFiniteFloat y <*> mkFiniteFloat z

-- | Zero vector. Uses Num instance for FiniteFloat (safe for literals).
vec3Zero :: Vec3
vec3Zero = Vec3 0 0 0

--------------------------------------------------------------------------------
-- Separate Dimensions
--------------------------------------------------------------------------------

data SeparateDimensions = SeparateDimensions
  { sdPosition :: !Bool
  , sdScale    :: !Bool
  } deriving stock (Eq, Show, Generic)

defaultSeparateDimensions :: SeparateDimensions
defaultSeparateDimensions = SeparateDimensions False False

--------------------------------------------------------------------------------
-- Layer Transform
--------------------------------------------------------------------------------

data LayerTransform = LayerTransform
  { ltPositionPropertyId    :: !NonEmptyString
  , ltPositionXPropertyId   :: !(Maybe NonEmptyString)
  , ltPositionYPropertyId   :: !(Maybe NonEmptyString)
  , ltPositionZPropertyId   :: !(Maybe NonEmptyString)
  , ltOriginPropertyId      :: !NonEmptyString
  , ltScalePropertyId       :: !NonEmptyString
  , ltScaleXPropertyId      :: !(Maybe NonEmptyString)
  , ltScaleYPropertyId      :: !(Maybe NonEmptyString)
  , ltScaleZPropertyId      :: !(Maybe NonEmptyString)
  , ltRotationPropertyId    :: !NonEmptyString
  , ltOrientationPropertyId :: !(Maybe NonEmptyString)
  , ltRotationXPropertyId   :: !(Maybe NonEmptyString)
  , ltRotationYPropertyId   :: !(Maybe NonEmptyString)
  , ltRotationZPropertyId   :: !(Maybe NonEmptyString)
  , ltSeparateDimensions    :: !(Maybe SeparateDimensions)
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Motion Blur
--------------------------------------------------------------------------------

data MotionBlurType
  = MBTStandard
  | MBTPixel
  | MBTDirectional
  | MBTRadial
  | MBTVector
  | MBTAdaptive
  deriving stock (Eq, Show, Generic)

data RadialMode = RMSpin | RMZoom
  deriving stock (Eq, Show, Generic)

data LayerMotionBlurSettings = LayerMotionBlurSettings
  { lmbBlurType        :: !MotionBlurType
  , lmbShutterAngle    :: !FiniteFloat  -- 0-720
  , lmbShutterPhase    :: !FiniteFloat  -- -180 to 180
  , lmbSamplesPerFrame :: !Int          -- 2-64
  , lmbDirection       :: !(Maybe FiniteFloat)
  , lmbBlurLength      :: !(Maybe FiniteFloat)
  , lmbRadialMode      :: !(Maybe RadialMode)
  , lmbRadialCenterX   :: !(Maybe UnitFloat)
  , lmbRadialCenterY   :: !(Maybe UnitFloat)
  , lmbRadialAmount    :: !(Maybe FiniteFloat)  -- 0-100
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Material Options
--------------------------------------------------------------------------------

data CastsShadows = CSOff | CSOn | CSOnly
  deriving stock (Eq, Show, Generic)

data LayerMaterialOptions = LayerMaterialOptions
  { lmoCastsShadows      :: !CastsShadows
  , lmoLightTransmission :: !Percentage  -- 0-100
  , lmoAcceptsShadows    :: !Bool
  , lmoAcceptsLights     :: !Bool
  , lmoAmbient           :: !Percentage
  , lmoDiffuse           :: !Percentage
  , lmoSpecularIntensity :: !Percentage
  , lmoSpecularShininess :: !Percentage
  , lmoMetal             :: !Percentage
  } deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Auto-Orient
--------------------------------------------------------------------------------

data AutoOrientMode
  = AOMOff
  | AOMToCamera
  | AOMAlongPath
  | AOMToPointOfInterest
  deriving stock (Eq, Show, Generic)

--------------------------------------------------------------------------------
-- Follow Path
--------------------------------------------------------------------------------

data LoopMode = LMClamp | LMLoop | LMPingpong
  deriving stock (Eq, Show, Generic)

data FollowPathConstraint = FollowPathConstraint
  { fpcEnabled                  :: !Bool
  , fpcPathLayerId              :: !Text  -- Empty = no target
  , fpcProgressPropertyId       :: !NonEmptyString
  , fpcOffsetPropertyId         :: !NonEmptyString
  , fpcTangentOffset            :: !UnitFloat
  , fpcAutoOrient               :: !Bool
  , fpcRotationOffsetPropertyId :: !NonEmptyString
  , fpcBankingPropertyId        :: !NonEmptyString
  , fpcLoopMode                 :: !LoopMode
  } deriving stock (Eq, Show, Generic)
