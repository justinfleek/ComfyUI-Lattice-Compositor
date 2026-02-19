-- | Lattice.Transform - Layer transforms and motion blur
-- |
-- | Source: lattice-core/lean/Lattice/Transform.lean

module Lattice.Transform
  ( Vec2
  , mkVec2
  , vec2Zero
  , Vec3
  , mkVec3
  , vec3Zero
  , SeparateDimensions
  , defaultSeparateDimensions
  , LayerTransform
  , MotionBlurType(..)
  , RadialMode(..)
  , LayerMotionBlurSettings
  , CastsShadows(..)
  , LayerMaterialOptions
  , AutoOrientMode(..)
  , LoopMode(..)
  , FollowPathConstraint
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Lattice.Primitives

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

vec2Zero :: Vec2
vec2Zero = case mkVec2 0.0 0.0 of
  Just v  -> v
  Nothing -> { x: safeFinite 0.0, y: safeFinite 0.0 }
  where
    safeFinite :: Number -> FiniteFloat
    safeFinite n = case mkFiniteFloat n of
      Just f -> f
      Nothing -> safeFinite 0.0

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

vec3Zero :: Vec3
vec3Zero = case mkVec3 0.0 0.0 0.0 of
  Just v  -> v
  Nothing -> { x: safeFinite 0.0, y: safeFinite 0.0, z: safeFinite 0.0 }
  where
    safeFinite :: Number -> FiniteFloat
    safeFinite n = case mkFiniteFloat n of
      Just f -> f
      Nothing -> safeFinite 0.0

-- ────────────────────────────────────────────────────────────────────────────
-- Separate Dimensions
-- ────────────────────────────────────────────────────────────────────────────

type SeparateDimensions =
  { position :: Boolean
  , scale    :: Boolean
  }

defaultSeparateDimensions :: SeparateDimensions
defaultSeparateDimensions = { position: false, scale: false }

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Transform
-- ────────────────────────────────────────────────────────────────────────────

type LayerTransform =
  { positionPropertyId    :: NonEmptyString
  , positionXPropertyId   :: Maybe NonEmptyString
  , positionYPropertyId   :: Maybe NonEmptyString
  , positionZPropertyId   :: Maybe NonEmptyString
  , originPropertyId      :: NonEmptyString
  , scalePropertyId       :: NonEmptyString
  , scaleXPropertyId      :: Maybe NonEmptyString
  , scaleYPropertyId      :: Maybe NonEmptyString
  , scaleZPropertyId      :: Maybe NonEmptyString
  , rotationPropertyId    :: NonEmptyString
  , orientationPropertyId :: Maybe NonEmptyString
  , rotationXPropertyId   :: Maybe NonEmptyString
  , rotationYPropertyId   :: Maybe NonEmptyString
  , rotationZPropertyId   :: Maybe NonEmptyString
  , separateDimensions    :: Maybe SeparateDimensions
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Blur
-- ────────────────────────────────────────────────────────────────────────────

data MotionBlurType
  = MBTStandard
  | MBTPixel
  | MBTDirectional
  | MBTRadial
  | MBTVector
  | MBTAdaptive

derive instance Eq MotionBlurType
derive instance Generic MotionBlurType _
instance Show MotionBlurType where show = genericShow

data RadialMode = RMSpin | RMZoom

derive instance Eq RadialMode
derive instance Generic RadialMode _
instance Show RadialMode where show = genericShow

type LayerMotionBlurSettings =
  { blurType        :: MotionBlurType
  , shutterAngle    :: FiniteFloat  -- 0-720
  , shutterPhase    :: FiniteFloat  -- -180 to 180
  , samplesPerFrame :: Int          -- 2-64
  , direction       :: Maybe FiniteFloat
  , blurLength      :: Maybe FiniteFloat
  , radialMode      :: Maybe RadialMode
  , radialCenterX   :: Maybe UnitFloat
  , radialCenterY   :: Maybe UnitFloat
  , radialAmount    :: Maybe FiniteFloat  -- 0-100
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Material Options
-- ────────────────────────────────────────────────────────────────────────────

data CastsShadows = CSOff | CSOn | CSOnly

derive instance Eq CastsShadows
derive instance Generic CastsShadows _
instance Show CastsShadows where show = genericShow

type LayerMaterialOptions =
  { castsShadows      :: CastsShadows
  , lightTransmission :: Percentage  -- 0-100
  , acceptsShadows    :: Boolean
  , acceptsLights     :: Boolean
  , ambient           :: Percentage
  , diffuse           :: Percentage
  , specularIntensity :: Percentage
  , specularShininess :: Percentage
  , metal             :: Percentage
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Auto-Orient
-- ────────────────────────────────────────────────────────────────────────────

data AutoOrientMode
  = AOMOff
  | AOMToCamera
  | AOMAlongPath
  | AOMToPointOfInterest

derive instance Eq AutoOrientMode
derive instance Generic AutoOrientMode _
instance Show AutoOrientMode where show = genericShow

-- ────────────────────────────────────────────────────────────────────────────
-- Follow Path
-- ────────────────────────────────────────────────────────────────────────────

data LoopMode = LMClamp | LMLoop | LMPingpong

derive instance Eq LoopMode
derive instance Generic LoopMode _
instance Show LoopMode where show = genericShow

type FollowPathConstraint =
  { enabled                  :: Boolean
  , pathLayerId              :: String  -- Empty = no target
  , progressPropertyId       :: NonEmptyString
  , offsetPropertyId         :: NonEmptyString
  , tangentOffset            :: UnitFloat
  , autoOrient               :: Boolean
  , rotationOffsetPropertyId :: NonEmptyString
  , bankingPropertyId        :: NonEmptyString
  , loopMode                 :: LoopMode
  }
