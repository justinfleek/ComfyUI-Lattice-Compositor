-- |
-- Module      : Lattice.Types.Transform
-- Description : Layer transforms and motion blur
-- 
-- Migrated from ui/src/types/transform.ts
-- Uses AnimatableProperty for all animatable transform properties
--

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Transform
  ( LayerTransform(..)
  , SeparateDimensions(..)
  , MotionBlurType(..)
  , createDefaultTransform
  -- Re-exports
  , Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  ) where

import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  , withObject
  , withText
  , object
  , (.=)
  , (.:)
  , (.:?)
  )
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Generics (Generic)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , PropertyType(..)
  , createAnimatableProperty
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  )

-- ============================================================
-- LAYER TRANSFORM
-- ============================================================

-- | Layer transform with animatable properties
-- Position and origin can be 2D or 3D (z optional)
-- Scale always has z (defaults to 100%)
data LayerTransform = LayerTransform
  { transformPosition :: AnimatableProperty Position2DOr3D  -- Position {x, y, z?}
  , transformPositionX :: Maybe (AnimatableProperty Double)  -- Separate X property (when separateDimensions.position is true)
  , transformPositionY :: Maybe (AnimatableProperty Double)  -- Separate Y property
  , transformPositionZ :: Maybe (AnimatableProperty Double)  -- Separate Z property
  , transformOrigin :: AnimatableProperty Position2DOr3D  -- Origin point for rotation/scale
  , transformAnchorPoint :: Maybe (AnimatableProperty Position2DOr3D)  -- @deprecated Use origin instead
  , transformScale :: AnimatableProperty Vec3  -- Scale {x, y, z} - always has z
  , transformScaleX :: Maybe (AnimatableProperty Double)  -- Separate X property (when separateDimensions.scale is true)
  , transformScaleY :: Maybe (AnimatableProperty Double)  -- Separate Y property
  , transformScaleZ :: Maybe (AnimatableProperty Double)  -- Separate Z property
  , transformRotation :: AnimatableProperty Double  -- 2D Rotation in degrees
  , transformOrientation :: Maybe (AnimatableProperty Vec3)  -- 3D Rotations (only active if threeD is true)
  , transformRotationX :: Maybe (AnimatableProperty Double)
  , transformRotationY :: Maybe (AnimatableProperty Double)
  , transformRotationZ :: Maybe (AnimatableProperty Double)
  , transformSeparateDimensions :: Maybe SeparateDimensions  -- Separate dimensions flags
  }
  deriving (Eq, Show, Generic)

instance ToJSON LayerTransform where
  toJSON (LayerTransform pos posX posY posZ origin anchor scale scaleX scaleY scaleZ rot orient rotX rotY rotZ sepDim) =
    let
      baseFields = ["position" .= pos, "origin" .= origin, "scale" .= scale, "rotation" .= rot]
      f1 = case posX of Just x -> ("positionX" .= x) : baseFields; Nothing -> baseFields
      f2 = case posY of Just y -> ("positionY" .= y) : f1; Nothing -> f1
      f3 = case posZ of Just z -> ("positionZ" .= z) : f2; Nothing -> f2
      f4 = case anchor of Just a -> ("anchorPoint" .= a) : f3; Nothing -> f3
      f5 = case scaleX of Just x -> ("scaleX" .= x) : f4; Nothing -> f4
      f6 = case scaleY of Just y -> ("scaleY" .= y) : f5; Nothing -> f5
      f7 = case scaleZ of Just z -> ("scaleZ" .= z) : f6; Nothing -> f6
      f8 = case orient of Just o -> ("orientation" .= o) : f7; Nothing -> f7
      f9 = case rotX of Just x -> ("rotationX" .= x) : f8; Nothing -> f8
      f10 = case rotY of Just y -> ("rotationY" .= y) : f9; Nothing -> f9
      f11 = case rotZ of Just z -> ("rotationZ" .= z) : f10; Nothing -> f10
      f12 = case sepDim of Just s -> ("separateDimensions" .= s) : f11; Nothing -> f11
    in object f12

instance FromJSON LayerTransform where
  parseJSON = withObject "LayerTransform" $ \o -> do
    pos <- o .: "position"
    posX <- o .:? "positionX"
    posY <- o .:? "positionY"
    posZ <- o .:? "positionZ"
    origin <- o .: "origin"
    anchor <- o .:? "anchorPoint"
    scale <- o .: "scale"
    scaleX <- o .:? "scaleX"
    scaleY <- o .:? "scaleY"
    scaleZ <- o .:? "scaleZ"
    rot <- o .: "rotation"
    orient <- o .:? "orientation"
    rotX <- o .:? "rotationX"
    rotY <- o .:? "rotationY"
    rotZ <- o .:? "rotationZ"
    sepDim <- o .:? "separateDimensions"
    return (LayerTransform pos posX posY posZ origin anchor scale scaleX scaleY scaleZ rot orient rotX rotY rotZ sepDim)

-- | Separate dimensions flags
data SeparateDimensions = SeparateDimensions
  { separateDimensionsPosition :: Bool
  , separateDimensionsScale :: Bool
  }
  deriving (Eq, Show, Generic, ToJSON, FromJSON)

-- ============================================================
-- MOTION BLUR SETTINGS
-- ============================================================

data MotionBlurType
  = MotionBlurStandard    -- Standard shutter-based blur
  | MotionBlurPixel       -- Pixel motion blur
  | MotionBlurDirectional -- Directional blur (fixed direction)
  | MotionBlurRadial      -- Radial blur (spin/zoom from center)
  | MotionBlurVector      -- Vector-based (uses velocity data)
  | MotionBlurAdaptive    -- Auto-selects based on motion
  deriving (Eq, Show, Generic)

instance ToJSON MotionBlurType where
  toJSON MotionBlurStandard = "standard"
  toJSON MotionBlurPixel = "pixel"
  toJSON MotionBlurDirectional = "directional"
  toJSON MotionBlurRadial = "radial"
  toJSON MotionBlurVector = "vector"
  toJSON MotionBlurAdaptive = "adaptive"

instance FromJSON MotionBlurType where
  parseJSON = withText "MotionBlurType" $ \s ->
    case s of
      t | t == T.pack "standard" -> return MotionBlurStandard
      t | t == T.pack "pixel" -> return MotionBlurPixel
      t | t == T.pack "directional" -> return MotionBlurDirectional
      t | t == T.pack "radial" -> return MotionBlurRadial
      t | t == T.pack "vector" -> return MotionBlurVector
      t | t == T.pack "adaptive" -> return MotionBlurAdaptive
      _ -> fail "Invalid MotionBlurType"

-- ============================================================
-- DEFAULT VALUES
-- ============================================================

-- | Create default layer transform
-- Note: Requires ID generation - caller must provide IDs
createDefaultTransform
  :: Text  -- position ID
  -> Text  -- origin ID
  -> Text  -- scale ID
  -> Text  -- rotation ID
  -> Text  -- orientation ID
  -> Text  -- rotationX ID
  -> Text  -- rotationY ID
  -> Text  -- rotationZ ID
  -> LayerTransform
createDefaultTransform posId originId scaleId rotId orientId rotXId rotYId rotZId =
  let originVal = Position2DOr3D 0.0 0.0 (Just 0.0)
      originProp = createAnimatableProperty originId "origin" originVal PropertyTypePosition Nothing
      positionVal = Position2DOr3D 0.0 0.0 (Just 0.0)
      positionProp = createAnimatableProperty posId "position" positionVal PropertyTypePosition Nothing
      scaleVal = Vec3 100.0 100.0 100.0  -- 100% scale
      scaleProp = createAnimatableProperty scaleId "scale" scaleVal PropertyTypeVector3 Nothing
      rotationProp = createAnimatableProperty rotId "rotation" 0.0 PropertyTypeNumber Nothing
      orientationVal = Vec3 0.0 0.0 0.0
      orientationProp = createAnimatableProperty orientId "orientation" orientationVal PropertyTypeVector3 Nothing
      rotationXProp = createAnimatableProperty rotXId "rotationX" 0.0 PropertyTypeNumber Nothing
      rotationYProp = createAnimatableProperty rotYId "rotationY" 0.0 PropertyTypeNumber Nothing
      rotationZProp = createAnimatableProperty rotZId "rotationZ" 0.0 PropertyTypeNumber Nothing
  in LayerTransform
    { transformPosition = positionProp
    , transformPositionX = Nothing
    , transformPositionY = Nothing
    , transformPositionZ = Nothing
    , transformOrigin = originProp
    , transformAnchorPoint = Just originProp  -- Backwards compatibility
    , transformScale = scaleProp
    , transformScaleX = Nothing
    , transformScaleY = Nothing
    , transformScaleZ = Nothing
    , transformRotation = rotationProp
    , transformOrientation = Just orientationProp
    , transformRotationX = Just rotationXProp
    , transformRotationY = Just rotationYProp
    , transformRotationZ = Just rotationZProp
    , transformSeparateDimensions = Nothing
    }
