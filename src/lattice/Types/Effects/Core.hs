{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}

module Lattice.Types.Effects.Core
  ( EffectCategory (..),
    EffectParameterValue (..),
    EffectParameter (..),
    Effect (..),
    EffectInstance (..),
    MeshDeformEffectInstance (..),
    EffectParameterType (..),
    getAnimatableType,
    EffectDefinition (..),
  )
where

import Data.Aeson (FromJSON, ToJSON)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Lattice.Types.Animation (AnimatableProperty, PropertyValue)
-- TODO: Import MeshWarp types once meshWarp.ts is migrated (Phase 4.1)
-- import Lattice.Types.MeshWarp (WarpMesh, WarpPin)

-- | Effect category classification
data EffectCategory
  = BlurSharpen
  | ColorCorrection
  | Distort
  | Generate
  | Keying
  | Matte
  | NoiseGrain
  | Perspective
  | Stylize
  | Time
  | Transition
  | Utility
  deriving (Eq, Show, Generic, Hashable, FromJSON, ToJSON)

-- | Effect parameter value types based on parameter type
data EffectParameterValue
  = ParamNumber Double -- For "number", "angle" types
  | ParamString String -- For "string", "layer", "dropdown" types
  | ParamBool Bool -- For "checkbox" type
  | ParamPoint Double Double -- For "point" type (x, y)
  | ParamPoint3D Double Double Double -- For "point3D" type (x, y, z)
  | ParamColor Double Double Double (Maybe Double) -- For "color" type (r, g, b, a?)
  | ParamCurve [(Double, Double)] -- For "curve" type (bezier curve points)
  | ParamData (Maybe String) -- For "data" type (arbitrary JSON data, encoded as string)
  | ParamNull -- For optional parameters (layer, data)
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Effect parameter definition
data EffectParameter = EffectParameter
  { paramId :: String,
    paramName :: String,
    paramType :: EffectParameterType,
    paramValue :: EffectParameterValue,
    paramDefaultValue :: EffectParameterValue,
    paramMin :: Maybe Double,
    paramMax :: Maybe Double,
    paramStep :: Maybe Double,
    paramOptions :: Maybe [(String, EffectParameterValue)], -- (label, value)
    paramAnimatable :: Bool,
    paramGroup :: Maybe String
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Effect definition (template)
data Effect = Effect
  { effectId :: String,
    effectName :: String,
    effectCategory :: EffectCategory,
    effectEnabled :: Bool,
    effectExpanded :: Bool,
    effectParameters :: [EffectParameter],
    effectFragmentShader :: Maybe String -- Optional GPU shader code
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Effect instance stored on a layer - parameters are animatable
data EffectInstance = EffectInstance
  { instanceId :: String,
    instanceEffectKey :: String, -- Key into EFFECT_DEFINITIONS (e.g., 'gaussian-blur')
    instanceName :: String,
    instanceCategory :: EffectCategory,
    instanceEnabled :: Bool,
    instanceExpanded :: Bool,
    -- Parameters as AnimatableProperty for keyframe support
    instanceParameters :: [(String, AnimatableProperty PropertyValue)]
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Mesh Deform effect instance with puppet pins
-- Extends base EffectInstance with pin storage and cached mesh
-- TODO: Update once MeshWarp types are migrated (Phase 4.1)
-- For now, using String placeholders - will be replaced with proper types
data MeshDeformEffectInstance = MeshDeformEffectInstance
  { meshDeformInstance :: EffectInstance,
    meshDeformPins :: [String], -- TODO: Replace with [WarpPin] once MeshWarp is migrated
    meshDeformCachedMesh :: Maybe String, -- TODO: Replace with Maybe WarpMesh once MeshWarp is migrated
    meshDeformMeshDirty :: Bool -- Whether mesh needs rebuild
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Parameter type mapping for effect definitions
data EffectParameterType
  = ParamTypeNumber
  | ParamTypeColor
  | ParamTypePoint
  | ParamTypePoint3D
  | ParamTypeAngle
  | ParamTypeCheckbox
  | ParamTypeDropdown
  | ParamTypeLayer
  | ParamTypeString
  | ParamTypeCurve
  | ParamTypeData
  deriving (Eq, Show, Generic, FromJSON, ToJSON)

-- | Get the AnimatableProperty type string for a parameter type
-- Returns the type that matches AnimatableProperty.type
getAnimatableType :: EffectParameterType -> String
getAnimatableType ParamTypeNumber = "number"
getAnimatableType ParamTypeAngle = "number"
getAnimatableType ParamTypePoint = "position"
getAnimatableType ParamTypePoint3D = "vector3"
getAnimatableType ParamTypeColor = "color"
getAnimatableType ParamTypeCheckbox = "enum"
getAnimatableType ParamTypeDropdown = "enum"
getAnimatableType ParamTypeLayer = "enum"
getAnimatableType ParamTypeString = "enum"
getAnimatableType ParamTypeCurve = "enum"
getAnimatableType ParamTypeData = "enum"

-- | Effect definition template (for EFFECT_DEFINITIONS)
data EffectDefinition = EffectDefinition
  { defName :: String,
    defCategory :: EffectCategory,
    defDescription :: String,
    defParameters :: [EffectParameter], -- Without id and value (template)
    defFragmentShader :: Maybe String
  }
  deriving (Eq, Show, Generic, FromJSON, ToJSON)
