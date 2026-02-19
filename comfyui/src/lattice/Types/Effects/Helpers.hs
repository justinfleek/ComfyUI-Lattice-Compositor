{-# LANGUAGE OverloadedStrings #-}

module Lattice.Types.Effects.Helpers
  ( createEffectInstance,
    createMeshDeformEffectInstance,
    isMeshDeformEffect,
  )
where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Animation
  ( AnimatableProperty (..),
    PropertyType (..),
    PropertyValue (..),
    createAnimatableProperty,
  )
import Lattice.Types.Primitives (RGBAColor (..), Vec2 (..), Vec3 (..))

--                                                                      // note
-- This assumes AnimatableProperty PropertyValue - Core.hs may need updating to be explicit
import Lattice.Types.Effects.Core
  ( EffectDefinition (..),
    EffectInstance (..),
    EffectParameter (..),
    EffectParameterType (..),
    EffectParameterValue (..),
    MeshDeformEffectInstance (..),
    getAnimatableType,
  )
import Lattice.Types.Effects.Definitions (allEffectDefinitions)

-- | Convert EffectParameterValue to PropertyValue
effectParamValueToPropertyValue :: EffectParameterValue -> PropertyValue
effectParamValueToPropertyValue (ParamNumber n) = PropertyValueNumber n
effectParamValueToPropertyValue (ParamString s) = PropertyValueString (T.pack s)
effectParamValueToPropertyValue (ParamBool b) = PropertyValueBool b
effectParamValueToPropertyValue (ParamPoint x y) = PropertyValueVec2 (Vec2 x y)
effectParamValueToPropertyValue (ParamPoint3D x y z) = PropertyValueVec3 (Vec3 x y z)
effectParamValueToPropertyValue (ParamColor r g b mAlpha) =
  PropertyValueRGBA (RGBAColor r g b (maybe 1.0 id mAlpha))
effectParamValueToPropertyValue (ParamCurve _) = PropertyValueString (T.pack "curve") -- TODO: Proper curve representation
effectParamValueToPropertyValue (ParamData _) = PropertyValueString (T.pack "data") -- TODO: Proper data representation
effectParamValueToPropertyValue ParamNull = PropertyValueString (T.pack "")

-- | Convert EffectParameterType to PropertyType
effectParamTypeToPropertyType :: EffectParameterType -> PropertyType
effectParamTypeToPropertyType ParamTypeNumber = PropertyTypeNumber
effectParamTypeToPropertyType ParamTypeAngle = PropertyTypeNumber
effectParamTypeToPropertyType ParamTypePoint = PropertyTypePosition
effectParamTypeToPropertyType ParamTypePoint3D = PropertyTypeVector3
effectParamTypeToPropertyType ParamTypeColor = PropertyTypeColor
effectParamTypeToPropertyType ParamTypeCheckbox = PropertyTypeEnum
effectParamTypeToPropertyType ParamTypeDropdown = PropertyTypeEnum
effectParamTypeToPropertyType ParamTypeLayer = PropertyTypeEnum
effectParamTypeToPropertyType ParamTypeString = PropertyTypeEnum
effectParamTypeToPropertyType ParamTypeCurve = PropertyTypeEnum
effectParamTypeToPropertyType ParamTypeData = PropertyTypeEnum

-- | Create effect instance with animatable parameters
-- Migrated from ui/src/types/effects.ts createEffectInstance function
createEffectInstance :: String -> Maybe EffectInstance
createEffectInstance definitionKey =
  case HM.lookup definitionKey allEffectDefinitions of
    Nothing -> Nothing
    Just def -> do
      let parameters =
            map
              ( \(index, param) ->
                  let paramKey =
                        T.unpack
                          ( T.replace " " "_"
                              ( T.replace "-" "_"
                                  ( T.toLower
                                      ( T.pack (paramName param)
                                      )
                                  )
                              )
                          )
                      propValue = effectParamValueToPropertyValue (paramDefaultValue param)
                      propType = effectParamTypeToPropertyType (paramType param)
                      propId = T.pack (definitionKey <> "-" <> paramKey <> "-" <> show index)
                      propName = T.pack (paramName param)
                      propGroup = fmap T.pack (paramGroup param)
                   in ( paramKey,
                        createAnimatableProperty propId propName propValue propType propGroup
                      )
              )
              (zip [0 ..] (defParameters def))
      Just
        EffectInstance
          { instanceId = "effect-placeholder-id", -- TODO: Generate proper ID
            instanceEffectKey = definitionKey,
            instanceName = defName def,
            instanceCategory = defCategory def,
            instanceEnabled = True,
            instanceExpanded = True,
            instanceParameters = parameters
          }

-- | Create a mesh-deform effect instance with empty pins array
-- Migrated from ui/src/types/effects.ts createMeshDeformEffectInstance function
--                                                                      // note
createMeshDeformEffectInstance :: Maybe MeshDeformEffectInstance
createMeshDeformEffectInstance =
  case createEffectInstance "mesh-deform" of
    Nothing -> Nothing
    Just baseInstance ->
      Just
        MeshDeformEffectInstance
          { meshDeformInstance = baseInstance,
            meshDeformPins = [], -- TODO: Use WarpPin type when MeshWarp is migrated
            meshDeformCachedMesh = Nothing, -- TODO: Use WarpMesh type when MeshWarp is migrated
            meshDeformMeshDirty = True
          }

-- | Type guard to check if an effect instance is a MeshDeformEffectInstance
-- Migrated from ui/src/types/effects.ts isMeshDeformEffect function
-- Note: In Haskell, we'd use a sum type instead of runtime check
-- This is a placeholder until we have proper type-level distinction
isMeshDeformEffect :: EffectInstance -> Bool
isMeshDeformEffect effect =
  instanceEffectKey effect == "mesh-deform"
    && any ((== "pins") . fst) (instanceParameters effect)
