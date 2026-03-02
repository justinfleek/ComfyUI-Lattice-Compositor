-- | Lattice.Schemas.Effects.EffectsSchema - Effect category and parameter type enums
-- |
-- | Effect category and parameter type enums.
-- |
-- | Source: ui/src/schemas/effects/effects-schema.ts

module Lattice.Schemas.Effects.EffectsSchema
  ( -- Effect Category
    EffectCategory(..)
  , effectCategoryFromString
  , effectCategoryToString
    -- Effect Parameter Type
  , EffectParameterType(..)
  , effectParameterTypeFromString
  , effectParameterTypeToString
    -- Constants
  , maxParameters
  , maxPins
  , maxLabelLength
  , maxValueLength
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
-- Effect Category
--------------------------------------------------------------------------------

-- | Effect category options
data EffectCategory
  = EffectBlurSharpen
  | EffectColorCorrection
  | EffectDistort
  | EffectGenerate
  | EffectKeying
  | EffectMatte
  | EffectNoiseGrain
  | EffectPerspective
  | EffectStylize
  | EffectTime
  | EffectTransition
  | EffectUtility

derive instance Eq EffectCategory
derive instance Generic EffectCategory _

instance Show EffectCategory where
  show = genericShow

effectCategoryFromString :: String -> Maybe EffectCategory
effectCategoryFromString = case _ of
  "blur-sharpen" -> Just EffectBlurSharpen
  "color-correction" -> Just EffectColorCorrection
  "distort" -> Just EffectDistort
  "generate" -> Just EffectGenerate
  "keying" -> Just EffectKeying
  "matte" -> Just EffectMatte
  "noise-grain" -> Just EffectNoiseGrain
  "perspective" -> Just EffectPerspective
  "stylize" -> Just EffectStylize
  "time" -> Just EffectTime
  "transition" -> Just EffectTransition
  "utility" -> Just EffectUtility
  _ -> Nothing

effectCategoryToString :: EffectCategory -> String
effectCategoryToString = case _ of
  EffectBlurSharpen -> "blur-sharpen"
  EffectColorCorrection -> "color-correction"
  EffectDistort -> "distort"
  EffectGenerate -> "generate"
  EffectKeying -> "keying"
  EffectMatte -> "matte"
  EffectNoiseGrain -> "noise-grain"
  EffectPerspective -> "perspective"
  EffectStylize -> "stylize"
  EffectTime -> "time"
  EffectTransition -> "transition"
  EffectUtility -> "utility"

--------------------------------------------------------------------------------
-- Effect Parameter Type
--------------------------------------------------------------------------------

-- | Effect parameter type options
data EffectParameterType
  = ParamNumber
  | ParamColor
  | ParamPoint
  | ParamPoint3D
  | ParamAngle
  | ParamCheckbox
  | ParamDropdown
  | ParamLayer
  | ParamString
  | ParamCurve
  | ParamData

derive instance Eq EffectParameterType
derive instance Generic EffectParameterType _

instance Show EffectParameterType where
  show = genericShow

effectParameterTypeFromString :: String -> Maybe EffectParameterType
effectParameterTypeFromString = case _ of
  "number" -> Just ParamNumber
  "color" -> Just ParamColor
  "point" -> Just ParamPoint
  "point3D" -> Just ParamPoint3D
  "angle" -> Just ParamAngle
  "checkbox" -> Just ParamCheckbox
  "dropdown" -> Just ParamDropdown
  "layer" -> Just ParamLayer
  "string" -> Just ParamString
  "curve" -> Just ParamCurve
  "data" -> Just ParamData
  _ -> Nothing

effectParameterTypeToString :: EffectParameterType -> String
effectParameterTypeToString = case _ of
  ParamNumber -> "number"
  ParamColor -> "color"
  ParamPoint -> "point"
  ParamPoint3D -> "point3D"
  ParamAngle -> "angle"
  ParamCheckbox -> "checkbox"
  ParamDropdown -> "dropdown"
  ParamLayer -> "layer"
  ParamString -> "string"
  ParamCurve -> "curve"
  ParamData -> "data"

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxParameters :: Int
maxParameters = 1000

maxPins :: Int
maxPins = 10000

maxLabelLength :: Int
maxLabelLength = 200

maxValueLength :: Int
maxValueLength = 500
