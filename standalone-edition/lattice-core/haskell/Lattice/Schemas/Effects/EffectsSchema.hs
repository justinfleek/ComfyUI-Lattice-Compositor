{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Effects.EffectsSchema
Description : Effect category and parameter type enums
Copyright   : (c) Lattice, 2026
License     : MIT

Effect category and parameter type enums.

Source: ui/src/schemas/effects/effects-schema.ts
-}

module Lattice.Schemas.Effects.EffectsSchema
  ( -- * Effect Category
    EffectCategory(..)
  , effectCategoryFromText
  , effectCategoryToText
    -- * Effect Parameter Type
  , EffectParameterType(..)
  , effectParameterTypeFromText
  , effectParameterTypeToText
    -- * Constants
  , maxParameters
  , maxPins
  , maxLabelLength
  , maxValueLength
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Category
-- ────────────────────────────────────────────────────────────────────────────

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

effectCategoryFromText :: Text -> Maybe EffectCategory
effectCategoryFromText "blur-sharpen" = Just EffectBlurSharpen
effectCategoryFromText "color-correction" = Just EffectColorCorrection
effectCategoryFromText "distort" = Just EffectDistort
effectCategoryFromText "generate" = Just EffectGenerate
effectCategoryFromText "keying" = Just EffectKeying
effectCategoryFromText "matte" = Just EffectMatte
effectCategoryFromText "noise-grain" = Just EffectNoiseGrain
effectCategoryFromText "perspective" = Just EffectPerspective
effectCategoryFromText "stylize" = Just EffectStylize
effectCategoryFromText "time" = Just EffectTime
effectCategoryFromText "transition" = Just EffectTransition
effectCategoryFromText "utility" = Just EffectUtility
effectCategoryFromText _ = Nothing

effectCategoryToText :: EffectCategory -> Text
effectCategoryToText EffectBlurSharpen = "blur-sharpen"
effectCategoryToText EffectColorCorrection = "color-correction"
effectCategoryToText EffectDistort = "distort"
effectCategoryToText EffectGenerate = "generate"
effectCategoryToText EffectKeying = "keying"
effectCategoryToText EffectMatte = "matte"
effectCategoryToText EffectNoiseGrain = "noise-grain"
effectCategoryToText EffectPerspective = "perspective"
effectCategoryToText EffectStylize = "stylize"
effectCategoryToText EffectTime = "time"
effectCategoryToText EffectTransition = "transition"
effectCategoryToText EffectUtility = "utility"

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Parameter Type
-- ────────────────────────────────────────────────────────────────────────────

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
  deriving stock (Eq, Show, Generic, Enum, Bounded)

effectParameterTypeFromText :: Text -> Maybe EffectParameterType
effectParameterTypeFromText "number" = Just ParamNumber
effectParameterTypeFromText "color" = Just ParamColor
effectParameterTypeFromText "point" = Just ParamPoint
effectParameterTypeFromText "point3D" = Just ParamPoint3D
effectParameterTypeFromText "angle" = Just ParamAngle
effectParameterTypeFromText "checkbox" = Just ParamCheckbox
effectParameterTypeFromText "dropdown" = Just ParamDropdown
effectParameterTypeFromText "layer" = Just ParamLayer
effectParameterTypeFromText "string" = Just ParamString
effectParameterTypeFromText "curve" = Just ParamCurve
effectParameterTypeFromText "data" = Just ParamData
effectParameterTypeFromText _ = Nothing

effectParameterTypeToText :: EffectParameterType -> Text
effectParameterTypeToText ParamNumber = "number"
effectParameterTypeToText ParamColor = "color"
effectParameterTypeToText ParamPoint = "point"
effectParameterTypeToText ParamPoint3D = "point3D"
effectParameterTypeToText ParamAngle = "angle"
effectParameterTypeToText ParamCheckbox = "checkbox"
effectParameterTypeToText ParamDropdown = "dropdown"
effectParameterTypeToText ParamLayer = "layer"
effectParameterTypeToText ParamString = "string"
effectParameterTypeToText ParamCurve = "curve"
effectParameterTypeToText ParamData = "data"

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

maxParameters :: Int
maxParameters = 1000

maxPins :: Int
maxPins = 10000

maxLabelLength :: Int
maxLabelLength = 200

maxValueLength :: Int
maxValueLength = 500
