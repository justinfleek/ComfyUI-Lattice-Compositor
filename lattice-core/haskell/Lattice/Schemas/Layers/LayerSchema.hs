{-# LANGUAGE StrictData #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Schemas.Layers.LayerSchema
Description : Layer type enum
Copyright   : (c) Lattice, 2026
License     : MIT

All layer types supported by the compositor.

Source: ui/src/schemas/layers/layer-schema.ts
-}

module Lattice.Schemas.Layers.LayerSchema
  ( -- * Layer Type
    LayerType(..)
  , layerTypeFromText
  , layerTypeToText
  , isDeprecatedLayerType
  , getModernReplacement
    -- * Constants
  , maxMasksPerLayer
  , maxPropertiesPerLayer
  , maxEffectsPerLayer
  , maxTimeStretch
  , minTimeStretch
  ) where

import GHC.Generics (Generic)
import Data.Text (Text)

--------------------------------------------------------------------------------
-- Layer Type
--------------------------------------------------------------------------------

-- | All layer types supported by the compositor
data LayerType
  = LayerDepth
  | LayerNormal
  | LayerSpline
  | LayerPath
  | LayerText
  | LayerShape
  | LayerParticle
  | LayerParticles
  | LayerDepthflow
  | LayerImage
  | LayerVideo
  | LayerAudio
  | LayerGenerated
  | LayerCamera
  | LayerLight
  | LayerSolid
  | LayerControl
  | LayerNull      -- ^ @deprecated Use LayerControl
  | LayerGroup
  | LayerNestedComp
  | LayerMatte
  | LayerModel
  | LayerPointcloud
  | LayerPose
  | LayerEffectLayer
  | LayerAdjustment -- ^ @deprecated Use LayerEffectLayer
  deriving stock (Eq, Show, Generic, Enum, Bounded)

layerTypeFromText :: Text -> Maybe LayerType
layerTypeFromText "depth" = Just LayerDepth
layerTypeFromText "normal" = Just LayerNormal
layerTypeFromText "spline" = Just LayerSpline
layerTypeFromText "path" = Just LayerPath
layerTypeFromText "text" = Just LayerText
layerTypeFromText "shape" = Just LayerShape
layerTypeFromText "particle" = Just LayerParticle
layerTypeFromText "particles" = Just LayerParticles
layerTypeFromText "depthflow" = Just LayerDepthflow
layerTypeFromText "image" = Just LayerImage
layerTypeFromText "video" = Just LayerVideo
layerTypeFromText "audio" = Just LayerAudio
layerTypeFromText "generated" = Just LayerGenerated
layerTypeFromText "camera" = Just LayerCamera
layerTypeFromText "light" = Just LayerLight
layerTypeFromText "solid" = Just LayerSolid
layerTypeFromText "control" = Just LayerControl
layerTypeFromText "null" = Just LayerNull
layerTypeFromText "group" = Just LayerGroup
layerTypeFromText "nestedComp" = Just LayerNestedComp
layerTypeFromText "matte" = Just LayerMatte
layerTypeFromText "model" = Just LayerModel
layerTypeFromText "pointcloud" = Just LayerPointcloud
layerTypeFromText "pose" = Just LayerPose
layerTypeFromText "effectLayer" = Just LayerEffectLayer
layerTypeFromText "adjustment" = Just LayerAdjustment
layerTypeFromText _ = Nothing

layerTypeToText :: LayerType -> Text
layerTypeToText LayerDepth = "depth"
layerTypeToText LayerNormal = "normal"
layerTypeToText LayerSpline = "spline"
layerTypeToText LayerPath = "path"
layerTypeToText LayerText = "text"
layerTypeToText LayerShape = "shape"
layerTypeToText LayerParticle = "particle"
layerTypeToText LayerParticles = "particles"
layerTypeToText LayerDepthflow = "depthflow"
layerTypeToText LayerImage = "image"
layerTypeToText LayerVideo = "video"
layerTypeToText LayerAudio = "audio"
layerTypeToText LayerGenerated = "generated"
layerTypeToText LayerCamera = "camera"
layerTypeToText LayerLight = "light"
layerTypeToText LayerSolid = "solid"
layerTypeToText LayerControl = "control"
layerTypeToText LayerNull = "null"
layerTypeToText LayerGroup = "group"
layerTypeToText LayerNestedComp = "nestedComp"
layerTypeToText LayerMatte = "matte"
layerTypeToText LayerModel = "model"
layerTypeToText LayerPointcloud = "pointcloud"
layerTypeToText LayerPose = "pose"
layerTypeToText LayerEffectLayer = "effectLayer"
layerTypeToText LayerAdjustment = "adjustment"

-- | Check if layer type is deprecated
isDeprecatedLayerType :: LayerType -> Bool
isDeprecatedLayerType LayerNull = True
isDeprecatedLayerType LayerAdjustment = True
isDeprecatedLayerType _ = False

-- | Get the modern replacement for deprecated layer types
getModernReplacement :: LayerType -> Maybe LayerType
getModernReplacement LayerNull = Just LayerControl
getModernReplacement LayerAdjustment = Just LayerEffectLayer
getModernReplacement _ = Nothing

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxMasksPerLayer :: Int
maxMasksPerLayer = 100

maxPropertiesPerLayer :: Int
maxPropertiesPerLayer = 10000

maxEffectsPerLayer :: Int
maxEffectsPerLayer = 1000

maxTimeStretch :: Double
maxTimeStretch = 100.0

minTimeStretch :: Double
minTimeStretch = 0.01
