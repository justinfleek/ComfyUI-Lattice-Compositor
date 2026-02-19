-- | Lattice.Schemas.Layers.LayerSchema - Layer type enum
-- |
-- | All layer types supported by the compositor.
-- |
-- | Source: ui/src/schemas/layers/layer-schema.ts

module Lattice.Schemas.Layers.LayerSchema
  ( -- Layer Type
    LayerType(..)
  , layerTypeFromString
  , layerTypeToString
  , isDeprecatedLayerType
  , getModernReplacement
    -- Constants
  , maxMasksPerLayer
  , maxPropertiesPerLayer
  , maxEffectsPerLayer
  , maxTimeStretch
  , minTimeStretch
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

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
  | LayerNull      -- @deprecated Use LayerControl
  | LayerGroup
  | LayerNestedComp
  | LayerMatte
  | LayerModel
  | LayerPointcloud
  | LayerPose
  | LayerEffectLayer
  | LayerAdjustment -- @deprecated Use LayerEffectLayer

derive instance Eq LayerType
derive instance Generic LayerType _

instance Show LayerType where
  show = genericShow

layerTypeFromString :: String -> Maybe LayerType
layerTypeFromString = case _ of
  "depth" -> Just LayerDepth
  "normal" -> Just LayerNormal
  "spline" -> Just LayerSpline
  "path" -> Just LayerPath
  "text" -> Just LayerText
  "shape" -> Just LayerShape
  "particle" -> Just LayerParticle
  "particles" -> Just LayerParticles
  "depthflow" -> Just LayerDepthflow
  "image" -> Just LayerImage
  "video" -> Just LayerVideo
  "audio" -> Just LayerAudio
  "generated" -> Just LayerGenerated
  "camera" -> Just LayerCamera
  "light" -> Just LayerLight
  "solid" -> Just LayerSolid
  "control" -> Just LayerControl
  "null" -> Just LayerNull
  "group" -> Just LayerGroup
  "nestedComp" -> Just LayerNestedComp
  "matte" -> Just LayerMatte
  "model" -> Just LayerModel
  "pointcloud" -> Just LayerPointcloud
  "pose" -> Just LayerPose
  "effectLayer" -> Just LayerEffectLayer
  "adjustment" -> Just LayerAdjustment
  _ -> Nothing

layerTypeToString :: LayerType -> String
layerTypeToString = case _ of
  LayerDepth -> "depth"
  LayerNormal -> "normal"
  LayerSpline -> "spline"
  LayerPath -> "path"
  LayerText -> "text"
  LayerShape -> "shape"
  LayerParticle -> "particle"
  LayerParticles -> "particles"
  LayerDepthflow -> "depthflow"
  LayerImage -> "image"
  LayerVideo -> "video"
  LayerAudio -> "audio"
  LayerGenerated -> "generated"
  LayerCamera -> "camera"
  LayerLight -> "light"
  LayerSolid -> "solid"
  LayerControl -> "control"
  LayerNull -> "null"
  LayerGroup -> "group"
  LayerNestedComp -> "nestedComp"
  LayerMatte -> "matte"
  LayerModel -> "model"
  LayerPointcloud -> "pointcloud"
  LayerPose -> "pose"
  LayerEffectLayer -> "effectLayer"
  LayerAdjustment -> "adjustment"

-- | Check if layer type is deprecated
isDeprecatedLayerType :: LayerType -> Boolean
isDeprecatedLayerType = case _ of
  LayerNull -> true
  LayerAdjustment -> true
  _ -> false

-- | Get the modern replacement for deprecated layer types
getModernReplacement :: LayerType -> Maybe LayerType
getModernReplacement = case _ of
  LayerNull -> Just LayerControl
  LayerAdjustment -> Just LayerEffectLayer
  _ -> Nothing

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

maxMasksPerLayer :: Int
maxMasksPerLayer = 100

maxPropertiesPerLayer :: Int
maxPropertiesPerLayer = 10000

maxEffectsPerLayer :: Int
maxEffectsPerLayer = 1000

maxTimeStretch :: Number
maxTimeStretch = 100.0

minTimeStretch :: Number
minTimeStretch = 0.01
