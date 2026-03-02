-- |
-- Module      : Lattice.State.Layer.Batch
-- Description : Batch operations for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for batch layer operations (sequencing, exponential scale)
--
{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Batch
  ( sequenceLayers
  , applyExponentialScale
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.List (mapAccumL)
import Data.Maybe (mapMaybe)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.State.Layer.Types
  ( SequenceLayersOptions(..)
  , ExponentialScaleOptions(..)
  , ExponentialScaleAxis(..)
  )
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , PropertyType(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , BezierHandle(..)
  , ControlMode(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives
  ( Vec3(..)
  , validateFinite
  )
import Lattice.Types.Transform (LayerTransform(..))

-- ============================================================================
-- BATCH OPERATIONS
-- ============================================================================

-- | Sequence layers - arrange them one after another in timeline
-- Pure function: takes layer IDs, sequencing options, and layers list
-- Returns number of layers sequenced and new layers list, or error
sequenceLayers ::
  [Text] -> -- Layer IDs to sequence
  SequenceLayersOptions -> -- Sequencing options
  [Layer] -> -- Current layers list
  Either Text (Int, [Layer]) -- Returns (number sequenced, new layers list), or error
sequenceLayers layerIds options layers =
  if length layerIds < 2
    then Left "sequenceLayers: need at least 2 layers"
    else
      let
        -- Get layers in order (filter out missing layers)
        orderedLayers = mapMaybe (\lid -> getLayerById layers lid) layerIds
        
        -- Optionally reverse the order
        finalOrderedLayers = case sequenceLayersOptionsReverse options of
          Just True -> reverse orderedLayers
          _ -> orderedLayers
      in
        if length finalOrderedLayers < 2
          then Left "sequenceLayers: could not find enough layers"
          else
            let
              gapFrames = maybe 0.0 id (sequenceLayersOptionsGapFrames options)
              startFrame = maybe 0.0 id (sequenceLayersOptionsStartFrame options)
              
              -- Sequence layers one after another
              sequenceOneLayer currentFrame layer =
                let
                  duration = layerEndFrame layer - layerStartFrame layer
                  newStartFrame = currentFrame
                  newEndFrame = currentFrame + duration
                  updatedLayer = layer
                    { layerStartFrame = newStartFrame
                    , layerEndFrame = newEndFrame
                    }
                  nextFrame = newEndFrame + gapFrames
                in
                  (nextFrame, updatedLayer)
              
              (_, updatedLayers) = mapAccumL sequenceOneLayer startFrame finalOrderedLayers
              
              -- Create map of updated layers
              updatedLayerMap = HM.fromList (map (\l -> (layerId l, l)) updatedLayers)
              
              -- Update layers list
              newLayers =
                map (\l ->
                  case HM.lookup (layerId l) updatedLayerMap of
                    Just updated -> updated
                    Nothing -> l
                )
                layers
            in
              Right (length finalOrderedLayers, newLayers)

-- | Create exponential scale animation on a layer
-- Pure function: takes layer ID, scale options, ID generators, and layers list
-- Returns number of keyframes created and new layers list, or error
-- Uses exponential curve: scale(t) = startScale * (endScale/startScale)^t
applyExponentialScale ::
  Text -> -- Layer ID
  ExponentialScaleOptions -> -- Scale animation options
  (Text -> Text) -> -- ID generator for scale property keyframes
  [Layer] -> -- Current layers list
  Either Text (Int, [Layer]) -- Returns (number of keyframes created, new layers list), or error
applyExponentialScale targetLayerId options genKeyframeId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      let
        startScale = maybe 100.0 id (exponentialScaleOptionsStartScale options)
        endScale = maybe 200.0 id (exponentialScaleOptionsEndScale options)
        startFrame = maybe 0.0 id (exponentialScaleOptionsStartFrame options)
        endFrame = maybe 30.0 id (exponentialScaleOptionsEndFrame options)
        keyframeCount = maybe 10 id (exponentialScaleOptionsKeyframeCount options)
        axis = maybe ExponentialScaleAxisBoth id (exponentialScaleOptionsAxis options)
        
        -- Validate scale values (prevent division by zero)
        ratio = if startScale == 0.0 || not (validateFinite startScale) || not (validateFinite endScale)
          then Left "applyExponentialScale: startScale must be a non-zero finite number, endScale must be finite"
          else Right (endScale / startScale)
      in
        case ratio of
          Left err -> Left err
          Right ratioVal ->
            let
              duration = endFrame - startFrame
              
              -- Generate keyframes with exponential interpolation
              generateKeyframe i =
                let
                  t = fromIntegral i / fromIntegral keyframeCount  -- 0 to 1
                  frame = startFrame + t * duration
                  -- Exponential formula: startScale * ratio^t
                  scaleValue = startScale * (ratioVal ** t)
                  
                  -- Get current scale value
                  currentScale = transformScale (layerTransform existingLayer)
                  currentScaleVal = animatablePropertyValue currentScale
                  
                  -- Apply to appropriate axis
                  newScaleVal = case axis of
                    ExponentialScaleAxisBoth -> Vec3 scaleValue scaleValue (vec3Z currentScaleVal)
                    ExponentialScaleAxisX -> Vec3 scaleValue (vec3Y currentScaleVal) (vec3Z currentScaleVal)
                    ExponentialScaleAxisY -> Vec3 (vec3X currentScaleVal) scaleValue (vec3Z currentScaleVal)
                  
                  keyframeId_ = genKeyframeId ("expScale_" <> T.pack (show i))
                  
                  keyframe = Keyframe
                    { keyframeId = keyframeId_
                    , keyframeFrame = frame
                    , keyframeValue = newScaleVal
                    , keyframeInterpolation = InterpolationBase InterpolationBezier
                    , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                    , keyframeOutHandle = BezierHandle 5.0 0.0 True
                    , keyframeControlMode = ControlSmooth
                    , keyframeSpatialInTangent = Nothing
                    , keyframeSpatialOutTangent = Nothing
                    }
                in
                  keyframe
              
              keyframes = map generateKeyframe [0..keyframeCount]
              
              -- Update scale property with new keyframes
              scaleProp = transformScale (layerTransform existingLayer)
              updatedScaleProp = scaleProp
                { animatablePropertyValue = animatablePropertyValue scaleProp  -- Keep current value as default
                , animatablePropertyKeyframes = Just keyframes
                }
              
              updatedTransform = (layerTransform existingLayer)
                { transformScale = updatedScaleProp
                }
              
              updatedLayer = existingLayer
                { layerTransform = updatedTransform
                }
              
              newLayers = map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers
            in
              Right (length keyframes, newLayers)
