-- |
-- Module      : Lattice.State.Layer.Time
-- Description : Time operations for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for time manipulation (stretch, reverse, freeze, split, speed map)
--
{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Time
  ( timeStretchLayer
  , reverseLayer
  , freezeFrameAtPlayhead
  , splitLayerAtPlayhead
  , enableSpeedMap
  , disableSpeedMap
  , toggleSpeedMap
  ) where

import Data.List (findIndex, splitAt)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.CRUD (regenerateKeyframeIds)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.State.Layer.Types (TimeStretchOptions(..))
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , PropertyType(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , createAnimatableProperty
  , BezierHandle(..)
  , ControlMode(..)
  )
import Lattice.Types.Layer
  ( Layer(..)
  , LayerType(..)
  , LayerData(..)
  )
import Lattice.Types.LayerDataAsset (NestedCompData(..), VideoData(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                        // time // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Apply time stretch to a video or nested comp layer
-- Pure function: takes layer ID, time stretch options, and layers list
-- Returns new layers list with stretched layer, or error if layer not found or invalid type
timeStretchLayer ::
  Text -> -- Layer ID
  TimeStretchOptions -> -- Time stretch options
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with stretched layer, or error
timeStretchLayer targetLayerId options layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case layerType existingLayer of
        LayerTypeVideo ->
          case layerData existingLayer of
            Just (LayerDataVideo videoData) ->
              let
                -- Update layer start/end frames
                updatedLayer = existingLayer
                  { layerStartFrame = timeStretchOptionsNewStartFrame options
                  , layerEndFrame = timeStretchOptionsNewEndFrame options
                  , layerData = Just (LayerDataVideo videoData {videoDataSpeed = timeStretchOptionsSpeed options})
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Video layer has no video data: " <> targetLayerId)
        LayerTypeNestedComp ->
          case layerData existingLayer of
            Just (LayerDataNestedComp nestedCompData) ->
              let
                -- Update nested comp timewarp speed if enabled
                updatedNestedCompData = case nestedCompDataTimewarpSpeed nestedCompData of
                  Just timewarpSpeed ->
                    nestedCompData
                      { nestedCompDataTimewarpSpeed = Just (timewarpSpeed {animatablePropertyValue = timeStretchOptionsSpeed options * 100.0})
                      }
                  Nothing -> nestedCompData
                
                updatedLayer = existingLayer
                  { layerStartFrame = timeStretchOptionsNewStartFrame options
                  , layerEndFrame = timeStretchOptionsNewEndFrame options
                  , layerData = Just (LayerDataNestedComp updatedNestedCompData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Nested comp layer has no nested comp data: " <> targetLayerId)
        _ -> Left ("Time stretch only works on video/nestedComp layers: " <> targetLayerId)

-- | Reverse layer playback
-- Pure function: takes layer ID and layers list
-- Returns new layers list with reversed layer, or error if layer not found or invalid type
reverseLayer ::
  Text -> -- Layer ID
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with reversed layer, or error
reverseLayer targetLayerId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case layerType existingLayer of
        LayerTypeVideo ->
          case layerData existingLayer of
            Just (LayerDataVideo videoData) ->
              let
                -- Negate speed (reverse playback)
                currentSpeed = videoDataSpeed videoData
                newSpeed = if currentSpeed == 0.0 then -1.0 else -currentSpeed
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataVideo videoData {videoDataSpeed = newSpeed})
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Video layer has no video data: " <> targetLayerId)
        LayerTypeNestedComp ->
          case layerData existingLayer of
            Just (LayerDataNestedComp nestedCompData) ->
              let
                -- Negate timewarp speed if enabled
                updatedNestedCompData = case nestedCompDataTimewarpSpeed nestedCompData of
                  Just timewarpSpeed ->
                    let
                      currentSpeed = animatablePropertyValue timewarpSpeed
                      newSpeed = if currentSpeed == 0.0 then -100.0 else -currentSpeed
                    in
                      nestedCompData
                        { nestedCompDataTimewarpSpeed = Just (timewarpSpeed {animatablePropertyValue = newSpeed})
                        }
                  Nothing -> nestedCompData
                
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataNestedComp updatedNestedCompData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Nested comp layer has no nested comp data: " <> targetLayerId)
        _ -> Left ("Reverse only works on video/nestedComp layers: " <> targetLayerId)

-- | Create a freeze frame at the current playhead position
-- Pure function: takes layer ID, current frame, FPS, frame count, ID generator, and layers list
-- Returns new layers list with frozen layer (speed map enabled), or error if layer not found or invalid type
-- Note: Creates speed map keyframes to freeze at current frame
freezeFrameAtPlayhead ::
  Text -> -- Layer ID
  Double -> -- Current frame (playhead position)
  Double -> -- Composition FPS
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for speed map property
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with frozen layer, or error
freezeFrameAtPlayhead targetLayerId currentFrame fps frameCount genSpeedMapId genKeyframeId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case layerType existingLayer of
        LayerTypeVideo ->
          case layerData existingLayer of
            Just (LayerDataVideo videoData) ->
              let
                -- Calculate source time at current frame
                sourceTime = currentFrame / fps
                
                -- Create speed map property with freeze keyframes
                speedMapId = genSpeedMapId "speedMap"
                startKeyframeId = genKeyframeId "freeze_start"
                endKeyframeId = genKeyframeId "freeze_end"
                
                -- Create keyframes to freeze at current frame
                -- Start keyframe at current frame
                startKeyframe = Keyframe
                  { keyframeId = startKeyframeId
                  , keyframeFrame = currentFrame
                  , keyframeValue = sourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationHold
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                -- End keyframe at layer end (or comp end)
                endFrame = min (layerEndFrame existingLayer) (fromIntegral (frameCount - 1))
                endKeyframe = Keyframe
                  { keyframeId = endKeyframeId
                  , keyframeFrame = endFrame
                  , keyframeValue = sourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationHold
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                -- Create speed map property
                speedMapProp = (createAnimatableProperty speedMapId "Speed Map" sourceTime PropertyTypeNumber Nothing)
                  { animatablePropertyKeyframes = [startKeyframe, endKeyframe]
                  , animatablePropertyAnimated = True
                  }
                
                updatedVideoData = videoData
                  { videoDataSpeedMapEnabled = Just True
                  , videoDataSpeedMap = Just speedMapProp
                  , videoDataTimeRemapEnabled = Just True
                  }
                
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataVideo updatedVideoData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Video layer has no video data: " <> targetLayerId)
        LayerTypeNestedComp ->
          case layerData existingLayer of
            Just (LayerDataNestedComp nestedCompData) ->
              let
                -- Similar logic for nested comp (using speedMap in nestedCompData)
                sourceTime = currentFrame / fps
                speedMapId = genSpeedMapId "speedMap"
                startKeyframeId = genKeyframeId "freeze_start"
                endKeyframeId = genKeyframeId "freeze_end"
                
                startKeyframe = Keyframe
                  { keyframeId = startKeyframeId
                  , keyframeFrame = currentFrame
                  , keyframeValue = sourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationHold
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                endFrame = min (layerEndFrame existingLayer) (fromIntegral (frameCount - 1))
                endKeyframe = Keyframe
                  { keyframeId = endKeyframeId
                  , keyframeFrame = endFrame
                  , keyframeValue = sourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationHold
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                speedMapProp = (createAnimatableProperty speedMapId "Speed Map" sourceTime PropertyTypeNumber Nothing)
                  { animatablePropertyKeyframes = [startKeyframe, endKeyframe]
                  , animatablePropertyAnimated = True
                  }
                
                updatedNestedCompData = nestedCompData
                  { nestedCompDataSpeedMapEnabled = Just True
                  , nestedCompDataSpeedMap = Just speedMapProp
                  , nestedCompDataTimeRemapEnabled = Just True
                  }
                
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataNestedComp updatedNestedCompData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Nested comp layer has no nested comp data: " <> targetLayerId)
        _ -> Left ("Freeze frame only works on video/nestedComp layers: " <> targetLayerId)

-- | Split layer at the current playhead position
-- Pure function: takes layer ID, current frame, FPS, ID generators, and layers list
-- Returns new layers list with split layers (original truncated, new layer created), or error
splitLayerAtPlayhead ::
  Text -> -- Layer ID
  Double -> -- Current frame (playhead position)
  Double -> -- Composition FPS
  (Text -> Text) -> -- ID generator for new layer ID
  (Text -> Text) -> -- ID generator for regenerating keyframe IDs
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with split layers, or error
splitLayerAtPlayhead targetLayerId currentFrame fps genLayerId genKeyframeId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      let
        startFrame = layerStartFrame existingLayer
        endFrame = layerEndFrame existingLayer
      in
        if currentFrame <= startFrame || currentFrame >= endFrame
          then Left ("Split point must be within layer bounds: " <> T.pack (show startFrame) <> " < " <> T.pack (show currentFrame) <> " < " <> T.pack (show endFrame))
          else
            let
              -- Create new layer (duplicate of original)
              newLayerId = genLayerId targetLayerId
              duplicatedLayer = existingLayer
                { layerId = newLayerId
                , layerName = layerName existingLayer <> " (split)"
                , layerStartFrame = currentFrame
                , layerEndFrame = endFrame
                }
              
              -- Regenerate keyframe IDs in new layer
              layerWithNewKeyframes = regenerateKeyframeIds genKeyframeId duplicatedLayer
              
              -- Update video startTime if video layer
              updatedNewLayer = case layerData layerWithNewKeyframes of
                Just (LayerDataVideo videoData) ->
                  let
                    -- Calculate time offset
                    frameOffset = currentFrame - startFrame
                    timeOffset = (frameOffset / fps) * videoDataSpeed videoData
                    originalStartTime = videoDataStartTime videoData
                    newStartTime = originalStartTime + timeOffset
                  in
                    layerWithNewKeyframes
                      { layerData = Just (LayerDataVideo videoData {videoDataStartTime = newStartTime})
                      }
                _ -> layerWithNewKeyframes
              
              -- Truncate original layer
              updatedOriginalLayer = existingLayer
                { layerEndFrame = currentFrame
                }
              
              -- Insert new layer after original
              insertionIndex = case findIndex (\l -> layerId l == targetLayerId) layers of
                Nothing -> length layers
                Just idx -> idx + 1
              
              (before, after) = splitAt insertionIndex layers
              updatedBefore = map (\l -> if layerId l == targetLayerId then updatedOriginalLayer else l) before
            in
              Right (updatedBefore ++ [updatedNewLayer] ++ after)

-- | Enable SpeedMap (time remapping) on a video or nested comp layer
-- Pure function: takes layer ID, FPS, frame count, ID generators, and layers list
-- Returns new layers list with speed map enabled, or error if layer not found or invalid type
enableSpeedMap ::
  Text -> -- Layer ID
  Double -> -- Composition FPS
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for speed map property
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with speed map enabled, or error
enableSpeedMap targetLayerId fps frameCount genSpeedMapId genKeyframeId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case layerType existingLayer of
        LayerTypeVideo ->
          case layerData existingLayer of
            Just (LayerDataVideo videoData) ->
              let
                startFrame = layerStartFrame existingLayer
                endFrame = layerEndFrame existingLayer
                layerDuration = endFrame - startFrame
                startSourceTime = 0.0
                endSourceTime = layerDuration / fps
                
                -- Create speed map property with start/end keyframes
                speedMapId = genSpeedMapId "speedMap"
                startKeyframeId = genKeyframeId "speedMap_start"
                endKeyframeId = genKeyframeId "speedMap_end"
                
                startKeyframe = Keyframe
                  { keyframeId = startKeyframeId
                  , keyframeFrame = startFrame
                  , keyframeValue = startSourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationLinear
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                endKeyframe = Keyframe
                  { keyframeId = endKeyframeId
                  , keyframeFrame = endFrame
                  , keyframeValue = endSourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationLinear
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                speedMapProp = (createAnimatableProperty speedMapId "Speed Map" startSourceTime PropertyTypeNumber Nothing)
                  { animatablePropertyKeyframes = [startKeyframe, endKeyframe]
                  , animatablePropertyAnimated = True
                  }
                
                updatedVideoData = videoData
                  { videoDataSpeedMapEnabled = Just True
                  , videoDataSpeedMap = Just speedMapProp
                  , videoDataTimeRemapEnabled = Just True
                  }
                
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataVideo updatedVideoData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Video layer has no video data: " <> targetLayerId)
        LayerTypeNestedComp ->
          case layerData existingLayer of
            Just (LayerDataNestedComp nestedCompData) ->
              let
                startFrame = layerStartFrame existingLayer
                endFrame = layerEndFrame existingLayer
                layerDuration = endFrame - startFrame
                startSourceTime = 0.0
                endSourceTime = layerDuration / fps
                
                speedMapId = genSpeedMapId "speedMap"
                startKeyframeId = genKeyframeId "speedMap_start"
                endKeyframeId = genKeyframeId "speedMap_end"
                
                startKeyframe = Keyframe
                  { keyframeId = startKeyframeId
                  , keyframeFrame = startFrame
                  , keyframeValue = startSourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationLinear
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                endKeyframe = Keyframe
                  { keyframeId = endKeyframeId
                  , keyframeFrame = endFrame
                  , keyframeValue = endSourceTime
                  , keyframeInterpolation = InterpolationBase InterpolationLinear
                  , keyframeInHandle = BezierHandle (-5.0) 0.0 True
                  , keyframeOutHandle = BezierHandle 5.0 0.0 True
                  , keyframeControlMode = ControlSmooth
                  , keyframeSpatialInTangent = Nothing
                  , keyframeSpatialOutTangent = Nothing
                  }
                
                speedMapProp = (createAnimatableProperty speedMapId "Speed Map" startSourceTime PropertyTypeNumber Nothing)
                  { animatablePropertyKeyframes = [startKeyframe, endKeyframe]
                  , animatablePropertyAnimated = True
                  }
                
                updatedNestedCompData = nestedCompData
                  { nestedCompDataSpeedMapEnabled = Just True
                  , nestedCompDataSpeedMap = Just speedMapProp
                  , nestedCompDataTimeRemapEnabled = Just True
                  }
                
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataNestedComp updatedNestedCompData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Nested comp layer has no nested comp data: " <> targetLayerId)
        _ -> Left ("SpeedMap only works on video/nestedComp layers: " <> targetLayerId)

-- | Disable SpeedMap (time remapping) on a video or nested comp layer
-- Pure function: takes layer ID and layers list
-- Returns new layers list with speed map disabled, or error if layer not found or invalid type
disableSpeedMap ::
  Text -> -- Layer ID
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with speed map disabled, or error
disableSpeedMap targetLayerId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case layerType existingLayer of
        LayerTypeVideo ->
          case layerData existingLayer of
            Just (LayerDataVideo videoData) ->
              let
                updatedVideoData = videoData
                  { videoDataSpeedMapEnabled = Just False
                  , videoDataSpeedMap = Nothing
                  , videoDataTimeRemapEnabled = Just False
                  }
                
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataVideo updatedVideoData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Video layer has no video data: " <> targetLayerId)
        LayerTypeNestedComp ->
          case layerData existingLayer of
            Just (LayerDataNestedComp nestedCompData) ->
              let
                updatedNestedCompData = nestedCompData
                  { nestedCompDataSpeedMapEnabled = Just False
                  , nestedCompDataSpeedMap = Nothing
                  , nestedCompDataTimeRemapEnabled = Just False
                  }
                
                updatedLayer = existingLayer
                  { layerData = Just (LayerDataNestedComp updatedNestedCompData)
                  }
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
            _ -> Left ("Nested comp layer has no nested comp data: " <> targetLayerId)
        _ -> Left ("SpeedMap only works on video/nestedComp layers: " <> targetLayerId)

-- | Toggle SpeedMap (time remapping) on a video or nested comp layer
-- Pure function: takes layer ID, FPS, frame count, ID generators, and layers list
-- Returns new layers list with speed map toggled, or error if layer not found or invalid type
toggleSpeedMap ::
  Text -> -- Layer ID
  Double -> -- Composition FPS
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for speed map property
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text (Bool, [Layer]) -- Returns (new speed map state, new layers list), or error
toggleSpeedMap targetLayerId fps frameCount genSpeedMapId genKeyframeId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case layerType existingLayer of
        LayerTypeVideo ->
          case layerData existingLayer of
            Just (LayerDataVideo videoData) ->
              case videoDataSpeedMapEnabled videoData of
                Just True ->
                  -- Currently enabled, disable it
                  case disableSpeedMap targetLayerId layers of
                    Right newLayers -> Right (False, newLayers)
                    Left err -> Left err
                _ ->
                  -- Currently disabled, enable it
                  case enableSpeedMap targetLayerId fps frameCount genSpeedMapId genKeyframeId layers of
                    Right newLayers -> Right (True, newLayers)
                    Left err -> Left err
            _ -> Left ("Video layer has no video data: " <> targetLayerId)
        LayerTypeNestedComp ->
          case layerData existingLayer of
            Just (LayerDataNestedComp nestedCompData) ->
              case nestedCompDataSpeedMapEnabled nestedCompData of
                Just True ->
                  -- Currently enabled, disable it
                  case disableSpeedMap targetLayerId layers of
                    Right newLayers -> Right (False, newLayers)
                    Left err -> Left err
                _ ->
                  -- Currently disabled, enable it
                  case enableSpeedMap targetLayerId fps frameCount genSpeedMapId genKeyframeId layers of
                    Right newLayers -> Right (True, newLayers)
                    Left err -> Left err
            _ -> Left ("Nested comp layer has no nested comp data: " <> targetLayerId)
        _ -> Left ("SpeedMap only works on video/nestedComp layers: " <> targetLayerId)
