-- |
-- Module      : Lattice.State.Keyframe.Property
-- Description : Property value and animation state operations
--
-- Migrated from ui/src/stores/keyframeStore/property.ts
-- Pure functions for setting property values and animation state
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Property
  ( setPropertyValue
  , setPropertyAnimated
  ) where

import Data.List (find)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.CRUD (setKeyframeValue)
import Lattice.State.Keyframe.Helpers (safeFrame)
import Lattice.State.Keyframe.Interpolation (updatePropertyInLayer)
import Lattice.State.Keyframe.PropertyUpdate (setPropertyAnimated)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , PropertyValue(..)
  , createKeyframe
  , InterpolationType(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives
  ( Position2DOr3D(..)
  , Vec2(..)
  , Vec3(..)
  , validateFinite
  )
import Lattice.Types.Transform (LayerTransform(..))

-- ============================================================================
-- PROPERTY VALUE OPERATIONS
-- ============================================================================

-- | Set a property's value (for direct editing in timeline)
-- Pure function: takes layer ID, property path, value, current frame, and layers list
-- Returns updated layers list or error
-- If property is animated and at a keyframe, updates that keyframe's value too
setPropertyValue ::
  Text -> -- Layer ID
  Text -> -- Property path
  PropertyValue -> -- Value to set
  Double -> -- Current frame (for keyframe update check)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setPropertyValue layerId propertyPath value currentFrame layers =
  -- Validate current frame is finite and >= 1
  if not (validateFinite currentFrame) || currentFrame < 1
    then Right layers
    else
      case getLayerById layerId layers of
        Nothing -> Right layers
        Just layer ->
          let
            normalizedPath = T.replace "transform." "" propertyPath
            transform = layerTransform layer
            
            -- Convert PropertyValue to appropriate type and update property
            -- Use updatePropertyInLayer which works with typed properties
            mUpdatedLayer = if normalizedPath == "position"
              then
                -- Convert PropertyValue to Position2DOr3D
                case value of
                  PropertyValuePosition2DOr3D (Vec2 x y) mz ->
                    let
                      posValue = Position2DOr3D x y mz
                    in
                      updatePropertyInLayer layer propertyPath (\prop ->
                        let
                          updatedProp = prop {animatablePropertyValue = posValue}
                          -- If animated and at keyframe, update keyframe value
                          updatedPropWithKeyframe = if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                            then
                              let
                                keyframes = animatablePropertyKeyframes prop
                                mKeyframeAtFrame = find (\k -> keyframeFrame k == currentFrame) keyframes
                              in
                                case mKeyframeAtFrame of
                                  Nothing -> updatedProp
                                  Just kf ->
                                    let
                                      updatedKeyframes = map (\k -> if keyframeId k == keyframeId kf then k {keyframeValue = posValue} else k) keyframes
                                    in
                                      updatedProp {animatablePropertyKeyframes = updatedKeyframes}
                            else updatedProp
                        in
                          updatedPropWithKeyframe
                        )
                  _ -> Nothing
              
              else if normalizedPath == "scale"
                then
                  -- Convert PropertyValue to Vec3
                  case value of
                    PropertyValueVec3 (Vec3 x y z) ->
                      let
                        vecValue = Vec3 x y z
                      in
                        updatePropertyInLayer layer propertyPath (\prop ->
                          let
                            updatedProp = prop {animatablePropertyValue = vecValue}
                            updatedPropWithKeyframe = if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                              then
                                let
                                  keyframes = animatablePropertyKeyframes prop
                                  mKeyframeAtFrame = find (\k -> keyframeFrame k == currentFrame) keyframes
                                in
                                  case mKeyframeAtFrame of
                                    Nothing -> updatedProp
                                    Just kf ->
                                      let
                                        updatedKeyframes = map (\k -> if keyframeId k == keyframeId kf then k {keyframeValue = vecValue} else k) keyframes
                                      in
                                        updatedProp {animatablePropertyKeyframes = updatedKeyframes}
                              else updatedProp
                          in
                            updatedPropWithKeyframe
                          )
                    _ -> Nothing
              
              else if normalizedPath == "rotation"
                then
                  -- Convert PropertyValue to Double
                  case value of
                    PropertyValueNumber d ->
                      updatePropertyInLayer layer propertyPath (\prop ->
                        let
                          updatedProp = prop {animatablePropertyValue = d}
                          updatedPropWithKeyframe = if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                            then
                              let
                                keyframes = animatablePropertyKeyframes prop
                                mKeyframeAtFrame = find (\k -> keyframeFrame k == currentFrame) keyframes
                              in
                                case mKeyframeAtFrame of
                                  Nothing -> updatedProp
                                  Just kf ->
                                    let
                                      updatedKeyframes = map (\k -> if keyframeId k == keyframeId kf then k {keyframeValue = d} else k) keyframes
                                    in
                                      updatedProp {animatablePropertyKeyframes = updatedKeyframes}
                            else updatedProp
                        in
                          updatedPropWithKeyframe
                        )
                    _ -> Nothing
              
              else if normalizedPath == "origin"
                then
                  -- Convert PropertyValue to Position2DOr3D
                  case value of
                    PropertyValuePosition2DOr3D (Vec2 x y) mz ->
                      let
                        posValue = Position2DOr3D x y mz
                      in
                        updatePropertyInLayer layer propertyPath (\prop ->
                          let
                            updatedProp = prop {animatablePropertyValue = posValue}
                            updatedPropWithKeyframe = if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                              then
                                let
                                  keyframes = animatablePropertyKeyframes prop
                                  mKeyframeAtFrame = find (\k -> keyframeFrame k == currentFrame) keyframes
                                in
                                  case mKeyframeAtFrame of
                                    Nothing -> updatedProp
                                    Just kf ->
                                      let
                                        updatedKeyframes = map (\k -> if keyframeId k == keyframeId kf then k {keyframeValue = posValue} else k) keyframes
                                      in
                                        updatedProp {animatablePropertyKeyframes = updatedKeyframes}
                              else updatedProp
                          in
                            updatedPropWithKeyframe
                          )
                    _ -> Nothing
              
              else if propertyPath == "opacity"
                then
                  -- Convert PropertyValue to Double
                  case value of
                    PropertyValueNumber d ->
                      updatePropertyInLayer layer propertyPath (\prop ->
                        let
                          updatedProp = prop {animatablePropertyValue = d}
                          updatedPropWithKeyframe = if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                            then
                              let
                                keyframes = animatablePropertyKeyframes prop
                                mKeyframeAtFrame = find (\k -> keyframeFrame k == currentFrame) keyframes
                              in
                                case mKeyframeAtFrame of
                                  Nothing -> updatedProp
                                  Just kf ->
                                    let
                                      updatedKeyframes = map (\k -> if keyframeId k == keyframeId kf then k {keyframeValue = d} else k) keyframes
                                    in
                                      updatedProp {animatablePropertyKeyframes = updatedKeyframes}
                            else updatedProp
                        in
                          updatedPropWithKeyframe
                        )
                    _ -> Nothing
              
              else Nothing
          in
            case mUpdatedLayer of
              Nothing -> Right layers
              Just updatedLayer ->
                let
                  updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
                in
                  Right updatedLayers

-- ============================================================================
-- PROPERTY ANIMATION STATE OPERATIONS
-- ============================================================================

-- | Set a property's animated state
-- Pure function: takes layer ID, property path, animated flag, current frame, ID generator, and layers list
-- Returns updated layers list or error
-- If enabling animation and no keyframes exist, adds a keyframe at current frame
setPropertyAnimated ::
  Text -> -- Layer ID
  Text -> -- Property path
  Bool -> -- Animated flag
  Double -> -- Current frame (for adding keyframe if enabling animation)
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setPropertyAnimated layerId propertyPath animated currentFrame genId layers =
  case getLayerById layerId layers of
    Nothing -> Right layers
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Right layers
        Just prop ->
          let
            normalizedPath = T.replace "transform." "" propertyPath
            transform = layerTransform layer
            
            -- Update property animated state
            updatePropertyAnimatedInLayer =
              if normalizedPath == "position"
                then
                  let
                    updatedProp = setPropertyAnimated (transformPosition transform) animated
                    -- If enabling animation and no keyframes, add one at current frame
                    finalProp = if animated && null (animatablePropertyKeyframes updatedProp)
                      then
                        let
                          -- Ensure currentFrame is >= 1
                          safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
                          frame = safeFrame (Just safeCurrentFrame) safeCurrentFrame
                          keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor frame)))
                          mKeyframe = createKeyframe keyframeId frame (animatablePropertyValue updatedProp) InterpolationLinear
                        in
                          case mKeyframe of
                            Left _ -> updatedProp
                            Right kf -> updatedProp {animatablePropertyKeyframes = [kf]}
                      else updatedProp
                    newTransform = transform {transformPosition = finalProp}
                    newLayer = layer {layerTransform = newTransform}
                  in
                    newLayer
                else if normalizedPath == "scale"
                  then
                    let
                      updatedProp = setPropertyAnimated (transformScale transform) animated
                      finalProp = if animated && null (animatablePropertyKeyframes updatedProp)
                        then
                          let
                            safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
                            frame = safeFrame (Just safeCurrentFrame) safeCurrentFrame
                            keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor frame)))
                            mKeyframe = createKeyframe keyframeId frame (animatablePropertyValue updatedProp) InterpolationLinear
                          in
                            case mKeyframe of
                              Left _ -> updatedProp
                              Right kf -> updatedProp {animatablePropertyKeyframes = [kf]}
                        else updatedProp
                      newTransform = transform {transformScale = finalProp}
                      newLayer = layer {layerTransform = newTransform}
                    in
                      newLayer
                  else if normalizedPath == "rotation"
                    then
                      let
                        updatedProp = setPropertyAnimated (transformRotation transform) animated
                        finalProp = if animated && null (animatablePropertyKeyframes updatedProp)
                          then
                            let
                              safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
                              frame = safeFrame (Just safeCurrentFrame) safeCurrentFrame
                              keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor frame)))
                              mKeyframe = createKeyframe keyframeId frame (animatablePropertyValue updatedProp) InterpolationLinear
                            in
                              case mKeyframe of
                                Left _ -> updatedProp
                                Right kf -> updatedProp {animatablePropertyKeyframes = [kf]}
                          else updatedProp
                        newTransform = transform {transformRotation = finalProp}
                        newLayer = layer {layerTransform = newTransform}
                      in
                        newLayer
                    else if normalizedPath == "anchorPoint"
                      then
                        case transformAnchorPoint transform of
                          Nothing -> layer
                          Just anchorProp ->
                            let
                              updatedProp = setPropertyAnimated anchorProp animated
                              finalProp = if animated && null (animatablePropertyKeyframes updatedProp)
                                then
                                  let
                                    safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
                                    frame = safeFrame (Just safeCurrentFrame) safeCurrentFrame
                                    keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor frame)))
                                    mKeyframe = createKeyframe keyframeId frame (animatablePropertyValue updatedProp) InterpolationLinear
                                  in
                                    case mKeyframe of
                                      Left _ -> updatedProp
                                      Right kf -> updatedProp {animatablePropertyKeyframes = [kf]}
                                else updatedProp
                              newTransform = transform {transformAnchorPoint = Just finalProp}
                              newLayer = layer {layerTransform = newTransform}
                            in
                              newLayer
                      else if normalizedPath == "origin"
                        then
                          let
                            updatedProp = setPropertyAnimated (transformOrigin transform) animated
                            finalProp = if animated && null (animatablePropertyKeyframes updatedProp)
                              then
                                let
                                  safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
                                  frame = safeFrame (Just safeCurrentFrame) safeCurrentFrame
                                  keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor frame)))
                                  mKeyframe = createKeyframe keyframeId frame (animatablePropertyValue updatedProp) InterpolationLinear
                                in
                                  case mKeyframe of
                                    Left _ -> updatedProp
                                    Right kf -> updatedProp {animatablePropertyKeyframes = [kf]}
                              else updatedProp
                            newTransform = transform {transformOrigin = finalProp}
                            newLayer = layer {layerTransform = newTransform}
                          in
                            newLayer
                        else if propertyPath == "opacity"
                          then
                            let
                              updatedProp = setPropertyAnimated (layerOpacity layer) animated
                              finalProp = if animated && null (animatablePropertyKeyframes updatedProp)
                                then
                                  let
                                    safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
                                    frame = safeFrame (Just safeCurrentFrame) safeCurrentFrame
                                    keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor frame)))
                                    mKeyframe = createKeyframe keyframeId frame (animatablePropertyValue updatedProp) InterpolationLinear
                                  in
                                    case mKeyframe of
                                      Left _ -> updatedProp
                                      Right kf -> updatedProp {animatablePropertyKeyframes = [kf]}
                                else updatedProp
                              newLayer = layer {layerOpacity = finalProp}
                            in
                              newLayer
                          else
                            -- Unknown property path
                            layer
            
            updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
            updatedLayer = updatePropertyAnimatedInLayer
          in
            Right updatedLayers
