-- |
-- Module      : Lattice.State.Keyframe.CRUD
-- Description : CRUD operations for keyframes
--
-- Migrated from ui/src/stores/keyframeStore/crud.ts
-- Pure functions for adding, removing, moving, and updating keyframes
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.CRUD
  ( -- Type-specific functions (for type safety)
    addKeyframeToPositionProperty
  , addKeyframeToVec3Property
  , addKeyframeToDoubleProperty
  -- Generic PropertyValue-based function (for convenience)
  , addKeyframeWithPropertyValue
  -- Other CRUD operations
  , removeKeyframe
  , clearKeyframes
  , moveKeyframe
  , setKeyframeValue
  , updateKeyframe
  ) where

import Data.List (find, findIndex, sortBy)
import Data.Maybe (Maybe(..), isJust)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.Helpers (safeFrame)
import Lattice.State.Keyframe.PropertyUpdate
  ( updateKeyframesInProperty
  , setPropertyAnimated
  )
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( Keyframe(..)
  , InterpolationType(..)
  , PropertyValue(..)
  , createKeyframe
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives
  ( Position2DOr3D(..)
  , Vec2(..)
  , Vec3(..)
  , validateFinite
  )
import Lattice.Types.Transform (LayerTransform(..))

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // helper // functions // for // property // updates
-- ════════════════════════════════════════════════════════════════════════════

-- | Add keyframe to a Position2DOr3D property
addKeyframeToPositionProperty ::
  Text -> -- Layer ID
  Text -> -- Property path (for error messages)
  Position2DOr3D -> -- Value
  Double -> -- Frame
  (Text -> Text) -> -- ID generator
  Layer -> -- Current layer
  Either Text (Keyframe Position2DOr3D, Layer)
addKeyframeToPositionProperty layerId propertyPath value frame genId layer =
  -- Validate frame is >= 1
  -- Frames start at 1, not 0
  if not (validateFinite frame) || frame < 1
    then Left ("addKeyframeToPositionProperty: Invalid frame value (must be finite and >= 1): " <> T.pack (show frame))
    else
      let
        -- Defensive clamp: frame already validated above (>= 1), but clamp ensures determinism
        -- This is defensive programming - if validation logic changes, this prevents invalid frames
        clampedFrame = max 1.0 frame
        keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor clampedFrame)))
        mKeyframe = createKeyframe keyframeId clampedFrame value InterpolationLinear
        transform = layerTransform layer
        normalizedPath = T.replace "transform." "" propertyPath
      in
        case mKeyframe of
          Left err -> Left err
          Right keyframe ->
            let
              -- Update property based on path
              (updatedTransform, updatedLayer) =
                if normalizedPath == "position"
                  then
                    let
                      prop = transformPosition transform
                      updatedProp = updateKeyframesInProperty prop (\kfs ->
                        let
                          existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                        in
                          case existingIndex of
                            Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                            Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                      )
                      newTransform = transform {transformPosition = updatedProp}
                      newLayer = layer {layerTransform = newTransform}
                in
                  (newTransform, newLayer)
              else if normalizedPath == "origin"
                then
                  let
                    prop = transformOrigin transform
                    updatedProp = updateKeyframesInProperty prop (\kfs ->
                      let
                        existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                      in
                        case existingIndex of
                          Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                          Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                    )
                    newTransform = transform {transformOrigin = updatedProp}
                    newLayer = layer {layerTransform = newTransform}
                  in
                    (newTransform, newLayer)
                else if normalizedPath == "anchorPoint"
                  then
                    case transformAnchorPoint transform of
                      Nothing -> (transform, layer) -- Property doesn't exist
                      Just prop ->
                        let
                          updatedProp = updateKeyframesInProperty prop (\kfs ->
                            let
                              existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                            in
                              case existingIndex of
                                Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                                Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                          )
                          newTransform = transform {transformAnchorPoint = Just updatedProp}
                          newLayer = layer {layerTransform = newTransform}
                        in
                          (newTransform, newLayer)
                  else
                    (transform, layer) -- Unknown property path
        in
          Right (keyframe, updatedLayer)

-- | Add keyframe to a Vec3 property
addKeyframeToVec3Property ::
  Text -> -- Layer ID
  Text -> -- Property path
  Vec3 -> -- Value
  Double -> -- Frame
  (Text -> Text) -> -- ID generator
  Layer -> -- Current layer
  Either Text (Keyframe Vec3, Layer)
addKeyframeToVec3Property layerId propertyPath value frame genId layer =
  -- Validate frame is >= 1
  -- Frames start at 1, not 0
  if not (validateFinite frame) || frame < 1
    then Left ("addKeyframeToVec3Property: Invalid frame value (must be finite and >= 1): " <> T.pack (show frame))
    else
      let
        -- Defensive clamp: frame already validated above (>= 1), but clamp ensures determinism
        -- This is defensive programming - if validation logic changes, this prevents invalid frames
        clampedFrame = max 1.0 frame
        keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor clampedFrame)))
        mKeyframe = createKeyframe keyframeId clampedFrame value InterpolationLinear
        transform = layerTransform layer
        normalizedPath = T.replace "transform." "" propertyPath
      in
        case mKeyframe of
          Left err -> Left err
          Right keyframe ->
            let
              (updatedTransform, updatedLayer) =
            if normalizedPath == "scale"
              then
                let
                  prop = transformScale transform
                  updatedProp = updateKeyframesInProperty prop (\kfs ->
                    let
                      existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                    in
                      case existingIndex of
                        Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                        Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                  )
                  newTransform = transform {transformScale = updatedProp}
                  newLayer = layer {layerTransform = newTransform}
                in
                  (newTransform, newLayer)
              else if normalizedPath == "orientation"
                then
                  case transformOrientation transform of
                    Nothing -> (transform, layer)
                    Just prop ->
                      let
                        updatedProp = updateKeyframesInProperty prop (\kfs ->
                          let
                            existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                          in
                            case existingIndex of
                              Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                              Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                        )
                        newTransform = transform {transformOrientation = Just updatedProp}
                        newLayer = layer {layerTransform = newTransform}
                      in
                        (newTransform, newLayer)
                else
                  (transform, layer)
        in
          Right (keyframe, updatedLayer)

-- | Add keyframe to a Double property
addKeyframeToDoubleProperty ::
  Text -> -- Layer ID
  Text -> -- Property path
  Double -> -- Value
  Double -> -- Frame
  (Text -> Text) -> -- ID generator
  Layer -> -- Current layer
  Either Text (Keyframe Double, Layer)
addKeyframeToDoubleProperty layerId propertyPath value frame genId layer =
  -- Validate frame is >= 1
  -- Frames start at 1, not 0
  if not (validateFinite frame) || frame < 1
    then Left ("addKeyframeToDoubleProperty: Invalid frame value (must be finite and >= 1): " <> T.pack (show frame))
    else
      let
        -- Defensive clamp: frame already validated above (>= 1), but clamp ensures determinism
        -- This is defensive programming - if validation logic changes, this prevents invalid frames
        clampedFrame = max 1.0 frame
        keyframeId = genId ("kf_" <> layerId <> "_" <> propertyPath <> "_" <> T.pack (show (floor clampedFrame)))
        mKeyframe = createKeyframe keyframeId clampedFrame value InterpolationLinear
        transform = layerTransform layer
        normalizedPath = T.replace "transform." "" propertyPath
      in
        case mKeyframe of
          Left err -> Left err
          Right keyframe ->
            let
              updatedLayer =
            if normalizedPath == "rotation"
              then
                let
                  prop = transformRotation transform
                  updatedProp = updateKeyframesInProperty prop (\kfs ->
                    let
                      existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                    in
                      case existingIndex of
                        Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                        Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                  )
                  newTransform = transform {transformRotation = updatedProp}
                in
                  layer {layerTransform = newTransform}
              else if propertyPath == "opacity"
                then
                  let
                    prop = layerOpacity layer
                    updatedProp = updateKeyframesInProperty prop (\kfs ->
                      let
                        existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                      in
                        case existingIndex of
                          Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                          Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                    )
                  in
                    layer {layerOpacity = updatedProp}
                else if normalizedPath == "rotationX"
                  then
                    case transformRotationX transform of
                      Nothing -> layer
                      Just prop ->
                        let
                          updatedProp = updateKeyframesInProperty prop (\kfs ->
                            let
                              existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                            in
                              case existingIndex of
                                Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                                Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                          )
                          newTransform = transform {transformRotationX = Just updatedProp}
                        in
                          layer {layerTransform = newTransform}
                  else if normalizedPath == "rotationY"
                    then
                      case transformRotationY transform of
                        Nothing -> layer
                        Just prop ->
                          let
                            updatedProp = updateKeyframesInProperty prop (\kfs ->
                              let
                                existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                              in
                                case existingIndex of
                                  Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                                  Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                            )
                            newTransform = transform {transformRotationY = Just updatedProp}
                          in
                            layer {layerTransform = newTransform}
                    else if normalizedPath == "rotationZ"
                      then
                        case transformRotationZ transform of
                          Nothing -> layer
                          Just prop ->
                            let
                              updatedProp = updateKeyframesInProperty prop (\kfs ->
                                let
                                  existingIndex = findIndex (\k -> keyframeFrame k == clampedFrame) kfs
                                in
                                  case existingIndex of
                                    Just idx -> take idx kfs ++ [keyframe] ++ drop (idx + 1) kfs
                                    Nothing -> sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) (keyframe : kfs)
                              )
                              newTransform = transform {transformRotationZ = Just updatedProp}
                            in
                              layer {layerTransform = newTransform}
                      else
                        layer -- Unknown property path
        in
          Right (keyframe, updatedLayer)

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // keyframe // creation
-- ════════════════════════════════════════════════════════════════════════════

-- | Add a keyframe using PropertyValue (convenience function)
-- Pure function: converts PropertyValue to appropriate type and calls type-specific function
-- Returns created keyframe and updated layers list or error
addKeyframeWithPropertyValue ::
  Text -> -- Layer ID
  Text -> -- Property path
  PropertyValue -> -- Value (will be converted to appropriate type)
  Maybe Double -> -- Frame (Nothing = use current frame)
  Double -> -- Current frame (fallback)
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text (Keyframe PropertyValue, [Layer]) -- Returns created keyframe and updated layers
addKeyframeWithPropertyValue layerId propertyPath propValue mAtFrame currentFrame genId layers =
  case getLayerById layerId layers of
    Nothing -> Left ("Cannot add keyframe: Layer \"" <> T.unpack layerId <> "\" not found")
    Just layer ->
      let
        normalizedPath = T.replace "transform." "" propertyPath
        -- Ensure currentFrame is >= 1
        -- Frames start at 1, not 0
        safeCurrentFrame = if validateFinite currentFrame && currentFrame >= 1 then currentFrame else 1.0
        frame = safeFrame mAtFrame safeCurrentFrame
      in
        -- Route to appropriate type-specific function based on property path
        if normalizedPath == "position" || normalizedPath == "origin" || normalizedPath == "anchorPoint"
          then
            -- Convert PropertyValue to Position2DOr3D
            case propValue of
              PropertyValuePosition2DOr3D (Vec2 x y) mz ->
                let
                  pos = Position2DOr3D x y mz
                  -- Frame already validated by safeFrame (>= 1)
                  result = addKeyframeToPositionProperty layerId propertyPath pos frame genId layer
                in
                  case result of
                    Left err -> Left err
                    Right (kf, updatedLayer) ->
                      -- Convert keyframe back to PropertyValue
                      let
                        propKf = kf {keyframeValue = propValue}
                        updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
                      in
                        Right (propKf, updatedLayers)
              _ -> Left ("addKeyframeWithPropertyValue: PropertyValue must be Position2DOr3D for property: " <> T.unpack propertyPath)
          else if normalizedPath == "scale" || normalizedPath == "orientation"
            then
              -- Convert PropertyValue to Vec3
              case propValue of
                PropertyValueVec3 (Vec3 x y z) ->
                  let
                    vec = Vec3 x y z
                    -- Frame already validated by safeFrame (>= 1)
                    result = addKeyframeToVec3Property layerId propertyPath vec frame genId layer
                  in
                    case result of
                      Left err -> Left err
                      Right (kf, updatedLayer) ->
                        let
                          propKf = kf {keyframeValue = propValue}
                          updatedLayers = map (\l -> if layerId l == layerId then updatedLayer else l) layers
                        in
                          Right (propKf, updatedLayers)
                _ -> Left ("addKeyframeWithPropertyValue: PropertyValue must be Vec3 for property: " <> T.unpack propertyPath)
            else
              -- Convert PropertyValue to Double
              case propValue of
                PropertyValueNumber d ->
                  let
                    -- Frame already validated by safeFrame (>= 1)
                    result = addKeyframeToDoubleProperty layerId propertyPath d frame genId layer
                  in
                    case result of
                      Left err -> Left err
                      Right (kf, updatedLayer) ->
                        let
                          propKf = kf {keyframeValue = propValue}
                          updatedLayers = map (\l -> if layerId l == layerId then updatedLayer else l) layers
                        in
                          Right (propKf, updatedLayers)
                _ -> Left ("addKeyframeWithPropertyValue: PropertyValue must be Number for property: " <> T.unpack propertyPath)

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // keyframe // removal
-- ════════════════════════════════════════════════════════════════════════════

-- | Remove a keyframe by ID from a Position2DOr3D property
removeKeyframeFromPositionProperty ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Layer -> -- Current layer
  Either Text Layer -- Updated layer or error
removeKeyframeFromPositionProperty layerId propertyPath keyframeId layer =
  let
    normalizedPath = T.replace "transform." "" propertyPath
    transform = layerTransform layer
    
    updateProperty prop =
      let
        keyframes = animatablePropertyKeyframes prop
        filteredKeyframes = filter (\k -> keyframeId k /= keyframeId) keyframes
        updatedProp = prop
          { animatablePropertyKeyframes = filteredKeyframes
          , animatablePropertyAnimated = not (null filteredKeyframes)
          }
      in
        updatedProp
    
    (updatedTransform, updatedLayer) =
      if normalizedPath == "position"
        then
          let
            prop = transformPosition transform
            updatedProp = updateProperty prop
            newTransform = transform {transformPosition = updatedProp}
            newLayer = layer {layerTransform = newTransform}
          in
            (newTransform, newLayer)
        else if normalizedPath == "origin"
          then
            let
              prop = transformOrigin transform
              updatedProp = updateProperty prop
              newTransform = transform {transformOrigin = updatedProp}
              newLayer = layer {layerTransform = newTransform}
            in
              (newTransform, newLayer)
          else if normalizedPath == "anchorPoint"
            then
              case transformAnchorPoint transform of
                Nothing -> (transform, layer)
                Just prop ->
                  let
                    updatedProp = updateProperty prop
                    newTransform = transform {transformAnchorPoint = Just updatedProp}
                    newLayer = layer {layerTransform = newTransform}
                  in
                    (newTransform, newLayer)
            else
              (transform, layer)
  in
    Right updatedLayer

-- | Remove a keyframe by ID from a Vec3 property
removeKeyframeFromVec3Property ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Layer -> -- Current layer
  Either Text Layer -- Updated layer or error
removeKeyframeFromVec3Property layerId propertyPath keyframeId layer =
  let
    normalizedPath = T.replace "transform." "" propertyPath
    transform = layerTransform layer
    
    updateProperty prop =
      let
        keyframes = animatablePropertyKeyframes prop
        filteredKeyframes = filter (\k -> keyframeId k /= keyframeId) keyframes
        updatedProp = prop
          { animatablePropertyKeyframes = filteredKeyframes
          , animatablePropertyAnimated = not (null filteredKeyframes)
          }
      in
        updatedProp
    
    (updatedTransform, updatedLayer) =
      if normalizedPath == "scale"
        then
          let
            prop = transformScale transform
            updatedProp = updateProperty prop
            newTransform = transform {transformScale = updatedProp}
            newLayer = layer {layerTransform = newTransform}
          in
            (newTransform, newLayer)
        else if normalizedPath == "orientation"
          then
            case transformOrientation transform of
              Nothing -> (transform, layer)
              Just prop ->
                let
                  updatedProp = updateProperty prop
                  newTransform = transform {transformOrientation = Just updatedProp}
                  newLayer = layer {layerTransform = newTransform}
                in
                  (newTransform, newLayer)
          else
            (transform, layer)
  in
    Right updatedLayer

-- | Remove a keyframe by ID from a Double property
removeKeyframeFromDoubleProperty ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Layer -> -- Current layer
  Either Text Layer -- Updated layer or error
removeKeyframeFromDoubleProperty layerId propertyPath keyframeId layer =
  let
    normalizedPath = T.replace "transform." "" propertyPath
    transform = layerTransform layer
    
    updateProperty prop =
      let
        keyframes = animatablePropertyKeyframes prop
        filteredKeyframes = filter (\k -> keyframeId k /= keyframeId) keyframes
        updatedProp = prop
          { animatablePropertyKeyframes = filteredKeyframes
          , animatablePropertyAnimated = not (null filteredKeyframes)
          }
      in
        updatedProp
    
    updatedLayer =
      if normalizedPath == "rotation"
        then
          let
            prop = transformRotation transform
            updatedProp = updateProperty prop
            newTransform = transform {transformRotation = updatedProp}
          in
            layer {layerTransform = newTransform}
        else if propertyPath == "opacity"
          then
            let
              prop = layerOpacity layer
              updatedProp = updateProperty prop
            in
              layer {layerOpacity = updatedProp}
          else if normalizedPath == "rotationX"
            then
              case transformRotationX transform of
                Nothing -> layer
                Just prop ->
                  let
                    updatedProp = updateProperty prop
                    newTransform = transform {transformRotationX = Just updatedProp}
                  in
                    layer {layerTransform = newTransform}
            else if normalizedPath == "rotationY"
              then
                case transformRotationY transform of
                  Nothing -> layer
                  Just prop ->
                    let
                      updatedProp = updateProperty prop
                      newTransform = transform {transformRotationY = Just updatedProp}
                    in
                      layer {layerTransform = newTransform}
              else if normalizedPath == "rotationZ"
                then
                  case transformRotationZ transform of
                    Nothing -> layer
                    Just prop ->
                      let
                        updatedProp = updateProperty prop
                        newTransform = transform {transformRotationZ = Just updatedProp}
                      in
                        layer {layerTransform = newTransform}
                else
                  layer
  in
    Right updatedLayer

-- | Remove a keyframe by ID
-- Pure function: takes layer ID, property path, keyframe ID, and layers list
-- Returns updated layers list or error
removeKeyframe ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
removeKeyframe layerId propertyPath keyframeId layers =
  case getLayerById layerId layers of
    Nothing -> Right layers -- Layer not found, return unchanged
    Just layer ->
      let
        normalizedPath = T.replace "transform." "" propertyPath
        result =
          if normalizedPath == "position" || normalizedPath == "origin" || normalizedPath == "anchorPoint"
            then removeKeyframeFromPositionProperty layerId propertyPath keyframeId layer
            else if normalizedPath == "scale" || normalizedPath == "orientation"
              then removeKeyframeFromVec3Property layerId propertyPath keyframeId layer
              else removeKeyframeFromDoubleProperty layerId propertyPath keyframeId layer
      in
        case result of
          Left err -> Left err
          Right updatedLayer ->
            let
              updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
            in
              Right updatedLayers

-- | Clear all keyframes from a property
-- Pure function: takes layer ID, property path, and layers list
-- Returns updated layers list or error
clearKeyframes ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
clearKeyframes layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> Right layers -- Layer not found, return unchanged
    Just layer ->
      let
        normalizedPath = T.replace "transform." "" propertyPath
        transform = layerTransform layer
        
        clearProperty prop = prop
          { animatablePropertyKeyframes = []
          , animatablePropertyAnimated = False
          }
        
        updatedLayer =
          if normalizedPath == "position"
            then
              let
                prop = transformPosition transform
                updatedProp = clearProperty prop
                newTransform = transform {transformPosition = updatedProp}
              in
                layer {layerTransform = newTransform}
            else if normalizedPath == "scale"
              then
                let
                  prop = transformScale transform
                  updatedProp = clearProperty prop
                  newTransform = transform {transformScale = updatedProp}
                in
                  layer {layerTransform = newTransform}
              else if normalizedPath == "rotation"
                then
                  let
                    prop = transformRotation transform
                    updatedProp = clearProperty prop
                    newTransform = transform {transformRotation = updatedProp}
                  in
                    layer {layerTransform = newTransform}
                else if normalizedPath == "origin"
                  then
                    let
                      prop = transformOrigin transform
                      updatedProp = clearProperty prop
                      newTransform = transform {transformOrigin = updatedProp}
                    in
                      layer {layerTransform = newTransform}
                  else if normalizedPath == "anchorPoint"
                    then
                      case transformAnchorPoint transform of
                        Nothing -> layer
                        Just prop ->
                          let
                            updatedProp = clearProperty prop
                            newTransform = transform {transformAnchorPoint = Just updatedProp}
                          in
                            layer {layerTransform = newTransform}
                    else if propertyPath == "opacity"
                      then
                        let
                          prop = layerOpacity layer
                          updatedProp = clearProperty prop
                        in
                          layer {layerOpacity = updatedProp}
                      else if normalizedPath == "rotationX"
                        then
                          case transformRotationX transform of
                            Nothing -> layer
                            Just prop ->
                              let
                                updatedProp = clearProperty prop
                                newTransform = transform {transformRotationX = Just updatedProp}
                              in
                                layer {layerTransform = newTransform}
                        else if normalizedPath == "rotationY"
                          then
                            case transformRotationY transform of
                              Nothing -> layer
                              Just prop ->
                                let
                                  updatedProp = clearProperty prop
                                  newTransform = transform {transformRotationY = Just updatedProp}
                                in
                                  layer {layerTransform = newTransform}
                          else if normalizedPath == "rotationZ"
                            then
                              case transformRotationZ transform of
                                Nothing -> layer
                                Just prop ->
                                  let
                                    updatedProp = clearProperty prop
                                    newTransform = transform {transformRotationZ = Just updatedProp}
                                  in
                                    layer {layerTransform = newTransform}
                            else if normalizedPath == "orientation"
                              then
                                case transformOrientation transform of
                                  Nothing -> layer
                                  Just prop ->
                                    let
                                      updatedProp = clearProperty prop
                                      newTransform = transform {transformOrientation = Just updatedProp}
                                    in
                                      layer {layerTransform = newTransform}
                              else
                                layer -- Unknown property path
        
        updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
      in
        Right updatedLayers

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // keyframe // movement
-- ════════════════════════════════════════════════════════════════════════════

-- | Move a keyframe to a new frame position
-- Pure function: takes layer ID, property path, keyframe ID, new frame, and layers list
-- Returns updated layers list or error
-- Handles collisions: if keyframe exists at target frame, removes it first
moveKeyframe ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Double -> -- New frame
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
moveKeyframe layerId propertyPath keyframeId newFrame layers =
  -- Validate frame is finite and >= 1
  -- Frames start at 1, not 0
  if not (validateFinite newFrame) || newFrame < 1
    then Left ("moveKeyframe: Invalid frame value (must be finite and >= 1): " <> T.pack (show newFrame))
    else
      let
        -- Clamp frame to minimum (>= 1)
        -- Shouldn't happen after validation, but ensures determinism
        clampedFrame = max 1.0 newFrame
      in
        case getLayerById layerId layers of
          Nothing -> Right layers
          Just layer ->
            let
              normalizedPath = T.replace "transform." "" propertyPath
              transform = layerTransform layer
              
              -- Helper to move keyframe in a property
              moveKeyframeInProperty prop =
                let
                  keyframes = animatablePropertyKeyframes prop
                  mKeyframe = find (\k -> keyframeId k == keyframeId) keyframes
                in
                  case mKeyframe of
                    Nothing -> prop -- Keyframe not found
                    Just kf ->
                      let
                        -- Remove existing keyframe at target frame (if different from moving keyframe)
                        filteredKeyframes = filter (\k -> 
                          not (keyframeFrame k == clampedFrame && keyframeId k /= keyframeId)
                        ) keyframes
                        
                        -- Update keyframe frame
                        updatedKeyframe = kf {keyframeFrame = clampedFrame}
                      
                      -- Replace old keyframe with updated one
                      updatedKeyframes = map (\k -> 
                        if keyframeId k == keyframeId then updatedKeyframe else k
                      ) filteredKeyframes
                      
                      -- Sort by frame
                      sortedKeyframes = sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) updatedKeyframes
                    in
                      prop
                        { animatablePropertyKeyframes = sortedKeyframes
                        }
            
            updatedLayer =
              if normalizedPath == "position"
                then
                  let
                    prop = transformPosition transform
                    updatedProp = moveKeyframeInProperty prop
                    newTransform = transform {transformPosition = updatedProp}
                  in
                    layer {layerTransform = newTransform}
                else if normalizedPath == "scale"
                  then
                    let
                      prop = transformScale transform
                      updatedProp = moveKeyframeInProperty prop
                      newTransform = transform {transformScale = updatedProp}
                    in
                      layer {layerTransform = newTransform}
                  else if normalizedPath == "rotation"
                    then
                      let
                        prop = transformRotation transform
                        updatedProp = moveKeyframeInProperty prop
                        newTransform = transform {transformRotation = updatedProp}
                      in
                        layer {layerTransform = newTransform}
                    else if normalizedPath == "origin"
                      then
                        let
                          prop = transformOrigin transform
                          updatedProp = moveKeyframeInProperty prop
                          newTransform = transform {transformOrigin = updatedProp}
                        in
                          layer {layerTransform = newTransform}
                      else if normalizedPath == "anchorPoint"
                        then
                          case transformAnchorPoint transform of
                            Nothing -> layer
                            Just prop ->
                              let
                                updatedProp = moveKeyframeInProperty prop
                                newTransform = transform {transformAnchorPoint = Just updatedProp}
                              in
                                layer {layerTransform = newTransform}
                        else if propertyPath == "opacity"
                          then
                            let
                              prop = layerOpacity layer
                              updatedProp = moveKeyframeInProperty prop
                            in
                              layer {layerOpacity = updatedProp}
                          else if normalizedPath == "rotationX"
                            then
                              case transformRotationX transform of
                                Nothing -> layer
                                Just prop ->
                                  let
                                    updatedProp = moveKeyframeInProperty prop
                                    newTransform = transform {transformRotationX = Just updatedProp}
                                  in
                                    layer {layerTransform = newTransform}
                            else if normalizedPath == "rotationY"
                              then
                                case transformRotationY transform of
                                  Nothing -> layer
                                  Just prop ->
                                    let
                                      updatedProp = moveKeyframeInProperty prop
                                      newTransform = transform {transformRotationY = Just updatedProp}
                                    in
                                      layer {layerTransform = newTransform}
                              else if normalizedPath == "rotationZ"
                                then
                                  case transformRotationZ transform of
                                    Nothing -> layer
                                    Just prop ->
                                      let
                                        updatedProp = moveKeyframeInProperty prop
                                        newTransform = transform {transformRotationZ = Just updatedProp}
                                      in
                                        layer {layerTransform = newTransform}
                                else if normalizedPath == "orientation"
                                  then
                                    case transformOrientation transform of
                                      Nothing -> layer
                                      Just prop ->
                                        let
                                          updatedProp = moveKeyframeInProperty prop
                                          newTransform = transform {transformOrientation = Just updatedProp}
                                        in
                                          layer {layerTransform = newTransform}
                                  else
                                    layer -- Unknown property path
            
            updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
          in
            Right updatedLayers

-- ════════════════════════════════════════════════════════════════════════════
--                                              // keyframe // value // updates
-- ════════════════════════════════════════════════════════════════════════════

-- | Update a keyframe's value
-- Pure function: takes layer ID, property path, keyframe ID, new value, and layers list
-- Returns updated layers list or error
--                                                                      // note
setKeyframeValue ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  a -> -- New value (type must match property)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setKeyframeValue layerId propertyPath keyframeId newValue layers =
  case getLayerById layerId layers of
    Nothing -> Right layers
    Just layer ->
      let
        normalizedPath = T.replace "transform." "" propertyPath
        transform = layerTransform layer
        
        -- Helper to update keyframe value in a property
        updateKeyframeValueInProperty prop =
          let
            keyframes = animatablePropertyKeyframes prop
            updatedKeyframes = map (\k -> 
              if keyframeId k == keyframeId 
                then k {keyframeValue = newValue}
                else k
            ) keyframes
          in
            prop {animatablePropertyKeyframes = updatedKeyframes}
        
        updatedLayer =
          if normalizedPath == "position"
            then
              let
                prop = transformPosition transform
                updatedProp = updateKeyframeValueInProperty prop
                newTransform = transform {transformPosition = updatedProp}
              in
                layer {layerTransform = newTransform}
            else if normalizedPath == "scale"
              then
                let
                  prop = transformScale transform
                  updatedProp = updateKeyframeValueInProperty prop
                  newTransform = transform {transformScale = updatedProp}
                in
                  layer {layerTransform = newTransform}
              else if normalizedPath == "rotation"
                then
                  let
                    prop = transformRotation transform
                    updatedProp = updateKeyframeValueInProperty prop
                    newTransform = transform {transformRotation = updatedProp}
                  in
                    layer {layerTransform = newTransform}
                else if normalizedPath == "origin"
                  then
                    let
                      prop = transformOrigin transform
                      updatedProp = updateKeyframeValueInProperty prop
                      newTransform = transform {transformOrigin = updatedProp}
                    in
                      layer {layerTransform = newTransform}
                  else if normalizedPath == "anchorPoint"
                    then
                      case transformAnchorPoint transform of
                        Nothing -> layer
                        Just prop ->
                          let
                            updatedProp = updateKeyframeValueInProperty prop
                            newTransform = transform {transformAnchorPoint = Just updatedProp}
                          in
                            layer {layerTransform = newTransform}
                    else if propertyPath == "opacity"
                      then
                        let
                          prop = layerOpacity layer
                          updatedProp = updateKeyframeValueInProperty prop
                        in
                          layer {layerOpacity = updatedProp}
                      else if normalizedPath == "rotationX"
                        then
                          case transformRotationX transform of
                            Nothing -> layer
                            Just prop ->
                              let
                                updatedProp = updateKeyframeValueInProperty prop
                                newTransform = transform {transformRotationX = Just updatedProp}
                              in
                                layer {layerTransform = newTransform}
                        else if normalizedPath == "rotationY"
                          then
                            case transformRotationY transform of
                              Nothing -> layer
                              Just prop ->
                                let
                                  updatedProp = updateKeyframeValueInProperty prop
                                  newTransform = transform {transformRotationY = Just updatedProp}
                                in
                                  layer {layerTransform = newTransform}
                          else if normalizedPath == "rotationZ"
                            then
                              case transformRotationZ transform of
                                Nothing -> layer
                                Just prop ->
                                  let
                                    updatedProp = updateKeyframeValueInProperty prop
                                    newTransform = transform {transformRotationZ = Just updatedProp}
                                  in
                                    layer {layerTransform = newTransform}
                            else if normalizedPath == "orientation"
                              then
                                case transformOrientation transform of
                                  Nothing -> layer
                                  Just prop ->
                                    let
                                      updatedProp = updateKeyframeValueInProperty prop
                                      newTransform = transform {transformOrientation = Just updatedProp}
                                    in
                                      layer {layerTransform = newTransform}
                              else
                                layer -- Unknown property path
        
        updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
      in
        Right updatedLayers

-- | Update keyframe frame position and/or value
-- Pure function: takes layer ID, property path, keyframe ID, updates, and layers list
-- Returns updated layers list or error
-- Handles collisions: if updating frame and keyframe exists at target, removes it first
updateKeyframe ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Maybe Double -> -- New frame (Nothing = don't change)
  Maybe a -> -- New value (Nothing = don't change)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
updateKeyframe layerId propertyPath keyframeId mNewFrame mNewValue layers =
  case getLayerById layerId layers of
    Nothing -> Right layers
    Just layer ->
      let
        normalizedPath = T.replace "transform." "" propertyPath
        transform = layerTransform layer
        
        -- Helper to update keyframe in a property
        updateKeyframeInProperty prop =
          let
            keyframes = animatablePropertyKeyframes prop
            mKeyframe = find (\k -> keyframeId k == keyframeId) keyframes
          in
            case mKeyframe of
              Nothing -> prop -- Keyframe not found
              Just kf ->
                let
                  -- Handle frame update
                  (filteredKeyframes, updatedKeyframe) =
                    case mNewFrame of
                      Nothing -> (keyframes, kf)
                      Just newFrame ->
                        -- Validate frame is finite and >= 1
                        -- Frames start at 1, not 0
                        if not (validateFinite newFrame) || newFrame < 1
                          then (keyframes, kf) -- Invalid frame, don't update
                          else
                            let
                              -- Defensive clamp: frame already validated above (>= 1), but clamp ensures determinism
                              -- This is defensive programming - if validation logic changes, this prevents invalid frames
                              clampedFrame = max 1.0 newFrame
                              -- Remove existing keyframe at target frame (if different from updating keyframe)
                              filtered = filter (\k -> 
                                not (keyframeFrame k == clampedFrame && keyframeId k /= keyframeId)
                              ) keyframes
                              updated = kf {keyframeFrame = clampedFrame}
                            in
                              (filtered, updated)
                  
                  -- Handle value update
                  --                                                                      // note
                  -- For now, we accept the value as-is (type system ensures correctness)
                  finalKeyframe =
                    case mNewValue of
                      Nothing -> updatedKeyframe
                      Just newValue -> updatedKeyframe {keyframeValue = newValue}
                  
                  -- Replace old keyframe with updated one
                  updatedKeyframes = map (\k -> 
                    if keyframeId k == keyframeId then finalKeyframe else k
                  ) filteredKeyframes
                  
                  -- Sort by frame (if frame was updated)
                  sortedKeyframes = 
                    if isJust mNewFrame
                      then sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) updatedKeyframes
                      else updatedKeyframes
                in
                  prop {animatablePropertyKeyframes = sortedKeyframes}
        
        updatedLayer =
          if normalizedPath == "position"
            then
              let
                prop = transformPosition transform
                updatedProp = updateKeyframeInProperty prop
                newTransform = transform {transformPosition = updatedProp}
              in
                layer {layerTransform = newTransform}
            else if normalizedPath == "scale"
              then
                let
                  prop = transformScale transform
                  updatedProp = updateKeyframeInProperty prop
                  newTransform = transform {transformScale = updatedProp}
                in
                  layer {layerTransform = newTransform}
              else if normalizedPath == "rotation"
                then
                  let
                    prop = transformRotation transform
                    updatedProp = updateKeyframeInProperty prop
                    newTransform = transform {transformRotation = updatedProp}
                  in
                    layer {layerTransform = newTransform}
                else if normalizedPath == "origin"
                  then
                    let
                      prop = transformOrigin transform
                      updatedProp = updateKeyframeInProperty prop
                      newTransform = transform {transformOrigin = updatedProp}
                    in
                      layer {layerTransform = newTransform}
                  else if normalizedPath == "anchorPoint"
                    then
                      case transformAnchorPoint transform of
                        Nothing -> layer
                        Just prop ->
                          let
                            updatedProp = updateKeyframeInProperty prop
                            newTransform = transform {transformAnchorPoint = Just updatedProp}
                          in
                            layer {layerTransform = newTransform}
                    else if propertyPath == "opacity"
                      then
                        let
                          prop = layerOpacity layer
                          updatedProp = updateKeyframeInProperty prop
                        in
                          layer {layerOpacity = updatedProp}
                      else if normalizedPath == "rotationX"
                        then
                          case transformRotationX transform of
                            Nothing -> layer
                            Just prop ->
                              let
                                updatedProp = updateKeyframeInProperty prop
                                newTransform = transform {transformRotationX = Just updatedProp}
                              in
                                layer {layerTransform = newTransform}
                        else if normalizedPath == "rotationY"
                          then
                            case transformRotationY transform of
                              Nothing -> layer
                              Just prop ->
                                let
                                  updatedProp = updateKeyframeInProperty prop
                                  newTransform = transform {transformRotationY = Just updatedProp}
                                in
                                  layer {layerTransform = newTransform}
                          else if normalizedPath == "rotationZ"
                            then
                              case transformRotationZ transform of
                                Nothing -> layer
                                Just prop ->
                                  let
                                    updatedProp = updateKeyframeInProperty prop
                                    newTransform = transform {transformRotationZ = Just updatedProp}
                                  in
                                    layer {layerTransform = newTransform}
                            else if normalizedPath == "orientation"
                              then
                                case transformOrientation transform of
                                  Nothing -> layer
                                  Just prop ->
                                    let
                                      updatedProp = updateKeyframeInProperty prop
                                      newTransform = transform {transformOrientation = Just updatedProp}
                                    in
                                      layer {layerTransform = newTransform}
                              else
                                layer -- Unknown property path
        
        updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
      in
        Right updatedLayers
