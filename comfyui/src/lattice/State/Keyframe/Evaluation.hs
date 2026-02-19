-- |
-- Module      : Lattice.State.Keyframe.Evaluation
-- Description : Property evaluation operations
--
-- Migrated from ui/src/stores/keyframeStore/evaluation.ts
-- Pure functions for evaluating property values at specific frames
-- Handles transform properties, custom properties, and returns appropriate types
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Evaluation
  ( getPropertyValueAtFrame
  , evaluatePropertyAtFrame
  -- Note: getInterpolatedValue is a convenience wrapper that can be implemented at call site
  ) where

import Data.List (find, findIndex, last)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.Helpers (findPropertyByPath)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , Keyframe(..)
  , PropertyValue(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives
  ( Position2DOr3D(..)
  , Vec2(..)
  , Vec3(..)
  , validateFinite
  )
import Lattice.Types.Transform (LayerTransform(..))
import Lattice.Utils.Interpolation
  ( findKeyframeIndex
  , interpolateNumber
  , interpolateVec3
  , cubicBezierEasing
  )
import Lattice.Utils.NumericSafety (safeLerp)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                    // property // evaluation
-- ════════════════════════════════════════════════════════════════════════════

-- | Interpolate an AnimatableProperty Double at a specific frame
-- Pure function: takes property, frame, returns interpolated value
interpolateDoubleProperty ::
  AnimatableProperty Double ->
  Double ->
  Double
interpolateDoubleProperty prop frame =
  if not (animatablePropertyAnimated prop) || null (animatablePropertyKeyframes prop)
    then animatablePropertyValue prop
    else
      case animatablePropertyKeyframes prop of
        [] -> animatablePropertyValue prop
        keyframes@(firstKf : _) ->
          let
            lastKf = last keyframes
          in
            if frame <= keyframeFrame firstKf
              then keyframeValue firstKf
              else if frame >= keyframeFrame lastKf
                then keyframeValue lastKf
                else
                  -- Find surrounding keyframes
                  let
                    idx = findKeyframeIndex keyframes frame
                    -- Safe array access: findKeyframeIndex guarantees idx is valid and idx+1 exists
                    -- Use drop with pattern matching - total and type-safe
                    k1 = case drop idx keyframes of
                      (kf : _) -> kf
                    k2 = case drop (idx + 1) keyframes of
                      (kf : _) -> kf
                    duration = keyframeFrame k2 - keyframeFrame k1
                    elapsed = frame - keyframeFrame k1
                    t = if duration > 0 then elapsed / duration else 0.0
                    
                    -- Apply interpolation
                    interpolatedT = case keyframeInterpolation k1 of
                      InterpolationBase InterpolationHold -> 0.0  -- Hold: use first value
                      InterpolationBase InterpolationLinear -> t
                      InterpolationBase InterpolationBezier ->
                        let
                          valueDelta = keyframeValue k2 - keyframeValue k1
                          outHandle = keyframeOutHandle k1
                          inHandle = keyframeInHandle k2
                        in
                          cubicBezierEasing t outHandle inHandle duration valueDelta
                      InterpolationEasing _ -> t  -- TODO: Implement easing functions
                  in
                    interpolateNumber (keyframeValue k1) (keyframeValue k2) interpolatedT

-- | Interpolate an AnimatableProperty Vec3 at a specific frame
-- Pure function: takes property, frame, returns interpolated value
interpolateVec3Property ::
  AnimatableProperty Vec3 ->
  Double ->
  Vec3
interpolateVec3Property prop frame =
  if not (animatablePropertyAnimated prop) || null (animatablePropertyKeyframes prop)
    then animatablePropertyValue prop
    else
      case animatablePropertyKeyframes prop of
        [] -> animatablePropertyValue prop
        keyframes@(firstKf : _) ->
          let
            lastKf = last keyframes
          in
            if frame <= keyframeFrame firstKf
              then keyframeValue firstKf
              else if frame >= keyframeFrame lastKf
                then keyframeValue lastKf
                else
                  -- Find surrounding keyframes
                  let
                    idx = findKeyframeIndex keyframes frame
                    -- Safe array access: findKeyframeIndex guarantees idx is valid and idx+1 exists
                    -- Use drop with pattern matching - total and type-safe
                    k1 = case drop idx keyframes of
                      (kf : _) -> kf
                    k2 = case drop (idx + 1) keyframes of
                      (kf : _) -> kf
                    duration = keyframeFrame k2 - keyframeFrame k1
                    elapsed = frame - keyframeFrame k1
                    t = if duration > 0 then elapsed / duration else 0.0
                    
                    -- Apply interpolation (simplified - full implementation would handle bezier for vectors)
                    interpolatedT = case keyframeInterpolation k1 of
                      InterpolationBase InterpolationHold -> 0.0
                      InterpolationBase InterpolationLinear -> t
                      InterpolationBase InterpolationBezier -> t  -- TODO: Implement bezier for Vec3
                      InterpolationEasing _ -> t
                  in
                    interpolateVec3 (keyframeValue k1) (keyframeValue k2) interpolatedT

-- | Interpolate an AnimatableProperty Position2DOr3D at a specific frame
-- Pure function: takes property, frame, returns interpolated value
interpolatePositionProperty ::
  AnimatableProperty Position2DOr3D ->
  Double ->
  Position2DOr3D
interpolatePositionProperty prop frame =
  if not (animatablePropertyAnimated prop) || null (animatablePropertyKeyframes prop)
    then animatablePropertyValue prop
    else
      case animatablePropertyKeyframes prop of
        [] -> animatablePropertyValue prop
        keyframes@(firstKf : _) ->
          let
            lastKf = last keyframes
          in
            if frame <= keyframeFrame firstKf
              then keyframeValue firstKf
              else if frame >= keyframeFrame lastKf
                then keyframeValue lastKf
                else
                  -- Find surrounding keyframes
              let
                idx = findKeyframeIndex keyframes frame
                -- Safe array access: findKeyframeIndex guarantees idx is valid and idx+1 exists
                -- Use drop with pattern matching - total and type-safe
                k1 = case drop idx keyframes of
                  (kf : _) -> kf
                k2 = case drop (idx + 1) keyframes of
                  (kf : _) -> kf
                duration = keyframeFrame k2 - keyframeFrame k1
                elapsed = frame - keyframeFrame k1
                t = if duration > 0 then elapsed / duration else 0.0
                
                -- Apply interpolation (simplified - full implementation would handle bezier for positions)
                interpolatedT = case keyframeInterpolation k1 of
                  InterpolationBase InterpolationHold -> 0.0
                  InterpolationBase InterpolationLinear -> t
                  InterpolationBase InterpolationBezier -> t  -- TODO: Implement bezier for Position2DOr3D
                  InterpolationEasing _ -> t
                
                -- Interpolate x, y, z components
                pos1 = keyframeValue k1
                pos2 = keyframeValue k2
                interpX = safeLerp (position2DOr3DX pos1) (position2DOr3DX pos2) interpolatedT
                interpY = safeLerp (position2DOr3DY pos1) (position2DOr3DY pos2) interpolatedT
                interpZ = case (position2DOr3DZ pos1, position2DOr3DZ pos2) of
                  (Just z1, Just z2) -> Just (safeLerp z1 z2 interpolatedT)
                  (Just z1, Nothing) -> Just z1
                  (Nothing, Just z2) -> Just z2
                  (Nothing, Nothing) -> Nothing
              in
                Position2DOr3D interpX interpY interpZ

-- | Get a single scalar property value at a specific frame
-- Pure function: takes layer ID, property path (e.g., 'transform.position.x'), frame, and layers list
-- Returns scalar value or error
-- Used by property driver system and expression evaluation
getPropertyValueAtFrame ::
  Text -> -- Layer ID
  Text -> -- Property path (e.g., 'transform.position.x', 'opacity')
  Double -> -- Frame number to evaluate at
  [Layer] -> -- Current layers list
  Either Text Double -- Scalar value or error
getPropertyValueAtFrame targetLayerId propertyPath frame layers =
  -- Validate frame is finite and >= 1
  if not (validateFinite frame) || frame < 1
    then Left ("getPropertyValueAtFrame: Invalid frame (must be finite and >= 1): " <> T.pack (show frame))
    else
      case getLayerById layers targetLayerId of
        Nothing -> Left (T.pack "Cannot get property value at frame: Layer \"" <> targetLayerId <> T.pack "\" not found")
        Just layer ->
          let
            parts = T.splitOn "." propertyPath
            transform = layerTransform layer
            firstPart = case parts of
              [] -> ""
              (p : _) -> p
          in
            if firstPart == "transform" && length parts >= 3
              then
                let
                  -- Safe array access: guarded by length parts >= 3
                  -- Use drop with pattern matching - total and type-safe
                  propName = case drop 1 parts of
                    (p : _) -> p
                    [] -> ""  -- Should never happen due to length check, but type-safe
                  component = case drop 2 parts of
                    (c : _) -> c
                    [] -> ""  -- Should never happen due to length check, but type-safe
                in
                  if propName == "position"
                    then
                      let
                        posProp = transformPosition transform
                        posValue = interpolatePositionProperty posProp frame
                        zVal = case position2DOr3DZ posValue of
                          Nothing -> 0.0
                          Just z -> z
                      in
                        if component == "x"
                          then Right (position2DOr3DX posValue)
                          else if component == "y"
                            then Right (position2DOr3DY posValue)
                            else Right zVal
                    else if propName == "anchorPoint" || propName == "origin"
                      then
                        -- Use origin (always present), fallback to anchorPoint if available
                        let
                          originProp = case transformAnchorPoint transform of
                            Just anchorProp -> anchorProp
                            Nothing -> transformOrigin transform
                          originValue = interpolatePositionProperty originProp frame
                          zVal = case position2DOr3DZ originValue of
                            Nothing -> 0.0
                            Just z -> z
                        in
                          if component == "x"
                            then Right (position2DOr3DX originValue)
                            else if component == "y"
                              then Right (position2DOr3DY originValue)
                              else Right zVal
                      else if propName == "scale"
                        then
                          let
                            scaleProp = transformScale transform
                            scaleValue = interpolateVec3Property scaleProp frame
                            zVal = vec3Z scaleValue
                          in
                            if component == "x"
                              then Right (vec3X scaleValue)
                              else if component == "y"
                                then Right (vec3Y scaleValue)
                                else Right zVal
                        else if propName == "rotation"
                          then
                            let
                              rotProp = transformRotation transform
                            in
                              Right (interpolateDoubleProperty rotProp frame)
                          else if propName == "rotationX"
                            then
                              case transformRotationX transform of
                                Nothing -> Left (T.pack "Property \"transform.rotationX\" not found on layer \"" <> targetLayerId <> T.pack "\"")
                                Just rotXProp -> Right (interpolateDoubleProperty rotXProp frame)
                            else if propName == "rotationY"
                              then
                                case transformRotationY transform of
                                  Nothing -> Left (T.pack "Property \"transform.rotationY\" not found on layer \"" <> targetLayerId <> T.pack "\"")
                                  Just rotYProp -> Right (interpolateDoubleProperty rotYProp frame)
                              else if propName == "rotationZ"
                                then
                                  case transformRotationZ transform of
                                    Nothing -> Left (T.pack "Property \"transform.rotationZ\" not found on layer \"" <> targetLayerId <> T.pack "\"")
                                    Just rotZProp -> Right (interpolateDoubleProperty rotZProp frame)
                                else Left (T.pack "Unsupported transform property: " <> propName)
              else if firstPart == "opacity"
                then
                  let
                    opacityProp = layerOpacity layer
                  in
                    Right (interpolateDoubleProperty opacityProp frame)
                else Left (T.pack "Unsupported property path: " <> propertyPath)

-- | Evaluate a property at a specific frame and return the full value
-- Pure function: takes layer ID, property path, frame, and layers list
-- Returns array for vector properties, number for scalars, or error
-- Used by MotionPathOverlay to get full position values for path rendering
evaluatePropertyAtFrame ::
  Text -> -- Layer ID
  Text -> -- Property path (e.g., 'position', 'transform.position', 'opacity')
  Double -> -- Frame number to evaluate at
  [Layer] -> -- Current layers list
  Either Text ([Double], Maybe Double) -- (array for vectors, scalar for numbers) or error
evaluatePropertyAtFrame targetLayerId propertyPath frame layers =
  -- Validate frame is finite and >= 1
  if not (validateFinite frame) || frame < 1
    then Left ("evaluatePropertyAtFrame: Invalid frame (must be finite and >= 1): " <> T.pack (show frame))
    else
      case getLayerById layers targetLayerId of
        Nothing -> Left (T.pack "Cannot evaluate property at frame: Layer \"" <> targetLayerId <> T.pack "\" not found")
        Just layer ->
          let
            -- Normalize path
            normalizedPath = T.replace "transform." "" propertyPath
            transform = layerTransform layer
          in
            if normalizedPath == "position"
              then
                let
                  posProp = transformPosition transform
                  posValue = interpolatePositionProperty posProp frame
                  zVal = case position2DOr3DZ posValue of
                    Nothing -> 0.0
                    Just z -> z
                in
                  Right ([position2DOr3DX posValue, position2DOr3DY posValue, zVal], Nothing)
              else if normalizedPath == "anchorPoint" || normalizedPath == "origin"
                then
                  -- Use origin (always present), fallback to anchorPoint if available
                  let
                    originProp = case transformAnchorPoint transform of
                      Just anchorProp -> anchorProp
                      Nothing -> transformOrigin transform
                    originValue = interpolatePositionProperty originProp frame
                    zVal = case position2DOr3DZ originValue of
                      Nothing -> 0.0
                      Just z -> z
                  in
                    Right ([position2DOr3DX originValue, position2DOr3DY originValue, zVal], Nothing)
                else if normalizedPath == "scale"
                  then
                    let
                      scaleProp = transformScale transform
                      scaleValue = interpolateVec3Property scaleProp frame
                    in
                      Right ([vec3X scaleValue, vec3Y scaleValue, vec3Z scaleValue], Nothing)
                  else if normalizedPath == "rotation"
                    then
                      let
                        rotProp = transformRotation transform
                      in
                        Right ([], Just (interpolateDoubleProperty rotProp frame))
                    else if normalizedPath == "rotationX"
                      then
                        case transformRotationX transform of
                          Nothing -> Left (T.pack "Property \"rotationX\" not found on layer \"" <> targetLayerId <> T.pack "\"")
                          Just rotXProp -> Right ([], Just (interpolateDoubleProperty rotXProp frame))
                      else if normalizedPath == "rotationY"
                        then
                          case transformRotationY transform of
                            Nothing -> Left (T.pack "Property \"rotationY\" not found on layer \"" <> targetLayerId <> T.pack "\"")
                            Just rotYProp -> Right ([], Just (interpolateDoubleProperty rotYProp frame))
                        else if normalizedPath == "rotationZ"
                          then
                            case transformRotationZ transform of
                              Nothing -> Left (T.pack "Property \"rotationZ\" not found on layer \"" <> targetLayerId <> T.pack "\"")
                              Just rotZProp -> Right ([], Just (interpolateDoubleProperty rotZProp frame))
                          else if normalizedPath == "orientation"
                            then
                              case transformOrientation transform of
                                Nothing -> Left (T.pack "Property \"orientation\" not found on layer \"" <> targetLayerId <> T.pack "\"")
                                Just orientProp ->
                                  let
                                    orientValue = interpolateVec3Property orientProp frame
                                  in
                                    Right ([vec3X orientValue, vec3Y orientValue, vec3Z orientValue], Nothing)
                            else if propertyPath == "opacity"
                              then
                                let
                                  opacityProp = layerOpacity layer
                                in
                                  Right ([], Just (interpolateDoubleProperty opacityProp frame))
                              else
                                -- Property not found in standard or custom properties
                                Left (T.pack "Cannot evaluate property \"" <> propertyPath <> T.pack "\" at frame " <> T.pack (show frame) <> T.pack " for layer \"" <> targetLayerId <> T.pack "\": Property not found or unsupported")
