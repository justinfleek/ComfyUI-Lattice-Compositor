-- |
-- Module      : Lattice.State.Keyframe.Interpolation
-- Description : Interpolation operations for keyframes
--
-- Migrated from ui/src/stores/keyframeStore/interpolation.ts
-- Pure functions for setting interpolation type, bezier handles, and control modes
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Interpolation
  ( setKeyframeInterpolation
  , setKeyframeHandle
  , setKeyframeControlMode
  , setKeyframeHandleWithMode
  ) where

import Data.List (find)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , BezierHandle(..)
  , ControlMode(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , Keyframe(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives (validateFinite)
import Lattice.Types.Transform (LayerTransform(..))

-- ============================================================================
-- HELPER FUNCTIONS FOR PROPERTY UPDATES
-- ============================================================================

-- | Update a keyframe in a property
-- Pure function: takes property, keyframe ID, and update function
-- Returns updated property
updateKeyframeInProperty ::
  AnimatableProperty a ->
  Text ->
  (Keyframe a -> Keyframe a) ->
  AnimatableProperty a
updateKeyframeInProperty prop kfId updateFunc =
  let
    keyframes = animatablePropertyKeyframes prop
    updatedKeyframes = map (\k -> if keyframeId k == kfId then updateFunc k else k) keyframes
  in
    prop {animatablePropertyKeyframes = updatedKeyframes}

-- | Helper to update property in layer based on path
updatePropertyInLayer ::
  Layer ->
  Text ->
  (forall a. AnimatableProperty a -> AnimatableProperty a) ->
  Maybe Layer
updatePropertyInLayer layer propertyPath updateFunc =
  let
    normalizedPath = T.replace "transform." "" propertyPath
    transform = layerTransform layer
  in
    if normalizedPath == "position"
      then Just (layer
        { layerTransform = transform
          { transformPosition = updateFunc (transformPosition transform)
          }
        })
      else if normalizedPath == "scale"
        then Just (layer
          { layerTransform = transform
            { transformScale = updateFunc (transformScale transform)
            }
          })
        else if normalizedPath == "rotation"
          then Just (layer
            { layerTransform = transform
              { transformRotation = updateFunc (transformRotation transform)
              }
            })
          else if normalizedPath == "anchorPoint"
            then case transformAnchorPoint transform of
              Nothing -> Nothing
              Just prop -> Just (layer
                { layerTransform = transform
                  { transformAnchorPoint = Just (updateFunc prop)
                  }
                })
            else if normalizedPath == "origin"
              then Just (layer
                { layerTransform = transform
                  { transformOrigin = updateFunc (transformOrigin transform)
                  }
                })
              else if propertyPath == "opacity"
                then Just (layer
                  { layerOpacity = updateFunc (layerOpacity layer)
                  })
                else if normalizedPath == "rotationX"
                  then case transformRotationX transform of
                    Nothing -> Nothing
                    Just prop -> Just (layer
                      { layerTransform = transform
                        { transformRotationX = Just (updateFunc prop)
                      }
                      })
                  else if normalizedPath == "rotationY"
                    then case transformRotationY transform of
                      Nothing -> Nothing
                      Just prop -> Just (layer
                        { layerTransform = transform
                          { transformRotationY = Just (updateFunc prop)
                        }
                        })
                    else if normalizedPath == "rotationZ"
                      then case transformRotationZ transform of
                        Nothing -> Nothing
                        Just prop -> Just (layer
                          { layerTransform = transform
                            { transformRotationZ = Just (updateFunc prop)
                          }
                          })
                      else if normalizedPath == "orientation"
                        then case transformOrientation transform of
                          Nothing -> Nothing
                          Just prop -> Just (layer
                            { layerTransform = transform
                              { transformOrientation = Just (updateFunc prop)
                            }
                            })
                        else
                          Nothing

-- ============================================================================
-- KEYFRAME INTERPOLATION
-- ============================================================================

-- | Set keyframe interpolation type
-- Pure function: takes layer ID, property path, keyframe ID, interpolation type, and layers list
-- Returns updated layers list or error
setKeyframeInterpolation ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  InterpolationType -> -- Interpolation type
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setKeyframeInterpolation targetLayerId propertyPath targetKeyframeId interpolation layers =
  case getLayerById layers targetLayerId of
    Nothing -> Right layers
    Just layer ->
      case updatePropertyInLayer layer propertyPath (\prop ->
        updateKeyframeInProperty prop targetKeyframeId (\kf -> kf {keyframeInterpolation = interpolation})
      ) of
        Nothing -> Right layers -- Property not found
        Just updatedLayer ->
          let
            updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
          in
            Right updatedLayers

-- | Set keyframe bezier handle
-- Pure function: takes layer ID, property path, keyframe ID, handle type, handle, and layers list
-- Returns updated layers list or error
-- Enables bezier interpolation if handle is enabled and interpolation is linear
-- Validates handle values are finite
setKeyframeHandle ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Bool -> -- Handle type (True = inHandle, False = outHandle)
  BezierHandle -> -- Handle
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setKeyframeHandle targetLayerId propertyPath targetKeyframeId isInHandle handle layers =
  -- Validate handle values are finite
  -- Both frame and value components must be finite numbers
  if not (validateFinite (bezierHandleFrame handle)) || not (validateFinite (bezierHandleValue handle))
    then Left ("setKeyframeHandle: Invalid handle values (must be finite): frame=" <> T.pack (show (bezierHandleFrame handle)) <> ", value=" <> T.pack (show (bezierHandleValue handle)))
    else
      case getLayerById layers targetLayerId of
        Nothing -> Right layers
        Just layer ->
          case updatePropertyInLayer layer propertyPath (\prop ->
            updateKeyframeInProperty prop targetKeyframeId (\kf ->
              let
                -- Update handle
                updatedKf = if isInHandle
                  then kf {keyframeInHandle = handle}
                  else kf {keyframeOutHandle = handle}
                -- Enable bezier interpolation if handle is enabled and interpolation is linear
                finalKf = if bezierHandleEnabled handle && keyframeInterpolation updatedKf == InterpolationBase InterpolationLinear
                  then updatedKf {keyframeInterpolation = InterpolationBase InterpolationBezier}
                  else updatedKf
              in
                finalKf
            )
          ) of
          Nothing -> Right layers
          Just updatedLayer ->
            let
              updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
            in
              Right updatedLayers

-- | Set keyframe control mode
-- Pure function: takes layer ID, property path, keyframe ID, control mode, and layers list
-- Returns updated layers list or error
setKeyframeControlMode ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  ControlMode -> -- Control mode
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setKeyframeControlMode targetLayerId propertyPath targetKeyframeId controlMode layers =
  case getLayerById layers targetLayerId of
    Nothing -> Right layers
    Just layer ->
      case updatePropertyInLayer layer propertyPath (\prop ->
        updateKeyframeInProperty prop targetKeyframeId (\kf -> kf {keyframeControlMode = controlMode})
      ) of
        Nothing -> Right layers
        Just updatedLayer ->
          let
            updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
          in
            Right updatedLayers

-- ============================================================================
-- HANDLE WITH CONTROL MODE (BREAK HANDLES)
-- ============================================================================

-- | Calculate handle length (magnitude)
handleLength :: BezierHandle -> Double
handleLength (BezierHandle frame value _) =
  sqrt (frame * frame + value * value)

-- | Scale handle by factor
scaleHandle :: Double -> BezierHandle -> BezierHandle
scaleHandle scale (BezierHandle frame value enabled) =
  BezierHandle (frame * scale) (value * scale) enabled

-- | Mirror handle (negate both frame and value)
mirrorHandle :: BezierHandle -> BezierHandle
mirrorHandle (BezierHandle frame value enabled) =
  BezierHandle (-frame) (-value) enabled

-- | Set keyframe bezier handle with control mode awareness
-- Pure function: takes layer ID, property path, keyframe ID, handle type, handle, break flag, and layers list
-- Returns updated layers list or error
-- Control modes:
-- - 'symmetric': Both handles have same length and opposite direction
-- - 'smooth': Both handles maintain angle but can have different lengths
-- - 'corner': Handles are independent (broken)
-- Validates handle values are finite and prevents division by zero
setKeyframeHandleWithMode ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Bool -> -- Handle type (True = inHandle, False = outHandle)
  BezierHandle -> -- Handle
  Bool -> -- Break handle (if True, sets controlMode to corner)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
setKeyframeHandleWithMode targetLayerId propertyPath targetKeyframeId isInHandle handle breakHandle layers =
  -- Validate handle values are finite
  -- Both frame and value components must be finite numbers
  if not (validateFinite (bezierHandleFrame handle)) || not (validateFinite (bezierHandleValue handle))
    then Left ("setKeyframeHandleWithMode: Invalid handle values (must be finite): frame=" <> T.pack (show (bezierHandleFrame handle)) <> ", value=" <> T.pack (show (bezierHandleValue handle)))
    else
      case getLayerById layers targetLayerId of
        Nothing -> Right layers
        Just layer ->
          case updatePropertyInLayer layer propertyPath (\prop ->
            let
              keyframes = animatablePropertyKeyframes prop
              mKeyframe = find (\k -> keyframeId k == targetKeyframeId) keyframes
        in
          case mKeyframe of
            Nothing -> prop -- Keyframe not found
            Just kf ->
              let
                -- If breaking handle (Ctrl+drag), set to corner mode
                (updatedKf, newControlMode) = if breakHandle
                  then
                    let
                      updated = if isInHandle
                        then kf {keyframeInHandle = handle}
                        else kf {keyframeOutHandle = handle}
                    in
                      (updated, ControlCorner)
                  else
                    -- Respect existing control mode
                    let
                      mode = keyframeControlMode kf
                      (updated, newMode) = if isInHandle
                        then
                          let
                            updatedIn = kf {keyframeInHandle = handle}
                            (finalKf, finalMode) = case mode of
                              ControlSymmetric ->
                                -- Mirror both angle and length to outHandle
                                (updatedIn {keyframeOutHandle = mirrorHandle handle}, ControlSymmetric)
                              ControlSmooth ->
                                -- Mirror angle, keep outHandle length
                                let
                                  inLen = handleLength handle
                                  outLen = handleLength (keyframeOutHandle kf)
                                in
                                  -- Prevent division by zero: if either length is zero, don't scale
                                  if inLen > 0 && outLen > 0
                                    then
                                      let
                                        scale = outLen / inLen
                                        scaledMirror = scaleHandle scale (mirrorHandle handle)
                                        updatedOut = updatedIn {keyframeOutHandle = scaledMirror {bezierHandleEnabled = bezierHandleEnabled (keyframeOutHandle kf)}}
                                      in
                                        (updatedOut, ControlSmooth)
                                    else if inLen == 0 && outLen == 0
                                      then
                                        -- Both zero: use symmetric mirror
                                        let
                                          mirroredHandle = mirrorHandle handle
                                          updatedOutHandle = mirroredHandle {bezierHandleEnabled = bezierHandleEnabled (keyframeOutHandle kf)}
                                        in
                                          (updatedIn {keyframeOutHandle = updatedOutHandle}, ControlSmooth)
                                      else
                                        -- One is zero: keep current outHandle
                                        (updatedIn, ControlSmooth)
                              ControlCorner ->
                                -- No adjustment to other handle
                                (updatedIn, ControlCorner)
                          in
                            (finalKf, finalMode)
                        else
                          let
                            updatedOut = kf {keyframeOutHandle = handle}
                            (finalKf, finalMode) = case mode of
                              ControlSymmetric ->
                                -- Mirror both angle and length to inHandle
                                (updatedOut {keyframeInHandle = mirrorHandle handle}, ControlSymmetric)
                              ControlSmooth ->
                                -- Mirror angle, keep inHandle length
                                let
                                  outLen = handleLength handle
                                  inLen = handleLength (keyframeInHandle kf)
                                in
                                  -- Prevent division by zero: if either length is zero, don't scale
                                  if outLen > 0 && inLen > 0
                                    then
                                      let
                                        scale = inLen / outLen
                                        scaledMirror = scaleHandle scale (mirrorHandle handle)
                                        updatedIn = updatedOut {keyframeInHandle = scaledMirror {bezierHandleEnabled = bezierHandleEnabled (keyframeInHandle kf)}}
                                      in
                                        (updatedIn, ControlSmooth)
                                    else if outLen == 0 && inLen == 0
                                      then
                                        -- Both zero: use symmetric mirror
                                        let
                                          mirroredHandle = mirrorHandle handle
                                          updatedInHandle = mirroredHandle {bezierHandleEnabled = bezierHandleEnabled (keyframeInHandle kf)}
                                        in
                                          (updatedOut {keyframeInHandle = updatedInHandle}, ControlSmooth)
                                      else
                                        -- One is zero: keep current inHandle
                                        (updatedOut, ControlSmooth)
                              ControlCorner ->
                                -- No adjustment to other handle
                                (updatedOut, ControlCorner)
                          in
                            (finalKf, finalMode)
                  in
                    (updatedKf {keyframeControlMode = newControlMode}, newControlMode)
                
                -- Enable bezier interpolation if handle is enabled and interpolation is linear
                finalKf = if bezierHandleEnabled handle && keyframeInterpolation updatedKf == InterpolationBase InterpolationLinear
                  then updatedKf {keyframeInterpolation = InterpolationBase InterpolationBezier}
                  else updatedKf
                
                updatedKeyframes = map (\k -> if keyframeId k == targetKeyframeId then finalKf else k) keyframes
              in
                prop {animatablePropertyKeyframes = updatedKeyframes}
          ) of
            Nothing -> Right layers
            Just updatedLayer ->
              let
                updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
              in
                Right updatedLayers
