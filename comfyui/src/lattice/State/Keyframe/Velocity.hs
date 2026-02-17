-- |
-- Module      : Lattice.State.Keyframe.Velocity
-- Description : Keyframe velocity operations
--
-- Migrated from ui/src/stores/keyframeStore/velocity.ts
-- Pure functions for applying and retrieving velocity settings for keyframe handles
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Velocity
  ( applyKeyframeVelocity
  , getKeyframeVelocity
  ) where

import Data.List (findIndex)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.Helpers (findPropertyByPath)
import Lattice.State.Keyframe.Interpolation
  ( setKeyframeHandle
  , setKeyframeInterpolation
  )
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.State.Keyframe.Types (VelocitySettings(..))
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , BezierHandle(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , Keyframe(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives (validateFinite)

-- ============================================================================
-- KEYFRAME VELOCITY
-- ============================================================================

-- | Apply velocity settings to a keyframe
-- Pure function: takes layer ID, property path, keyframe ID, velocity settings, FPS, and layers list
-- Returns updated layers list or error
-- Converts velocity and influence to bezier handle values
applyKeyframeVelocity ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  VelocitySettings -> -- Velocity settings
  Double -> -- FPS (frames per second)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
applyKeyframeVelocity layerId propertyPath keyframeId settings fps layers =
  -- Validate FPS is finite and > 0
  if not (validateFinite fps) || fps <= 0
    then Left ("applyKeyframeVelocity: Invalid FPS (must be finite and > 0): " <> T.pack (show fps))
    else
      -- Validate velocity settings
      if not (validateFinite (velocitySettingsIncomingVelocity settings)) ||
         not (validateFinite (velocitySettingsOutgoingVelocity settings)) ||
         not (validateFinite (velocitySettingsIncomingInfluence settings)) ||
         not (validateFinite (velocitySettingsOutgoingInfluence settings)) ||
         velocitySettingsIncomingInfluence settings < 0 || velocitySettingsIncomingInfluence settings > 100 ||
         velocitySettingsOutgoingInfluence settings < 0 || velocitySettingsOutgoingInfluence settings > 100
        then Left ("applyKeyframeVelocity: Invalid velocity settings (velocities must be finite, influences must be in [0, 100])")
        else
          case getLayerById layerId layers of
            Nothing -> Right layers
            Just layer ->
              case findPropertyByPath layer propertyPath of
                Nothing -> Right layers
                Just prop ->
                  let
                    keyframes = animatablePropertyKeyframes prop
                    mKfIndex = findIndex (\kf -> keyframeId kf == keyframeId) keyframes
                  in
                    case mKfIndex of
                      Nothing -> Right layers
                      Just kfIndex ->
                        let
                          -- Safe array access: kfIndex is guaranteed valid from findIndex
                          -- findIndex returns Just only if element exists, so we can safely use drop
                          -- Pattern match on drop result - guaranteed non-empty since findIndex succeeded
                          keyframe = case drop kfIndex keyframes of
                            (kf : _) -> kf
                          prevKf = if kfIndex > 0
                            then case drop (kfIndex - 1) keyframes of
                              (kf : _) -> Just kf
                              [] -> Nothing  -- Should never happen, but type-safe
                            else Nothing
                          nextKf = case drop (kfIndex + 1) keyframes of
                            (kf : _) -> Just kf
                            [] -> Nothing
                          
                          -- Calculate handle frame offsets from influence percentages
                          -- Default duration is 10 frames if no neighbor exists
                          inDuration = case prevKf of
                            Nothing -> 10.0
                            Just prev -> 
                              let
                                diff = keyframeFrame keyframe - keyframeFrame prev
                              in
                                if validateFinite diff && diff > 0 then diff else 10.0
                          
                          outDuration = case nextKf of
                            Nothing -> 10.0
                            Just next ->
                              let
                                diff = keyframeFrame next - keyframeFrame keyframe
                              in
                                if validateFinite diff && diff > 0 then diff else 10.0
                          
                          -- Convert influence percentages to ratios
                          inInfluence = velocitySettingsIncomingInfluence settings / 100.0
                          outInfluence = velocitySettingsOutgoingInfluence settings / 100.0
                          
                          -- Convert velocity to value offset
                          -- Velocity is in units per second, convert to units per frame segment
                          inVelocityPerFrame = velocitySettingsIncomingVelocity settings / fps
                          outVelocityPerFrame = velocitySettingsOutgoingVelocity settings / fps
                          
                          -- Set bezier handles
                          -- In handle: negative frame offset, negative value offset
                          inHandle = BezierHandle
                            { bezierHandleFrame = -inDuration * inInfluence
                            , bezierHandleValue = -inVelocityPerFrame * inDuration * inInfluence
                            , bezierHandleEnabled = True
                            }
                          
                          -- Out handle: positive frame offset, positive value offset
                          outHandle = BezierHandle
                            { bezierHandleFrame = outDuration * outInfluence
                            , bezierHandleValue = outVelocityPerFrame * outDuration * outInfluence
                            , bezierHandleEnabled = True
                            }
                          
                          -- Apply handles and set interpolation to bezier
                          -- First set in handle
                          result1 = setKeyframeHandle layerId propertyPath keyframeId True inHandle layers
                        in
                          case result1 of
                            Left err -> Left err
                            Right updatedLayers1 ->
                              -- Then set out handle
                              case setKeyframeHandle layerId propertyPath keyframeId False outHandle updatedLayers1 of
                                Left err -> Left err
                                Right updatedLayers2 ->
                                  -- Finally set interpolation to bezier
                                  setKeyframeInterpolation layerId propertyPath keyframeId (InterpolationBase InterpolationBezier) updatedLayers2

-- | Get the current velocity settings from a keyframe's handles
-- Pure function: takes layer ID, property path, keyframe ID, FPS, and layers list
-- Returns velocity settings or error
getKeyframeVelocity ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  Double -> -- FPS (frames per second)
  [Layer] -> -- Current layers list
  Either Text VelocitySettings -- Velocity settings or error
getKeyframeVelocity layerId propertyPath keyframeId fps layers =
  -- Validate FPS is finite and > 0
  if not (validateFinite fps) || fps <= 0
    then Left ("getKeyframeVelocity: Invalid FPS (must be finite and > 0): " <> T.pack (show fps))
    else
      case getLayerById layerId layers of
        Nothing -> Left ("Cannot get keyframe velocity: Layer \"" <> T.unpack layerId <> "\" not found")
        Just layer ->
          case findPropertyByPath layer propertyPath of
            Nothing -> Left ("Cannot get keyframe velocity: Property \"" <> T.unpack propertyPath <> "\" not found or has no keyframes on layer \"" <> T.unpack layerId <> "\"")
            Just prop ->
              let
                keyframes = animatablePropertyKeyframes prop
                mKfIndex = findIndex (\kf -> keyframeId kf == keyframeId) keyframes
              in
                case mKfIndex of
                  Nothing -> Left ("Cannot get keyframe velocity: Keyframe \"" <> T.unpack keyframeId <> "\" not found in property \"" <> T.unpack propertyPath <> "\" on layer \"" <> T.unpack layerId <> "\"")
                  Just kfIndex ->
                    let
                      -- Safe array access: kfIndex is guaranteed valid from findIndex
                      -- findIndex returns Just only if element exists, so we can safely use drop
                      -- Pattern match on drop result - guaranteed non-empty since findIndex succeeded
                      keyframe = case drop kfIndex keyframes of
                        (kf : _) -> kf
                      prevKf = if kfIndex > 0
                        then case drop (kfIndex - 1) keyframes of
                          (kf : _) -> Just kf
                          [] -> Nothing  -- Should never happen, but type-safe
                        else Nothing
                      nextKf = case drop (kfIndex + 1) keyframes of
                        (kf : _) -> Just kf
                        [] -> Nothing
                      
                      -- Calculate durations
                      -- Default duration is 10 frames if no neighbor exists
                      inDuration = case prevKf of
                        Nothing -> 10.0
                        Just prev ->
                          let
                            diff = keyframeFrame keyframe - keyframeFrame prev
                          in
                            if validateFinite diff && diff > 0 then diff else 10.0
                      
                      outDuration = case nextKf of
                        Nothing -> 10.0
                        Just next ->
                          let
                            diff = keyframeFrame next - keyframeFrame keyframe
                          in
                            if validateFinite diff && diff > 0 then diff else 10.0
                      
                      -- Extract influence from handle frame offset (guard against div/0)
                      inHandle = keyframeInHandle keyframe
                      inHandleEnabled = bezierHandleEnabled inHandle
                      inHandleFrameAbs = abs (bezierHandleFrame inHandle)
                      inInfluence = if inHandleEnabled && inDuration > 0 && inHandleFrameAbs > 0
                        then (inHandleFrameAbs / inDuration) * 100.0
                        else 33.33
                      
                      outHandle = keyframeOutHandle keyframe
                      outHandleEnabled = bezierHandleEnabled outHandle
                      outHandleFrame = bezierHandleFrame outHandle
                      outInfluence = if outHandleEnabled && outDuration > 0 && outHandleFrame > 0
                        then (outHandleFrame / outDuration) * 100.0
                        else 33.33
                      
                      -- Convert value offset back to velocity
                      -- Guard against division by zero
                      inVelocity = if inHandleEnabled && inHandleFrameAbs > 0
                        then (-bezierHandleValue inHandle / inHandleFrameAbs) * fps
                        else 0.0
                      
                      outVelocity = if outHandleEnabled && outHandleFrame > 0
                        then (bezierHandleValue outHandle / outHandleFrame) * fps
                        else 0.0
                      
                      -- Clamp influences to [0, 100]
                      clampedInInfluence = max 0.0 (min 100.0 inInfluence)
                      clampedOutInfluence = max 0.0 (min 100.0 outInfluence)
                    in
                      Right (VelocitySettings
                        { velocitySettingsIncomingVelocity = inVelocity
                        , velocitySettingsOutgoingVelocity = outVelocity
                        , velocitySettingsIncomingInfluence = clampedInInfluence
                        , velocitySettingsOutgoingInfluence = clampedOutInfluence
                        })
