-- |
-- Module      : Lattice.State.Keyframe.Timing
-- Description : Keyframe timing operations
--
-- Migrated from ui/src/stores/keyframeStore/timing.ts
-- Pure functions for scaling, reversing, inserting, and roving keyframes
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.Timing
  ( scaleKeyframeTiming
  , timeReverseKeyframes
  , insertKeyframeOnPath
  , checkRovingImpact
  -- Note: applyRovingToPosition requires roving service migration
  ) where

import Data.List (find, sortBy)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.CRUD (addKeyframeWithPropertyValue)
import Lattice.State.Keyframe.Helpers (findPropertyByPath)
import Lattice.State.Keyframe.Interpolation (updatePropertyInLayer)
import Lattice.State.Keyframe.Query (findSurroundingKeyframes)
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
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
import Lattice.Utils.NumericSafety (safeLerpD)

-- ============================================================================
-- KEYFRAME TIMING SCALE
-- ============================================================================

-- | Scale keyframe timing by a factor
-- Pure function: takes layer ID, property path (Nothing = all transform properties), scale factor, anchor frame, and layers list
-- Returns updated layers list and count of scaled keyframes
-- Used for Alt+drag last keyframe to scale all keyframes proportionally
scaleKeyframeTiming ::
  Text -> -- Layer ID
  Maybe Text -> -- Property path (Nothing = all transform properties)
  Double -> -- Scale factor (e.g., 2.0 = twice as long, 0.5 = half)
  Double -> -- Anchor frame (default: 0, but should be >= 1)
  [Layer] -> -- Current layers list
  Either Text (Int, [Layer]) -- (scaled count, updated layers list) or error
scaleKeyframeTiming layerId mPropertyPath scaleFactor anchorFrame layers =
  -- Validate numeric parameters
  if not (validateFinite scaleFactor) || not (validateFinite anchorFrame)
    then Left ("scaleKeyframeTiming: Invalid parameters: scaleFactor=" <> T.pack (show scaleFactor) <> ", anchorFrame=" <> T.pack (show anchorFrame))
    else
      case getLayerById layerId layers of
        Nothing -> Right (0, layers)
        Just layer ->
          let
            -- Ensure anchor frame is >= 1
            safeAnchorFrame = if anchorFrame >= 1 then anchorFrame else 1.0
            
            -- Determine which properties to scale
            propertyPaths = case mPropertyPath of
              Nothing -> ["position", "scale", "rotation", "opacity", "origin"]
              Just path -> [path]
            
            -- Scale keyframes in each property using updatePropertyInLayer
            scalePropertyInLayer accLayer propPath =
              case updatePropertyInLayer accLayer propPath (\prop ->
                if animatablePropertyAnimated prop && not (null (animatablePropertyKeyframes prop))
                  then
                    let
                      -- Scale each keyframe's frame number relative to anchor
                      scaledKeyframes = map (\kf ->
                        let
                          relativeFrame = keyframeFrame kf - safeAnchorFrame
                          newFrame = safeAnchorFrame + relativeFrame * scaleFactor
                          -- Ensure new frame is >= 1
                          clampedFrame = if validateFinite newFrame && newFrame >= 1 then newFrame else 1.0
                          roundedFrame = fromIntegral (round clampedFrame)
                        in
                          kf {keyframeFrame = roundedFrame}
                        ) (animatablePropertyKeyframes prop)
                      
                      -- Re-sort keyframes to maintain order
                      sortedKeyframes = sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) scaledKeyframes
                    in
                      prop {animatablePropertyKeyframes = sortedKeyframes}
                  else prop
                ) of
                  Nothing -> accLayer
                  Just updatedLayer -> updatedLayer
            
            -- Apply scaling to all properties
            updatedLayer = foldl (\accLayer propPath -> scalePropertyInLayer accLayer propPath) layer propertyPaths
            
            -- Count scaled keyframes
            scaledCount = sum (map (\propPath ->
              case findPropertyByPath updatedLayer propPath of
                Nothing -> 0
                Just prop -> length (animatablePropertyKeyframes prop)
              ) propertyPaths)
            
            updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
          in
            Right (scaledCount, updatedLayers)

-- ============================================================================
-- KEYFRAME TIME REVERSE
-- ============================================================================

-- | Reverse keyframe timing (values swap, frames stay same)
-- Pure function: takes layer ID, property path (Nothing = all transform properties), and layers list
-- Returns updated layers list and count of reversed keyframes
-- Creates the effect of playing the animation backward
timeReverseKeyframes ::
  Text -> -- Layer ID
  Maybe Text -> -- Property path (Nothing = all transform properties)
  [Layer] -> -- Current layers list
  Either Text (Int, [Layer]) -- (reversed count, updated layers list) or error
timeReverseKeyframes layerId mPropertyPath layers =
  case getLayerById layerId layers of
    Nothing -> Right (0, layers)
    Just layer ->
      let
        -- Determine which properties to reverse
        propertyPaths = case mPropertyPath of
          Nothing -> ["position", "scale", "rotation", "opacity", "origin"]
          Just path -> [path]
        
        -- Reverse keyframes in each property using updatePropertyInLayer
        reversePropertyInLayer accLayer propPath =
          case updatePropertyInLayer accLayer propPath (\prop ->
            if animatablePropertyAnimated prop && length (animatablePropertyKeyframes prop) >= 2
              then
                let
                  keyframes = animatablePropertyKeyframes prop
                  -- Collect values in order
                  values = map keyframeValue keyframes
                  -- Reverse the values
                  reversedValues = reverse values
                  -- Assign reversed values back to keyframes (frames stay same)
                  reversedKeyframes = zipWith (\kf val -> kf {keyframeValue = val}) keyframes reversedValues
                in
                  prop {animatablePropertyKeyframes = reversedKeyframes}
              else prop
            ) of
              Nothing -> accLayer
              Just updatedLayer -> updatedLayer
        
        -- Apply reversal to all properties
        updatedLayer = foldl (\accLayer propPath -> reversePropertyInLayer accLayer propPath) layer propertyPaths
        
        -- Count reversed keyframes
        reversedCount = sum (map (\propPath ->
          case findPropertyByPath updatedLayer propPath of
            Nothing -> 0
            Just prop -> length (animatablePropertyKeyframes prop)
          ) propertyPaths)
        
        updatedLayers = map (\l -> if layerId l == layerId updatedLayer then updatedLayer else l) layers
      in
        Right (reversedCount, updatedLayers)

-- ============================================================================
-- INSERT KEYFRAME ON PATH
-- ============================================================================

-- | Insert a keyframe at a specific position along a motion path
-- Pure function: takes layer ID, frame, ID generator, and layers list
-- Returns created keyframe ID and updated layers list or error
-- Used for Pen tool click on path to add control point
-- Interpolates value between surrounding keyframes
insertKeyframeOnPath ::
  Text -> -- Layer ID
  Double -> -- Frame number to insert at
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text (Text, [Layer]) -- (created keyframe ID, updated layers list) or error
insertKeyframeOnPath layerId frame genId layers =
  -- Validate frame is finite and >= 1
  if not (validateFinite frame) || frame < 1
    then Left ("insertKeyframeOnPath: Invalid frame value (must be finite and >= 1): " <> T.pack (show frame))
    else
      case getLayerById layerId layers of
        Nothing -> Left ("Cannot insert keyframe on path: Layer \"" <> T.unpack layerId <> "\" not found")
        Just layer ->
          case findPropertyByPath layer "transform.position" of
            Nothing -> Left ("Cannot insert keyframe on path: Property \"transform.position\" not found on layer \"" <> T.unpack layerId <> "\"")
            Just positionProp ->
              if not (animatablePropertyAnimated positionProp) || length (animatablePropertyKeyframes positionProp) < 2
                then Left ("Cannot insert keyframe on path: Property \"transform.position\" is not animated or has fewer than 2 keyframes on layer \"" <> T.unpack layerId <> "\"")
                else
                  let
                    keyframes = animatablePropertyKeyframes positionProp
                    -- Check if keyframe already exists at this frame
                    mExisting = find (\k -> keyframeFrame k == frame) keyframes
                  in
                    case mExisting of
                      Just existing -> Right (keyframeId existing, layers)
                      Nothing ->
                        -- Find surrounding keyframes
                        let
                          (mBefore, mAfter) = findSurroundingKeyframes positionProp frame
                        in
                          case (mBefore, mAfter) of
                            (Nothing, _) -> Left ("Cannot insert keyframe on path: No keyframe before frame " <> T.pack (show frame) <> " for layer \"" <> T.unpack layerId <> "\"")
                            (_, Nothing) -> Left ("Cannot insert keyframe on path: No keyframe after frame " <> T.pack (show frame) <> " for layer \"" <> T.unpack layerId <> "\"")
                            (Just before, Just after) ->
                              -- Guard against division by zero (identical frames)
                              let
                                frameDiff = keyframeFrame after - keyframeFrame before
                              in
                                if frameDiff == 0
                                  then Left ("Cannot insert keyframe on path: Surrounding keyframes have identical frames (" <> T.pack (show (keyframeFrame before)) <> ")")
                                  else
                                    -- Interpolate the value at this frame
                                    let
                                      t = (frame - keyframeFrame before) / frameDiff
                                      -- Extract Position2DOr3D from PropertyValue
                                      interpolatedValue = case (keyframeValue before, keyframeValue after) of
                                        (PropertyValuePosition2DOr3D (Vec2 bx by) mbz, PropertyValuePosition2DOr3D (Vec2 ax ay) maz) ->
                                          let
                                            -- Interpolate x, y
                                            interpX = safeLerpD bx ax t
                                            interpY = safeLerpD by ay t
                                            -- Interpolate z if both have z
                                            interpZ = case (mbz, maz) of
                                              (Just bz, Just az) -> Just (safeLerpD bz az t)
                                              _ -> mbz -- Use before's z if available, otherwise Nothing
                                          in
                                            PropertyValuePosition2DOr3D (Vec2 interpX interpY) interpZ
                                        _ -> keyframeValue before -- Fallback to before value if types don't match
                                      
                                      -- Create the keyframe using addKeyframeWithPropertyValue
                                      result = addKeyframeWithPropertyValue layerId "transform.position" interpolatedValue (Just frame) frame genId layers
                                    in
                                      case result of
                                        Left err -> Left err
                                        Right (createdKf, updatedLayers) -> Right (keyframeId createdKf, updatedLayers)

-- ============================================================================
-- ROVING KEYFRAMES
-- ============================================================================

-- | Check if roving would significantly change keyframe timing
-- Pure function: takes layer ID and layers list
-- Returns true if roving would make significant changes (requires at least 3 keyframes)
checkRovingImpact ::
  Text -> -- Layer ID
  [Layer] -> -- Layers list
  Bool -- True if roving would make significant changes
checkRovingImpact layerId layers =
  case getLayerById layerId layers of
    Nothing -> False
    Just layer ->
      case findPropertyByPath layer "transform.position" of
        Nothing -> False
        Just positionProp ->
          if animatablePropertyAnimated positionProp && not (null (animatablePropertyKeyframes positionProp))
            then length (animatablePropertyKeyframes positionProp) >= 3
            else False

-- Note: applyRovingToPosition requires roving service migration
-- The roving service uses Three.js for curve path calculation
-- This will be implemented after the roving service is migrated to Haskell
