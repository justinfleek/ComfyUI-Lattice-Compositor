-- |
-- Module      : Lattice.State.Keyframe.AutoBezier
-- Description : Auto bezier tangent operations
--
-- Migrated from ui/src/stores/keyframeStore/autoBezier.ts
-- Pure functions for auto-calculating bezier tangents for smooth keyframe curves
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Keyframe.AutoBezier
  ( autoCalculateBezierTangents
  , autoCalculateAllBezierTangents
  ) where

import Data.List (findIndex, sortBy)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Keyframe.Helpers (findPropertyByPath)
import Lattice.State.Keyframe.Interpolation
  ( setKeyframeHandle
  , setKeyframeInterpolation
  , setKeyframeControlMode
  )
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , BezierHandle(..)
  , ControlMode(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , Keyframe(..)
  , PropertyValue(..)
  )
import Lattice.Types.Layer (Layer(..))
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , validateFinite
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // auto // bezier // tangent // calculation
-- ════════════════════════════════════════════════════════════════════════════

-- | Extract numeric value from PropertyValue for tangent calculation
-- Returns first component of vector types, or the number itself
extractNumericValue :: PropertyValue -> Double
extractNumericValue pv = case pv of
  PropertyValueNumber n -> n
  PropertyValueVec3 (Vec3 x _ _) -> x
  PropertyValuePosition2DOr3D (Vec2 x _) _ -> x
  _ -> 0.0

-- | Auto-calculate bezier tangents for a keyframe based on surrounding keyframes
-- Pure function: takes layer ID, property path, keyframe ID, and layers list
-- Returns updated layers list or error
-- Creates smooth curves through keyframe values
-- Algorithm:
-- - For keyframes with both neighbors: tangent angle points from prev to next
-- - For first keyframe: tangent is horizontal (uses slope to next)
-- - For last keyframe: tangent is horizontal (uses slope from previous)
-- - Tangent magnitude is proportional to segment length
autoCalculateBezierTangents ::
  Text -> -- Layer ID
  Text -> -- Property path
  Text -> -- Keyframe ID
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Updated layers list or error
autoCalculateBezierTangents layerId propertyPath keyframeId layers =
  case getLayerById layerId layers of
    Nothing -> Right layers
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Right layers
        Just prop ->
          let
            keyframes = animatablePropertyKeyframes prop
          in
            if length keyframes < 2
              then Right layers
              else
                let
                  -- Sort keyframes by frame
                  sorted = sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) keyframes
                  mKfIndex = findIndex (\kf -> keyframeId kf == keyframeId) sorted
                in
                  case mKfIndex of
                    Nothing -> Right layers
                    Just kfIndex ->
                      let
                        -- Safe array access: kfIndex is guaranteed valid from findIndex
                        -- findIndex returns Just only if element exists, so we can safely use drop
                        -- Pattern match on drop result - guaranteed non-empty since findIndex succeeded
                        keyframe = case drop kfIndex sorted of
                          (kf : _) -> kf
                        prevKf = if kfIndex > 0
                          then case drop (kfIndex - 1) sorted of
                            (kf : _) -> Just kf
                            [] -> Nothing  -- Should never happen, but type-safe
                          else Nothing
                        nextKf = case drop (kfIndex + 1) sorted of
                          (kf : _) -> Just kf
                          [] -> Nothing
                        
                        -- Extract numeric value for tangent calculation
                        currentValue = extractNumericValue (keyframeValue keyframe)
                        
                        -- Calculate tangent direction (slope from prev to next)
                        (slopeFrame, slopeValue) = case (prevKf, nextKf) of
                          (Just prev, Just next) ->
                            -- Middle keyframe: slope from prev to next
                            let
                              prevValue = extractNumericValue (keyframeValue prev)
                              nextValue = extractNumericValue (keyframeValue next)
                              frameDelta = keyframeFrame next - keyframeFrame prev
                              valueDelta = nextValue - prevValue
                            in
                              (frameDelta / 2.0, valueDelta / 2.0)
                          
                          (Just prev, Nothing) ->
                            -- Last keyframe: use slope from previous segment
                            let
                              prevValue = extractNumericValue (keyframeValue prev)
                              frameDelta = keyframeFrame keyframe - keyframeFrame prev
                              valueDelta = currentValue - prevValue
                            in
                              (frameDelta / 3.0, valueDelta / 3.0)
                          
                          (Nothing, Just next) ->
                            -- First keyframe: use slope to next segment
                            let
                              nextValue = extractNumericValue (keyframeValue next)
                              frameDelta = keyframeFrame next - keyframeFrame keyframe
                              valueDelta = nextValue - currentValue
                            in
                              (frameDelta / 3.0, valueDelta / 3.0)
                          
                          (Nothing, Nothing) ->
                            -- Single keyframe: no tangent
                            (0.0, 0.0)
                        
                        -- Ensure slopes are finite
                        safeSlopeFrame = if validateFinite slopeFrame then slopeFrame else 0.0
                        safeSlopeValue = if validateFinite slopeValue then slopeValue else 0.0
                        
                        -- Set handles with calculated tangents
                        inHandle = BezierHandle
                          { bezierHandleFrame = -safeSlopeFrame
                          , bezierHandleValue = -safeSlopeValue
                          , bezierHandleEnabled = True
                          }
                        
                        outHandle = BezierHandle
                          { bezierHandleFrame = safeSlopeFrame
                          , bezierHandleValue = safeSlopeValue
                          , bezierHandleEnabled = True
                          }
                        
                        -- Apply handles, interpolation, and control mode
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
                                -- Set interpolation to bezier
                                case setKeyframeInterpolation layerId propertyPath keyframeId (InterpolationBase InterpolationBezier) updatedLayers2 of
                                  Left err -> Left err
                                  Right updatedLayers3 ->
                                    -- Set control mode to smooth
                                    setKeyframeControlMode layerId propertyPath keyframeId ControlSmooth updatedLayers3

-- | Auto-calculate bezier tangents for ALL keyframes on a property
-- Pure function: takes layer ID, property path, and layers list
-- Returns updated layers list and count of keyframes processed or error
-- Useful when converting from linear to bezier interpolation
autoCalculateAllBezierTangents ::
  Text -> -- Layer ID
  Text -> -- Property path
  [Layer] -> -- Current layers list
  Either Text (Int, [Layer]) -- (count processed, updated layers list) or error
autoCalculateAllBezierTangents layerId propertyPath layers =
  case getLayerById layerId layers of
    Nothing -> Right (0, layers)
    Just layer ->
      case findPropertyByPath layer propertyPath of
        Nothing -> Right (0, layers)
        Just prop ->
          let
            keyframes = animatablePropertyKeyframes prop
          in
            if length keyframes < 2
              then Right (0, layers)
              else
                let
                  -- Sort keyframes by frame
                  sorted = sortBy (\a b -> compare (keyframeFrame a) (keyframeFrame b)) keyframes
                  
                  -- Process each keyframe
                  processKeyframe accLayers index =
                    let
                      -- Safe array access: index is guaranteed valid (checked before calling)
                      -- Use drop with pattern matching - total and type-safe
                      keyframe = case drop index sorted of
                        (kf : _) -> kf
                      prevKf = if index > 0
                        then case drop (index - 1) sorted of
                          (kf : _) -> Just kf
                          [] -> Nothing  -- Should never happen, but type-safe
                        else Nothing
                      nextKf = case drop (index + 1) sorted of
                        (kf : _) -> Just kf
                        [] -> Nothing
                      
                      -- Extract numeric value
                      currentValue = extractNumericValue (keyframeValue keyframe)
                      
                      -- Calculate tangent direction
                      (slopeFrame, slopeValue) = case (prevKf, nextKf) of
                        (Just prev, Just next) ->
                          -- Middle keyframe: less aggressive for all-at-once
                          let
                            prevValue = extractNumericValue (keyframeValue prev)
                            nextValue = extractNumericValue (keyframeValue next)
                            frameDelta = keyframeFrame next - keyframeFrame prev
                            valueDelta = nextValue - prevValue
                          in
                            (frameDelta / 4.0, valueDelta / 4.0)
                        
                        (Just prev, Nothing) ->
                          -- Last keyframe
                          let
                            prevValue = extractNumericValue (keyframeValue prev)
                            frameDelta = keyframeFrame keyframe - keyframeFrame prev
                            valueDelta = currentValue - prevValue
                          in
                            (frameDelta / 3.0, valueDelta / 3.0)
                        
                        (Nothing, Just next) ->
                          -- First keyframe
                          let
                            nextValue = extractNumericValue (keyframeValue next)
                            frameDelta = keyframeFrame next - keyframeFrame keyframe
                            valueDelta = nextValue - currentValue
                          in
                            (frameDelta / 3.0, valueDelta / 3.0)
                        
                        (Nothing, Nothing) ->
                          -- Single keyframe: no tangent
                          (0.0, 0.0)
                      
                      -- Ensure slopes are finite
                      safeSlopeFrame = if validateFinite slopeFrame then slopeFrame else 0.0
                      safeSlopeValue = if validateFinite slopeValue then slopeValue else 0.0
                      
                      -- Set handles
                      inHandle = BezierHandle
                        { bezierHandleFrame = -safeSlopeFrame
                        , bezierHandleValue = -safeSlopeValue
                        , bezierHandleEnabled = True
                        }
                      
                      outHandle = BezierHandle
                        { bezierHandleFrame = safeSlopeFrame
                        , bezierHandleValue = safeSlopeValue
                        , bezierHandleEnabled = True
                        }
                      
                      -- Apply handles, interpolation, and control mode
                      result1 = setKeyframeHandle layerId propertyPath (keyframeId keyframe) True inHandle accLayers
                    in
                      case result1 of
                        Left err -> Left err
                        Right updatedLayers1 ->
                          case setKeyframeHandle layerId propertyPath (keyframeId keyframe) False outHandle updatedLayers1 of
                            Left err -> Left err
                            Right updatedLayers2 ->
                              case setKeyframeInterpolation layerId propertyPath (keyframeId keyframe) (InterpolationBase InterpolationBezier) updatedLayers2 of
                                Left err -> Left err
                                Right updatedLayers3 ->
                                  case setKeyframeControlMode layerId propertyPath (keyframeId keyframe) ControlSmooth updatedLayers3 of
                                    Left err -> Left err
                                    Right updatedLayers4 -> Right updatedLayers4
                  
                  -- Process all keyframes sequentially
                  processAll accLayers index =
                    if index >= length sorted
                      then Right (length sorted, accLayers)
                      else
                        case processKeyframe accLayers index of
                          Left err -> Left err
                          Right updatedLayers -> processAll updatedLayers (index + 1)
                in
                  processAll layers 0
