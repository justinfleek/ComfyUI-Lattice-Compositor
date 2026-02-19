-- |
-- Module      : Lattice.State.Layer.Spline
-- Description : Spline operations for layers
-- 
-- Extracted from Lattice.State.Layer
-- Pure functions for spline control point manipulation, evaluation, and simplification
--
{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Spline
  ( addSplineControlPoint
  , insertSplineControlPoint
  , updateSplineControlPoint
  , deleteSplineControlPoint
  , enableSplineAnimation
  , addSplinePointKeyframe
  , addSplinePointPositionKeyframe
  , updateSplinePointWithKeyframe
  , getEvaluatedSplinePoints
  , simplifySpline
  , smoothSplineHandles
  , EvaluatedControlPoint(..)
  , SplinePointProperty(..)
  ) where

import Data.List (find, findIndex, last, splitAt, sortBy)
import Data.List.Index (imap)
import Data.Maybe (Maybe(..), isJust)
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , AnimatableControlPoint(..)
  , AnimatableHandle(..)
  , PropertyType(..)
  , Keyframe(..)
  , InterpolationType(..)
  , BaseInterpolationType(..)
  , ControlMode(..)
  , BezierHandle(..)
  , createAnimatableProperty
  , createKeyframe
  )
import Lattice.Types.Layer
  ( Layer(..)
  , LayerType(..)
  , LayerData(..)
  )
import Lattice.Types.LayerDataSpline
  ( SplineData(..)
  , ControlPoint(..)
  , ControlPointHandle(..)
  , ControlPointType(..)
  )
import Lattice.Utils.Interpolation
  ( findKeyframeIndex
  , interpolateNumber
  , cubicBezierEasing
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                      // spline // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Add a control point to a spline layer
-- Pure function: takes layer ID, control point, and layers list
-- Returns new layers list with added control point, or error if layer not found or not a spline layer
addSplineControlPoint ::
  Text -> -- Layer ID
  ControlPoint -> -- Control point to add
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with added control point, or error
addSplineControlPoint targetLayerId newPoint layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          let
            -- Add control point to list
            updatedControlPoints = splineDataControlPoints splineData ++ [newPoint]
            updatedSplineData = splineData {splineDataControlPoints = updatedControlPoints}
            updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
          in
            Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- | Insert a control point at a specific index in a spline layer
-- Pure function: takes layer ID, control point, index, and layers list
-- Returns new layers list with inserted control point, or error
insertSplineControlPoint ::
  Text -> -- Layer ID
  ControlPoint -> -- Control point to insert
  Int -> -- Index to insert at
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with inserted control point, or error
insertSplineControlPoint targetLayerId newPoint index layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          let
            -- Clamp index to valid range
            controlPoints = splineDataControlPoints splineData
            insertIndex = max 0 (min index (length controlPoints))
            
            -- Insert control point
            (before, after) = splitAt insertIndex controlPoints
            updatedControlPoints = before ++ [newPoint] ++ after
            
            updatedSplineData = splineData {splineDataControlPoints = updatedControlPoints}
            updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
          in
            Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- | Update a spline control point
-- Pure function: takes layer ID, point ID, partial updates, and layers list
-- Returns new layers list with updated control point, or error
updateSplineControlPoint ::
  Text -> -- Layer ID
  Text -> -- Point ID
  Maybe Double -> -- X update
  Maybe Double -> -- Y update
  Maybe Double -> -- Depth update
  Maybe ControlPointHandle -> -- HandleIn update
  Maybe ControlPointHandle -> -- HandleOut update
  Maybe ControlPointType -> -- Type update
  Maybe Text -> -- Group update
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with updated control point, or error
updateSplineControlPoint targetLayerId pointId mX mY mDepth mHandleIn mHandleOut mType mGroup layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          let
            -- Find and update control point
            updatePoint cp =
              if controlPointId cp == pointId
                then cp
                  { controlPointX = maybe (controlPointX cp) id mX
                  , controlPointY = maybe (controlPointY cp) id mY
                  , controlPointDepth = maybe (controlPointDepth cp) id mDepth
                  , controlPointHandleIn = maybe (controlPointHandleIn cp) id mHandleIn
                  , controlPointHandleOut = maybe (controlPointHandleOut cp) id mHandleOut
                  , controlPointType = maybe (controlPointType cp) id mType
                  , controlPointGroup = maybe (controlPointGroup cp) id mGroup
                  }
                else cp
            
            updatedControlPoints = map updatePoint (splineDataControlPoints splineData)
            
            -- Check if point was found
            pointFound = any (\cp -> controlPointId cp == pointId) (splineDataControlPoints splineData)
          in
            if pointFound
              then
                let
                  updatedSplineData = splineData {splineDataControlPoints = updatedControlPoints}
                  updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              else Left ("Control point not found: " <> pointId)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- | Delete a spline control point
-- Pure function: takes layer ID, point ID, and layers list
-- Returns new layers list with deleted control point, or error
deleteSplineControlPoint ::
  Text -> -- Layer ID
  Text -> -- Point ID
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with deleted control point, or error
deleteSplineControlPoint targetLayerId pointId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          let
            -- Filter out the control point
            updatedControlPoints = filter (\cp -> controlPointId cp /= pointId) (splineDataControlPoints splineData)
            
            -- Check if point was found
            pointFound = any (\cp -> controlPointId cp == pointId) (splineDataControlPoints splineData)
          in
            if pointFound
              then
                let
                  updatedSplineData = splineData {splineDataControlPoints = updatedControlPoints}
                  updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
              else Left ("Control point not found: " <> pointId)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- | Enable animation mode on a spline layer
-- Pure function: takes layer ID, ID generators for animatable properties, and layers list
-- Converts static controlPoints to animatedControlPoints
-- Returns new layers list with animation enabled, or error
enableSplineAnimation ::
  Text -> -- Layer ID
  (Text -> Text) -> -- ID generator for X property
  (Text -> Text) -> -- ID generator for Y property
  (Text -> Text) -> -- ID generator for depth property (if needed)
  (Text -> Text) -> -- ID generator for handle properties (if needed)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with animation enabled, or error
enableSplineAnimation targetLayerId genXId genYId genDepthId genHandleId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          -- Check if already animated
          if maybe False id (splineDataAnimated splineData) && isJust (splineDataAnimatedControlPoints splineData)
            then Right layers  -- Already animated, no change needed
            else
              let
                -- Convert static control points to animatable
                convertToAnimatable cp =
                  let
                    pointId = controlPointId cp
                    xId = genXId (pointId <> "_x")
                    yId = genYId (pointId <> "_y")
                    xProp = createAnimatableProperty xId "x" (controlPointX cp) PropertyTypeNumber Nothing
                    yProp = createAnimatableProperty yId "y" (controlPointY cp) PropertyTypeNumber Nothing
                    
                    depthProp = case controlPointDepth cp of
                      Just depth ->
                        let
                          depthId = genDepthId (pointId <> "_depth")
                        in
                          Just (createAnimatableProperty depthId "depth" depth PropertyTypeNumber Nothing)
                      Nothing -> Nothing
                    
                    handleInProp = case controlPointHandleIn cp of
                      Just handle ->
                        let
                          handleXId = genHandleId (pointId <> "_handleIn_x")
                          handleYId = genHandleId (pointId <> "_handleIn_y")
                          handleXProp = createAnimatableProperty handleXId "handleIn.x" (controlPointHandleX handle) PropertyTypeNumber Nothing
                          handleYProp = createAnimatableProperty handleYId "handleIn.y" (controlPointHandleY handle) PropertyTypeNumber Nothing
                        in
                          Just (AnimatableHandle handleXProp handleYProp)
                      Nothing -> Nothing
                    
                    handleOutProp = case controlPointHandleOut cp of
                      Just handle ->
                        let
                          handleXId = genHandleId (pointId <> "_handleOut_x")
                          handleYId = genHandleId (pointId <> "_handleOut_y")
                          handleXProp = createAnimatableProperty handleXId "handleOut.x" (controlPointHandleX handle) PropertyTypeNumber Nothing
                          handleYProp = createAnimatableProperty handleYId "handleOut.y" (controlPointHandleY handle) PropertyTypeNumber Nothing
                        in
                          Just (AnimatableHandle handleXProp handleYProp)
                      Nothing -> Nothing
                  in
                    AnimatableControlPoint
                      { animatableControlPointId = pointId
                      , animatableControlPointX = xProp
                      , animatableControlPointY = yProp
                      , animatableControlPointDepth = depthProp
                      , animatableControlPointHandleIn = handleInProp
                      , animatableControlPointHandleOut = handleOutProp
                      , animatableControlPointType = controlPointType cp
                      , animatableControlPointGroup = controlPointGroup cp
                      }
                
                animatedPoints = map convertToAnimatable (splineDataControlPoints splineData)
                
                updatedSplineData = splineData
                  { splineDataAnimatedControlPoints = Just animatedPoints
                  , splineDataAnimated = Just True
                  }
                
                updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
              in
                Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- ════════════════════════════════════════════════════════════════════════════
--                                       // spline // point // property // type
-- ════════════════════════════════════════════════════════════════════════════

-- | Property type for spline control point properties
data SplinePointProperty
  = SplinePointPropertyX
  | SplinePointPropertyY
  | SplinePointPropertyDepth
  | SplinePointPropertyHandleInX
  | SplinePointPropertyHandleInY
  | SplinePointPropertyHandleOutX
  | SplinePointPropertyHandleOutY
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                          // spline // keyframe // operations
-- ════════════════════════════════════════════════════════════════════════════

-- | Add a keyframe to a spline control point property at the specified frame
-- Pure function: takes layer ID, point ID, property, frame, ID generator, and layers list
-- Returns new layers list with added keyframe, or error
-- Auto-enables animation if needed
addSplinePointKeyframe ::
  Text -> -- Layer ID
  Text -> -- Point ID
  SplinePointProperty -> -- Property to keyframe
  Double -> -- Frame number
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with added keyframe, or error
addSplinePointKeyframe targetLayerId pointId property frame genKeyframeId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          -- Auto-enable animation if needed
          let
            (layersAfterAnimation, splineDataAfterAnimation) = if maybe False id (splineDataAnimated splineData) && isJust (splineDataAnimatedControlPoints splineData)
              then (layers, splineData)
              else
                -- Enable animation first
                case enableSplineAnimation targetLayerId (\s -> s <> "_x") (\s -> s <> "_y") (\s -> s <> "_depth") (\s -> s <> "_handle") layers of
                  Right updatedLayers ->
                    case getLayerById updatedLayers targetLayerId of
                      Just updatedLayer ->
                        case layerData updatedLayer of
                          Just (LayerDataSpline updatedSplineData) -> (updatedLayers, updatedSplineData)
                          _ -> (layers, splineData)
                      _ -> (layers, splineData)
                  Left _ -> (layers, splineData)
            
            -- Find the animated control point
            animatedPoints = case splineDataAnimatedControlPoints splineDataAfterAnimation of
              Just points -> points
              Nothing -> []
            
            point = find (\acp -> animatableControlPointId acp == pointId) animatedPoints
          in
            case point of
              Nothing -> Left ("Control point not found: " <> pointId)
              Just acp ->
                -- Get the property to keyframe
                let
                  (mProp, propName) = case property of
                    SplinePointPropertyX -> (Just (animatableControlPointX acp), "x")
                    SplinePointPropertyY -> (Just (animatableControlPointY acp), "y")
                    SplinePointPropertyDepth -> (animatableControlPointDepth acp, "depth")
                    SplinePointPropertyHandleInX -> case animatableControlPointHandleIn acp of
                      Just (AnimatableHandle hx _) -> (Just hx, "handleIn.x")
                      Nothing -> (Nothing, "handleIn.x")
                    SplinePointPropertyHandleInY -> case animatableControlPointHandleIn acp of
                      Just (AnimatableHandle _ hy) -> (Just hy, "handleIn.y")
                      Nothing -> (Nothing, "handleIn.y")
                    SplinePointPropertyHandleOutX -> case animatableControlPointHandleOut acp of
                      Just (AnimatableHandle hx _) -> (Just hx, "handleOut.x")
                      Nothing -> (Nothing, "handleOut.x")
                    SplinePointPropertyHandleOutY -> case animatableControlPointHandleOut acp of
                      Just (AnimatableHandle _ hy) -> (Just hy, "handleOut.y")
                      Nothing -> (Nothing, "handleOut.y")
                in
                  case mProp of
                    Nothing -> Left ("Property not found on control point: " <> propName)
                    Just prop ->
                      let
                        currentValue = animatablePropertyValue prop
                        currentKeyframes = animatablePropertyKeyframes prop
                        
                        -- Check if keyframe already exists at this frame
                        existingKeyframeIndex = findIndex (\kf -> keyframeFrame kf == frame) currentKeyframes
                        
                        -- Create new keyframe or update existing
                        mUpdatedKeyframes = case existingKeyframeIndex of
                          Just idx ->
                            -- Update existing keyframe value
                            let
                              -- Safe array access: idx is guaranteed valid from findIndex
                              -- findIndex returns Just only if element exists, so we can safely use drop
                              -- Pattern match on drop result - guaranteed non-empty since findIndex succeeded
                              existingKf = case drop idx currentKeyframes of
                                (kf : _) -> kf
                              updatedKf = existingKf {keyframeValue = currentValue}
                              before = take idx currentKeyframes
                              after = drop (idx + 1) currentKeyframes
                            in
                              Just (before ++ [updatedKf] ++ after)
                          Nothing ->
                            -- Add new keyframe
                            case createKeyframe (genKeyframeId ("kf_" <> pointId <> "_" <> propName)) frame currentValue (InterpolationBase InterpolationBezier) of
                              Right newKf ->
                                let
                                  allKeyframes = currentKeyframes ++ [newKf]
                                  sorted = sortBy (\k1 k2 -> compare (keyframeFrame k1) (keyframeFrame k2)) allKeyframes
                                in
                                  Just sorted
                              Left err -> Nothing
                      in
                        case mUpdatedKeyframes of
                          Nothing -> Left ("Failed to create keyframe: invalid frame value")
                          Just updatedKeyframes ->
                            let
                              -- Update the property
                              updatedProp = prop
                                { animatablePropertyKeyframes = updatedKeyframes
                                , animatablePropertyAnimated = True
                                }
                              
                              -- Update the control point with the new property
                              updatedAcp = case property of
                                SplinePointPropertyX -> acp {animatableControlPointX = updatedProp}
                                SplinePointPropertyY -> acp {animatableControlPointY = updatedProp}
                                SplinePointPropertyDepth -> acp {animatableControlPointDepth = Just updatedProp}
                                SplinePointPropertyHandleInX -> case animatableControlPointHandleIn acp of
                                  Just (AnimatableHandle _ hy) -> acp {animatableControlPointHandleIn = Just (AnimatableHandle updatedProp hy)}
                                  Nothing -> acp
                                SplinePointPropertyHandleInY -> case animatableControlPointHandleIn acp of
                                  Just (AnimatableHandle hx _) -> acp {animatableControlPointHandleIn = Just (AnimatableHandle hx updatedProp)}
                                  Nothing -> acp
                                SplinePointPropertyHandleOutX -> case animatableControlPointHandleOut acp of
                                  Just (AnimatableHandle _ hy) -> acp {animatableControlPointHandleOut = Just (AnimatableHandle updatedProp hy)}
                                  Nothing -> acp
                                SplinePointPropertyHandleOutY -> case animatableControlPointHandleOut acp of
                                  Just (AnimatableHandle hx _) -> acp {animatableControlPointHandleOut = Just (AnimatableHandle hx updatedProp)}
                                  Nothing -> acp
                              
                              -- Update animated control points list
                              updatedAnimatedPoints = map (\p -> if animatableControlPointId p == pointId then updatedAcp else p) animatedPoints
                              
                              -- Update spline data
                              updatedSplineData = splineDataAfterAnimation
                                { splineDataAnimatedControlPoints = Just updatedAnimatedPoints
                                , splineDataAnimated = Just True
                                }
                              
                              updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
                            in
                              Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layersAfterAnimation)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- | Add keyframes to all position properties (x, y) of a control point at once
-- Pure function: takes layer ID, point ID, frame, ID generator, and layers list
-- Returns new layers list with added keyframes, or error
addSplinePointPositionKeyframe ::
  Text -> -- Layer ID
  Text -> -- Point ID
  Double -> -- Frame number
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with added keyframes, or error
addSplinePointPositionKeyframe targetLayerId pointId frame genKeyframeId layers =
  case addSplinePointKeyframe targetLayerId pointId SplinePointPropertyX frame genKeyframeId layers of
    Left err -> Left err
    Right layersAfterX ->
      case addSplinePointKeyframe targetLayerId pointId SplinePointPropertyY frame genKeyframeId layersAfterX of
        Left err -> Left err
        Right layersAfterY -> Right layersAfterY

-- | Update a spline control point position and optionally add keyframe
-- Pure function: takes layer ID, point ID, x, y, frame, addKeyframe flag, ID generator, and layers list
-- Returns new layers list with updated position, or error
-- Used when dragging control points in the editor
updateSplinePointWithKeyframe ::
  Text -> -- Layer ID
  Text -> -- Point ID
  Double -> -- X position
  Double -> -- Y position
  Double -> -- Frame number
  Bool -> -- Add keyframe flag
  (Text -> Text) -> -- ID generator for keyframes
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with updated position, or error
updateSplinePointWithKeyframe targetLayerId pointId x y frame addKeyframe genKeyframeId layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          if maybe False id (splineDataAnimated splineData) && isJust (splineDataAnimatedControlPoints splineData)
            then
              -- Update animated control point
              case splineDataAnimatedControlPoints splineData of
                Just animatedPoints ->
                  case find (\acp -> animatableControlPointId acp == pointId) animatedPoints of
                    Nothing -> Left ("Control point not found: " <> pointId)
                    Just acp ->
                      let
                        -- Update X and Y values
                        updatedXProp = (animatableControlPointX acp) {animatablePropertyValue = x}
                        updatedYProp = (animatableControlPointY acp) {animatablePropertyValue = y}
                        updatedAcp = acp
                          { animatableControlPointX = updatedXProp
                          , animatableControlPointY = updatedYProp
                          }
                        
                        -- Update animated control points list
                        updatedAnimatedPoints = map (\p -> if animatableControlPointId p == pointId then updatedAcp else p) animatedPoints
                        
                        -- Update spline data
                        updatedSplineData = splineData
                          { splineDataAnimatedControlPoints = Just updatedAnimatedPoints
                          }
                        
                        updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
                        layersAfterUpdate = map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers
                        
                        -- Also update static control points for backwards compatibility
                        updatedStaticPoints =
                          map (\cp ->
                            if controlPointId cp == pointId
                              then cp { controlPointX = x, controlPointY = y }
                              else cp)
                            (splineDataControlPoints splineData)
                        
                        finalSplineData = updatedSplineData {splineDataControlPoints = updatedStaticPoints}
                        finalLayer = updatedLayer {layerData = Just (LayerDataSpline finalSplineData)}
                        finalLayers = map (\l -> if layerId l == targetLayerId then finalLayer else l) layersAfterUpdate
                        
                        -- Add keyframes if requested
                        result = if addKeyframe
                          then addSplinePointPositionKeyframe targetLayerId pointId frame genKeyframeId finalLayers
                          else Right finalLayers
                      in
                        result
                Nothing -> Left ("Animated control points not found for layer: " <> targetLayerId)
            else
              -- Update static control point
              let
                updatedControlPoints =
                  map (\cp ->
                    if controlPointId cp == pointId
                      then cp { controlPointX = x, controlPointY = y }
                      else cp
                  )
                  (splineDataControlPoints splineData)
                
                pointFound = any (\cp -> controlPointId cp == pointId) (splineDataControlPoints splineData)
              in
                if pointFound
                  then
                    let
                      updatedSplineData = splineData {splineDataControlPoints = updatedControlPoints}
                      updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
                    in
                      Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
                  else Left ("Control point not found: " <> pointId)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- ════════════════════════════════════════════════════════════════════════════
--                             // spline // evaluation // and // simplification
-- ════════════════════════════════════════════════════════════════════════════

-- | Evaluated control point at a specific frame
-- Result of interpolating an AnimatableControlPoint
data EvaluatedControlPoint = EvaluatedControlPoint
  { evaluatedControlPointId :: Text
  , evaluatedControlPointX :: Double
  , evaluatedControlPointY :: Double
  , evaluatedControlPointDepth :: Double
  , evaluatedControlPointHandleIn :: Maybe (Double, Double)  -- (x, y)
  , evaluatedControlPointHandleOut :: Maybe (Double, Double)  -- (x, y)
  , evaluatedControlPointType :: ControlPointType
  }
  deriving (Eq, Show)

-- | Interpolate an AnimatableProperty Double at a specific frame
-- Pure function: takes property, frame, returns interpolated value
interpolateAnimatableProperty ::
  AnimatableProperty Double ->
  Double ->
  Double
interpolateAnimatableProperty prop frame =
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

-- | Get evaluated (interpolated) control points at a specific frame
-- Pure function: takes layer ID, frame, and layers list, returns evaluated control points
getEvaluatedSplinePoints ::
  Text -> -- Layer ID
  Double -> -- Frame number
  [Layer] -> -- Current layers list
  Either Text [EvaluatedControlPoint] -- Returns evaluated control points, or error
getEvaluatedSplinePoints targetLayerId frame layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          -- If not animated, return static points as evaluated
          if maybe False id (splineDataAnimated splineData) && isJust (splineDataAnimatedControlPoints splineData)
            then
              case splineDataAnimatedControlPoints splineData of
                Just animatedPoints ->
                  Right (map (\acp ->
                    let
                      x = interpolateAnimatableProperty (animatableControlPointX acp) frame
                      y = interpolateAnimatableProperty (animatableControlPointY acp) frame
                      depth = maybe 0.0 (\d -> interpolateAnimatableProperty d frame) (animatableControlPointDepth acp)
                      
                      handleIn = case animatableControlPointHandleIn acp of
                        Just (AnimatableHandle handleX handleY) ->
                          Just (interpolateAnimatableProperty handleX frame, interpolateAnimatableProperty handleY frame)
                        Nothing -> Nothing
                      
                      handleOut = case animatableControlPointHandleOut acp of
                        Just (AnimatableHandle handleX handleY) ->
                          Just (interpolateAnimatableProperty handleX frame, interpolateAnimatableProperty handleY frame)
                        Nothing -> Nothing
                      
                      -- Get point type from static control point if available
                      pointType = case find (\cp -> controlPointId cp == animatableControlPointId acp) (splineDataControlPoints splineData) of
                        Just cp -> controlPointType cp
                        Nothing -> ControlPointTypeSmooth  -- Default
                    in
                      EvaluatedControlPoint
                        { evaluatedControlPointId = animatableControlPointId acp
                        , evaluatedControlPointX = x
                        , evaluatedControlPointY = y
                        , evaluatedControlPointDepth = depth
                        , evaluatedControlPointHandleIn = handleIn
                        , evaluatedControlPointHandleOut = handleOut
                        , evaluatedControlPointType = pointType
                        }
                  ) animatedPoints)
                Nothing -> Right []
            else
              -- Return static control points as evaluated
              Right (map (\cp ->
                EvaluatedControlPoint
                  { evaluatedControlPointId = controlPointId cp
                  , evaluatedControlPointX = controlPointX cp
                  , evaluatedControlPointY = controlPointY cp
                  , evaluatedControlPointDepth = maybe 0.0 id (controlPointDepth cp)
                  , evaluatedControlPointHandleIn = case controlPointHandleIn cp of
                      Just (ControlPointHandle hx hy) -> Just (hx, hy)
                      Nothing -> Nothing
                  , evaluatedControlPointHandleOut = case controlPointHandleOut cp of
                      Just (ControlPointHandle hx hy) -> Just (hx, hy)
                      Nothing -> Nothing
                  , evaluatedControlPointType = controlPointType cp
                  }
              ) (splineDataControlPoints splineData))
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- | Simplify a spline by reducing control points using Douglas-Peucker algorithm
-- Pure function: takes layer ID, tolerance, ID generator, and layers list
-- Returns new layers list with simplified spline, or error
simplifySpline ::
  Text -> -- Layer ID
  Double -> -- Tolerance (distance threshold in pixels, higher = more simplification)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with simplified spline, or error
simplifySpline targetLayerId tolerance layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          let
            controlPoints = splineDataControlPoints splineData
          in
            if length controlPoints <= 2
              then Right layers  -- Can't simplify with 2 or fewer points
              else
                let
                  -- Convert to simple points for Douglas-Peucker
                  points = map (\cp -> (controlPointX cp, controlPointY cp)) controlPoints
                  
                  -- Apply Douglas-Peucker simplification
                  simplified = douglasPeuckerSimplify points tolerance
                  
                  -- Map back to original control points (keep ones that survived simplification)
                  newControlPoints = filter (\cp ->
                    any (\(sx, sy) -> abs (controlPointX cp - sx) < 0.01 && abs (controlPointY cp - sy) < 0.01) simplified
                  ) controlPoints
                  
                  -- Also update animated control points if present
                  updatedAnimatedPoints = if maybe False id (splineDataAnimated splineData) && isJust (splineDataAnimatedControlPoints splineData)
                    then
                      case splineDataAnimatedControlPoints splineData of
                        Just animatedPoints ->
                          Just (filter (\acp -> any (\cp -> controlPointId cp == animatableControlPointId acp) newControlPoints) animatedPoints)
                        Nothing -> Nothing
                    else
                      splineDataAnimatedControlPoints splineData
                  
                  updatedSplineData = splineData
                    { splineDataControlPoints = newControlPoints
                    , splineDataAnimatedControlPoints = updatedAnimatedPoints
                    }
                  
                  updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)

-- | Douglas-Peucker line simplification algorithm
-- Pure function: takes points and tolerance, returns simplified points
douglasPeuckerSimplify ::
  [(Double, Double)] -> -- Points (x, y)
  Double -> -- Tolerance
  [(Double, Double)] -- Simplified points
douglasPeuckerSimplify points tolerance =
  case points of
    [] -> []
    [_] -> points
    [p1, p2] -> points
    start : rest ->
      let
        end = last (start : rest)
        middlePoints = init rest
        
        -- Find point with maximum distance from line between first and last
        (maxDist, maxIndex) = foldl (\(maxD, maxI) (i, (px, py)) ->
          let dist = perpendicularDist (px, py) start end
          in if dist > maxD then (dist, i) else (maxD, maxI)
        ) (0.0, 0) (zip [1..] middlePoints)
      in
        -- If max distance exceeds tolerance, recursively simplify
        if maxDist > tolerance
          then
            let
              left = douglasPeuckerSimplify (take (maxIndex + 1) points) tolerance
              right = douglasPeuckerSimplify (drop maxIndex points) tolerance
            in
              init left ++ right
          else
            [start, end]

-- | Calculate perpendicular distance from point to line segment
-- Pure function: takes point and line endpoints, returns distance
perpendicularDist ::
  (Double, Double) -> -- Point (x, y)
  (Double, Double) -> -- Line start (x, y)
  (Double, Double) -> -- Line end (x, y)
  Double -- Distance
perpendicularDist (px, py) (sx, sy) (ex, ey) =
  let
    dx = ex - sx
    dy = ey - sy
    length = sqrt (dx * dx + dy * dy)
  in
    if length < 0.0001
      then sqrt ((px - sx) ** 2 + (py - sy) ** 2)
      else
        let
          -- Project point onto line
          t = ((px - sx) * dx + (py - sy) * dy) / (length * length)
          closestX = sx + t * dx
          closestY = sy + t * dy
        in
          sqrt ((px - closestX) ** 2 + (py - closestY) ** 2)

-- | Smooth spline handles to create smoother curves
-- Pure function: takes layer ID, amount (0-100), ID generator, and layers list
-- Returns new layers list with smoothed handles, or error
smoothSplineHandles ::
  Text -> -- Layer ID
  Double -> -- Smoothing amount 0-100 (100 = fully smooth bezier handles)
  [Layer] -> -- Current layers list
  Either Text [Layer] -- Returns new layers list with smoothed handles, or error
smoothSplineHandles targetLayerId amount layers =
  case getLayerById layers targetLayerId of
    Nothing -> Left ("Layer not found: " <> targetLayerId)
    Just existingLayer ->
      case (layerType existingLayer, layerData existingLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          let
            controlPoints = splineDataControlPoints splineData
            factor = max 0.0 (min 100.0 amount) / 100.0
            closed = splineDataClosed splineData
          in
            if length controlPoints < 2
              then Right layers
              else
                let
                  -- Smooth handles for each control point
                  smoothPoint i cp =
                    let
                      prevIdx = (i - 1 + length controlPoints) `mod` length controlPoints
                      nextIdx = (i + 1) `mod` length controlPoints
                      -- Safe array access: indices are modulo-wrapped, so always valid
                      -- Use drop with pattern matching - modulo guarantees valid index
                      prev = case drop prevIdx controlPoints of
                        (p : _) -> p
                        [] -> cp  -- Should never happen due to mod, but type-safe fallback
                      next = case drop nextIdx controlPoints of
                        (n : _) -> n
                        [] -> cp  -- Should never happen due to mod, but type-safe fallback
                    in
                      -- Skip first/last point if path is not closed
                      if not closed && (i == 0 || i == length controlPoints - 1)
                        then cp
                        else
                          let
                            -- Calculate direction vectors
                            toPrevX = controlPointX prev - controlPointX cp
                            toPrevY = controlPointY prev - controlPointY cp
                            toNextX = controlPointX next - controlPointX cp
                            toNextY = controlPointY next - controlPointY cp
                            
                            -- Average direction (tangent)
                            avgDirX = toNextX - toPrevX
                            avgDirY = toNextY - toPrevY
                            avgLength = sqrt (avgDirX * avgDirX + avgDirY * avgDirY)
                          in
                            if avgLength < 0.01
                              then cp
                              else
                                let
                                  -- Normalize
                                  normalizedX = avgDirX / avgLength
                                  normalizedY = avgDirY / avgLength
                                  
                                  -- Calculate ideal handle length (1/3 of distance to neighbors)
                                  distPrev = sqrt (toPrevX * toPrevX + toPrevY * toPrevY)
                                  distNext = sqrt (toNextX * toNextX + toNextY * toNextY)
                                  handleLength = (distPrev + distNext) / 6.0
                                  
                                  -- Calculate ideal smooth handles
                                  idealInX = controlPointX cp - normalizedX * handleLength
                                  idealInY = controlPointY cp - normalizedY * handleLength
                                  idealOutX = controlPointX cp + normalizedX * handleLength
                                  idealOutY = controlPointY cp + normalizedY * handleLength
                                  
                                  -- Blend current handles toward ideal
                                  (newHandleIn, newHandleOut) = case (controlPointHandleIn cp, controlPointHandleOut cp) of
                                    (Just (ControlPointHandle hInX hInY), Just (ControlPointHandle hOutX hOutY)) ->
                                      ( Just (ControlPointHandle (hInX + (idealInX - hInX) * factor) (hInY + (idealInY - hInY) * factor))
                                      , Just (ControlPointHandle (hOutX + (idealOutX - hOutX) * factor) (hOutY + (idealOutY - hOutY) * factor))
                                      )
                                    (Just (ControlPointHandle hInX hInY), Nothing) ->
                                      ( Just (ControlPointHandle (hInX + (idealInX - hInX) * factor) (hInY + (idealInY - hInY) * factor))
                                      , Just (ControlPointHandle (idealOutX * factor + controlPointX cp * (1 - factor)) (idealOutY * factor + controlPointY cp * (1 - factor)))
                                      )
                                    (Nothing, Just (ControlPointHandle hOutX hOutY)) ->
                                      ( Just (ControlPointHandle (idealInX * factor + controlPointX cp * (1 - factor)) (idealInY * factor + controlPointY cp * (1 - factor)))
                                      , Just (ControlPointHandle (hOutX + (idealOutX - hOutX) * factor) (hOutY + (idealOutY - hOutY) * factor))
                                      )
                                    (Nothing, Nothing) ->
                                      ( Just (ControlPointHandle (idealInX * factor + controlPointX cp * (1 - factor)) (idealInY * factor + controlPointY cp * (1 - factor)))
                                      , Just (ControlPointHandle (idealOutX * factor + controlPointX cp * (1 - factor)) (idealOutY * factor + controlPointY cp * (1 - factor)))
                                      )
                                  
                                  updatedCp = cp
                                    { controlPointHandleIn = newHandleIn
                                    , controlPointHandleOut = newHandleOut
                                    , controlPointType = ControlPointTypeSmooth
                                    }
                                in
                                  updatedCp
                  
                  newControlPoints = imap smoothPoint controlPoints
                  
                  updatedSplineData = splineData {splineDataControlPoints = newControlPoints}
                  updatedLayer = existingLayer {layerData = Just (LayerDataSpline updatedSplineData)}
                in
                  Right (map (\l -> if layerId l == targetLayerId then updatedLayer else l) layers)
        _ -> Left ("Layer is not a spline layer: " <> targetLayerId)
