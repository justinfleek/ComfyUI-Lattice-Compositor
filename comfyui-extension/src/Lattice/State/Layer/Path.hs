-- |
-- Module      : Lattice.State.Layer.Path
-- Description : Path operations and calculations for layers
--
-- Extracted from Lattice.State.Layer
-- Pure functions for path sampling, bezier evaluation, and path-to-position conversion
--
{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Layer.Path
  ( copyPathToPosition
  , samplePathPoints
  , approximateBezierLength
  , evaluateCubicBezier
  , evaluateCubicBezierDerivative
  , SampledPoint(..)
  , PathSegment(..)
  ) where

import Data.List (find, reverse, zip)
import Data.List.Index (imap)
import Data.Maybe (Maybe(..))
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.State.Layer.Queries (getLayerById)
import Lattice.Types.Animation
  ( AnimatableProperty(..)
  , Keyframe(..)
  , InterpolationType(..)
  , BezierHandle(..)
  , ControlMode(..)
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
  )
import Lattice.Types.Primitives
  ( Vec2(..)
  , Vec3(..)
  , Position2DOr3D(..)
  )
import Lattice.Types.Transform (LayerTransform(..))

-- ============================================================================
-- PATH OPERATIONS
-- ============================================================================

-- | Copy a path from a spline layer and paste it as position keyframes on a target layer
-- Pure function: takes source spline layer ID, target layer ID, options, ID generators, and layers list
-- Returns number of keyframes created and new layers list, or error
copyPathToPosition ::
  Text -> -- Source spline layer ID
  Text -> -- Target layer ID
  Bool -> -- Use full duration
  Maybe Double -> -- Start frame (if not using full duration)
  Maybe Double -> -- End frame (if not using full duration)
  Maybe Int -> -- Keyframe count
  InterpolationType -> -- Interpolation type
  Bool -> -- Use spatial tangents
  Bool -> -- Reverse path
  Int -> -- Composition frame count
  (Text -> Text) -> -- ID generator for position property keyframes
  [Layer] -> -- Current layers list
  Either Text (Int, [Layer]) -- Returns (number of keyframes created, new layers list), or error
copyPathToPosition sourceSplineLayerId targetLayerId useFullDuration mStartFrame mEndFrame mKeyframeCount interpolation useSpatialTangents reversed frameCount genKeyframeId layers =
  case (getLayerById layers sourceSplineLayerId, getLayerById layers targetLayerId) of
    (Nothing, _) -> Left ("Source spline layer not found: " <> sourceSplineLayerId)
    (_, Nothing) -> Left ("Target layer not found: " <> targetLayerId)
    (Just sourceLayer, Just targetLayer) ->
      case (layerType sourceLayer, layerData sourceLayer) of
        (LayerTypeSpline, Just (LayerDataSpline splineData)) ->
          let
            controlPoints = splineDataControlPoints splineData
          in
            if length controlPoints < 2
              then Left ("Path needs at least 2 control points (found " <> T.pack (show (length controlPoints)) <> ")")
              else
                let
                  -- Calculate frame range
                  frameStart = if useFullDuration then 0.0 else maybe 0.0 id mStartFrame
                  frameEnd = if useFullDuration then fromIntegral (frameCount - 1) else maybe (fromIntegral (frameCount - 1)) id mEndFrame
                  frameDuration = frameEnd - frameStart
                  
                  -- Determine keyframe count
                  defaultKeyframeCount = max (length controlPoints) (ceiling (frameDuration / 5.0))
                  keyframeCount = maybe defaultKeyframeCount id mKeyframeCount
                  
                  -- Sample points along the path
                  closed = splineDataClosed splineData
                  sampledPoints = samplePathPoints controlPoints keyframeCount closed
                  finalSampledPoints = if reversed then reverse sampledPoints else sampledPoints
                  
                  -- Create keyframes
                  createKeyframe i sp =
                    let
                      t = if length finalSampledPoints > 1 then fromIntegral i / fromIntegral (length finalSampledPoints - 1) else 0.0
                      keyframeFrame = frameStart + t * frameDuration
                      depth = maybe 0.0 id (sampledPointDepth sp)
                      posValue = Position2DOr3D (sampledPointX sp) (sampledPointY sp) (Just depth)
                      
                      -- Calculate handle influence
                      prevFrame = if i > 0
                        then frameStart + (fromIntegral (i - 1) / fromIntegral (length finalSampledPoints - 1)) * frameDuration
                        else 0.0
                      nextFrame = if i < length finalSampledPoints - 1
                        then frameStart + (fromIntegral (i + 1) / fromIntegral (length finalSampledPoints - 1)) * frameDuration
                        else frameDuration
                      
                      inInfluence = (keyframeFrame - prevFrame) * 0.33
                      outInfluence = (nextFrame - keyframeFrame) * 0.33
                      
                      keyframeId_ = genKeyframeId ("path_" <> T.pack (show i))
                      
                      -- Apply spatial tangents if available
                      (spatialInTangent, spatialOutTangent) = if useSpatialTangents
                        then
                          case (sampledPointHandleIn sp, sampledPointHandleOut sp) of
                            (Just handleIn, Just handleOut) ->
                              let
                                inTan = Vec3 (vec2X handleIn - sampledPointX sp) (vec2Y handleIn - sampledPointY sp) 0.0
                                outTan = Vec3 (vec2X handleOut - sampledPointX sp) (vec2Y handleOut - sampledPointY sp) 0.0
                              in
                                (Just inTan, Just outTan)
                            _ -> (Nothing, Nothing)
                        else
                          (Nothing, Nothing)
                      
                      keyframe = Keyframe
                        { keyframeId = keyframeId_
                        , keyframeFrame = keyframeFrame
                        , keyframeValue = posValue
                        , keyframeInterpolation = interpolation
                        , keyframeInHandle = BezierHandle (-inInfluence) 0.0 True
                        , keyframeOutHandle = BezierHandle outInfluence 0.0 True
                        , keyframeControlMode = ControlSmooth
                        , keyframeSpatialInTangent = spatialInTangent
                        , keyframeSpatialOutTangent = spatialOutTangent
                        }
                    in
                      keyframe
                  
                  keyframes = imap createKeyframe finalSampledPoints
                  
                  -- Update target layer's position property
                  transform = layerTransform targetLayer
                  positionProp = transformPosition transform
                  updatedPositionProp = positionProp
                    { animatablePropertyKeyframes = keyframes
                    , animatablePropertyAnimated = True
                    }
                  
                  updatedTransform = transform {transformPosition = updatedPositionProp}
                  updatedTargetLayer = targetLayer {layerTransform = updatedTransform}
                  
                  newLayers = map (\l -> if layerId l == targetLayerId then updatedTargetLayer else l) layers
                in
                  Right (length keyframes, newLayers)
        _ -> Left ("Source layer is not a spline layer: " <> sourceSplineLayerId)

-- ============================================================================
-- PATH CALCULATIONS
-- ============================================================================

-- | Sampled point along a path
data SampledPoint = SampledPoint
  { sampledPointX :: Double
  , sampledPointY :: Double
  , sampledPointDepth :: Maybe Double
  , sampledPointHandleIn :: Maybe Vec2
  , sampledPointHandleOut :: Maybe Vec2
  }
  deriving (Eq, Show)

-- | Path segment for sampling
data PathSegment = PathSegment
  { segmentP0 :: Vec2
  , segmentP1 :: Vec2
  , segmentP2 :: Vec2
  , segmentP3 :: Vec2
  , segmentLength :: Double
  }
  deriving (Eq, Show)

-- | Sample points along a path at regular intervals
-- Pure function: takes control points, count, and closed flag, returns sampled points
samplePathPoints ::
  [ControlPoint] ->
  Int ->
  Bool ->
  [SampledPoint]
samplePathPoints controlPoints count closed =
  case controlPoints of
    [] -> []
    [cp] -> [SampledPoint (controlPointX cp) (controlPointY cp) (controlPointDepth cp) Nothing Nothing]
    _ ->
      let
        segments = buildPathSegments controlPoints closed
        totalLength = sum (map segmentLength segments)
        step = if count < 2 then 0 else totalLength / fromIntegral (count - 1)
      in
        sampleAlongPath segments step count

-- | Build path segments from control points
buildPathSegments ::
  [ControlPoint] ->
  Bool ->
  [PathSegment]
buildPathSegments controlPoints closed =
  let
    pairs = case controlPoints of
      [] -> []
      (_:rest) -> zip controlPoints rest
    segments =
      map (\(curr, next) ->
        let
          p0 = Vec2 (controlPointX curr) (controlPointY curr)
          p3 = Vec2 (controlPointX next) (controlPointY next)
          p1 = case controlPointHandleOut curr of
            Just (ControlPointHandle hx hy) -> Vec2 hx hy
            Nothing -> p0
          p2 = case controlPointHandleIn next of
            Just (ControlPointHandle hx hy) -> Vec2 hx hy
            Nothing -> p3
          len = approximateBezierLength p0 p1 p2 p3 10
        in
          PathSegment p0 p1 p2 p3 len)
        pairs
    
    closedSegment = if closed && length controlPoints > 2
      then
        case (reverse controlPoints, controlPoints) of
          (lastCp:remainingCps, firstCp:remainingCps2) ->  -- Explicit pattern match for both lists
            let
              p0 = Vec2 (controlPointX lastCp) (controlPointY lastCp)
              p3 = Vec2 (controlPointX firstCp) (controlPointY firstCp)
              p1 = case controlPointHandleOut lastCp of
                Just (ControlPointHandle hx hy) -> Vec2 hx hy
                Nothing -> p0
              p2 = case controlPointHandleIn firstCp of
                Just (ControlPointHandle hx hy) -> Vec2 hx hy
                Nothing -> p3
              len = approximateBezierLength p0 p1 p2 p3 10
            in
              [PathSegment p0 p1 p2 p3 len]
          _ -> []
      else []
  in
    segments ++ closedSegment

-- | Sample points along path segments
sampleAlongPath ::
  [PathSegment] ->
  Double ->
  Int ->
  [SampledPoint]
sampleAlongPath segments step count =
  if count < 2
    then case segments of
      [] -> []
      seg:_ -> [SampledPoint (vec2X (segmentP0 seg)) (vec2Y (segmentP0 seg)) Nothing Nothing Nothing]
    else
      let
        sampleAt dist = findPointAtDistance segments dist
      in
        map (\i -> sampleAt (fromIntegral i * step)) [0..count-1]

-- | Find point at specific distance along path
findPointAtDistance ::
  [PathSegment] ->
  Double ->
  SampledPoint
findPointAtDistance segments targetDist =
  case findSegment segments targetDist 0 of
    Nothing -> case segments of
      [] -> SampledPoint 0 0 Nothing Nothing Nothing
      seg:_ -> SampledPoint (vec2X (segmentP0 seg)) (vec2Y (segmentP0 seg)) Nothing Nothing Nothing
    Just (seg, segDist, currentDist) ->
      let
        segLen = segmentLength seg
        t = if segLen > 0
          then min 1.0 (segDist / segLen)
          else 0.0
        point = evaluateCubicBezier (segmentP0 seg) (segmentP1 seg) (segmentP2 seg) (segmentP3 seg) t
        tangent = evaluateCubicBezierDerivative (segmentP0 seg) (segmentP1 seg) (segmentP2 seg) (segmentP3 seg) t
        handleScale = 20.0
        handleIn = Vec2 (vec2X point - vec2X tangent * handleScale) (vec2Y point - vec2Y tangent * handleScale)
        handleOut = Vec2 (vec2X point + vec2X tangent * handleScale) (vec2Y point + vec2Y tangent * handleScale)
      in
        SampledPoint (vec2X point) (vec2Y point) Nothing (Just handleIn) (Just handleOut)

-- | Find segment containing target distance
findSegment ::
  [PathSegment] ->
  Double ->
  Double ->
  Maybe (PathSegment, Double, Double)
findSegment [] _ _ = Nothing
findSegment (seg:segs) targetDist currentDist =
  if targetDist <= currentDist + segmentLength seg
    then Just (seg, targetDist - currentDist, currentDist)
    else findSegment segs targetDist (currentDist + segmentLength seg)

-- | Approximate the length of a cubic bezier curve using chord length approximation
-- Pure function: takes bezier control points and sample count, returns approximate length
approximateBezierLength ::
  Vec2 ->
  Vec2 ->
  Vec2 ->
  Vec2 ->
  Int ->
  Double
approximateBezierLength p0 p1 p2 p3 samples =
  if samples <= 0
    then 0.0
    else
      let
        samplePoints = [0..samples]
        evaluateAt t = evaluateCubicBezier p0 p1 p2 p3 t
        points = map (\i -> evaluateAt (fromIntegral i / fromIntegral samples)) samplePoints
        pairs = case points of
          [] -> []
          (_:rest) -> zip points rest
      in
        sum (map (\(prev, curr) -> distance prev curr) pairs)
  where
    distance (Vec2 x1 y1) (Vec2 x2 y2) = sqrt ((x2 - x1) ** 2 + (y2 - y1) ** 2)

-- | Evaluate a cubic bezier curve at parameter t
-- Pure function: takes bezier control points and t (0-1), returns point on curve
evaluateCubicBezier ::
  Vec2 ->
  Vec2 ->
  Vec2 ->
  Vec2 ->
  Double ->
  Vec2
evaluateCubicBezier (Vec2 x0 y0) (Vec2 x1 y1) (Vec2 x2 y2) (Vec2 x3 y3) t =
  let
    t2 = t * t
    t3 = t2 * t
    mt = 1 - t
    mt2 = mt * mt
    mt3 = mt2 * mt
    x = mt3 * x0 + 3 * mt2 * t * x1 + 3 * mt * t2 * x2 + t3 * x3
    y = mt3 * y0 + 3 * mt2 * t * y1 + 3 * mt * t2 * y2 + t3 * y3
  in
    Vec2 x y

-- | Evaluate the derivative (tangent) of a cubic bezier curve at parameter t
-- Pure function: takes bezier control points and t (0-1), returns normalized tangent vector
evaluateCubicBezierDerivative ::
  Vec2 ->
  Vec2 ->
  Vec2 ->
  Vec2 ->
  Double ->
  Vec2
evaluateCubicBezierDerivative (Vec2 x0 y0) (Vec2 x1 y1) (Vec2 x2 y2) (Vec2 x3 y3) t =
  let
    t2 = t * t
    mt = 1 - t
    mt2 = mt * mt
    dx = 3 * mt2 * (x1 - x0) + 6 * mt * t * (x2 - x1) + 3 * t2 * (x3 - x2)
    dy = 3 * mt2 * (y1 - y0) + 6 * mt * t * (y2 - y1) + 3 * t2 * (y3 - y2)
    len = sqrt (dx * dx + dy * dy)
  in
    if len == 0
      then Vec2 0 0
      else Vec2 (dx / len) (dy / len)

-- | Vec2 accessors
vec2X :: Vec2 -> Double
vec2X (Vec2 x _) = x

vec2Y :: Vec2 -> Double
vec2Y (Vec2 _ y) = y
