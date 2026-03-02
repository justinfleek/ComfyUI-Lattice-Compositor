{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Depthflow.Motion
Description : Depthflow Motion Components
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for evaluating motion components in
depth-based parallax animations. Includes easing functions and
motion type evaluators.

Features:
- 7 easing types (linear, ease-in/out, bounce, elastic, back)
- 8 motion types (linear, exponential, sine, cosine, arc, setTarget, bounce, elastic)
- Motion component evaluation
- Additive motion combination

Source: ui/src/services/depthflow.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Depthflow.Motion
  ( -- * Types
    EasingType(..)
  , MotionType(..)
  , MotionComponent(..)
  , DepthflowParams(..)
    -- * Easing
  , applyEasing
    -- * Motion Evaluation
  , evaluateLinear
  , evaluateExponential
  , evaluateSine
  , evaluateCosine
  , evaluateArc
  , evaluateBounce
  , evaluateElastic
  , evaluateMotionComponent
    -- * Motion Combination
  , combineMotions
  , evaluateParams
    -- * Parallax
  , calculateParallaxOffset
  , applyZoom
  , applyRotation
    -- * Defaults
  , defaultMotionComponent
  , defaultDepthflowParams
  ) where

import Data.Maybe (fromMaybe)
import Data.Vector (Vector)
import qualified Data.Vector as V

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Easing type for motion curves
data EasingType
  = EasingLinear
  | EasingEaseIn
  | EasingEaseOut
  | EasingEaseInOut
  | EasingBounce
  | EasingElastic
  | EasingBack
  deriving (Show, Eq)

-- | Motion interpolation type
data MotionType
  = MotionLinear
  | MotionExponential
  | MotionSine
  | MotionCosine
  | MotionArc
  | MotionSetTarget
  | MotionBounce
  | MotionElastic
  deriving (Show, Eq)

-- | Motion component configuration
data MotionComponent = MotionComponent
  { mcMotionType :: MotionType
  , mcStartValue :: Double
  , mcEndValue   :: Double
  , mcStartFrame :: Double
  , mcEndFrame   :: Double
  , mcEasing     :: EasingType
  , mcAmplitude  :: Double   -- For sine/cosine/arc
  , mcFrequency  :: Double   -- For sine/cosine
  , mcLoops      :: Double   -- Number of cycles
  , mcPhase      :: Double   -- Starting phase (0-1)
  , mcEnabled    :: Bool
  } deriving (Show, Eq)

-- | Default motion component
defaultMotionComponent :: MotionComponent
defaultMotionComponent = MotionComponent
  { mcMotionType = MotionLinear
  , mcStartValue = 0
  , mcEndValue = 1
  , mcStartFrame = 0
  , mcEndFrame = 30
  , mcEasing = EasingLinear
  , mcAmplitude = 0
  , mcFrequency = 1
  , mcLoops = 1
  , mcPhase = 0
  , mcEnabled = True
  }

-- | Animated parameters for depth-based parallax
data DepthflowParams = DepthflowParams
  { dpZoom       :: Double
  , dpOffsetX    :: Double
  , dpOffsetY    :: Double
  , dpRotation   :: Double
  , dpDepthScale :: Double
  , dpFocusDepth :: Double
  } deriving (Show, Eq)

-- | Default depthflow params
defaultDepthflowParams :: DepthflowParams
defaultDepthflowParams = DepthflowParams
  { dpZoom = 1.0
  , dpOffsetX = 0.0
  , dpOffsetY = 0.0
  , dpRotation = 0.0
  , dpDepthScale = 1.0
  , dpFocusDepth = 0.5
  }

--------------------------------------------------------------------------------
-- Easing Functions
--------------------------------------------------------------------------------

-- | Apply easing function to normalized time (0-1).
--
-- Converts linear progression to curved progression.
applyEasing :: Double -> EasingType -> Double
applyEasing t easing = case easing of
  EasingLinear -> t

  EasingEaseIn -> t * t

  EasingEaseOut -> 1 - (1 - t) * (1 - t)

  EasingEaseInOut ->
    if t < 0.5
    then 2 * t * t
    else 1 - ((-2 * t + 2) ** 2) / 2

  EasingBounce ->
    let n1 = 7.5625
        d1 = 2.75
    in if t < 1 / d1
       then n1 * t * t
       else if t < 2 / d1
            then let t' = t - 1.5 / d1 in n1 * t' * t' + 0.75
            else if t < 2.5 / d1
                 then let t' = t - 2.25 / d1 in n1 * t' * t' + 0.9375
                 else let t' = t - 2.625 / d1 in n1 * t' * t' + 0.984375

  EasingElastic ->
    let c4 = 2 * pi / 3
    in if t == 0 then 0
       else if t == 1 then 1
       else (2 ** (-10 * t)) * sin ((t * 10 - 0.75) * c4) + 1

  EasingBack ->
    let c1 = 1.70158
        c3 = c1 + 1
    in 1 + c3 * ((t - 1) ** 3) + c1 * ((t - 1) ** 2)

--------------------------------------------------------------------------------
-- Motion Evaluation
--------------------------------------------------------------------------------

-- | Evaluate linear interpolation between start and end values
evaluateLinear :: Double -> Double -> Double -> Double
evaluateLinear startValue endValue easedT =
  startValue + (endValue - startValue) * easedT

-- | Evaluate exponential interpolation.
-- Falls back to linear when startValue is zero.
evaluateExponential :: Double -> Double -> Double -> Double
evaluateExponential startValue endValue easedT =
  if startValue == 0
  then endValue * easedT
  else let ratio = endValue / startValue
       in startValue * (ratio ** easedT)

-- | Evaluate sinusoidal motion
evaluateSine :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double
evaluateSine startValue endValue easedT amplitude frequency loops phase =
  let amp = if amplitude == 0 then (endValue - startValue) / 2 else amplitude
      freq = if frequency <= 0 then 1 else frequency
      baseValue = (startValue + endValue) / 2
  in baseValue + amp * sin ((easedT * loops + phase) * pi * 2 * freq)

-- | Evaluate cosinusoidal motion
evaluateCosine :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double
evaluateCosine startValue endValue easedT amplitude frequency loops phase =
  let amp = if amplitude == 0 then (endValue - startValue) / 2 else amplitude
      freq = if frequency <= 0 then 1 else frequency
      baseValue = (startValue + endValue) / 2
  in baseValue + amp * cos ((easedT * loops + phase) * pi * 2 * freq)

-- | Evaluate arc/parabolic motion
evaluateArc :: Double -> Double -> Double -> Double -> Double
evaluateArc startValue endValue easedT amplitude =
  let amp = if amplitude < 0 then 1 else amplitude
      range = endValue - startValue
      -- Parabolic arc: offset peaks at t=0.5
      arcOffset = amp * 4 * easedT * (1 - easedT)
  in startValue + range * easedT + arcOffset

-- | Evaluate bouncy motion with decay
evaluateBounce :: Double -> Double -> Double -> Double
evaluateBounce startValue endValue easedT =
  let baseValue = startValue + (endValue - startValue) * easedT
      bounceDecay = exp (-easedT * 5)
      bounce = sin (easedT * pi * 4) * bounceDecay * 0.2
  in baseValue * (1 + bounce)

-- | Evaluate elastic motion with overshoot
evaluateElastic :: Double -> Double -> Double -> Double
evaluateElastic startValue endValue easedT =
  let baseValue = startValue + (endValue - startValue) * easedT
  in if easedT == 0 || easedT == 1
     then baseValue
     else let elasticDecay = exp (-easedT * 3)
              elastic = sin (easedT * pi * 6) * elasticDecay * 0.3
          in baseValue * (1 + elastic)

-- | Evaluate a motion component at a specific frame.
--
-- Returns Nothing if motion is disabled.
evaluateMotionComponent :: MotionComponent -> Double -> Maybe Double
evaluateMotionComponent motion frame
  | not (mcEnabled motion) = Nothing
  | frame < mcStartFrame motion = Just (mcStartValue motion)
  | frame > mcEndFrame motion = Just (mcEndValue motion)
  | otherwise =
      let duration = mcEndFrame motion - mcStartFrame motion
          localFrame = frame - mcStartFrame motion
          t = if duration > 0 then localFrame / duration else 1
          easedT = applyEasing t (mcEasing motion)
          startVal = mcStartValue motion
          endVal = mcEndValue motion
      in Just $ case mcMotionType motion of
           MotionLinear ->
             evaluateLinear startVal endVal easedT

           MotionExponential ->
             evaluateExponential startVal endVal easedT

           MotionSine ->
             evaluateSine startVal endVal easedT
               (mcAmplitude motion) (mcFrequency motion)
               (mcLoops motion) (mcPhase motion)

           MotionCosine ->
             evaluateCosine startVal endVal easedT
               (mcAmplitude motion) (mcFrequency motion)
               (mcLoops motion) (mcPhase motion)

           MotionArc ->
             evaluateArc startVal endVal easedT (mcAmplitude motion)

           MotionSetTarget ->
             if frame >= mcStartFrame motion then endVal else startVal

           MotionBounce ->
             evaluateBounce startVal endVal easedT

           MotionElastic ->
             evaluateElastic startVal endVal easedT

--------------------------------------------------------------------------------
-- Motion Combination
--------------------------------------------------------------------------------

-- | Combine multiple motion components additively.
--
-- Each motion's delta from its start value is added to the base.
combineMotions :: Vector MotionComponent -> Double -> Double -> Double
combineMotions motions frame baseValue =
  V.foldl' addMotion baseValue motions
  where
    addMotion acc motion =
      case evaluateMotionComponent motion frame of
        Nothing -> acc  -- Disabled motion, skip
        Just value ->
          let delta = value - mcStartValue motion
          in acc + delta

-- | Evaluate all motion parameters at a frame
evaluateParams :: Vector MotionComponent  -- ^ Zoom motions
               -> Vector MotionComponent  -- ^ OffsetX motions
               -> Vector MotionComponent  -- ^ OffsetY motions
               -> Vector MotionComponent  -- ^ Rotation motions
               -> Vector MotionComponent  -- ^ DepthScale motions
               -> Vector MotionComponent  -- ^ FocusDepth motions
               -> Double                  -- ^ Frame
               -> DepthflowParams         -- ^ Base params
               -> DepthflowParams
evaluateParams zoomM offsetXM offsetYM rotationM depthScaleM focusDepthM frame base =
  DepthflowParams
    { dpZoom = combineMotions zoomM frame (dpZoom base)
    , dpOffsetX = combineMotions offsetXM frame (dpOffsetX base)
    , dpOffsetY = combineMotions offsetYM frame (dpOffsetY base)
    , dpRotation = combineMotions rotationM frame (dpRotation base)
    , dpDepthScale = combineMotions depthScaleM frame (dpDepthScale base)
    , dpFocusDepth = combineMotions focusDepthM frame (dpFocusDepth base)
    }

--------------------------------------------------------------------------------
-- Parallax Calculation
--------------------------------------------------------------------------------

-- | Calculate parallax offset based on depth.
--
-- Objects closer than focus depth move more, objects further move less.
-- Returns the offset multiplier for a given depth value.
calculateParallaxOffset :: Double -> Double -> Double -> Double
calculateParallaxOffset depth focusDepth depthScale =
  (depth - focusDepth) * depthScale

-- | Apply zoom to coordinate (relative to center 0.5, 0.5)
applyZoom :: Double -> Double -> Double
applyZoom coord zoom =
  if zoom == 0 then coord else coord / zoom

-- | Apply rotation to 2D coordinates.
--
-- Rotates point around origin by given angle in degrees.
applyRotation :: Double -> Double -> Double -> (Double, Double)
applyRotation x y angleDegrees =
  let angleRadians = angleDegrees * pi / 180
      cosA = cos angleRadians
      sinA = sin angleRadians
  in (x * cosA - y * sinA, x * sinA + y * cosA)
