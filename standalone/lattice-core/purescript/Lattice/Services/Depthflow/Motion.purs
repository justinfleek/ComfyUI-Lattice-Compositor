-- | Lattice.Services.Depthflow.Motion - Depthflow Motion Components
-- |
-- | Pure mathematical functions for evaluating motion components in
-- | depth-based parallax animations. Includes easing functions and
-- | motion type evaluators.
-- |
-- | Features:
-- | - 7 easing types (linear, ease-in/out, bounce, elastic, back)
-- | - 8 motion types (linear, exponential, sine, cosine, arc, setTarget, bounce, elastic)
-- | - Motion component evaluation
-- | - Additive motion combination
-- |
-- | Source: ui/src/services/depthflow.ts

module Lattice.Services.Depthflow.Motion
  ( EasingType(..)
  , MotionType(..)
  , MotionComponent
  , mkMotionComponent
  , DepthflowParams
  , mkDepthflowParams
  , defaultMotionComponent
  , defaultDepthflowParams
  , applyEasing
  , evaluateLinear
  , evaluateExponential
  , evaluateSine
  , evaluateCosine
  , evaluateArc
  , evaluateBounce
  , evaluateElastic
  , evaluateMotionComponent
  , combineMotions
  , evaluateParams
  , calculateParallaxOffset
  , applyZoom
  , applyRotation
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (cos, exp, pi, pow, sin)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Easing type for motion curves
data EasingType
  = EasingLinear
  | EasingEaseIn
  | EasingEaseOut
  | EasingEaseInOut
  | EasingBounce
  | EasingElastic
  | EasingBack

derive instance eqEasingType :: Eq EasingType

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

derive instance eqMotionType :: Eq MotionType

-- | Motion component configuration
type MotionComponent =
  { motionType :: MotionType
  , startValue :: Number
  , endValue   :: Number
  , startFrame :: Number
  , endFrame   :: Number
  , easing     :: EasingType
  , amplitude  :: Number   -- For sine/cosine/arc
  , frequency  :: Number   -- For sine/cosine
  , loops      :: Number   -- Number of cycles
  , phase      :: Number   -- Starting phase (0-1)
  , enabled    :: Boolean
  }

mkMotionComponent :: MotionType -> Number -> Number -> Number -> Number -> EasingType -> MotionComponent
mkMotionComponent motionType startValue endValue startFrame endFrame easing =
  { motionType
  , startValue
  , endValue
  , startFrame
  , endFrame
  , easing
  , amplitude: 0.0
  , frequency: 1.0
  , loops: 1.0
  , phase: 0.0
  , enabled: true
  }

defaultMotionComponent :: MotionComponent
defaultMotionComponent =
  { motionType: MotionLinear
  , startValue: 0.0
  , endValue: 1.0
  , startFrame: 0.0
  , endFrame: 30.0
  , easing: EasingLinear
  , amplitude: 0.0
  , frequency: 1.0
  , loops: 1.0
  , phase: 0.0
  , enabled: true
  }

-- | Animated parameters for depth-based parallax
type DepthflowParams =
  { zoom       :: Number
  , offsetX    :: Number
  , offsetY    :: Number
  , rotation   :: Number
  , depthScale :: Number
  , focusDepth :: Number
  }

mkDepthflowParams :: Number -> Number -> Number -> Number -> Number -> Number -> DepthflowParams
mkDepthflowParams zoom offsetX offsetY rotation depthScale focusDepth =
  { zoom, offsetX, offsetY, rotation, depthScale, focusDepth }

defaultDepthflowParams :: DepthflowParams
defaultDepthflowParams =
  { zoom: 1.0
  , offsetX: 0.0
  , offsetY: 0.0
  , rotation: 0.0
  , depthScale: 1.0
  , focusDepth: 0.5
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Easing Functions
-- ────────────────────────────────────────────────────────────────────────────

-- | Apply easing function to normalized time (0-1).
-- |
-- | Converts linear progression to curved progression.
applyEasing :: Number -> EasingType -> Number
applyEasing t easing = case easing of
  EasingLinear -> t

  EasingEaseIn -> t * t

  EasingEaseOut -> 1.0 - (1.0 - t) * (1.0 - t)

  EasingEaseInOut ->
    if t < 0.5
    then 2.0 * t * t
    else 1.0 - (pow (-2.0 * t + 2.0) 2.0) / 2.0

  EasingBounce ->
    let n1 = 7.5625
        d1 = 2.75
    in if t < 1.0 / d1
       then n1 * t * t
       else if t < 2.0 / d1
            then let t' = t - 1.5 / d1 in n1 * t' * t' + 0.75
            else if t < 2.5 / d1
                 then let t' = t - 2.25 / d1 in n1 * t' * t' + 0.9375
                 else let t' = t - 2.625 / d1 in n1 * t' * t' + 0.984375

  EasingElastic ->
    let c4 = 2.0 * pi / 3.0
    in if t == 0.0 then 0.0
       else if t == 1.0 then 1.0
       else (pow 2.0 (-10.0 * t)) * sin ((t * 10.0 - 0.75) * c4) + 1.0

  EasingBack ->
    let c1 = 1.70158
        c3 = c1 + 1.0
    in 1.0 + c3 * (pow (t - 1.0) 3.0) + c1 * (pow (t - 1.0) 2.0)

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Evaluation
-- ────────────────────────────────────────────────────────────────────────────

-- | Evaluate linear interpolation between start and end values
evaluateLinear :: Number -> Number -> Number -> Number
evaluateLinear startValue endValue easedT =
  startValue + (endValue - startValue) * easedT

-- | Evaluate exponential interpolation.
-- | Falls back to linear when startValue is zero.
evaluateExponential :: Number -> Number -> Number -> Number
evaluateExponential startValue endValue easedT =
  if startValue == 0.0
  then endValue * easedT
  else let ratio = endValue / startValue
       in startValue * (pow ratio easedT)

-- | Evaluate sinusoidal motion
evaluateSine :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number
evaluateSine startValue endValue easedT amplitude frequency loops phase =
  let amp = if amplitude == 0.0 then (endValue - startValue) / 2.0 else amplitude
      freq = if frequency <= 0.0 then 1.0 else frequency
      baseValue = (startValue + endValue) / 2.0
  in baseValue + amp * sin ((easedT * loops + phase) * pi * 2.0 * freq)

-- | Evaluate cosinusoidal motion
evaluateCosine :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number
evaluateCosine startValue endValue easedT amplitude frequency loops phase =
  let amp = if amplitude == 0.0 then (endValue - startValue) / 2.0 else amplitude
      freq = if frequency <= 0.0 then 1.0 else frequency
      baseValue = (startValue + endValue) / 2.0
  in baseValue + amp * cos ((easedT * loops + phase) * pi * 2.0 * freq)

-- | Evaluate arc/parabolic motion
evaluateArc :: Number -> Number -> Number -> Number -> Number
evaluateArc startValue endValue easedT amplitude =
  let amp = if amplitude < 0.0 then 1.0 else amplitude
      range = endValue - startValue
      -- Parabolic arc: offset peaks at t=0.5
      arcOffset = amp * 4.0 * easedT * (1.0 - easedT)
  in startValue + range * easedT + arcOffset

-- | Evaluate bouncy motion with decay
evaluateBounce :: Number -> Number -> Number -> Number
evaluateBounce startValue endValue easedT =
  let baseValue = startValue + (endValue - startValue) * easedT
      bounceDecay = exp (-easedT * 5.0)
      bounce = sin (easedT * pi * 4.0) * bounceDecay * 0.2
  in baseValue * (1.0 + bounce)

-- | Evaluate elastic motion with overshoot
evaluateElastic :: Number -> Number -> Number -> Number
evaluateElastic startValue endValue easedT =
  let baseValue = startValue + (endValue - startValue) * easedT
  in if easedT == 0.0 || easedT == 1.0
     then baseValue
     else let elasticDecay = exp (-easedT * 3.0)
              elastic = sin (easedT * pi * 6.0) * elasticDecay * 0.3
          in baseValue * (1.0 + elastic)

-- | Evaluate a motion component at a specific frame.
-- |
-- | Returns Nothing if motion is disabled.
evaluateMotionComponent :: MotionComponent -> Number -> Maybe Number
evaluateMotionComponent motion frame
  | not motion.enabled = Nothing
  | frame < motion.startFrame = Just motion.startValue
  | frame > motion.endFrame = Just motion.endValue
  | otherwise =
      let duration = motion.endFrame - motion.startFrame
          localFrame = frame - motion.startFrame
          t = if duration > 0.0 then localFrame / duration else 1.0
          easedT = applyEasing t motion.easing
          startVal = motion.startValue
          endVal = motion.endValue
      in Just $ case motion.motionType of
           MotionLinear ->
             evaluateLinear startVal endVal easedT

           MotionExponential ->
             evaluateExponential startVal endVal easedT

           MotionSine ->
             evaluateSine startVal endVal easedT
               motion.amplitude motion.frequency
               motion.loops motion.phase

           MotionCosine ->
             evaluateCosine startVal endVal easedT
               motion.amplitude motion.frequency
               motion.loops motion.phase

           MotionArc ->
             evaluateArc startVal endVal easedT motion.amplitude

           MotionSetTarget ->
             if frame >= motion.startFrame then endVal else startVal

           MotionBounce ->
             evaluateBounce startVal endVal easedT

           MotionElastic ->
             evaluateElastic startVal endVal easedT

-- ────────────────────────────────────────────────────────────────────────────
-- Motion Combination
-- ────────────────────────────────────────────────────────────────────────────

-- | Combine multiple motion components additively.
-- |
-- | Each motion's delta from its start value is added to the base.
combineMotions :: Array MotionComponent -> Number -> Number -> Number
combineMotions motions frame baseValue =
  foldl addMotion baseValue motions
  where
    addMotion acc motion =
      case evaluateMotionComponent motion frame of
        Nothing -> acc  -- Disabled motion, skip
        Just value ->
          let delta = value - motion.startValue
          in acc + delta

-- | Evaluate all motion parameters at a frame
evaluateParams :: Array MotionComponent  -- ^ Zoom motions
               -> Array MotionComponent  -- ^ OffsetX motions
               -> Array MotionComponent  -- ^ OffsetY motions
               -> Array MotionComponent  -- ^ Rotation motions
               -> Array MotionComponent  -- ^ DepthScale motions
               -> Array MotionComponent  -- ^ FocusDepth motions
               -> Number                  -- ^ Frame
               -> DepthflowParams         -- ^ Base params
               -> DepthflowParams
evaluateParams zoomM offsetXM offsetYM rotationM depthScaleM focusDepthM frame base =
  { zoom: combineMotions zoomM frame base.zoom
  , offsetX: combineMotions offsetXM frame base.offsetX
  , offsetY: combineMotions offsetYM frame base.offsetY
  , rotation: combineMotions rotationM frame base.rotation
  , depthScale: combineMotions depthScaleM frame base.depthScale
  , focusDepth: combineMotions focusDepthM frame base.focusDepth
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Parallax Calculation
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate parallax offset based on depth.
-- |
-- | Objects closer than focus depth move more, objects further move less.
-- | Returns the offset multiplier for a given depth value.
calculateParallaxOffset :: Number -> Number -> Number -> Number
calculateParallaxOffset depth focusDepth depthScale =
  (depth - focusDepth) * depthScale

-- | Apply zoom to coordinate (relative to center 0.5, 0.5)
applyZoom :: Number -> Number -> Number
applyZoom coord zoom =
  if zoom == 0.0 then coord else coord / zoom

-- | Apply rotation to 2D coordinates.
-- |
-- | Rotates point around origin by given angle in degrees.
applyRotation :: Number -> Number -> Number -> Tuple Number Number
applyRotation x y angleDegrees =
  let angleRadians = angleDegrees * pi / 180.0
      cosA = cos angleRadians
      sinA = sin angleRadians
  in Tuple (x * cosA - y * sinA) (x * sinA + y * cosA)
