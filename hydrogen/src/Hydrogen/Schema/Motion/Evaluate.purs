-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // schema // motion // evaluate
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Keyframe Evaluation Engine
-- |
-- | Evaluates keyframe sequences at arbitrary frame positions, applying
-- | easing curves and interpolation. This is the core of motion graphics
-- | playback and animation preview.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.Evaluate as Eval
-- | import Hydrogen.Schema.Motion.Keyframe as KF
-- | import Hydrogen.Schema.Dimension.Temporal (frames)
-- |
-- | -- Define keyframes
-- | keyframes =
-- |   [ KF.keyframe (frames 0.0) (KF.NumberValue 0.0)
-- |   , KF.keyframe (frames 30.0) (KF.NumberValue 100.0)
-- |       # KF.withBezierTangents (KF.tangent 0.4 0.0) (KF.tangent 0.0 0.0)
-- |   , KF.keyframe (frames 60.0) (KF.NumberValue 50.0)
-- |   ]
-- |
-- | -- Evaluate at frame 15
-- | Eval.evaluateAt (frames 15.0) keyframes
-- | -- Returns: NumberValue 50.0 (halfway through first segment)
-- | ```
-- |
-- | ## Interpolation Modes
-- |
-- | - **Linear**: Straight lerp between keyframes
-- | - **Bezier**: Uses easing curve from outgoing keyframe's tangent
-- | - **Hold**: Value stays constant until next keyframe
-- | - **Auto**: Treated as linear (smooth tangents computed at edit time)
module Hydrogen.Schema.Motion.Evaluate
  ( -- * Core Evaluation
    evaluateAt
  , evaluateAtWithEasing
  
  -- * Keyframe Finding
  , findBracketingKeyframes
  , Bracket(..)
  
  -- * Progress Calculation
  , calculateProgress
  , applyEasing
  ) where

import Prelude
  ( compare
  , (-)
  , (/)
  , (<)
  , (<=)
  , (==)
  , (>)
  )

import Data.Array (head, last, sortBy, filter)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering)
import Hydrogen.Schema.Dimension.Temporal (Frames(Frames))
import Hydrogen.Schema.Motion.Easing (Easing)
import Hydrogen.Schema.Motion.Easing as Easing
import Hydrogen.Schema.Motion.Keyframe 
  ( Keyframe(Keyframe)
  , KeyframeValue
  , InterpolationType(Linear, Bezier, Hold, Auto)
  , Tangent(Tangent)
  , lerpValue
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // bracketing // keyframes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of finding keyframes that bracket a given frame position.
data Bracket
  = BeforeFirst Keyframe
    -- ^ Frame is before the first keyframe; return first keyframe value
  | AfterLast Keyframe
    -- ^ Frame is after the last keyframe; return last keyframe value
  | Between Keyframe Keyframe
    -- ^ Frame is between two keyframes; interpolate between them
  | ExactMatch Keyframe
    -- ^ Frame matches a keyframe exactly; return that keyframe value
  | NoKeyframes
    -- ^ No keyframes in the sequence

-- | Find the keyframes that bracket a given frame position.
-- |
-- | Keyframes are sorted by frame before searching.
findBracketingKeyframes :: Frames -> Array Keyframe -> Bracket
findBracketingKeyframes targetFrame keyframes =
  let
    sorted = sortBy compareKeyframeFrame keyframes
    Frames target = targetFrame
  in
    case head sorted, last sorted of
      Nothing, _ -> NoKeyframes
      _, Nothing -> NoKeyframes
      Just first, Just lastKf ->
        let
          Keyframe firstRec = first
          Keyframe lastRec = lastKf
          Frames firstFrame = firstRec.frame
          Frames lastFrame = lastRec.frame
        in
          -- Check bounds
          case target < firstFrame of
            true -> BeforeFirst first
            false -> case target > lastFrame of
              true -> AfterLast lastKf
              false -> findBetween target sorted

-- | Find the two keyframes that bracket the target frame.
findBetween :: Number -> Array Keyframe -> Bracket
findBetween target keyframes =
  let
    -- Find keyframes at or before target
    atOrBefore = filter (\(Keyframe kf) -> 
      let Frames f = kf.frame in f <= target) keyframes
    -- Find keyframes after target
    after = filter (\(Keyframe kf) -> 
      let Frames f = kf.frame in f > target) keyframes
  in
    case last atOrBefore, head after of
      Just prev, Just next ->
        let
          Keyframe prevRec = prev
          Frames prevFrame = prevRec.frame
        in
          case prevFrame == target of
            true -> ExactMatch prev
            false -> Between prev next
      Just kf, Nothing -> ExactMatch kf
      Nothing, Just kf -> BeforeFirst kf
      Nothing, Nothing -> NoKeyframes

-- | Compare keyframes by frame position
compareKeyframeFrame :: Keyframe -> Keyframe -> Ordering
compareKeyframeFrame (Keyframe a) (Keyframe b) =
  let
    Frames fa = a.frame
    Frames fb = b.frame
  in
    compare fa fb

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // progress // calculation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate the linear progress (0 to 1) between two keyframes.
calculateProgress :: Frames -> Keyframe -> Keyframe -> Number
calculateProgress (Frames target) (Keyframe prev) (Keyframe next) =
  let
    Frames startFrame = prev.frame
    Frames endFrame = next.frame
    duration = endFrame - startFrame
  in
    case duration <= 0.0 of
      true -> 1.0
      false -> (target - startFrame) / duration

-- | Apply easing based on the outgoing keyframe's tangent.
-- |
-- | For Bezier interpolation, we convert the tangent handles to a cubic
-- | bezier curve and evaluate it.
applyEasing :: InterpolationType -> Tangent -> Number -> Number
applyEasing interp (Tangent outTangent) t = case interp of
  Linear -> t
  Auto -> t  -- Auto is treated as linear at evaluation time
  Hold -> 0.0  -- Hold means no interpolation
  Bezier ->
    -- Convert tangent to cubic bezier and evaluate
    let
      -- Tangent x/y represent control point offsets
      -- Convert to normalized bezier control points
      p1x = outTangent.x
      p1y = outTangent.y
      -- Assume symmetric for now (in tangent of next keyframe)
      p2x = 1.0 - outTangent.x
      p2y = 1.0
      bezier = Easing.cubicBezier p1x p1y p2x p2y
    in
      Easing.evaluate bezier t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // core // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate keyframe sequence at a given frame position.
-- |
-- | This is the primary evaluation function. It:
-- | 1. Finds the bracketing keyframes
-- | 2. Calculates linear progress
-- | 3. Applies easing from the outgoing keyframe
-- | 4. Interpolates the value
evaluateAt :: Frames -> Array Keyframe -> Maybe KeyframeValue
evaluateAt targetFrame keyframes = case findBracketingKeyframes targetFrame keyframes of
  NoKeyframes -> Nothing
  
  BeforeFirst (Keyframe kf) -> Just kf.value
  
  AfterLast (Keyframe kf) -> Just kf.value
  
  ExactMatch (Keyframe kf) -> Just kf.value
  
  Between prev@(Keyframe prevRec) next@(Keyframe nextRec) ->
    let
      -- Linear progress
      t = calculateProgress targetFrame prev next
      -- Apply easing from outgoing keyframe
      easedT = case prevRec.interpolation of
        Hold -> 0.0  -- Hold stays at previous value
        _ -> applyEasing prevRec.interpolation prevRec.outTangent t
    in
      Just (lerpValue easedT prevRec.value nextRec.value)

-- | Evaluate with explicit easing override.
-- |
-- | Useful for spring animations where the easing comes from physics
-- | rather than keyframe tangents.
evaluateAtWithEasing :: Frames -> Easing -> Array Keyframe -> Maybe KeyframeValue
evaluateAtWithEasing targetFrame easing keyframes = 
  case findBracketingKeyframes targetFrame keyframes of
    NoKeyframes -> Nothing
    BeforeFirst (Keyframe kf) -> Just kf.value
    AfterLast (Keyframe kf) -> Just kf.value
    ExactMatch (Keyframe kf) -> Just kf.value
    Between prev@(Keyframe prevRec) (Keyframe nextRec) ->
      let
        t = calculateProgress targetFrame prev (Keyframe nextRec)
        easedT = Easing.evaluate easing t
      in
        Just (lerpValue easedT prevRec.value nextRec.value)


