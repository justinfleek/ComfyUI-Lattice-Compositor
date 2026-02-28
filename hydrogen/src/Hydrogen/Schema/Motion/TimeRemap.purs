-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // motion // time-remap
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TimeRemap — Variable speed, time remapping, and ramps for animation.
-- |
-- | ## Design Philosophy
-- |
-- | Time remapping allows non-linear playback of animations:
-- |
-- | - **Speed curves**: Gradual acceleration/deceleration
-- | - **Time freeze**: Hold at specific frame
-- | - **Time reverse**: Play backwards
-- | - **Time stretch**: Slow motion or fast forward
-- | - **Ramps**: Gradual speed transitions
-- |
-- | This mirrors After Effects' Time Remap effect and Cinema 4D's
-- | F-Curve editor with explicit time control.
-- |
-- | ## Core Concept
-- |
-- | A TimeRemap maps input time to output time:
-- |
-- | ```
-- | outputTime = remap(inputTime)
-- | ```
-- |
-- | For example:
-- | - Linear: outputTime = inputTime (normal playback)
-- | - Reverse: outputTime = totalDuration - inputTime
-- | - Slow motion: outputTime = inputTime * 0.5
-- | - Speed ramp: outputTime follows a curve
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Schema.Motion.TimeRemap as TR
-- |
-- | -- Create slow motion (50% speed)
-- | slowMo = TR.uniformSpeed 0.5
-- |
-- | -- Create speed ramp (slow start, fast end)
-- | ramp = TR.speedRamp TR.easeIn 0.2 1.5
-- |
-- | -- Apply to animation time
-- | remappedTime = TR.apply 30.0 ramp  -- Remap frame 30
-- |
-- | -- Create freeze frame
-- | freeze = TR.freezeAt 60.0  -- Hold at frame 60
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Schema.Motion.Easing (curves for speed transitions)
-- | - Schema.Dimension.Temporal (Frames)

module Hydrogen.Schema.Motion.TimeRemap
  ( -- * Core Types
    TimeRemap(TimeRemap)
  , SpeedKeyframe(SpeedKeyframe)
  , RemapMode(..)
  
  -- * Construction
  , identity
  , uniformSpeed
  , reverse
  , freezeAt
  , timeStretch
  
  -- * Speed Ramps
  , speedRamp
  , speedRampIn
  , speedRampOut
  , speedRampInOut
  
  -- * Keyframe-Based
  , fromSpeedKeyframes
  , addSpeedKeyframe
  , removeSpeedKeyframe
  
  -- * Evaluation
  , apply
  , applyInverse
  , applyToProgress
  , speedAt
  , derivativeAt
  
  -- * Duration
  , remappedDuration
  , originalDuration
  , setOriginalDuration
  
  -- * Composition
  , compose
  , chain
  , blend
  
  -- * Presets
  , slowMotion
  , fastForward
  , pingPong
  , loop
  , hold
  , bounce
  
  -- * Analysis
  , averageSpeed
  , minSpeed
  , maxSpeed
  , isConstantSpeed
  
  -- * Sampling
  , sampleRemap
  , sampleSpeed
  
  -- * Utilities
  , defaultSpeed
  , isValidRemap
  , normalizeRemap
  , speedKeyframe
  , combineRemaps
  , speedMagnitude
  
  -- * Predicates
  , hasSpeedChange
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (/=)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , otherwise
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, index, snoc, foldl, sortBy, filter)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, abs)
import Data.Int (toNumber) as Int
import Data.Ordering (Ordering(..))

import Hydrogen.Schema.Motion.Easing (Easing, evaluate, linear, easeIn, easeOut, easeInOut)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mode of time remapping.
data RemapMode
  = LinearRemap              -- Constant speed factor
  | CurveRemap Easing        -- Speed follows easing curve
  | KeyframeRemap            -- Speed defined by keyframes
  | FreezeRemap Number       -- Frozen at specific time
  | PingPongRemap            -- Forward then backward
  | LoopRemap Number         -- Loop every n frames

derive instance eqRemapMode :: Eq RemapMode

instance showRemapMode :: Show RemapMode where
  show LinearRemap = "LinearRemap"
  show (CurveRemap _) = "CurveRemap"
  show KeyframeRemap = "KeyframeRemap"
  show (FreezeRemap t) = "(FreezeRemap " <> show t <> ")"
  show PingPongRemap = "PingPongRemap"
  show (LoopRemap n) = "(LoopRemap " <> show n <> ")"

-- | Speed keyframe for variable speed control.
-- |
-- | speed = 1.0 is normal, 0.5 is half speed, 2.0 is double, 0.0 is freeze.
newtype SpeedKeyframe = SpeedKeyframe
  { frame :: Number
  , speed :: Number
  , easing :: Easing  -- Transition to next keyframe
  }

derive instance eqSpeedKeyframe :: Eq SpeedKeyframe

instance showSpeedKeyframe :: Show SpeedKeyframe where
  show (SpeedKeyframe kf) = "(SpeedKeyframe frame:" <> show kf.frame 
    <> " speed:" <> show kf.speed <> ")"

-- | Complete time remap configuration.
newtype TimeRemap = TimeRemap
  { mode :: RemapMode
  , speedFactor :: Number           -- Base speed multiplier
  , startSpeed :: Number            -- Speed at start (for ramps)
  , endSpeed :: Number              -- Speed at end (for ramps)
  , originalDuration :: Number      -- Duration of source material (frames)
  , keyframes :: Array SpeedKeyframe
  }

derive instance eqTimeRemap :: Eq TimeRemap

instance showTimeRemap :: Show TimeRemap where
  show (TimeRemap tr) = "(TimeRemap mode:" <> show tr.mode 
    <> " speed:" <> show tr.speedFactor <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Identity remap (no change).
identity :: Number -> TimeRemap
identity dur = TimeRemap
  { mode: LinearRemap
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Uniform speed change.
-- |
-- | speed = 0.5 is slow motion, 2.0 is fast forward.
uniformSpeed :: Number -> Number -> TimeRemap
uniformSpeed speed dur = TimeRemap
  { mode: LinearRemap
  , speedFactor: speed
  , startSpeed: speed
  , endSpeed: speed
  , originalDuration: dur
  , keyframes: []
  }

-- | Reverse playback.
reverse :: Number -> TimeRemap
reverse dur = TimeRemap
  { mode: LinearRemap
  , speedFactor: negate 1.0
  , startSpeed: negate 1.0
  , endSpeed: negate 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Freeze at specific frame.
freezeAt :: Number -> Number -> TimeRemap
freezeAt freezeFrame dur = TimeRemap
  { mode: FreezeRemap freezeFrame
  , speedFactor: 0.0
  , startSpeed: 0.0
  , endSpeed: 0.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Time stretch (uniform speed to achieve target duration).
-- |
-- | targetDuration: how long you want the animation to last.
timeStretch :: Number -> Number -> TimeRemap
timeStretch targetDuration originalDur =
  let speed = if targetDuration < epsilon then 1.0 else originalDur / targetDuration
  in uniformSpeed speed originalDur

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // speed ramps
-- ═════════════════════════════════════════════════════════════════════════════

-- | Speed ramp with custom easing.
-- |
-- | Transitions from startSpeed to endSpeed following the easing curve.
speedRamp :: Easing -> Number -> Number -> Number -> TimeRemap
speedRamp eas startSpd endSpd dur = TimeRemap
  { mode: CurveRemap eas
  , speedFactor: (startSpd + endSpd) / 2.0  -- Average for reference
  , startSpeed: startSpd
  , endSpeed: endSpd
  , originalDuration: dur
  , keyframes: []
  }

-- | Speed ramp in (slow start).
speedRampIn :: Number -> Number -> Number -> TimeRemap
speedRampIn startSpd endSpd = speedRamp easeIn startSpd endSpd

-- | Speed ramp out (slow end).
speedRampOut :: Number -> Number -> Number -> TimeRemap
speedRampOut startSpd endSpd = speedRamp easeOut startSpd endSpd

-- | Speed ramp in-out (slow start and end).
speedRampInOut :: Number -> Number -> Number -> TimeRemap
speedRampInOut startSpd endSpd = speedRamp easeInOut startSpd endSpd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // keyframe-based
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create time remap from array of speed keyframes.
fromSpeedKeyframes :: Array SpeedKeyframe -> Number -> TimeRemap
fromSpeedKeyframes kfs dur = TimeRemap
  { mode: KeyframeRemap
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: sortKeyframes kfs
  }

-- | Add a speed keyframe.
addSpeedKeyframe :: SpeedKeyframe -> TimeRemap -> TimeRemap
addSpeedKeyframe kf (TimeRemap tr) = TimeRemap
  (tr { keyframes = sortKeyframes (snoc tr.keyframes kf), mode = KeyframeRemap })

-- | Remove speed keyframe at frame.
removeSpeedKeyframe :: Number -> TimeRemap -> TimeRemap
removeSpeedKeyframe frame (TimeRemap tr) = TimeRemap
  (tr { keyframes = filter (\(SpeedKeyframe k) -> k.frame /= frame) tr.keyframes })

-- | Sort keyframes by frame.
sortKeyframes :: Array SpeedKeyframe -> Array SpeedKeyframe
sortKeyframes = sortBy (\(SpeedKeyframe a) (SpeedKeyframe b) ->
  if a.frame < b.frame then LT
  else if a.frame > b.frame then GT
  else EQ
)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Apply time remap to input frame.
-- |
-- | Returns the output time (which frame of the source to display).
apply :: Number -> TimeRemap -> Number
apply inputFrame (TimeRemap tr) = case tr.mode of
  FreezeRemap freezeFrame -> freezeFrame
  
  PingPongRemap ->
    let 
      cycle = inputFrame / tr.originalDuration
      cycleInt = floorNum cycle
      frac = cycle - cycleInt
      isReverse = mod (floorInt cycleInt) 2 == 1
    in
      if isReverse then tr.originalDuration * (1.0 - frac)
      else tr.originalDuration * frac
  
  LoopRemap loopLen ->
    let normalizedFrame = inputFrame - loopLen * floorNum (inputFrame / loopLen)
    in clampNumber 0.0 tr.originalDuration normalizedFrame
  
  LinearRemap ->
    inputFrame * tr.speedFactor
  
  CurveRemap eas ->
    let
      -- Progress through animation
      progress = clamp01 (inputFrame / tr.originalDuration)
      -- Integrate speed to get position using trapezoidal approximation
    in
      integrateSpeed progress tr.startSpeed tr.endSpeed eas tr.originalDuration
  
  KeyframeRemap ->
    integrateKeyframes inputFrame tr.keyframes

-- | Apply inverse time remap: given output frame, find input frame.
-- |
-- | This is the inverse of `apply`: `applyInverse (apply x remap) remap ≈ x`
-- |
-- | **Limitations:**
-- | - FreezeRemap: Returns the freeze frame (not truly invertible)
-- | - KeyframeRemap: Uses linear approximation (may have error for complex curves)
-- | - CurveRemap: Uses Newton-Raphson iteration (may have numerical error)
-- |
-- | For modes where many inputs map to one output (freeze, loop), this returns
-- | a single representative input.
applyInverse :: Number -> TimeRemap -> Number
applyInverse outputFrame (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 
    -- Not invertible: any input maps to freezeFrame
    -- Return 0 as representative input
    0.0
  
  LinearRemap ->
    -- output = input * speed → input = output / speed
    if abs tr.speedFactor < epsilon then 0.0
    else outputFrame / tr.speedFactor
  
  PingPongRemap ->
    -- Forward: output = progress * duration
    -- Reverse: output = (1 - progress) * duration
    -- Invert by determining which phase and inverting
    let normalizedOutput = outputFrame / tr.originalDuration
    in if normalizedOutput <= 1.0
       then outputFrame  -- Forward phase: input = output
       else tr.originalDuration * 2.0 - outputFrame  -- Reverse phase
  
  LoopRemap _ ->
    -- output = input mod loopLen
    -- Inverse: just return the output (within one loop)
    outputFrame
  
  CurveRemap eas ->
    -- Use Newton-Raphson to solve: apply(x) = outputFrame
    invertCurveRemap outputFrame tr.startSpeed tr.endSpeed eas tr.originalDuration
  
  KeyframeRemap ->
    -- Approximate inverse using binary search
    invertKeyframeRemap outputFrame tr.keyframes tr.originalDuration

-- | Invert curve remap using Newton-Raphson iteration.
-- |
-- | Solves: integrateSpeed(x) = target for x
invertCurveRemap :: Number -> Number -> Number -> Easing -> Number -> Number
invertCurveRemap target startSpd endSpd eas dur =
  let
    -- Initial guess: assume average speed
    avgSpeed = (startSpd + endSpd) / 2.0
    initialGuess = if abs avgSpeed < epsilon then 0.0 else target / avgSpeed
    
    -- Newton-Raphson iteration
    iterate :: Int -> Number -> Number
    iterate 0 x = x
    iterate n x =
      let
        progress = clamp01 (x / dur)
        fx = integrateSpeed progress startSpd endSpd eas dur
        dfx = speedAtProgress progress startSpd endSpd eas
        newX = if abs dfx < epsilon then x else x - (fx - target) / dfx
      in
        if abs (fx - target) < epsilon then x
        else iterate (n - 1) (clamp01 newX * dur)
  in
    iterate 10 (clamp01 (initialGuess / dur) * dur)

-- | Speed at normalized progress for curve remap
speedAtProgress :: Number -> Number -> Number -> Easing -> Number
speedAtProgress progress startSpd endSpd eas =
  let easedProgress = evaluate eas progress
  in startSpd + easedProgress * (endSpd - startSpd)

-- | Invert keyframe remap using binary search.
invertKeyframeRemap :: Number -> Array SpeedKeyframe -> Number -> Number
invertKeyframeRemap target keyframes dur =
  let
    -- Binary search for input that produces target output
    search :: Number -> Number -> Int -> Number
    search lo hi 0 = (lo + hi) / 2.0
    search lo hi n =
      let mid = (lo + hi) / 2.0
          midOutput = integrateKeyframes mid keyframes
      in if abs (midOutput - target) < epsilon then mid
         else if midOutput < target then search mid hi (n - 1)
         else search lo mid (n - 1)
  in
    search 0.0 dur 20

-- | Apply remap to normalized progress (0-1).
applyToProgress :: Number -> TimeRemap -> Number
applyToProgress progress (TimeRemap tr) =
  let frame = progress * tr.originalDuration
      remappedFrame = apply frame (TimeRemap tr)
  in clamp01 (remappedFrame / tr.originalDuration)

-- | Get speed at specific frame.
speedAt :: Number -> TimeRemap -> Number
speedAt frame (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 
    let 
      cycle = frame / tr.originalDuration
      cycleInt = floorNum cycle
      isReverse = mod (floorInt cycleInt) 2 == 1
    in if isReverse then negate 1.0 else 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> tr.speedFactor
  CurveRemap eas ->
    let progress = clamp01 (frame / tr.originalDuration)
        easedProgress = evaluate eas progress
    in tr.startSpeed + easedProgress * (tr.endSpeed - tr.startSpeed)
  KeyframeRemap -> speedAtKeyframes frame tr.keyframes

-- | Derivative of remap function (rate of time change).
derivativeAt :: Number -> TimeRemap -> Number
derivativeAt = speedAt

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get remapped (output) duration.
remappedDuration :: TimeRemap -> Number
remappedDuration (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> tr.originalDuration  -- Input duration unchanged
  PingPongRemap -> tr.originalDuration * 2.0
  LoopRemap _ -> tr.originalDuration  -- Each loop
  LinearRemap -> 
    if abs tr.speedFactor < epsilon then tr.originalDuration
    else tr.originalDuration / abs tr.speedFactor
  CurveRemap _ ->
    -- Approximate by average speed
    let avgSpeed = (abs tr.startSpeed + abs tr.endSpeed) / 2.0
    in if avgSpeed < epsilon then tr.originalDuration
       else tr.originalDuration / avgSpeed
  KeyframeRemap -> tr.originalDuration  -- Complex, use original

-- | Get original duration.
originalDuration :: TimeRemap -> Number
originalDuration (TimeRemap tr) = tr.originalDuration

-- | Set original duration.
setOriginalDuration :: Number -> TimeRemap -> TimeRemap
setOriginalDuration dur (TimeRemap tr) = TimeRemap (tr { originalDuration = dur })

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // composition
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compose two remaps (apply first, then second).
compose :: TimeRemap -> TimeRemap -> TimeRemap
compose first second =
  -- Simplified: multiply speed factors
  let (TimeRemap f) = first
      (TimeRemap s) = second
  in TimeRemap
    { mode: LinearRemap
    , speedFactor: f.speedFactor * s.speedFactor
    , startSpeed: f.startSpeed * s.startSpeed
    , endSpeed: f.endSpeed * s.endSpeed
    , originalDuration: f.originalDuration
    , keyframes: []
    }

-- | Chain remaps (first plays, then second).
chain :: TimeRemap -> TimeRemap -> TimeRemap
chain first second =
  let (TimeRemap f) = first
      (TimeRemap s) = second
  in TimeRemap
    { mode: f.mode  -- Keep first's mode
    , speedFactor: f.speedFactor
    , startSpeed: f.startSpeed
    , endSpeed: f.endSpeed
    , originalDuration: f.originalDuration + s.originalDuration
    , keyframes: f.keyframes
    }

-- | Blend two remaps with weight.
-- |
-- | weight = 0.0 gives first, weight = 1.0 gives second.
blend :: Number -> TimeRemap -> TimeRemap -> TimeRemap
blend weight first second =
  let 
    w = clamp01 weight
    mw = 1.0 - w
    (TimeRemap f) = first
    (TimeRemap s) = second
  in TimeRemap
    { mode: LinearRemap
    , speedFactor: mw * f.speedFactor + w * s.speedFactor
    , startSpeed: mw * f.startSpeed + w * s.startSpeed
    , endSpeed: mw * f.endSpeed + w * s.endSpeed
    , originalDuration: f.originalDuration
    , keyframes: []
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Slow motion preset (50% speed).
slowMotion :: Number -> TimeRemap
slowMotion = uniformSpeed 0.5

-- | Fast forward preset (2x speed).
fastForward :: Number -> TimeRemap
fastForward = uniformSpeed 2.0

-- | Ping-pong preset (forward then reverse).
pingPong :: Number -> TimeRemap
pingPong dur = TimeRemap
  { mode: PingPongRemap
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Loop preset.
loop :: Number -> Number -> TimeRemap
loop loopLen dur = TimeRemap
  { mode: LoopRemap loopLen
  , speedFactor: 1.0
  , startSpeed: 1.0
  , endSpeed: 1.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Hold preset (freeze at end).
hold :: Number -> TimeRemap
hold dur = TimeRemap
  { mode: FreezeRemap dur
  , speedFactor: 0.0
  , startSpeed: 0.0
  , endSpeed: 0.0
  , originalDuration: dur
  , keyframes: []
  }

-- | Bounce preset (ease in-out with brief hold at extremes).
bounce :: Number -> TimeRemap
bounce dur = speedRampInOut 0.0 2.0 dur

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // analysis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Average speed over duration.
averageSpeed :: TimeRemap -> Number
averageSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> abs tr.speedFactor
  CurveRemap _ -> (abs tr.startSpeed + abs tr.endSpeed) / 2.0
  KeyframeRemap ->
    let speeds = map (\(SpeedKeyframe k) -> abs k.speed) tr.keyframes
        n = length speeds
    in if n == 0 then 1.0 else foldl (+) 0.0 speeds / Int.toNumber n

-- | Minimum speed in remap.
minSpeed :: TimeRemap -> Number
minSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> abs tr.speedFactor
  CurveRemap _ -> min (abs tr.startSpeed) (abs tr.endSpeed)
  KeyframeRemap -> 
    foldl (\acc (SpeedKeyframe k) -> min acc (abs k.speed)) infinity tr.keyframes

-- | Maximum speed in remap.
maxSpeed :: TimeRemap -> Number
maxSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> 0.0
  PingPongRemap -> 1.0
  LoopRemap _ -> 1.0
  LinearRemap -> abs tr.speedFactor
  CurveRemap _ -> max (abs tr.startSpeed) (abs tr.endSpeed)
  KeyframeRemap ->
    foldl (\acc (SpeedKeyframe k) -> max acc (abs k.speed)) 0.0 tr.keyframes

-- | Check if speed is constant.
isConstantSpeed :: TimeRemap -> Boolean
isConstantSpeed (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> true
  LinearRemap -> true
  LoopRemap _ -> true
  PingPongRemap -> false
  CurveRemap _ -> abs (tr.startSpeed - tr.endSpeed) < epsilon
  KeyframeRemap -> length tr.keyframes <= 1

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // sampling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sample remap at n evenly-spaced frames.
sampleRemap :: Int -> TimeRemap -> Array Number
sampleRemap n remap =
  let (TimeRemap tr) = remap
  in buildArray (n + 1) (\i ->
       let frame = Int.toNumber i / Int.toNumber n * tr.originalDuration
       in Just (apply frame remap)
     )

-- | Sample speed at n evenly-spaced frames.
sampleSpeed :: Int -> TimeRemap -> Array Number
sampleSpeed n remap =
  let (TimeRemap tr) = remap
  in buildArray (n + 1) (\i ->
       let frame = Int.toNumber i / Int.toNumber n * tr.originalDuration
       in Just (speedAt frame remap)
     )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Integrate speed curve to get position.
integrateSpeed :: Number -> Number -> Number -> Easing -> Number -> Number
integrateSpeed progress startSpd endSpd eas dur =
  -- Trapezoidal integration over the speed curve
  let 
    numSamples = 20
    dt = dur / Int.toNumber numSamples
    sumResult = foldl (\acc i ->
      let 
        t = Int.toNumber i / Int.toNumber numSamples
        -- Only integrate up to progress point
        contributionT = min t progress
        easedT = evaluate eas contributionT
        speed = startSpd + easedT * (endSpd - startSpd)
      in 
        if t <= progress then acc + speed * dt
        else acc
    ) 0.0 (buildIntArray (numSamples + 1))
  in sumResult

-- | Get speed at frame from keyframes.
speedAtKeyframes :: Number -> Array SpeedKeyframe -> Number
speedAtKeyframes frame kfs =
  let n = length kfs
  in if n == 0 then 1.0
     else
       case findSurroundingKeyframes frame kfs of
         { before: Just (SpeedKeyframe kb), after: Just (SpeedKeyframe ka) } ->
           if ka.frame == kb.frame then kb.speed
           else
             let 
               t = (frame - kb.frame) / (ka.frame - kb.frame)
               easedT = evaluate kb.easing t
             in kb.speed + easedT * (ka.speed - kb.speed)
         { before: Just (SpeedKeyframe kb), after: Nothing } -> kb.speed
         { before: Nothing, after: Just (SpeedKeyframe ka) } -> ka.speed
         _ -> 1.0

-- | Integrate keyframes to get time.
integrateKeyframes :: Number -> Array SpeedKeyframe -> Number
integrateKeyframes frame kfs =
  let n = length kfs
  in if n == 0 then frame  -- No keyframes = identity
     else
       -- Sum contributions from each keyframe segment
       foldl (\acc i ->
         case { k1: index kfs i, k2: index kfs (i + 1) } of
           { k1: Just (SpeedKeyframe kb), k2: Just (SpeedKeyframe ka) } ->
             if frame < kb.frame then acc
             else if frame >= ka.frame then
               -- Full segment
               let avgSpeed = (kb.speed + ka.speed) / 2.0
                   segDur = ka.frame - kb.frame
               in acc + avgSpeed * segDur
             else
               -- Partial segment
               let 
                 t = (frame - kb.frame) / (ka.frame - kb.frame)
                 easedT = evaluate kb.easing t
                 currentSpeed = kb.speed + easedT * (ka.speed - kb.speed)
                 avgSpeed = (kb.speed + currentSpeed) / 2.0
                 segDur = frame - kb.frame
               in acc + avgSpeed * segDur
           _ -> acc
       ) 0.0 (buildIntArray (max 0 (n - 1)))

-- | Find keyframes surrounding a frame.
findSurroundingKeyframes :: Number -> Array SpeedKeyframe 
  -> { before :: Maybe SpeedKeyframe, after :: Maybe SpeedKeyframe }
findSurroundingKeyframes frame kfs =
  let n = length kfs
  in foldl (\acc i ->
       case index kfs i of
         Nothing -> acc
         Just kf@(SpeedKeyframe k) ->
           if k.frame <= frame then
             case acc.before of
               Nothing -> acc { before = Just kf }
               Just (SpeedKeyframe prev) -> 
                 if k.frame > prev.frame then acc { before = Just kf }
                 else acc
           else
             case acc.after of
               Nothing -> acc { after = Just kf }
               Just (SpeedKeyframe next) ->
                 if k.frame < next.frame then acc { after = Just kf }
                 else acc
     ) { before: Nothing, after: Nothing } (buildIntArray n)

-- | Clamp to [0, 1]
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n

-- | Clamp to range
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi n
  | n < lo = lo
  | n > hi = hi
  | otherwise = n

-- | Floor
floorNum :: Number -> Number
floorNum n = Int.toNumber (floorInt n)

floorInt :: Number -> Int
floorInt n = 
  if n >= 0.0 then truncateToInt n
  else truncateToInt n - 1

truncateToInt :: Number -> Int
truncateToInt n = truncateImpl n 0

truncateImpl :: Number -> Int -> Int
truncateImpl n acc =
  if n < 1.0 then acc
  else truncateImpl (n - 1.0) (acc + 1)

-- | Integer modulo
mod :: Int -> Int -> Int
mod a b = a - (a / b) * b

-- | Small epsilon
epsilon :: Number
epsilon = 1.0e-10

-- | Large number for min comparisons
infinity :: Number
infinity = 1.0e308

-- | Build array from function
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default speed (normal playback).
defaultSpeed :: Number
defaultSpeed = 1.0

-- | Check if time remap is valid.
-- |
-- | A remap is valid if duration is positive and speeds are reasonable.
isValidRemap :: TimeRemap -> Boolean
isValidRemap (TimeRemap tr) =
  tr.originalDuration > 0.0 &&
  abs tr.speedFactor < infinity &&
  abs tr.startSpeed < infinity &&
  abs tr.endSpeed < infinity

-- | Normalize remap to have average speed of 1.0.
normalizeRemap :: TimeRemap -> TimeRemap
normalizeRemap remap =
  let 
    avg = averageSpeed remap
    (TimeRemap tr) = remap
    scaleFactor = if avg < epsilon then 1.0 else 1.0 / avg
  in TimeRemap
    { mode: tr.mode
    , speedFactor: tr.speedFactor * scaleFactor
    , startSpeed: tr.startSpeed * scaleFactor
    , endSpeed: tr.endSpeed * scaleFactor
    , originalDuration: tr.originalDuration
    , keyframes: map (\(SpeedKeyframe k) -> 
        SpeedKeyframe (k { speed = k.speed * scaleFactor })) tr.keyframes
    }

-- | Create a speed keyframe with linear easing.
speedKeyframe :: Number -> Number -> SpeedKeyframe
speedKeyframe frame spd = SpeedKeyframe
  { frame: frame
  , speed: spd
  , easing: linear
  }

-- | Combine multiple remaps by averaging their effects.
combineRemaps :: Array TimeRemap -> TimeRemap
combineRemaps remaps =
  let 
    n = length remaps
    nNum = Int.toNumber n
  in
    if n == 0 then identity 100.0
    else if n == 1 then fromMaybe (identity 100.0) (index remaps 0)
    else
      let
        sumSpeeds = foldl (\acc (TimeRemap tr) -> 
          { start: acc.start + tr.startSpeed
          , end: acc.end + tr.endSpeed
          , factor: acc.factor + tr.speedFactor
          , dur: max acc.dur tr.originalDuration
          }) { start: 0.0, end: 0.0, factor: 0.0, dur: 0.0 } remaps
      in TimeRemap
        { mode: LinearRemap
        , speedFactor: sumSpeeds.factor / nNum
        , startSpeed: sumSpeeds.start / nNum
        , endSpeed: sumSpeeds.end / nNum
        , originalDuration: sumSpeeds.dur
        , keyframes: []
        }

-- | Square root for speed calculations (2D speed vector magnitude).
speedMagnitude :: Number -> Number -> Number
speedMagnitude sx sy = sqrt (sx * sx + sy * sy)

-- | Check if remap has any speed change (not identity).
hasSpeedChange :: TimeRemap -> Boolean
hasSpeedChange (TimeRemap tr) = case tr.mode of
  FreezeRemap _ -> true
  PingPongRemap -> true
  LoopRemap _ -> false  -- Speed is constant in loop
  LinearRemap -> abs (tr.speedFactor - 1.0) > epsilon || tr.speedFactor < 0.0
  CurveRemap _ -> abs (tr.startSpeed - 1.0) > epsilon || abs (tr.endSpeed - 1.0) > epsilon
  KeyframeRemap -> length tr.keyframes > 0
