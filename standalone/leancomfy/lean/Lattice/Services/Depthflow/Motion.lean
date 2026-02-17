/-
  Lattice.Services.Depthflow.Motion - Depthflow Motion Components

  Pure mathematical functions for evaluating motion components in
  depth-based parallax animations. Includes easing functions and
  motion type evaluators.

  Features:
  - 7 easing types (linear, ease-in/out, bounce, elastic, back)
  - 8 motion types (linear, exponential, sine, cosine, arc, setTarget, bounce, elastic)
  - Motion component evaluation
  - Additive motion combination

  Source: ui/src/services/depthflow.ts
-/

namespace Lattice.Services.Depthflow.Motion

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Easing type for motion curves -/
inductive EasingType
  | linear
  | easeIn
  | easeOut
  | easeInOut
  | bounce
  | elastic
  | back
  deriving Repr, Inhabited, BEq

/-- Motion interpolation type -/
inductive MotionType
  | linear
  | exponential
  | sine
  | cosine
  | arc
  | setTarget
  | bounce
  | elastic
  deriving Repr, Inhabited, BEq

/-- Motion component configuration -/
structure MotionComponent where
  motionType : MotionType
  startValue : Float
  endValue : Float
  startFrame : Float
  endFrame : Float
  easing : EasingType
  amplitude : Float := 0.0   -- For sine/cosine/arc
  frequency : Float := 1.0   -- For sine/cosine
  loops : Float := 1.0       -- Number of cycles
  phase : Float := 0.0       -- Starting phase (0-1)
  enabled : Bool := true
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Easing Functions
--------------------------------------------------------------------------------

/-- Apply easing function to normalized time (0-1).

    Converts linear progression to curved progression. -/
def applyEasing (t : Float) (easing : EasingType) : Float :=
  match easing with
  | EasingType.linear => t

  | EasingType.easeIn => t * t

  | EasingType.easeOut =>
      1.0 - (1.0 - t) * (1.0 - t)

  | EasingType.easeInOut =>
      if t < 0.5 then
        2.0 * t * t
      else
        1.0 - ((-2.0 * t + 2.0) ^ 2) / 2.0

  | EasingType.bounce =>
      let n1 := 7.5625
      let d1 := 2.75
      if t < 1.0 / d1 then
        n1 * t * t
      else if t < 2.0 / d1 then
        let t' := t - 1.5 / d1
        n1 * t' * t' + 0.75
      else if t < 2.5 / d1 then
        let t' := t - 2.25 / d1
        n1 * t' * t' + 0.9375
      else
        let t' := t - 2.625 / d1
        n1 * t' * t' + 0.984375

  | EasingType.elastic =>
      let c4 := 2.0 * Float.pi / 3.0
      if t == 0.0 then 0.0
      else if t == 1.0 then 1.0
      else
        (2.0 : Float) ^ (-10.0 * t) * Float.sin ((t * 10.0 - 0.75) * c4) + 1.0

  | EasingType.back =>
      let c1 := 1.70158
      let c3 := c1 + 1.0
      1.0 + c3 * ((t - 1.0) ^ 3) + c1 * ((t - 1.0) ^ 2)

--------------------------------------------------------------------------------
-- Motion Evaluation
--------------------------------------------------------------------------------

/-- Evaluate linear interpolation between start and end values -/
def evaluateLinear (startValue endValue easedT : Float) : Float :=
  startValue + (endValue - startValue) * easedT

/-- Evaluate exponential interpolation.
    Falls back to linear when startValue is zero. -/
def evaluateExponential (startValue endValue easedT : Float) : Float :=
  if startValue == 0.0 then
    endValue * easedT
  else
    let ratio := endValue / startValue
    startValue * (ratio ^ easedT)

/-- Evaluate sinusoidal motion -/
def evaluateSine (startValue endValue easedT amplitude frequency loops phase : Float) : Float :=
  let amp := if amplitude == 0.0 then (endValue - startValue) / 2.0 else amplitude
  let freq := if frequency <= 0.0 then 1.0 else frequency
  let baseValue := (startValue + endValue) / 2.0
  baseValue + amp * Float.sin ((easedT * loops + phase) * Float.pi * 2.0 * freq)

/-- Evaluate cosinusoidal motion -/
def evaluateCosine (startValue endValue easedT amplitude frequency loops phase : Float) : Float :=
  let amp := if amplitude == 0.0 then (endValue - startValue) / 2.0 else amplitude
  let freq := if frequency <= 0.0 then 1.0 else frequency
  let baseValue := (startValue + endValue) / 2.0
  baseValue + amp * Float.cos ((easedT * loops + phase) * Float.pi * 2.0 * freq)

/-- Evaluate arc/parabolic motion -/
def evaluateArc (startValue endValue easedT amplitude : Float) : Float :=
  let amp := if amplitude < 0.0 then 1.0 else amplitude
  let range := endValue - startValue
  -- Parabolic arc: offset peaks at t=0.5
  let arcOffset := amp * 4.0 * easedT * (1.0 - easedT)
  startValue + range * easedT + arcOffset

/-- Evaluate bouncy motion with decay -/
def evaluateBounce (startValue endValue easedT : Float) : Float :=
  let baseValue := startValue + (endValue - startValue) * easedT
  let bounceDecay := Float.exp (-easedT * 5.0)
  let bounce := Float.sin (easedT * Float.pi * 4.0) * bounceDecay * 0.2
  baseValue * (1.0 + bounce)

/-- Evaluate elastic motion with overshoot -/
def evaluateElastic (startValue endValue easedT : Float) : Float :=
  let baseValue := startValue + (endValue - startValue) * easedT
  if easedT == 0.0 || easedT == 1.0 then baseValue
  else
    let elasticDecay := Float.exp (-easedT * 3.0)
    let elastic := Float.sin (easedT * Float.pi * 6.0) * elasticDecay * 0.3
    baseValue * (1.0 + elastic)

/-- Evaluate a motion component at a specific frame.

    Returns the interpolated value based on motion type, easing, and frame position. -/
def evaluateMotionComponent (motion : MotionComponent) (frame : Float) : Option Float :=
  -- Disabled motions return none
  if !motion.enabled then none
  else
    -- Handle frame outside motion range
    if frame < motion.startFrame then some motion.startValue
    else if frame > motion.endFrame then some motion.endValue
    else
      -- Calculate normalized time within motion range
      let duration := motion.endFrame - motion.startFrame
      let localFrame := frame - motion.startFrame
      let t := if duration > 0.0 then localFrame / duration else 1.0

      -- Apply easing
      let easedT := applyEasing t motion.easing

      -- Calculate value based on motion type
      some <| match motion.motionType with
      | MotionType.linear =>
          evaluateLinear motion.startValue motion.endValue easedT

      | MotionType.exponential =>
          evaluateExponential motion.startValue motion.endValue easedT

      | MotionType.sine =>
          evaluateSine motion.startValue motion.endValue easedT
            motion.amplitude motion.frequency motion.loops motion.phase

      | MotionType.cosine =>
          evaluateCosine motion.startValue motion.endValue easedT
            motion.amplitude motion.frequency motion.loops motion.phase

      | MotionType.arc =>
          evaluateArc motion.startValue motion.endValue easedT motion.amplitude

      | MotionType.setTarget =>
          if frame >= motion.startFrame then motion.endValue else motion.startValue

      | MotionType.bounce =>
          evaluateBounce motion.startValue motion.endValue easedT

      | MotionType.elastic =>
          evaluateElastic motion.startValue motion.endValue easedT

--------------------------------------------------------------------------------
-- Motion Combination
--------------------------------------------------------------------------------

/-- Combine multiple motion components additively.

    Each motion's delta from its start value is added to the base. -/
def combineMotions (motions : Array MotionComponent) (frame baseValue : Float) : Float :=
  motions.foldl (fun acc motion =>
    match evaluateMotionComponent motion frame with
    | none => acc  -- Disabled motion, skip
    | some value =>
        let delta := value - motion.startValue
        acc + delta
  ) baseValue

--------------------------------------------------------------------------------
-- Motion Parameters
--------------------------------------------------------------------------------

/-- Animated parameters for depth-based parallax -/
structure DepthflowParams where
  zoom : Float := 1.0
  offsetX : Float := 0.0
  offsetY : Float := 0.0
  rotation : Float := 0.0
  depthScale : Float := 1.0
  focusDepth : Float := 0.5
  deriving Repr, Inhabited

/-- Evaluate all motion parameters at a frame -/
def evaluateParams (zoomMotions offsetXMotions offsetYMotions rotationMotions
    depthScaleMotions focusDepthMotions : Array MotionComponent)
    (frame : Float) (base : DepthflowParams) : DepthflowParams :=
  { zoom := combineMotions zoomMotions frame base.zoom
  , offsetX := combineMotions offsetXMotions frame base.offsetX
  , offsetY := combineMotions offsetYMotions frame base.offsetY
  , rotation := combineMotions rotationMotions frame base.rotation
  , depthScale := combineMotions depthScaleMotions frame base.depthScale
  , focusDepth := combineMotions focusDepthMotions frame base.focusDepth }

--------------------------------------------------------------------------------
-- Parallax Calculation
--------------------------------------------------------------------------------

/-- Calculate parallax offset based on depth.

    Objects closer than focus depth move more, objects further move less.
    Returns the offset multiplier for a given depth value. -/
def calculateParallaxOffset (depth focusDepth depthScale : Float) : Float :=
  (depth - focusDepth) * depthScale

/-- Apply zoom to coordinate (relative to center 0.5, 0.5) -/
def applyZoom (coord zoom : Float) : Float :=
  if zoom == 0.0 then coord else coord / zoom

/-- Apply rotation to 2D coordinates.

    Rotates point around origin by given angle in degrees. -/
def applyRotation (x y angleDegrees : Float) : Float × Float :=
  let angleRadians := angleDegrees * Float.pi / 180.0
  let cosA := Float.cos angleRadians
  let sinA := Float.sin angleRadians
  (x * cosA - y * sinA, x * sinA + y * cosA)

end Lattice.Services.Depthflow.Motion
