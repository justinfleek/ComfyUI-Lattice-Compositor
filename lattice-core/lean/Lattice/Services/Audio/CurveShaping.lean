/-
  Lattice.Services.Audio.CurveShaping - Audio Curve Shaping Functions

  Pure mathematical functions for shaping audio-reactive values:
  - Value curve shaping (exponential, logarithmic, smoothstep, bounce)
  - Amplitude curves (power curves for noise gate/compressor)
  - Threshold gating

  Source: ui/src/services/audioReactiveMapping.ts (applyCurve)
-/

namespace Lattice.Services.Audio.CurveShaping

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Curve type for value shaping -/
inductive CurveType where
  | linear
  | exponential
  | logarithmic
  | smoothstep
  | bounce
  deriving Repr, DecidableEq, Inhabited

--------------------------------------------------------------------------------
-- Clamping
--------------------------------------------------------------------------------

/-- Clamp value to [0, 1] range -/
def clamp01 (value : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 value)

--------------------------------------------------------------------------------
-- Curve Shaping Functions
--------------------------------------------------------------------------------

/-- Apply exponential curve (square).

    Creates more dynamic response - low values become lower,
    high values relatively unchanged.
    Output: x² -/
def exponentialCurve (value : Float) : Float :=
  let clamped := clamp01 value
  clamped * clamped

/-- Apply logarithmic curve (square root).

    Creates compressed response - boosts low values,
    compresses high values.
    Output: √x -/
def logarithmicCurve (value : Float) : Float :=
  let clamped := clamp01 value
  Float.sqrt clamped

/-- Apply smoothstep curve.

    S-curve with smooth acceleration and deceleration.
    Output: 3x² - 2x³ -/
def smoothstepCurve (value : Float) : Float :=
  let clamped := clamp01 value
  clamped * clamped * (3.0 - 2.0 * clamped)

/-- Apply bounce curve.

    Overshoot and bounce back effect.
    Two-phase quadratic for snappy response. -/
def bounceCurve (value : Float) : Float :=
  let clamped := clamp01 value
  if clamped < 0.5 then
    -- First half: accelerate
    2.0 * clamped * clamped
  else
    -- Second half: overshoot and settle
    let t := clamped - 0.5
    let overshoot := 1.0 - 2.0 * t
    0.5 + 0.5 * (1.0 - overshoot * overshoot)

/-- Apply curve shaping to a value.

    Maps input value [0,1] through selected curve function.
    All curves preserve the [0,1] range. -/
def applyCurve (value : Float) (curve : CurveType) : Float :=
  match curve with
  | .linear => clamp01 value
  | .exponential => exponentialCurve value
  | .logarithmic => logarithmicCurve value
  | .smoothstep => smoothstepCurve value
  | .bounce => bounceCurve value

--------------------------------------------------------------------------------
-- Amplitude Curves (Power Law)
--------------------------------------------------------------------------------

/-- Apply amplitude curve (power law).

    amplitudeCurve > 1.0: Expander (emphasize loud, suppress quiet)
    amplitudeCurve = 1.0: Linear (no change)
    amplitudeCurve < 1.0: Compressor (boost quiet, limit loud)

    This is the core of ATI_AudioReactive style dynamics processing. -/
def applyAmplitudeCurve (value : Float) (power : Float) : Float :=
  if power == 1.0 then value
  else Float.pow (Float.max 0.0 value) power

--------------------------------------------------------------------------------
-- Threshold / Noise Gate
--------------------------------------------------------------------------------

/-- Apply threshold (noise gate).

    Values below threshold become 0.
    Values at or above threshold pass through unchanged.

    threshold: Gate threshold [0, 1]
    value: Input value [0, 1]

    Returns: 0 if value < threshold, else value -/
def applyThreshold (value : Float) (threshold : Float) : Float :=
  if value < threshold then 0.0 else value

/-- Apply threshold with soft knee.

    Soft knee provides gradual transition around threshold
    instead of hard cutoff.

    knee: Knee width (0 = hard, >0 = soft)
    Returns: Gated value with optional soft knee -/
def applyThresholdSoftKnee (value : Float) (threshold : Float) (knee : Float) : Float :=
  if knee <= 0.0 then
    -- Hard knee
    applyThreshold value threshold
  else
    let kneeStart := threshold - knee / 2.0
    let kneeEnd := threshold + knee / 2.0
    if value < kneeStart then
      0.0
    else if value > kneeEnd then
      value
    else
      -- In knee region: smooth transition
      let t := (value - kneeStart) / knee
      let curved := t * t  -- Quadratic fade-in
      value * curved

--------------------------------------------------------------------------------
-- Combined Processing
--------------------------------------------------------------------------------

/-- Apply full audio value processing chain.

    1. Threshold (noise gate)
    2. Amplitude curve (dynamics)
    3. Value curve (shaping)
    4. Inversion (optional)

    This matches the processing order in audioReactiveMapping.ts -/
def processAudioValue (value : Float)
    (threshold : Float) (amplitudeCurve : Float)
    (curve : CurveType) (invert : Bool) : Float :=
  let v1 := applyThreshold value threshold
  let v2 := applyAmplitudeCurve v1 amplitudeCurve
  let v3 := applyCurve v2 curve
  if invert then 1.0 - v3 else v3

end Lattice.Services.Audio.CurveShaping
