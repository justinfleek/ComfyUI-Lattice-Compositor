/-
  Lattice.Services.Audio.EnvelopeFollower - Envelope Follower Math

  Pure mathematical functions for audio envelope following:
  - Attack/release envelope calculation
  - Smoothing (low-pass filter)
  - Peak hold and decay

  These are the stateless mathematical kernels - actual state management
  happens in the TypeScript AudioReactiveMapper class.

  Source: ui/src/services/audioReactiveMapping.ts (release envelope logic)
-/

namespace Lattice.Services.Audio.EnvelopeFollower

--------------------------------------------------------------------------------
-- Attack/Release Envelope
--------------------------------------------------------------------------------

/-- Calculate new envelope value with attack and release.

    currentValue: Current input signal value
    envelopeValue: Previous envelope state
    release: Release parameter [0, 1] where 0=instant, 1=slow decay

    Attack: Instantly follows input when input > envelope
    Release: Decays exponentially when input < envelope

    Returns: New envelope value -/
def envelopeStep (currentValue : Float) (envelopeValue : Float)
    (release : Float) : Float :=
  if currentValue > envelopeValue then
    -- Attack: follow input immediately
    currentValue
  else
    -- Release: decay based on release parameter
    -- release=0 means instant decay (decayRate=1)
    -- release=1 means very slow decay (decayRate=0.02)
    let decayRate := 1.0 - release * 0.98
    envelopeValue * decayRate

/-- Calculate output value combining input with decaying envelope.

    Returns the maximum of current value and envelope for
    smooth decay behavior. -/
def envelopeOutput (currentValue : Float) (envelopeValue : Float) : Float :=
  Float.max currentValue envelopeValue

/-- Full envelope follower step.

    Returns (newEnvelope, outputValue) tuple. -/
def envelopeFollowerStep (currentValue : Float) (envelopeValue : Float)
    (release : Float) : Float × Float :=
  let newEnvelope := envelopeStep currentValue envelopeValue release
  let output := envelopeOutput currentValue newEnvelope
  (newEnvelope, output)

--------------------------------------------------------------------------------
-- Smoothing (Low-Pass Filter)
--------------------------------------------------------------------------------

/-- Apply exponential smoothing (one-pole low-pass filter).

    currentValue: New input value
    previousSmoothed: Previous smoothed output
    smoothing: Smoothing factor [0, 1] where 0=no smoothing, 1=no change

    Higher smoothing = slower response to changes.

    Returns: New smoothed value -/
def smoothingStep (currentValue : Float) (previousSmoothed : Float)
    (smoothing : Float) : Float :=
  previousSmoothed * smoothing + currentValue * (1.0 - smoothing)

/-- Calculate smoothing coefficient from time constant.

    tau: Time constant (frames for ~63% response)
    Returns: Smoothing coefficient for smoothingStep -/
def smoothingFromTimeConstant (tau : Float) : Float :=
  if tau <= 0.0 then 0.0
  else Float.exp (-1.0 / tau)

--------------------------------------------------------------------------------
-- Peak Hold
--------------------------------------------------------------------------------

/-- Peak hold with decay.

    Holds peak value for holdFrames, then decays.

    currentValue: New input value
    peakValue: Current held peak
    holdCounter: Frames remaining in hold
    holdFrames: Total hold time in frames
    decayRate: Decay rate after hold expires

    Returns: (newPeak, newHoldCounter) -/
def peakHoldStep (currentValue : Float) (peakValue : Float)
    (holdCounter : Nat) (holdFrames : Nat) (decayRate : Float) : Float × Nat :=
  if currentValue > peakValue then
    -- New peak: update and reset hold
    (currentValue, holdFrames)
  else if holdCounter > 0 then
    -- Still holding: maintain peak
    (peakValue, holdCounter - 1)
  else
    -- Hold expired: decay peak
    (peakValue * decayRate, 0)

--------------------------------------------------------------------------------
-- Combined Processing
--------------------------------------------------------------------------------

/-- Apply full envelope + smoothing chain.

    1. Envelope follower (attack/release)
    2. Smoothing (low-pass)

    Returns (newEnvelope, smoothedOutput) -/
def processWithEnvelopeAndSmoothing
    (currentValue : Float)
    (envelopeValue : Float)
    (previousSmoothed : Float)
    (release : Float)
    (smoothing : Float) : Float × Float :=
  let (newEnvelope, envelopeOut) := envelopeFollowerStep currentValue envelopeValue release
  let smoothedOut := smoothingStep envelopeOut previousSmoothed smoothing
  (newEnvelope, smoothedOut)

end Lattice.Services.Audio.EnvelopeFollower
