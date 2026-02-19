/-
  Lattice.Services.Time.Echo - Echo Effect Logic

  Pure functions for echo/motion trail effect:
  - Echo operator blending modes
  - Intensity calculations with decay
  - Echo frame compositing order

  Source: ui/src/services/effects/timeRenderer.ts (lines 207-388)
-/

namespace Lattice.Services.Time.Echo

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Echo operator - how echoes are composited. -/
inductive EchoOperator
  | add
  | screen
  | maximum
  | minimum
  | compositeBack
  | compositeFront
  | blend
  deriving Repr, DecidableEq

/-- Parse echo operator from string. -/
def parseEchoOperator (s : String) : EchoOperator :=
  match s with
  | "add" => EchoOperator.add
  | "screen" => EchoOperator.screen
  | "maximum" => EchoOperator.maximum
  | "minimum" => EchoOperator.minimum
  | "composite_back" => EchoOperator.compositeBack
  | "composite_front" => EchoOperator.compositeFront
  | "blend" => EchoOperator.blend
  | _ => EchoOperator.add  -- Default

/-- Convert echo operator to canvas composite operation name. -/
def echoOperatorToComposite (op : EchoOperator) : String :=
  match op with
  | EchoOperator.add => "lighter"
  | EchoOperator.screen => "screen"
  | EchoOperator.maximum => "lighten"
  | EchoOperator.minimum => "darken"
  | EchoOperator.compositeBack => "destination-over"
  | EchoOperator.compositeFront => "source-over"
  | EchoOperator.blend => "source-over"

--------------------------------------------------------------------------------
-- Parameter Validation
--------------------------------------------------------------------------------

/-- Validate and clamp number of echoes to [1, 50]. -/
def validateNumEchoes (n : Nat) : Nat :=
  Nat.max 1 (Nat.min 50 n)

/-- Validate and clamp starting intensity to [0, 1]. -/
def validateStartingIntensity (i : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 i)

/-- Validate and clamp decay to [0, 1]. -/
def validateDecay (d : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 d)

/-- Validate echo time (no clamping, can be negative for trailing). -/
def validateEchoTime (echoTime fps : Float) : Float :=
  if echoTime == 0.0 then -1.0 / fps else echoTime

--------------------------------------------------------------------------------
-- Intensity Calculation
--------------------------------------------------------------------------------

/-- Minimum intensity threshold for rendering echo. -/
def intensityThreshold : Float := 0.001

/-- Calculate intensities for all echoes.
    Returns array of intensities using exponential decay.
    intensity[i] = startingIntensity * (1 - decay)^i -/
def calculateEchoIntensities (startingIntensity decay : Float) (numEchoes : Nat) : Array Float :=
  let base := 1.0 - decay
  Array.range numEchoes |>.map fun i =>
    startingIntensity * (base ^ i.toFloat)

--------------------------------------------------------------------------------
-- Echo Ordering
--------------------------------------------------------------------------------

/-- Check if echoes should be drawn behind current frame. -/
def shouldDrawEchosBehind (op : EchoOperator) : Bool :=
  match op with
  | EchoOperator.compositeBack => true
  | _ => false

/-- Check if current frame needs to be drawn on top after echoes. -/
def echoRequiresCurrentOnTop (op : EchoOperator) : Bool :=
  match op with
  | EchoOperator.compositeBack => true
  | _ => false

end Lattice.Services.Time.Echo
