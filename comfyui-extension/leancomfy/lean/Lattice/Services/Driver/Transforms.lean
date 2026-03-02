/-
  Lattice.Services.Driver.Transforms - Property Driver Transforms

  Pure mathematical functions for transforming property values in
  property-to-property linking (drivers). These transforms are applied
  as a chain to map source values to target values.

  Features:
  - Scale, offset, clamp transforms
  - Value remapping (input range → output range)
  - Threshold gating (binary output)
  - Oscillation (sinusoidal modulation)
  - Value inversion
  - Temporal smoothing (low-pass filter)
  - Blend modes (replace, add, multiply)

  Source: ui/src/services/propertyDriver.ts
-/

namespace Lattice.Services.Driver.Transforms

--------------------------------------------------------------------------------
-- Transform Types
--------------------------------------------------------------------------------

/-- Transform type for property drivers -/
inductive TransformType
  | scale
  | offset
  | clamp
  | smooth
  | invert
  | remap
  | threshold
  | oscillate
  deriving Repr, Inhabited, BEq

/-- Blend mode for combining base and driven values -/
inductive BlendMode
  | replace   -- Use driven value directly
  | add       -- Add driven to base
  | multiply  -- Multiply base by driven
  deriving Repr, Inhabited, BEq

/-- Transform configuration -/
structure Transform where
  transformType : TransformType
  -- Scale
  factor : Float := 1.0
  -- Offset
  amount : Float := 0.0
  -- Clamp
  minVal : Float := 0.0
  maxVal : Float := 1.0
  -- Smooth (coefficient for previous value, 0-1)
  smoothing : Float := 0.5
  -- Remap
  inMin : Float := 0.0
  inMax : Float := 1.0
  outMin : Float := 0.0
  outMax : Float := 1.0
  -- Threshold
  thresholdVal : Float := 0.5
  -- Oscillate
  frequency : Float := 1.0
  amplitude : Float := 1.0
  phase : Float := 0.0
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Individual Transform Functions
--------------------------------------------------------------------------------

/-- Scale transform: value * factor -/
def applyScale (value factor : Float) : Float :=
  value * factor

/-- Offset transform: value + amount -/
def applyOffset (value amount : Float) : Float :=
  value + amount

/-- Clamp transform: clamp(value, min, max) -/
def applyClamp (value minVal maxVal : Float) : Float :=
  Float.max minVal (Float.min maxVal value)

/-- Smooth transform: exponential smoothing (one-pole low-pass filter).

    Formula: smoothed = prevValue * smoothing + value * (1 - smoothing)

    @param value Current input value
    @param prevValue Previous smoothed value
    @param smoothing Smoothing coefficient (0 = no smoothing, 1 = ignore current)
    @return Smoothed value -/
def applySmooth (value prevValue smoothing : Float) : Float :=
  let s := Float.max 0.0 (Float.min 1.0 smoothing)
  prevValue * s + value * (1.0 - s)

/-- Invert transform: 1 - value -/
def applyInvert (value : Float) : Float :=
  1.0 - value

/-- Remap transform: map value from [inMin, inMax] to [outMin, outMax].

    Handles zero input range by returning midpoint of output range. -/
def applyRemap (value inMin inMax outMin outMax : Float) : Float :=
  let inRange := inMax - inMin
  if inRange == 0.0 then
    -- Zero input range: return midpoint of output range
    (outMin + outMax) / 2.0
  else
    let normalized := (value - inMin) / inRange
    outMin + normalized * (outMax - outMin)

/-- Threshold transform: value > threshold ? 1 : 0 -/
def applyThreshold (value thresholdVal : Float) : Float :=
  if value > thresholdVal then 1.0 else 0.0

/-- Oscillate transform: sin((value * frequency + phase) * 2π) * amplitude -/
def applyOscillate (value frequency amplitude phase : Float) : Float :=
  let freq := if frequency <= 0.0 then 1.0 else frequency
  let amp := if amplitude < 0.0 then 0.0 else amplitude
  Float.sin ((value * freq + phase) * Float.pi * 2.0) * amp

--------------------------------------------------------------------------------
-- Transform Chain
--------------------------------------------------------------------------------

/-- Apply a single transform to a value.

    For smooth transform, requires previous smoothed value. -/
def applyTransformWithPrev (transform : Transform) (value prevValue : Float) : Float :=
  match transform.transformType with
  | TransformType.scale => applyScale value transform.factor
  | TransformType.offset => applyOffset value transform.amount
  | TransformType.clamp => applyClamp value transform.minVal transform.maxVal
  | TransformType.smooth => applySmooth value prevValue transform.smoothing
  | TransformType.invert => applyInvert value
  | TransformType.remap => applyRemap value transform.inMin transform.inMax
      transform.outMin transform.outMax
  | TransformType.threshold => applyThreshold value transform.thresholdVal
  | TransformType.oscillate => applyOscillate value transform.frequency
      transform.amplitude transform.phase

/-- Apply a single transform to a value (no smoothing state). -/
def applyTransform (transform : Transform) (value : Float) : Float :=
  applyTransformWithPrev transform value value

/-- Apply a chain of transforms to a value. -/
def applyTransformChain (transforms : Array Transform) (value : Float) : Float :=
  transforms.foldl (fun v t => applyTransform t v) value

--------------------------------------------------------------------------------
-- Blend Modes
--------------------------------------------------------------------------------

/-- Blend driven value with base value using blend mode.

    @param base Original property value
    @param driven Value computed by driver
    @param mode How to combine base and driven
    @param amount Blend amount (0 = use base, 1 = use blended result) -/
def blendValue (base driven : Float) (mode : BlendMode) (amount : Float) : Float :=
  let result := match mode with
    | BlendMode.replace => driven
    | BlendMode.add => base + driven
    | BlendMode.multiply => base * driven
  -- Mix between base and result based on blend amount
  base * (1.0 - amount) + result * amount

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

/-- Create a scale transform -/
def mkScaleTransform (factor : Float) : Transform :=
  { transformType := TransformType.scale, factor := factor }

/-- Create an offset transform -/
def mkOffsetTransform (amount : Float) : Transform :=
  { transformType := TransformType.offset, amount := amount }

/-- Create a clamp transform -/
def mkClampTransform (minVal maxVal : Float) : Transform :=
  { transformType := TransformType.clamp, minVal := minVal, maxVal := maxVal }

/-- Create a remap transform -/
def mkRemapTransform (inMin inMax outMin outMax : Float) : Transform :=
  { transformType := TransformType.remap
  , inMin := inMin
  , inMax := inMax
  , outMin := outMin
  , outMax := outMax }

/-- Create a threshold transform -/
def mkThresholdTransform (thresholdVal : Float) : Transform :=
  { transformType := TransformType.threshold, thresholdVal := thresholdVal }

/-- Create an oscillate transform -/
def mkOscillateTransform (frequency amplitude phase : Float) : Transform :=
  { transformType := TransformType.oscillate
  , frequency := frequency
  , amplitude := amplitude
  , phase := phase }

end Lattice.Services.Driver.Transforms
