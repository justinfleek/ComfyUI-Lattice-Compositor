/-
  Lattice.Services.Color.ValueMapping - Value Mapping for Reactivity

  Pure mathematical functions for mapping sampled values to output:
  - Sensitivity scaling
  - Smoothing (low-pass filter)
  - Range mapping (min/max)
  - Inversion
  - Depth normalization

  Source: ui/src/services/colorDepthReactivity.ts
-/

namespace Lattice.Services.Color.ValueMapping

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Configuration for value mapping. -/
structure ValueMappingConfig where
  sensitivity : Float  -- Multiplier for raw value
  smoothing : Float    -- 0-1 (0 = no smoothing, 1 = full smoothing)
  min : Float          -- Output minimum
  max : Float          -- Output maximum
  invert : Bool        -- Invert before mapping
  deriving Repr, Inhabited

/-- Default value mapping configuration. -/
def defaultValueMappingConfig : ValueMappingConfig :=
  { sensitivity := 1.0
  , smoothing := 0.0
  , min := 0.0
  , max := 1.0
  , invert := false }

/-- Depth mapping configuration. -/
structure DepthMappingConfig where
  nearPlane : Float  -- Depth value considered "near"
  farPlane : Float   -- Depth value considered "far"
  sensitivity : Float
  smoothing : Float
  min : Float
  max : Float
  invert : Bool
  deriving Repr, Inhabited

/-- Default depth mapping configuration. -/
def defaultDepthMappingConfig : DepthMappingConfig :=
  { nearPlane := 0.0
  , farPlane := 1.0
  , sensitivity := 1.0
  , smoothing := 0.0
  , min := 0.0
  , max := 1.0
  , invert := false }

--------------------------------------------------------------------------------
-- Core Mapping Functions
--------------------------------------------------------------------------------

/-- Clamp a value to 0-1 range. -/
def clamp01 (x : Float) : Float :=
  Float.max 0.0 (Float.min 1.0 x)

/-- Apply sensitivity scaling to a raw value.

    Multiplies the value by sensitivity and clamps to 0-1. -/
def applySensitivity (rawValue : Float) (sensitivity : Float) : Float :=
  clamp01 (rawValue * sensitivity)

/-- Apply inversion if needed.

    If invert is true, returns 1 - value. -/
def applyInversion (value : Float) (invert : Bool) : Float :=
  if invert then 1.0 - value else value

/-- Map a 0-1 value to an output range. -/
def mapToRange (value : Float) (min max : Float) : Float :=
  min + value * (max - min)

/-- Apply exponential smoothing (one-pole low-pass filter).

    output = previous * smoothing + current * (1 - smoothing)

    smoothing = 0: No smoothing (instant response)
    smoothing → 1: More smoothing (slower response) -/
def applySmoothing (currentValue : Float) (previousValue : Float)
    (smoothing : Float) : Float :=
  if smoothing <= 0.0 then currentValue
  else previousValue * smoothing + currentValue * (1.0 - smoothing)

--------------------------------------------------------------------------------
-- Complete Value Mapping
--------------------------------------------------------------------------------

/-- Apply complete value mapping pipeline.

    Pipeline:
    1. Apply sensitivity
    2. Clamp to 0-1
    3. Invert if needed
    4. Map to output range
    5. Apply smoothing -/
def mapValue (rawValue : Float) (config : ValueMappingConfig)
    (previousValue : Option Float := none) : Float :=
  -- Step 1: Apply sensitivity
  let scaled := applySensitivity rawValue config.sensitivity

  -- Step 2: Invert if needed
  let inverted := applyInversion scaled config.invert

  -- Step 3: Map to output range
  let mapped := mapToRange inverted config.min config.max

  -- Step 4: Apply smoothing
  match previousValue with
  | none => mapped
  | some prev => applySmoothing mapped prev config.smoothing

/-- Map value without smoothing (no previous value). -/
def mapValueSimple (rawValue : Float) (config : ValueMappingConfig) : Float :=
  mapValue rawValue config none

--------------------------------------------------------------------------------
-- Depth Mapping
--------------------------------------------------------------------------------

/-- Normalize depth value to near/far range.

    Converts raw depth to 0-1 where:
    - 0 = near plane
    - 1 = far plane -/
def normalizeDepth (depthValue : Float) (nearPlane farPlane : Float) : Float :=
  let range := farPlane - nearPlane
  if range <= 0.0 then depthValue
  else clamp01 ((depthValue - nearPlane) / range)

/-- Apply complete depth mapping pipeline.

    Pipeline:
    1. Normalize to near/far range
    2. Apply sensitivity
    3. Invert if needed
    4. Map to output range
    5. Apply smoothing -/
def mapDepthValue (depthValue : Float) (config : DepthMappingConfig)
    (previousValue : Option Float := none) : Float :=
  -- Step 1: Normalize to near/far range
  let normalized := normalizeDepth depthValue config.nearPlane config.farPlane

  -- Step 2: Apply sensitivity
  let scaled := applySensitivity normalized config.sensitivity

  -- Step 3: Invert if needed
  let inverted := applyInversion scaled config.invert

  -- Step 4: Map to output range
  let mapped := mapToRange inverted config.min config.max

  -- Step 5: Apply smoothing
  match previousValue with
  | none => mapped
  | some prev => applySmoothing mapped prev config.smoothing

--------------------------------------------------------------------------------
-- Motion Detection Math
--------------------------------------------------------------------------------

/-- Calculate per-pixel color difference (0-1).

    Returns average of RGB channel differences. -/
def pixelDifference (r1 g1 b1 r2 g2 b2 : Float) : Float :=
  let dr := Float.abs (r1 - r2)
  let dg := Float.abs (g1 - g2)
  let db := Float.abs (b1 - b2)
  (dr + dg + db) / 3.0

/-- Apply threshold to motion value.

    Returns 0 if below threshold, otherwise returns the value. -/
def applyMotionThreshold (difference : Float) (threshold : Float) : Float :=
  if difference > threshold then difference else 0.0

/-- Map motion value to output.

    Takes accumulated motion (0-1) and maps to output range. -/
def mapMotionValue (motionValue : Float) (sensitivity : Float)
    (min max : Float) (previousValue : Option Float)
    (smoothing : Float) : Float :=
  -- Apply sensitivity
  let scaled := clamp01 (motionValue * sensitivity)

  -- Map to output range
  let mapped := mapToRange scaled min max

  -- Apply smoothing
  match previousValue with
  | none => mapped
  | some prev => applySmoothing mapped prev smoothing

--------------------------------------------------------------------------------
-- Gradient Calculation
--------------------------------------------------------------------------------

/-- Calculate gradient magnitude from dx and dy. -/
def gradientMagnitude (dx dy : Float) : Float :=
  Float.sqrt (dx * dx + dy * dy)

/-- Sobel-like gradient calculation (given neighbor values).

    dx = right - left
    dy = bottom - top -/
def calculateGradient (left right top bottom : Float) : Float :=
  let dx := right - left
  let dy := bottom - top
  gradientMagnitude dx dy

--------------------------------------------------------------------------------
-- Statistics
--------------------------------------------------------------------------------

/-- Calculate variance of a list of values. -/
def calculateVariance (values : Array Float) : Float :=
  if values.size == 0 then 0.0
  else
    let sum := values.foldl (· + ·) 0.0
    let mean := sum / values.size.toFloat
    let squaredDiffs := values.map fun v => (v - mean) * (v - mean)
    let sumSquaredDiffs := squaredDiffs.foldl (· + ·) 0.0
    sumSquaredDiffs / values.size.toFloat

/-- Calculate standard deviation. -/
def calculateStdDev (values : Array Float) : Float :=
  Float.sqrt (calculateVariance values)

/-- Calculate mean of values. -/
def calculateMean (values : Array Float) : Float :=
  if values.size == 0 then 0.0
  else values.foldl (· + ·) 0.0 / values.size.toFloat

/-- Find minimum value in array. -/
def findMin (values : Array Float) : Float :=
  values.foldl Float.min (1.0 / 0.0)  -- Start with infinity

/-- Find maximum value in array. -/
def findMax (values : Array Float) : Float :=
  values.foldl Float.max (-1.0 / 0.0)  -- Start with -infinity

end Lattice.Services.Color.ValueMapping
