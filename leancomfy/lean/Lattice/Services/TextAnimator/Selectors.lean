/-
  Lattice.Services.TextAnimator.Selectors - Text Animator Selector Math

  Pure mathematical functions for text animation selectors:
  - Range selector shapes (square, ramp, triangle, round, smooth)
  - Selector mode combinations (add, subtract, intersect, min, max, difference)
  - Wiggly selector oscillation
  - Character position calculations

  Features:
  - 6 selector shapes for character influence curves
  - 6 selector modes for combining multiple selectors
  - Temporal wiggly oscillation with correlation
  - Ease high/low range mapping

  Source: ui/src/services/textAnimator.ts
-/

namespace Lattice.Services.TextAnimator.Selectors

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Selector shape for character influence curves -/
inductive SelectorShape
  | square     -- Constant 1 across range
  | rampUp     -- Linear 0 to 1
  | rampDown   -- Linear 1 to 0
  | triangle   -- Peak at center
  | round      -- Sinusoidal curve
  | smooth     -- Smooth step (ease in-out)
  deriving Repr, Inhabited, BEq

/-- Selector mode for combining multiple selectors -/
inductive SelectorMode
  | add        -- Clamp(base + new, 0, 1)
  | subtract   -- Clamp(base - new, 0, 1)
  | intersect  -- base * new
  | min        -- min(base, new)
  | max        -- max(base, new)
  | difference -- abs(base - new)
  deriving Repr, Inhabited, BEq

/-- Ease configuration for range mapping -/
structure EaseConfig where
  high : Float := 100.0  -- Output at shape value 1.0 (percentage)
  low : Float := 0.0     -- Output at shape value 0.0 (percentage)
  deriving Repr, Inhabited

/-- Wiggly selector configuration -/
structure WigglyConfig where
  wigglesPerSecond : Float := 2.0
  correlation : Float := 50.0      -- 0-100, blend between individual/group
  minAmount : Float := 0.0         -- Minimum output (percentage)
  maxAmount : Float := 100.0       -- Maximum output (percentage)
  lockDimensions : Bool := false   -- Use same value for X and Y
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Shape Functions
--------------------------------------------------------------------------------

/-- Apply selector shape to normalized position (0-1).

    Returns the raw shape value before ease mapping. -/
def applyShapeRaw (t : Float) (shape : SelectorShape) : Float :=
  match shape with
  | SelectorShape.square => 1.0
  | SelectorShape.rampUp => t
  | SelectorShape.rampDown => 1.0 - t
  | SelectorShape.triangle => 1.0 - Float.abs (2.0 * t - 1.0)
  | SelectorShape.round => Float.sin (t * Float.pi)
  | SelectorShape.smooth =>
      -- Smooth step: t² * (3 - 2t)
      t * t * (3.0 - 2.0 * t)

/-- Apply selector shape with ease high/low mapping.

    Maps shape output through [low, high] range. -/
def applyShape (t : Float) (shape : SelectorShape) (ease : EaseConfig) : Float :=
  let value := applyShapeRaw t shape
  let easeRange := (ease.high - ease.low) / 100.0
  ease.low / 100.0 + value * easeRange

--------------------------------------------------------------------------------
-- Selector Mode Combination
--------------------------------------------------------------------------------

/-- Combine two selector values based on mode.

    All outputs are clamped to [0, 1]. -/
def combineSelectorValues (baseValue newValue : Float) (mode : SelectorMode) : Float :=
  match mode with
  | SelectorMode.add => Float.min 1.0 (baseValue + newValue)
  | SelectorMode.subtract => Float.max 0.0 (baseValue - newValue)
  | SelectorMode.intersect => baseValue * newValue
  | SelectorMode.min => Float.min baseValue newValue
  | SelectorMode.max => Float.max baseValue newValue
  | SelectorMode.difference => Float.abs (baseValue - newValue)

--------------------------------------------------------------------------------
-- Character Position Calculation
--------------------------------------------------------------------------------

/-- Calculate character position as percentage (0-100).

    @param charIndex Zero-based character index
    @param totalChars Total number of characters
    @return Position percentage (0 for first char, 100 for last) -/
def characterPosition (charIndex totalChars : Nat) : Float :=
  if totalChars <= 1 then 0.0
  else (charIndex.toFloat / (totalChars - 1).toFloat) * 100.0

/-- Check if character is within selector range.

    Handles wraparound when offset causes start > end. -/
def isInRange (charPosition effectiveStart effectiveEnd : Float)
    (rangeWraps : Bool) : Bool × Float :=
  if rangeWraps then
    -- Wraparound range: affects [effectiveStart, 100] AND [0, effectiveEnd]
    if charPosition >= effectiveStart then
      -- In upper segment [effectiveStart, 100]
      let upperSegmentSize := 100.0 - effectiveStart
      let totalRangeSize := upperSegmentSize + effectiveEnd
      let positionInRange := if totalRangeSize > 0.0
        then (charPosition - effectiveStart) / totalRangeSize
        else 0.0
      (true, positionInRange)
    else if charPosition <= effectiveEnd then
      -- In lower segment [0, effectiveEnd]
      let upperSegmentSize := 100.0 - effectiveStart
      let totalRangeSize := upperSegmentSize + effectiveEnd
      let positionInRange := if totalRangeSize > 0.0
        then (upperSegmentSize + charPosition) / totalRangeSize
        else 1.0
      (true, positionInRange)
    else
      -- In the gap between end and start
      (false, 0.0)
  else
    -- Normal range (no wraparound)
    let normalizedStart := Float.min effectiveStart effectiveEnd
    let normalizedEnd := Float.max effectiveStart effectiveEnd
    if charPosition < normalizedStart || charPosition > normalizedEnd then
      (false, 0.0)
    else
      let rangeSize := normalizedEnd - normalizedStart
      let positionInRange := if rangeSize > 0.0
        then (charPosition - normalizedStart) / rangeSize
        else 0.5
      (true, positionInRange)

--------------------------------------------------------------------------------
-- Wiggly Selector Math
--------------------------------------------------------------------------------

/-- Calculate wiggly phase with correlation.

    Blends between individual character phase and group phase.

    @param time Current time in seconds
    @param wigglesPerSecond Oscillation frequency
    @param baseRandom Character's base random value (0-1)
    @param correlation Correlation factor (0-100)
    @return Combined phase value -/
def calculateWigglyPhase (time wigglesPerSecond baseRandom correlation : Float) : Float :=
  let wigglePhase := time * wigglesPerSecond * Float.pi * 2.0
  let correlationFactor := correlation / 100.0
  let groupPhase := wigglePhase
  let individualPhase := wigglePhase + baseRandom * Float.pi * 2.0
  individualPhase * (1.0 - correlationFactor) + groupPhase * correlationFactor

/-- Calculate wiggly influence from phase.

    Maps sine wave output to [minAmount, maxAmount] range.

    @param phase Calculated phase value
    @param minAmount Minimum output (percentage)
    @param maxAmount Maximum output (percentage)
    @return Normalized influence (0-1) -/
def wigglyInfluenceFromPhase (phase minAmount maxAmount : Float) : Float :=
  let wiggleValue := Float.sin phase  -- -1 to 1
  let range := maxAmount - minAmount
  let amount := minAmount + ((wiggleValue + 1.0) / 2.0) * range
  amount / 100.0  -- Normalize to 0-1

/-- Calculate wiggly offset for 2D properties.

    Returns (x, y) offsets that can be applied to position/scale.

    @param time Current time in seconds
    @param config Wiggly configuration
    @param baseRandomX X-axis random seed (0-1)
    @param baseRandomY Y-axis random seed (0-1, same as X if lockDimensions)
    @return (x, y) offset values -/
def calculateWigglyOffset (time : Float) (config : WigglyConfig)
    (baseRandomX baseRandomY : Float) : Float × Float :=
  let wigglePhase := time * config.wigglesPerSecond * Float.pi * 2.0
  let correlationFactor := config.correlation / 100.0

  -- Group phase
  let groupPhaseX := Float.sin wigglePhase
  let groupPhaseY := if config.lockDimensions then groupPhaseX else Float.cos wigglePhase

  -- Individual phase
  let individualPhaseX := Float.sin (wigglePhase + baseRandomX * Float.pi * 2.0)
  let individualPhaseY := Float.sin (wigglePhase + baseRandomY * Float.pi * 2.0)

  -- Blend individual and group
  let x := individualPhaseX * (1.0 - correlationFactor) + groupPhaseX * correlationFactor
  let y := individualPhaseY * (1.0 - correlationFactor) + groupPhaseY * correlationFactor

  -- Scale by average amount
  let amount := (config.maxAmount + config.minAmount) / 2.0 / 100.0

  (x * amount, y * amount)

--------------------------------------------------------------------------------
-- Smoothness Application
--------------------------------------------------------------------------------

/-- Apply smoothness to influence value.

    Interpolates towards 0.5 based on smoothness factor.

    @param influence Raw influence value (0-1)
    @param smoothness Smoothness percentage (0-100)
    @return Smoothed influence value -/
def applySmoothness (influence smoothness : Float) : Float :=
  if smoothness >= 100.0 then influence
  else
    let smoothFactor := smoothness / 100.0
    influence * smoothFactor + 0.5 * (1.0 - smoothFactor)

--------------------------------------------------------------------------------
-- Offset Wrapping
--------------------------------------------------------------------------------

/-- Wrap value to 0-100 range with proper handling of 100.

    100 stays as 100, doesn't wrap to 0. -/
def wrapTo100 (val : Float) : Float :=
  let modVal := Float.mod ((Float.mod val 100.0) + 100.0) 100.0
  if modVal == 0.0 && val != 0.0 then 100.0 else modVal

/-- Apply offset to start/end values with wrapping. -/
def applyOffset (startValue endValue offset : Float) : Float × Float :=
  (wrapTo100 (startValue + offset), wrapTo100 (endValue + offset))

end Lattice.Services.TextAnimator.Selectors
