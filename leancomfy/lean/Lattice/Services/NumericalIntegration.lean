/-
  Lattice.Services.NumericalIntegration - Numerical integration methods

  Pure numerical integration algorithms:
  - Simpson's rule for definite integrals
  - Trapezoidal rule
  - Binary search root finding
  - Frame blending calculations

  Source: ui/src/services/timewarp.ts (numerical parts)
-/

namespace Lattice.Services.NumericalIntegration

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Default tolerance for binary search -/
def defaultTolerance : Float := 0.01

/-- Minimum samples for Simpson's rule -/
def minSamples : Nat := 10

--------------------------------------------------------------------------------
-- Basic Integration
--------------------------------------------------------------------------------

/-- Trapezoidal rule for very short intervals.
    Averages function at endpoints and multiplies by interval width.

    f(a) and f(b) are the function values at endpoints.
    span is the interval width. -/
def trapezoid (fa fb : Float) (span : Float) : Float :=
  ((fa + fb) / 2) * span

/-- Simpson's rule for numerical integration.

    Approximates ∫ₐᵇ f(x) dx using weighted sum of samples.
    Formula: (h/3) * [f(a) + 4*f(a+h) + 2*f(a+2h) + 4*f(a+3h) + ... + f(b)]

    samples: Array of function values at evenly spaced points
    h: Step size between samples

    Requires at least 3 samples (odd number preferred). -/
def simpsonsRule (samples : Array Float) (h : Float) : Float :=
  if samples.size < 3 then
    -- Fallback to trapezoidal for too few samples
    if samples.size == 2 then
      let fa := samples[0]!
      let fb := samples[1]!
      trapezoid fa fb h
    else if samples.size == 1 then
      samples[0]! * h
    else
      0
  else
    let n := samples.size - 1
    let rec accumulate (i : Nat) (sum : Float) : Float :=
      if i >= n then sum
      else
        let coeff :=
          if i == 0 then 1
          else if i == n then 1
          else if i % 2 == 1 then 4
          else 2
        let val := samples[i]!
        accumulate (i + 1) (sum + coeff.toFloat * val)
    let total := accumulate 0 0 + samples[n]!  -- Add last point
    (h / 3) * total

/-- Calculate optimal number of samples for Simpson's rule.
    Ensures even number of intervals (odd number of points). -/
def optimalSampleCount (span : Float) (minPerFrame : Nat := 2) : Nat :=
  let raw := max minSamples (span.toUInt64.toNat * minPerFrame)
  if raw % 2 == 0 then raw + 1 else raw

--------------------------------------------------------------------------------
-- Numerical Integration with Function
--------------------------------------------------------------------------------

/-- Integrate a function from a to b using Simpson's rule.

    f: Function to integrate
    a: Lower bound
    b: Upper bound
    numSamples: Number of sample points (will be made odd if even)

    Returns: Approximate value of ∫ₐᵇ f(x) dx -/
def integrateSimpsons (f : Float → Float) (a b : Float) (numSamples : Nat := 0) : Float :=
  let span := b - a
  if span <= 0 then 0
  else if span < 1 then
    -- Very short span - use trapezoid
    trapezoid (f a) (f b) span
  else
    let n := if numSamples > 0 then numSamples else optimalSampleCount span
    let nOdd := if n % 2 == 0 then n + 1 else n
    let h := span / nOdd.toFloat
    let samples := Array.range nOdd |>.map fun i =>
      f (a + i.toFloat * h)
    -- Add endpoint
    let samplesWithEnd := samples.push (f b)
    simpsonsRule samplesWithEnd h

/-- Integrate a function using the trapezoidal rule.
    Simpler but less accurate than Simpson's rule. -/
def integrateTrapezoidal (f : Float → Float) (a b : Float) (numSamples : Nat := 10) : Float :=
  let span := b - a
  if span <= 0 then 0
  else
    let h := span / numSamples.toFloat
    let rec accumulate (i : Nat) (sum : Float) : Float :=
      if i >= numSamples then sum
      else
        let x := a + i.toFloat * h
        let coeff := if i == 0 || i == numSamples then 0.5 else 1.0
        accumulate (i + 1) (sum + coeff * f x)
    let total := accumulate 0 0 + 0.5 * f b
    h * total

--------------------------------------------------------------------------------
-- Binary Search Root Finding
--------------------------------------------------------------------------------

/-- Binary search to find x where cumulative integral equals target.

    This is the inverse of integration - given ∫ₐˣ f(t) dt = target,
    find x.

    integrator: Function that computes ∫ₐˣ f(t) dt for any x
    target: Target integral value
    low: Lower bound for search
    high: Upper bound for search
    tolerance: Convergence tolerance

    Returns: Approximate value of x -/
def binarySearchIntegral (integrator : Float → Float)
    (target : Float) (low high : Float) (tolerance : Float := defaultTolerance) : Float :=
  let rec search (lo hi : Float) (fuel : Nat) : Float :=
    match fuel with
    | 0 => (lo + hi) / 2
    | n + 1 =>
      if hi - lo <= tolerance then (lo + hi) / 2
      else
        let mid := (lo + hi) / 2
        let valueAtMid := integrator mid
        if valueAtMid < target then
          search mid hi n
        else
          search lo mid n
  search low high 100  -- Max 100 iterations

--------------------------------------------------------------------------------
-- Frame Blending
--------------------------------------------------------------------------------

/-- Result of frame blend calculation -/
structure FrameBlend where
  /-- Floor frame number -/
  floorFrame : Nat
  /-- Ceiling frame number -/
  ceilFrame : Nat
  /-- Blend factor (0 = all floor, 1 = all ceiling) -/
  blendFactor : Float
  deriving Repr, Inhabited

/-- Calculate frame blend information from fractional frame number -/
def calculateFrameBlend (fractionalFrame : Float) : FrameBlend :=
  let clamped := Float.max 0 fractionalFrame
  let floorF := Float.floor clamped
  let ceilF := Float.ceil clamped
  let blend := clamped - floorF
  {
    floorFrame := floorF.toUInt64.toNat
    ceilFrame := ceilF.toUInt64.toNat
    blendFactor := blend
  }

/-- Linear interpolation between two values -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Blend two frames based on blend factor -/
def blendFrameValues (valueAtFloor valueAtCeil : Float) (blend : FrameBlend) : Float :=
  lerp valueAtFloor valueAtCeil blend.blendFactor

--------------------------------------------------------------------------------
-- Speed-Based Integration (Timewarp)
--------------------------------------------------------------------------------

/-- Convert speed percentage to rate multiplier.
    100% = 1x, 200% = 2x, 50% = 0.5x -/
def speedToRate (speedPercent : Float) : Float :=
  speedPercent / 100

/-- Integrate speed curve to find source frame.

    speedSamples: Array of speed values (as percentages) at evenly spaced comp frames
    h: Step size (usually 1 frame or less)

    Returns: Cumulative source frames (integral of speed/100) -/
def integrateSpeedCurve (speedSamples : Array Float) (h : Float) : Float :=
  let rateSamples := speedSamples.map speedToRate
  simpsonsRule rateSamples h

/-- Calculate cumulative source frames at each sample point.
    Useful for building a lookup table. -/
def cumulativeSourceFrames (speedSamples : Array Float) (h : Float) : Array Float :=
  let rates := speedSamples.map speedToRate
  let rec accumulate (i : Nat) (acc : Float) (result : Array Float) : Array Float :=
    if i >= rates.size then result
    else
      let newAcc := acc + rates[i]! * h
      accumulate (i + 1) newAcc (result.push newAcc)
  accumulate 0 0 #[0]  -- Start with 0

end Lattice.Services.NumericalIntegration
