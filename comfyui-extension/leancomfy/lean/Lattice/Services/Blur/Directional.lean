/-
  Lattice.Services.Blur.Directional - Directional/Motion Blur Mathematics

  Pure mathematical functions for directional blur calculations:
  - Direction vector from angle
  - Sample position calculation
  - Motion blur trajectory

  Source: ui/src/services/effects/blurRenderer.ts (lines 1106-1148)
-/

namespace Lattice.Services.Blur.Directional

--------------------------------------------------------------------------------
-- Direction Vector
--------------------------------------------------------------------------------

/-- Calculate direction vector from angle in radians.

    @param angleRad Angle in radians (0 = right, π/2 = down)
    @return (dx, dy) unit direction vector -/
def directionVector (angleRad : Float) : Float × Float :=
  (Float.cos angleRad, Float.sin angleRad)

/-- Convert degrees to radians.

    @param degrees Angle in degrees
    @return Angle in radians -/
def degreesToRadians (degrees : Float) : Float :=
  degrees * Float.pi / 180.0

/-- Calculate direction vector from angle in degrees.

    @param angleDeg Angle in degrees (0 = right, 90 = down)
    @return (dx, dy) unit direction vector -/
def directionVectorDeg (angleDeg : Float) : Float × Float :=
  directionVector (degreesToRadians angleDeg)

--------------------------------------------------------------------------------
-- Sample Position Calculation
--------------------------------------------------------------------------------

/-- Calculate sample position along blur direction.

    For motion blur, samples are taken along a line in the direction
    of motion. This calculates where to sample for a given offset.

    @param x Current pixel X
    @param y Current pixel Y
    @param dx Direction X component
    @param dy Direction Y component
    @param offset Sample offset along direction
    @return (sampleX, sampleY) position -/
def samplePosition (x y dx dy offset : Float) : Float × Float :=
  (x + dx * offset, y + dy * offset)

/-- Calculate all sample positions for directional blur.

    Samples are distributed evenly from -halfLength to +halfLength
    along the blur direction.

    @param x Pixel X coordinate
    @param y Pixel Y coordinate
    @param dx Direction X
    @param dy Direction Y
    @param blurLength Total blur length in pixels
    @param sampleCount Number of samples
    @param sampleIndex Index of sample (0 to sampleCount-1)
    @return (sampleX, sampleY) position for this sample -/
def directionalSamplePosition
    (x y dx dy blurLength : Float)
    (sampleCount sampleIndex : Nat) : Float × Float :=
  let halfSamples := Float.ofNat sampleCount / 2.0
  let i := Float.ofNat sampleIndex - halfSamples
  let step := blurLength / Float.ofNat sampleCount
  let offset := i * step
  samplePosition x y dx dy offset

--------------------------------------------------------------------------------
-- Sample Weight
--------------------------------------------------------------------------------

/-- Calculate weight for directional blur sample.

    For basic motion blur, all samples have equal weight.
    For tapered motion blur, central samples have higher weight.

    @param sampleIndex Index of sample
    @param sampleCount Total number of samples
    @param tapered Whether to use tapered weights
    @return Weight for this sample (normalized) -/
def sampleWeight (sampleIndex sampleCount : Nat) (tapered : Bool) : Float :=
  if tapered then
    -- Triangular weighting (central samples weighted more)
    let center := Float.ofNat sampleCount / 2.0
    let dist := Float.abs (Float.ofNat sampleIndex - center)
    let maxDist := center
    if maxDist < 0.0001 then 1.0
    else 1.0 - (dist / maxDist) * 0.5  -- 50% tapering
  else
    -- Uniform weighting
    1.0

/-- Calculate optimal sample count for blur length.

    More samples = smoother blur, but slower.
    We use at least 3 samples, and scale with blur length.

    @param blurLength Blur length in pixels
    @return Recommended sample count -/
def optimalSampleCount (blurLength : Float) : Nat :=
  let samples := Float.ceil blurLength
  Nat.max 3 (Float.toUInt32 samples).toNat

--------------------------------------------------------------------------------
-- Bounds Clamping
--------------------------------------------------------------------------------

/-- Clamp sample position to image bounds.

    @param samplePos Sample (x, y) position
    @param width Image width
    @param height Image height
    @return Clamped (x, y) position -/
def clampSamplePosition (sampleX sampleY : Float) (width height : Nat) : Float × Float :=
  let clampedX := Float.max 0.0 (Float.min (Float.ofNat width - 1.0) sampleX)
  let clampedY := Float.max 0.0 (Float.min (Float.ofNat height - 1.0) sampleY)
  (clampedX, clampedY)

end Lattice.Services.Blur.Directional
