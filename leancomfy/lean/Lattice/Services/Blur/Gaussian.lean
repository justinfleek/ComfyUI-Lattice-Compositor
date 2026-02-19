/-
  Lattice.Services.Blur.Gaussian - Gaussian Blur Mathematics

  Pure mathematical functions for Gaussian blur calculations:
  - Gaussian kernel weights
  - Sigma calculation from radius
  - Kernel generation

  The Gaussian function: G(x) = exp(-x²/(2σ²))

  Source: ui/src/services/effects/blurRenderer.ts (lines 64-93)
-/

namespace Lattice.Services.Blur.Gaussian

--------------------------------------------------------------------------------
-- Gaussian Function
--------------------------------------------------------------------------------

/-- Calculate Gaussian weight for a given distance from center.

    Formula: G(x, σ) = exp(-x² / (2σ²))

    @param x Distance from center
    @param sigma Standard deviation (controls blur spread)
    @return Weight (0-1) -/
def gaussianWeight (x sigma : Float) : Float :=
  if sigma < 0.0001 then
    if x == 0.0 then 1.0 else 0.0
  else
    let twoSigmaSquared := 2.0 * sigma * sigma
    Float.exp (-(x * x) / twoSigmaSquared)

/-- Calculate sigma from blur radius.

    Common convention: σ = radius / 2
    This gives a good approximation where 95% of the Gaussian
    weight falls within the specified radius.

    @param radius Blur radius in pixels
    @return Standard deviation -/
def sigmaFromRadius (radius : Float) : Float :=
  Float.max (radius / 2.0) 1.0

--------------------------------------------------------------------------------
-- Kernel Generation
--------------------------------------------------------------------------------

/-- Calculate the sum of Gaussian weights for normalization.

    @param radius Number of samples on each side of center
    @param sigma Standard deviation
    @return Total weight sum -/
def gaussianWeightSum (radius : Nat) (sigma : Float) : Float :=
  let rec loop (i : Nat) (acc : Float) : Float :=
    if i > radius * 2 then acc
    else
      let x := Float.ofInt (Int.ofNat i - Int.ofNat radius)
      loop (i + 1) (acc + gaussianWeight x sigma)
  loop 0 0.0

/-- Calculate normalized Gaussian weight at position x.

    @param x Position relative to center
    @param sigma Standard deviation
    @param totalWeight Pre-computed sum of all weights
    @return Normalized weight -/
def normalizedGaussianWeight (x sigma totalWeight : Float) : Float :=
  if totalWeight < 0.0001 then 0.0
  else gaussianWeight x sigma / totalWeight

--------------------------------------------------------------------------------
-- 1D Gaussian Kernel
--------------------------------------------------------------------------------

/-- Generate a 1D Gaussian kernel of given size.

    @param radius Number of samples on each side (kernel size = 2*radius + 1)
    @param sigma Standard deviation
    @return Array of normalized weights, centered at radius -/
def generateKernel1D (radius : Nat) (sigma : Float) : Array Float :=
  let size := radius * 2 + 1
  let totalWeight := gaussianWeightSum radius sigma

  Array.ofFn fun i =>
    let x := Float.ofInt (Int.ofNat i - Int.ofNat radius)
    normalizedGaussianWeight x sigma totalWeight

--------------------------------------------------------------------------------
-- Separable Gaussian
--------------------------------------------------------------------------------

/-- Check if separable Gaussian blur is valid for given dimensions.

    Separable blur applies 1D kernel horizontally then vertically,
    achieving same result as 2D kernel in O(n) instead of O(n²).

    @param radiusX Horizontal radius
    @param radiusY Vertical radius
    @return True if radii are valid -/
def isValidSeparableBlur (radiusX radiusY : Float) : Bool :=
  radiusX >= 0.0 && radiusY >= 0.0

/-- Calculate effective kernel size for a given radius.

    @param radius Blur radius
    @return Kernel size (always odd) -/
def kernelSize (radius : Nat) : Nat :=
  radius * 2 + 1

--------------------------------------------------------------------------------
-- Blur Quality Estimation
--------------------------------------------------------------------------------

/-- Estimate blur quality based on kernel size and sigma.

    A good quality blur has sigma ≥ radius/3.
    If sigma is too small relative to kernel size, the blur will be choppy.

    @param radius Kernel radius
    @param sigma Standard deviation
    @return Quality score (0-1, higher is better) -/
def estimateQuality (radius : Nat) (sigma : Float) : Float :=
  let idealSigma := Float.ofNat radius / 3.0
  if sigma < 0.0001 then 0.0
  else Float.min 1.0 (sigma / idealSigma)

end Lattice.Services.Blur.Gaussian
