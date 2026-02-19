/-
  Lattice.Services.Noise.SimplexNoise - 2D Simplex/Perlin Noise

  Pure deterministic noise function for organic motion.
  Uses improved Perlin gradient noise with better bit mixing
  to avoid seed collisions.

  Source: ui/src/services/export/wanMoveFlowGenerators.ts (simplexNoise2D)
-/

namespace Lattice.Services.Noise.SimplexNoise

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

/-- Prime for x coordinate hashing -/
def primeX : UInt32 := 374761393

/-- Prime for y coordinate hashing -/
def primeY : UInt32 := 668265263

/-- MurmurHash3 mixing constant 1 -/
def mixConstant1 : UInt32 := 0x85ebca6b

/-- MurmurHash3 mixing constant 2 -/
def mixConstant2 : UInt32 := 0xc2b2ae35

/-- Final mixing constant -/
def mixConstant3 : UInt32 := 0x5bd1e995

--------------------------------------------------------------------------------
-- Bit Operations
--------------------------------------------------------------------------------

private def xor (a b : UInt32) : UInt32 := a ^^^ b
private def band (a b : UInt32) : UInt32 := a &&& b
private def shr (a : UInt32) (n : Nat) : UInt32 := a >>> n

--------------------------------------------------------------------------------
-- Hash Function
--------------------------------------------------------------------------------

/-- Hash function with improved bit mixing for seed/coordinate combination.

    Combines seed and 2D coordinates using MurmurHash3-style mixing
    to produce well-distributed pseudo-random values. -/
def hash (seed : UInt32) (px py : Int) : UInt32 :=
  -- Mix seed first
  let h0 := seed
  let h1 := xor h0 (shr h0 16)
  let h2 := h1 * mixConstant1
  let h3 := xor h2 (shr h2 13)
  let h4 := h3 * mixConstant2
  let h5 := xor h4 (shr h4 16)
  -- Mix in coordinates
  let pxu := px.toNat.toUInt32
  let pyu := py.toNat.toUInt32
  let h6 := h5 + pxu * primeX + pyu * primeY
  let h7 := xor h6 (shr h6 13)
  let h8 := h7 * mixConstant3
  xor h8 (shr h8 15)

--------------------------------------------------------------------------------
-- Gradient Function
--------------------------------------------------------------------------------

/-- Calculate gradient contribution from hash and offset.

    Uses 8 gradient directions for 2D noise:
    - h & 7 selects direction
    - Returns weighted sum of dx, dy based on direction -/
def grad (h : UInt32) (dx dy : Float) : Float :=
  let sel := band h 7
  let u := if sel < 4 then dx else dy
  let v := if sel < 4 then dy else dx
  let signU := if band sel 1 == 0 then u else -u
  let signV := if band sel 2 == 0 then 2.0 * v else -2.0 * v
  signU + signV

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

/-- Linear interpolation -/
def lerp (a b t : Float) : Float := a + t * (b - a)

/-- Quintic fade curve: 6t⁵ - 15t⁴ + 10t³
    Provides smooth derivative at boundaries -/
def fade (t : Float) : Float :=
  t * t * t * (t * (t * 6.0 - 15.0) + 10.0)

--------------------------------------------------------------------------------
-- Main Noise Function
--------------------------------------------------------------------------------

/-- 2D Simplex/Perlin noise.

    Generates smooth, continuous pseudo-random values based on
    2D coordinates and a seed. Output is normalized to [0, 1].

    x, y: Sample coordinates
    seed: Random seed for determinism

    Returns value in [0, 1] range. -/
def simplexNoise2D (x y : Float) (seed : UInt32) : Float :=
  -- Grid cell coordinates
  let ix := Float.floor x |>.toInt64.toInt
  let iy := Float.floor y |>.toInt64.toInt

  -- Fractional position within cell
  let fx := x - ix.toFloat
  let fy := y - iy.toFloat

  -- Hash the four corners
  let n00 := grad (hash seed ix iy) fx fy
  let n10 := grad (hash seed (ix + 1) iy) (fx - 1.0) fy
  let n01 := grad (hash seed ix (iy + 1)) fx (fy - 1.0)
  let n11 := grad (hash seed (ix + 1) (iy + 1)) (fx - 1.0) (fy - 1.0)

  -- Fade curves for interpolation
  let u := fade fx
  let v := fade fy

  -- Bilinear interpolation of corner values
  let nx0 := lerp n00 n10 u
  let nx1 := lerp n01 n11 u
  let result := lerp nx0 nx1 v

  -- Normalize to [0, 1] (raw range is approximately [-1, 1])
  result * 0.5 + 0.5

--------------------------------------------------------------------------------
-- Octave Noise (Fractal Brownian Motion)
--------------------------------------------------------------------------------

/-- Multi-octave noise for more natural-looking patterns.

    Sums multiple noise layers at different frequencies and amplitudes.

    x, y: Sample coordinates
    seed: Random seed
    octaves: Number of layers (1-8 recommended)
    persistence: Amplitude multiplier per octave (0.5 typical)
    lacunarity: Frequency multiplier per octave (2.0 typical) -/
def fbm (x y : Float) (seed : UInt32) (octaves : Nat)
    (persistence : Float := 0.5) (lacunarity : Float := 2.0) : Float :=
  -- Use explicit loop with fuel = octaves
  let rec go (fuel : Nat) (i : Nat) (freq amp total maxVal : Float) : Float × Float :=
    if fuel == 0 || i >= octaves then (total, maxVal)
    else
      let noise := simplexNoise2D (x * freq) (y * freq) seed
      let total' := total + noise * amp
      let maxVal' := maxVal + amp
      go (fuel - 1) (i + 1) (freq * lacunarity) (amp * persistence) total' maxVal'
  let (total, maxVal) := go octaves 0 1.0 1.0 0.0 0.0
  if maxVal > 0.0 then total / maxVal else 0.5

--------------------------------------------------------------------------------
-- Turbulence (Absolute Value Noise)
--------------------------------------------------------------------------------

/-- Turbulence noise using absolute value of noise layers.

    Creates sharper, more "turbulent" patterns than regular FBM. -/
def turbulence (x y : Float) (seed : UInt32) (octaves : Nat)
    (persistence : Float := 0.5) (lacunarity : Float := 2.0) : Float :=
  -- Use explicit loop with fuel = octaves
  let rec go (fuel : Nat) (i : Nat) (freq amp total maxVal : Float) : Float × Float :=
    if fuel == 0 || i >= octaves then (total, maxVal)
    else
      -- Use absolute value for turbulent effect
      let noise := simplexNoise2D (x * freq) (y * freq) seed
      let absNoise := Float.abs (noise * 2.0 - 1.0)  -- Map [0,1] to [-1,1] then abs
      let total' := total + absNoise * amp
      let maxVal' := maxVal + amp
      go (fuel - 1) (i + 1) (freq * lacunarity) (amp * persistence) total' maxVal'
  let (total, maxVal) := go octaves 0 1.0 1.0 0.0 0.0
  if maxVal > 0.0 then total / maxVal else 0.5

--------------------------------------------------------------------------------
-- Ridge Noise
--------------------------------------------------------------------------------

/-- Ridge noise for mountain-like patterns.

    Creates sharp ridges by inverting absolute noise. -/
def ridgeNoise (x y : Float) (seed : UInt32) (octaves : Nat)
    (persistence : Float := 0.5) (lacunarity : Float := 2.0)
    (gain : Float := 2.0) : Float :=
  -- Use explicit loop with fuel = octaves
  let rec go (fuel : Nat) (i : Nat) (freq amp total weight : Float) : Float :=
    if fuel == 0 || i >= octaves then total
    else
      let noise := simplexNoise2D (x * freq) (y * freq) seed
      -- Ridge transformation: 1 - |noise * 2 - 1|
      let ridge := 1.0 - Float.abs (noise * 2.0 - 1.0)
      let ridge' := ridge * ridge * weight
      let total' := total + ridge' * amp
      let weight' := Float.min 1.0 (ridge' * gain)
      go (fuel - 1) (i + 1) (freq * lacunarity) (amp * persistence) total' weight'
  go octaves 0 1.0 1.0 0.0 1.0

end Lattice.Services.Noise.SimplexNoise
