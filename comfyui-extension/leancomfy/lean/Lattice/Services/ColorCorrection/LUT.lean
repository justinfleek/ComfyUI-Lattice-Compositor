/-
  Lattice.Services.ColorCorrection.LUT - 3D Look-Up Table Math

  Pure mathematical functions for 3D LUT (Look-Up Table) operations:
  - Trilinear interpolation
  - LUT index calculation
  - Value sampling

  All functions are total (no partial def) and deterministic.

  Source: ui/src/services/effects/colorRenderer.ts (lines 1706-1773)
-/

namespace Lattice.Services.ColorCorrection.LUT

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Result of trilinear interpolation -/
structure LUTSample where
  r : Float
  g : Float
  b : Float
  deriving Repr, Inhabited

/-- Parameters for trilinear interpolation -/
structure TrilinearParams where
  /-- Lower R index -/
  r0 : Nat
  /-- Upper R index -/
  r1 : Nat
  /-- Lower G index -/
  g0 : Nat
  /-- Upper G index -/
  g1 : Nat
  /-- Lower B index -/
  b0 : Nat
  /-- Upper B index -/
  b1 : Nat
  /-- R fractional part -/
  rFrac : Float
  /-- G fractional part -/
  gFrac : Float
  /-- B fractional part -/
  bFrac : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Index Calculation
--------------------------------------------------------------------------------

/-- Calculate LUT array index from 3D coordinates.

    LUT data is stored in row-major order: B varies slowest, R varies fastest.
    Index = ((b * size + g) * size + r) * 3 + channel

    @param r Red index (0 to size-1)
    @param g Green index (0 to size-1)
    @param b Blue index (0 to size-1)
    @param size LUT cube size
    @param channel Color channel (0=R, 1=G, 2=B)
    @return Array index -/
def lutIndex (r g b size channel : Nat) : Nat :=
  ((b * size + g) * size + r) * 3 + channel

/-- Calculate trilinear interpolation parameters from normalized RGB.

    @param r Normalized red (0-1)
    @param g Normalized green (0-1)
    @param b Normalized blue (0-1)
    @param size LUT cube size
    @return Trilinear parameters -/
def trilinearParams (r g b : Float) (size : Nat) : TrilinearParams :=
  let maxIdx := size - 1
  let maxIdxF := Float.ofNat maxIdx

  -- Scale to LUT indices
  let rIdx := r * maxIdxF
  let gIdx := g * maxIdxF
  let bIdx := b * maxIdxF

  -- Get integer parts (floor)
  let r0 := Float.toUInt32 (Float.floor rIdx) |>.toNat
  let g0 := Float.toUInt32 (Float.floor gIdx) |>.toNat
  let b0 := Float.toUInt32 (Float.floor bIdx) |>.toNat

  -- Clamp to valid range
  let r0' := Nat.min r0 maxIdx
  let g0' := Nat.min g0 maxIdx
  let b0' := Nat.min b0 maxIdx

  -- Upper indices (clamped)
  let r1 := Nat.min (r0' + 1) maxIdx
  let g1 := Nat.min (g0' + 1) maxIdx
  let b1 := Nat.min (b0' + 1) maxIdx

  -- Fractional parts
  let rFrac := rIdx - Float.floor rIdx
  let gFrac := gIdx - Float.floor gIdx
  let bFrac := bIdx - Float.floor bIdx

  { r0 := r0', r1 := r1
  , g0 := g0', g1 := g1
  , b0 := b0', b1 := b1
  , rFrac := rFrac
  , gFrac := gFrac
  , bFrac := bFrac }

--------------------------------------------------------------------------------
-- Trilinear Interpolation
--------------------------------------------------------------------------------

/-- Perform trilinear interpolation for one channel.

    Trilinear interpolation samples 8 corners of a cube and blends them
    based on position within the cube.

    @param c000 Value at (0,0,0)
    @param c100 Value at (1,0,0)
    @param c010 Value at (0,1,0)
    @param c110 Value at (1,1,0)
    @param c001 Value at (0,0,1)
    @param c101 Value at (1,0,1)
    @param c011 Value at (0,1,1)
    @param c111 Value at (1,1,1)
    @param rFrac R fractional position
    @param gFrac G fractional position
    @param bFrac B fractional position
    @return Interpolated value -/
def trilinearInterpolateChannel
    (c000 c100 c010 c110 c001 c101 c011 c111 : Float)
    (rFrac gFrac bFrac : Float) : Float :=
  -- Interpolate along R axis
  let c00 := c000 + (c100 - c000) * rFrac
  let c10 := c010 + (c110 - c010) * rFrac
  let c01 := c001 + (c101 - c001) * rFrac
  let c11 := c011 + (c111 - c011) * rFrac

  -- Interpolate along G axis
  let c0 := c00 + (c10 - c00) * gFrac
  let c1 := c01 + (c11 - c01) * gFrac

  -- Interpolate along B axis
  c0 + (c1 - c0) * bFrac

/-- Perform full trilinear interpolation for RGB.

    @param corners Array of 8 corner samples, each with (r,g,b):
           [c000, c100, c010, c110, c001, c101, c011, c111]
    @param params Trilinear parameters
    @return Interpolated RGB values -/
def trilinearInterpolate
    (c000 c100 c010 c110 c001 c101 c011 c111 : LUTSample)
    (params : TrilinearParams) : LUTSample :=
  { r := trilinearInterpolateChannel
           c000.r c100.r c010.r c110.r c001.r c101.r c011.r c111.r
           params.rFrac params.gFrac params.bFrac
  , g := trilinearInterpolateChannel
           c000.g c100.g c010.g c110.g c001.g c101.g c011.g c111.g
           params.rFrac params.gFrac params.bFrac
  , b := trilinearInterpolateChannel
           c000.b c100.b c010.b c110.b c001.b c101.b c011.b c111.b
           params.rFrac params.gFrac params.bFrac
  }

--------------------------------------------------------------------------------
-- LUT Blending
--------------------------------------------------------------------------------

/-- Blend LUT result with original color.

    @param original Original normalized RGB (0-1)
    @param lutResult LUT-transformed RGB (0-1)
    @param intensity Blend intensity (0-1)
    @return Blended RGB (0-1) -/
def blendWithOriginal
    (originalR originalG originalB : Float)
    (lutResult : LUTSample)
    (intensity : Float) : LUTSample :=
  let invIntensity := 1.0 - intensity
  { r := originalR * invIntensity + lutResult.r * intensity
  , g := originalG * invIntensity + lutResult.g * intensity
  , b := originalB * invIntensity + lutResult.b * intensity
  }

/-- Convert LUT sample to 8-bit RGB values.

    @param sample LUT sample with values in 0-1
    @return (r, g, b) in 0-255 range -/
def sampleToRGB255 (sample : LUTSample) : Float × Float × Float :=
  ( Float.max 0.0 (Float.min 255.0 (sample.r * 255.0))
  , Float.max 0.0 (Float.min 255.0 (sample.g * 255.0))
  , Float.max 0.0 (Float.min 255.0 (sample.b * 255.0))
  )

end Lattice.Services.ColorCorrection.LUT
