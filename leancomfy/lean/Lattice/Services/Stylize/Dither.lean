/-
  Lattice.Services.Stylize.Dither - Dithering Mathematics

  Pure mathematical functions for dithering:
  - Bayer matrices (2x2, 4x4, 8x8)
  - Ordered dithering threshold calculation
  - Color quantization
  - Error diffusion coefficients

  Source: ui/src/services/effects/stylizeRenderer.ts (lines 790-948)
-/

namespace Lattice.Services.Stylize.Dither

--------------------------------------------------------------------------------
-- Dither Method Types
--------------------------------------------------------------------------------

/-- Dithering algorithm type -/
inductive DitherMethod
  | ordered         -- Bayer matrix ordered dithering
  | floydSteinberg  -- Floyd-Steinberg error diffusion
  | atkinson        -- Atkinson error diffusion
deriving Repr, BEq, Inhabited

--------------------------------------------------------------------------------
-- Bayer Matrices
--------------------------------------------------------------------------------

/-- Bayer 2x2 matrix values (divide by 4 for threshold).
    Pattern: [[0, 2], [3, 1]] -/
def bayer2 (x y : Nat) : Nat :=
  let row := y % 2
  let col := x % 2
  if row = 0 then
    if col = 0 then 0 else 2
  else
    if col = 0 then 3 else 1

/-- Bayer 4x4 matrix values (divide by 16 for threshold).
    Standard Bayer pattern used in ordered dithering. -/
def bayer4 (x y : Nat) : Nat :=
  let row := y % 4
  let col := x % 4
  let matrix := #[
    #[0, 8, 2, 10],
    #[12, 4, 14, 6],
    #[3, 11, 1, 9],
    #[15, 7, 13, 5]
  ]
  match matrix.get? row with
  | some rowArr =>
    match rowArr.get? col with
    | some v => v
    | none => 0
  | none => 0

/-- Bayer 8x8 matrix values (divide by 64 for threshold). -/
def bayer8 (x y : Nat) : Nat :=
  let row := y % 8
  let col := x % 8
  let matrix := #[
    #[0, 32, 8, 40, 2, 34, 10, 42],
    #[48, 16, 56, 24, 50, 18, 58, 26],
    #[12, 44, 4, 36, 14, 46, 6, 38],
    #[60, 28, 52, 20, 62, 30, 54, 22],
    #[3, 35, 11, 43, 1, 33, 9, 41],
    #[51, 19, 59, 27, 49, 17, 57, 25],
    #[15, 47, 7, 39, 13, 45, 5, 37],
    #[63, 31, 55, 23, 61, 29, 53, 21]
  ]
  match matrix.get? row with
  | some rowArr =>
    match rowArr.get? col with
    | some v => v
    | none => 0
  | none => 0

/-- Get Bayer matrix value for any supported size (2, 4, or 8).

    @param matrixSize Size of matrix (2, 4, or 8)
    @param x X coordinate
    @param y Y coordinate
    @return Matrix value at position -/
def bayerValue (matrixSize : Nat) (x y : Nat) : Nat :=
  if matrixSize = 2 then bayer2 x y
  else if matrixSize = 8 then bayer8 x y
  else bayer4 x y

--------------------------------------------------------------------------------
-- Ordered Dithering
--------------------------------------------------------------------------------

/-- Calculate ordered dithering threshold offset.

    @param x X coordinate
    @param y Y coordinate
    @param matrixSize Bayer matrix size (2, 4, or 8)
    @param levels Number of color levels
    @return Threshold offset to add to pixel value before quantization -/
def orderedThreshold (x y matrixSize levels : Nat) : Float :=
  let matrixMax := Float.ofNat (matrixSize * matrixSize)
  let matrixVal := Float.ofNat (bayerValue matrixSize x y)
  (matrixVal / matrixMax - 0.5) * (256.0 / Float.ofNat levels)

--------------------------------------------------------------------------------
-- Quantization
--------------------------------------------------------------------------------

/-- Quantize a color value to a reduced number of levels.

    @param val Original value (0-255)
    @param levels Number of output levels (2-256)
    @return Quantized value (0-255) -/
def quantize (val : Float) (levels : Nat) : Float :=
  let step := 255.0 / Float.ofNat (levels - 1)
  Float.round (val / step) * step

/-- Clamp value to 0-255 range.

    @param val Input value
    @return Clamped value in [0, 255] -/
def clamp255 (val : Float) : Float :=
  Float.max 0.0 (Float.min 255.0 val)

--------------------------------------------------------------------------------
-- Floyd-Steinberg Error Diffusion
--------------------------------------------------------------------------------

/-- Floyd-Steinberg error distribution coefficients.

    Distributes error to 4 neighboring pixels:
    - Right:        7/16
    - Bottom-left:  3/16
    - Bottom:       5/16
    - Bottom-right: 1/16

    Total: 16/16 = 100% of error distributed -/
structure FloydSteinbergCoeffs where
  right       : Float := 7.0 / 16.0
  bottomLeft  : Float := 3.0 / 16.0
  bottom      : Float := 5.0 / 16.0
  bottomRight : Float := 1.0 / 16.0
deriving Repr, Inhabited

/-- Standard Floyd-Steinberg coefficients -/
def floydSteinbergCoeffs : FloydSteinbergCoeffs :=
  { right := 7.0 / 16.0
  , bottomLeft := 3.0 / 16.0
  , bottom := 5.0 / 16.0
  , bottomRight := 1.0 / 16.0 }

/-- Calculate distributed error for Floyd-Steinberg.

    @param error The quantization error (oldVal - newVal)
    @return (right, bottomLeft, bottom, bottomRight) errors -/
def distributeErrorFS (error : Float) : Float × Float × Float × Float :=
  let c := floydSteinbergCoeffs
  (error * c.right, error * c.bottomLeft, error * c.bottom, error * c.bottomRight)

--------------------------------------------------------------------------------
-- Atkinson Error Diffusion
--------------------------------------------------------------------------------

/-- Atkinson error distribution.

    Distributes only 6/8 of error (more contrast than Floyd-Steinberg).
    Each of 6 neighbors gets 1/8 of error.

    Pattern:
        X  1  1
     1  1  1
        1

    @param error The quantization error
    @return Error per neighbor (same for all 6) -/
def atkinsonErrorPerNeighbor (error : Float) : Float :=
  error / 8.0

/-- Atkinson neighbor offsets relative to current pixel.

    Returns array of (dx, dy) offsets for the 6 neighbors. -/
def atkinsonOffsets : Array (Int × Int) :=
  #[(1, 0), (2, 0), (-1, 1), (0, 1), (1, 1), (0, 2)]

end Lattice.Services.Stylize.Dither
