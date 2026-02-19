/-
  Lattice.Services.Distort.Interpolation - Bilinear Interpolation Mathematics

  Pure mathematical functions for pixel interpolation:
  - Bilinear interpolation weights
  - Coordinate clamping
  - Index calculation

  This is used by all distortion effects for smooth pixel sampling.

  Source: ui/src/services/effects/distortRenderer.ts (lines 376-401, 792-816)
-/

namespace Lattice.Services.Distort.Interpolation

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Bilinear sample coordinates -/
structure BilinearCoords where
  x0 : Nat       -- Floor X
  y0 : Nat       -- Floor Y
  x1 : Nat       -- Ceil X (clamped)
  y1 : Nat       -- Ceil Y (clamped)
  fx : Float     -- Fractional X [0, 1)
  fy : Float     -- Fractional Y [0, 1)
deriving Repr, Inhabited

/-- Bilinear weights for 4 corners -/
structure BilinearWeights where
  w00 : Float    -- Top-left weight
  w10 : Float    -- Top-right weight
  w01 : Float    -- Bottom-left weight
  w11 : Float    -- Bottom-right weight
deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Coordinate Clamping
--------------------------------------------------------------------------------

/-- Clamp coordinate to valid pixel range.

    @param coord Coordinate value
    @param maxVal Maximum valid value (width-1 or height-1)
    @return Clamped coordinate in [0, maxVal] -/
def clampCoord (coord : Float) (maxVal : Nat) : Float :=
  Float.max 0.0 (Float.min (Float.ofNat maxVal) coord)

/-- Clamp source coordinates to image bounds.

    @param srcX Source X coordinate
    @param srcY Source Y coordinate
    @param width Image width
    @param height Image height
    @return (clampedX, clampedY) -/
def clampToBounds (srcX srcY : Float) (width height : Nat) : Float × Float :=
  let maxX := if width > 0 then width - 1 else 0
  let maxY := if height > 0 then height - 1 else 0
  (clampCoord srcX maxX, clampCoord srcY maxY)

--------------------------------------------------------------------------------
-- Bilinear Coordinate Calculation
--------------------------------------------------------------------------------

/-- Calculate bilinear interpolation coordinates.

    @param srcX Source X (floating point)
    @param srcY Source Y (floating point)
    @param width Image width
    @param height Image height
    @return Bilinear sampling coordinates -/
def bilinearCoords (srcX srcY : Float) (width height : Nat) : BilinearCoords :=
  let maxX := if width > 0 then width - 1 else 0
  let maxY := if height > 0 then height - 1 else 0

  let x0f := Float.floor srcX
  let y0f := Float.floor srcY

  let x0 := Nat.min maxX (Float.toUInt64 (Float.max 0.0 x0f)).toNat
  let y0 := Nat.min maxY (Float.toUInt64 (Float.max 0.0 y0f)).toNat
  let x1 := Nat.min maxX (x0 + 1)
  let y1 := Nat.min maxY (y0 + 1)

  let fx := srcX - x0f
  let fy := srcY - y0f

  { x0 := x0, y0 := y0, x1 := x1, y1 := y1, fx := fx, fy := fy }

--------------------------------------------------------------------------------
-- Bilinear Weights
--------------------------------------------------------------------------------

/-- Calculate bilinear interpolation weights from fractional parts.

    Weights sum to 1.0 for proper interpolation.

    @param fx Fractional X [0, 1)
    @param fy Fractional Y [0, 1)
    @return Weights for 4 corners -/
def bilinearWeights (fx fy : Float) : BilinearWeights :=
  let invFx := 1.0 - fx
  let invFy := 1.0 - fy
  { w00 := invFx * invFy   -- Top-left
  , w10 := fx * invFy      -- Top-right
  , w01 := invFx * fy      -- Bottom-left
  , w11 := fx * fy }       -- Bottom-right

/-- Get weights from bilinear coordinates.

    @param coords Bilinear coordinates
    @return Interpolation weights -/
def weightsFromCoords (coords : BilinearCoords) : BilinearWeights :=
  bilinearWeights coords.fx coords.fy

--------------------------------------------------------------------------------
-- Pixel Index Calculation
--------------------------------------------------------------------------------

/-- Calculate linear pixel index from 2D coordinates.

    @param x X coordinate
    @param y Y coordinate
    @param width Image width (stride)
    @return Linear index for RGBA data (multiply by 4 for byte offset) -/
def pixelIndex (x y width : Nat) : Nat :=
  y * width + x

/-- Calculate RGBA byte offset from pixel index.

    @param pixelIdx Pixel index
    @return Byte offset for first channel (R) -/
def rgbaOffset (pixelIdx : Nat) : Nat :=
  pixelIdx * 4

/-- Get all 4 corner indices for bilinear sampling.

    @param coords Bilinear coordinates
    @param width Image width
    @return (idx00, idx10, idx01, idx11) pixel indices -/
def cornerIndices (coords : BilinearCoords) (width : Nat) : Nat × Nat × Nat × Nat :=
  let idx00 := pixelIndex coords.x0 coords.y0 width
  let idx10 := pixelIndex coords.x1 coords.y0 width
  let idx01 := pixelIndex coords.x0 coords.y1 width
  let idx11 := pixelIndex coords.x1 coords.y1 width
  (idx00, idx10, idx01, idx11)

--------------------------------------------------------------------------------
-- Interpolation
--------------------------------------------------------------------------------

/-- Interpolate a single value using bilinear weights.

    @param v00 Top-left value
    @param v10 Top-right value
    @param v01 Bottom-left value
    @param v11 Bottom-right value
    @param weights Bilinear weights
    @return Interpolated value -/
def interpolateValue (v00 v10 v01 v11 : Float) (weights : BilinearWeights) : Float :=
  v00 * weights.w00 + v10 * weights.w10 + v01 * weights.w01 + v11 * weights.w11

/-- Interpolate and round to nearest integer (for 8-bit pixel values).

    @param v00 v10 v01 v11 Corner values
    @param weights Bilinear weights
    @return Rounded interpolated value -/
def interpolateRound (v00 v10 v01 v11 : Float) (weights : BilinearWeights) : Nat :=
  let result := interpolateValue v00 v10 v01 v11 weights
  (Float.toUInt64 (Float.round result)).toNat

end Lattice.Services.Distort.Interpolation
