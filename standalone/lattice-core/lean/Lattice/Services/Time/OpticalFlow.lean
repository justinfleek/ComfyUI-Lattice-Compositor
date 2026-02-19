/-
  Lattice.Services.Time.OpticalFlow - Motion Estimation Math

  Pure mathematical functions for optical flow-based frame interpolation:
  - Block matching using SAD (Sum of Absolute Differences)
  - Motion vector interpolation
  - Motion-compensated pixel sampling coordinates

  Source: ui/src/services/effects/timeRenderer.ts (lines 814-964)
-/

namespace Lattice.Services.Time.OpticalFlow

--------------------------------------------------------------------------------
-- Luminance Calculation
--------------------------------------------------------------------------------

/-- Calculate luminance from RGB using BT.601 coefficients.
    Y = 0.299*R + 0.587*G + 0.114*B -/
def luminance (r g b : Float) : Float :=
  r * 0.299 + g * 0.587 + b * 0.114

--------------------------------------------------------------------------------
-- Sum of Absolute Differences (SAD)
--------------------------------------------------------------------------------

/-- Calculate absolute difference between two luminance values. -/
def pixelSAD (lum1 lum2 : Float) : Float :=
  Float.abs (lum1 - lum2)

/-- Normalize SAD by number of valid pixels. -/
def normalizeSAD (totalSAD : Float) (validPixels : Nat) : Float :=
  if validPixels == 0 then Float.inf
  else totalSAD / validPixels.toFloat

--------------------------------------------------------------------------------
-- Block Coordinates
--------------------------------------------------------------------------------

/-- Calculate block index from pixel coordinates. -/
def pixelToBlockIndex (x y width blockSize : Nat) : Nat :=
  let blockX := x / blockSize
  let blockY := y / blockSize
  let blocksPerRow := (width + blockSize - 1) / blockSize
  blockY * blocksPerRow + blockX

/-- Calculate block start coordinates from block index. -/
def blockStartCoords (blockIndex width blockSize : Nat) : Nat × Nat :=
  let blocksPerRow := (width + blockSize - 1) / blockSize
  let blockY := blockIndex / blocksPerRow
  let blockX := blockIndex % blocksPerRow
  (blockX * blockSize, blockY * blockSize)

/-- Check if coordinates are within image bounds. -/
def inBounds (x y width height : Int) : Bool :=
  x >= 0 && y >= 0 && x < width && y < height

--------------------------------------------------------------------------------
-- Motion Vector Types
--------------------------------------------------------------------------------

/-- Motion vector (displacement in pixels). -/
structure MotionVector where
  x : Int
  y : Int
  deriving Repr, DecidableEq

/-- Zero motion vector. -/
def zeroMotion : MotionVector := { x := 0, y := 0 }

/-- Calculate motion vector magnitude. -/
def motionMagnitude (mv : MotionVector) : Float :=
  Float.sqrt (mv.x.toFloat * mv.x.toFloat + mv.y.toFloat * mv.y.toFloat)

--------------------------------------------------------------------------------
-- Motion-Compensated Sampling Coordinates
--------------------------------------------------------------------------------

/-- Calculate forward-compensated source position.
    Used to sample from frame1 with motion compensation. -/
def forwardSamplePosition (x y : Float) (mv : MotionVector) (blend : Float) : Float × Float :=
  ( x + mv.x.toFloat * (1.0 - blend)
  , y + mv.y.toFloat * (1.0 - blend)
  )

/-- Calculate backward-compensated source position.
    Used to sample from frame2 with motion compensation. -/
def backwardSamplePosition (x y : Float) (mv : MotionVector) (blend : Float) : Float × Float :=
  ( x - mv.x.toFloat * blend
  , y - mv.y.toFloat * blend
  )

--------------------------------------------------------------------------------
-- Search Window
--------------------------------------------------------------------------------

/-- Generate search offsets for motion estimation.
    Returns list of (dx, dy) offsets within search radius. -/
def searchOffsets (searchRadius : Nat) : List (Int × Int) :=
  let r := searchRadius.toInt
  List.join (List.map (fun dy =>
    List.map (fun dx => (dx, dy)) (List.range' (-r) (2 * r + 1))
  ) (List.range' (-r) (2 * r + 1)))

/-- Check if search offset produces valid block position. -/
def isValidSearchOffset (blockStartX blockStartY : Nat) (dx dy : Int)
                        (blockSize width height : Nat) : Bool :=
  let endX := blockStartX.toInt + blockSize.toInt + dx
  let endY := blockStartY.toInt + blockSize.toInt + dy
  blockStartX.toInt + dx >= 0 &&
  blockStartY.toInt + dy >= 0 &&
  endX <= width.toInt &&
  endY <= height.toInt

--------------------------------------------------------------------------------
-- Best Match Selection
--------------------------------------------------------------------------------

/-- Update best match if current SAD is lower. -/
def updateBestMatch (currentBest : MotionVector × Float) (candidate : MotionVector) (sad : Float)
                   : MotionVector × Float :=
  if sad < currentBest.2 then (candidate, sad)
  else currentBest

/-- Initial best match (no motion, infinite SAD). -/
def initialBestMatch : MotionVector × Float :=
  (zeroMotion, Float.inf)

--------------------------------------------------------------------------------
-- Block Matching Parameters
--------------------------------------------------------------------------------

/-- Default block size for motion estimation. -/
def defaultBlockSize : Nat := 8

/-- Default search radius for motion vectors. -/
def defaultSearchRadius : Nat := 8

/-- Calculate number of blocks in image. -/
def blockCount (width height blockSize : Nat) : Nat :=
  let blocksX := (width + blockSize - 1) / blockSize
  let blocksY := (height + blockSize - 1) / blockSize
  blocksX * blocksY

end Lattice.Services.Time.OpticalFlow
