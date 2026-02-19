/-
  Lattice.Services.Time.DisplacementMap - Temporal Displacement Map Generation

  Pure mathematical functions for time displacement effect maps:
  - Gradient (horizontal, vertical, diagonal)
  - Radial (center-out, edge-in)
  - Sinusoidal patterns

  Source: ui/src/services/effects/timeRenderer.ts (lines 459-514)
-/

namespace Lattice.Services.Time.DisplacementMap

--------------------------------------------------------------------------------
-- Horizontal Gradient
--------------------------------------------------------------------------------

/-- Generate horizontal gradient displacement value.
    Returns 0 at left edge, 1 at right edge. -/
def gradientH (x width : Nat) : Float :=
  if width == 0 then 0.5
  else x.toFloat / width.toFloat

--------------------------------------------------------------------------------
-- Vertical Gradient
--------------------------------------------------------------------------------

/-- Generate vertical gradient displacement value.
    Returns 0 at top edge, 1 at bottom edge. -/
def gradientV (y height : Nat) : Float :=
  if height == 0 then 0.5
  else y.toFloat / height.toFloat

--------------------------------------------------------------------------------
-- Diagonal Gradient
--------------------------------------------------------------------------------

/-- Generate diagonal gradient displacement value.
    Averages horizontal and vertical gradients. -/
def diagonal (x y width height : Nat) : Float :=
  (gradientH x width + gradientV y height) / 2.0

--------------------------------------------------------------------------------
-- Radial Distance
--------------------------------------------------------------------------------

/-- Calculate distance from center, normalized to [0, 1].
    Returns 0 at center, 1 at corners. -/
def radialDistance (x y width height : Nat) : Float :=
  if width == 0 || height == 0 then 0.5
  else
    let cx := width.toFloat / 2.0
    let cy := height.toFloat / 2.0
    let dx := x.toFloat - cx
    let dy := y.toFloat - cy
    let dist := Float.sqrt (dx * dx + dy * dy)
    let maxDist := Float.sqrt (cx * cx + cy * cy)
    if maxDist < 0.0001 then 0.0
    else dist / maxDist

/-- Radial displacement: 0 at center, 1 at edges. -/
def radial (x y width height : Nat) : Float :=
  radialDistance x y width height

/-- Center-out displacement: 1 at center, 0 at edges (inverted radial). -/
def centerOut (x y width height : Nat) : Float :=
  1.0 - radialDistance x y width height

--------------------------------------------------------------------------------
-- Sinusoidal Patterns
--------------------------------------------------------------------------------

/-- Horizontal sine wave displacement.
    scale controls number of wave periods. -/
def sineH (x width : Nat) (scale : Float) : Float :=
  if width == 0 then 0.5
  else
    let normalizedX := x.toFloat / width.toFloat
    0.5 + 0.5 * Float.sin (normalizedX * Float.pi * 2.0 * scale)

/-- Vertical sine wave displacement.
    scale controls number of wave periods. -/
def sineV (y height : Nat) (scale : Float) : Float :=
  if height == 0 then 0.5
  else
    let normalizedY := y.toFloat / height.toFloat
    0.5 + 0.5 * Float.sin (normalizedY * Float.pi * 2.0 * scale)

--------------------------------------------------------------------------------
-- Displacement Value Dispatcher
--------------------------------------------------------------------------------

/-- Map type enum. -/
inductive MapType
  | gradientH
  | gradientV
  | radial
  | sineH
  | sineV
  | diagonal
  | centerOut
  deriving Repr, DecidableEq

/-- Get displacement value for a pixel based on map type.
    Returns value in [0, 1] range. -/
def getDisplacementValue (mapType : MapType) (x y width height : Nat) (scale : Float) : Float :=
  match mapType with
  | MapType.gradientH => gradientH x width
  | MapType.gradientV => gradientV y height
  | MapType.radial => radial x y width height
  | MapType.sineH => sineH x width scale
  | MapType.sineV => sineV y height scale
  | MapType.diagonal => diagonal x y width height
  | MapType.centerOut => centerOut x y width height

--------------------------------------------------------------------------------
-- Frame Offset Calculation
--------------------------------------------------------------------------------

/-- Apply bias to displacement value.
    Shifts the 0.5 neutral point. -/
def applyBias (dispValue bias : Float) : Float :=
  dispValue + bias

/-- Convert biased displacement to frame offset.
    Maps [0, 1] (with bias) to [-maxDisplacement, +maxDisplacement]. -/
def toFrameOffset (biasedValue maxDisplacement : Float) : Int :=
  let offset := (biasedValue - 0.5) * 2.0 * maxDisplacement
  offset.toInt32.toInt

/-- Calculate target frame from current frame and displacement.
    Combines displacement value, bias, and max displacement. -/
def calculateTargetFrame (currentFrame : Int) (dispValue bias maxDisplacement : Float) : Int :=
  let biased := applyBias dispValue bias
  let offset := toFrameOffset biased maxDisplacement
  currentFrame + offset

end Lattice.Services.Time.DisplacementMap
