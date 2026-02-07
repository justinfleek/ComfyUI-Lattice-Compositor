/-
  Lattice.Services.Shader.Transition - Shader Transition Math

  Pure mathematical functions for GPU shader transitions:
  - Dissolve (noise-based threshold)
  - Wipe (directional threshold)
  - Smoothstep interpolation

  Source: ui/src/services/glsl/ShaderEffects.ts (transition effects)
-/

namespace Lattice.Services.Shader.Transition

--------------------------------------------------------------------------------
-- Smoothstep (Hermite interpolation)
--------------------------------------------------------------------------------

/-- Clamp value to [0, 1] range. -/
def clamp01 (x : Float) : Float :=
  if x < 0.0 then 0.0
  else if x > 1.0 then 1.0
  else x

/-- Smoothstep interpolation: S-curve from 0 to 1.

    Standard GLSL smoothstep formula.
    Returns 0 when x ≤ edge0, 1 when x ≥ edge1,
    and smooth Hermite interpolation between. -/
def smoothstep (edge0 edge1 x : Float) : Float :=
  if edge1 <= edge0 then
    if x < edge0 then 0.0 else 1.0
  else
    let t := clamp01 ((x - edge0) / (edge1 - edge0))
    t * t * (3.0 - 2.0 * t)

--------------------------------------------------------------------------------
-- Dissolve Transition
--------------------------------------------------------------------------------

/-- Calculate dissolve edge value.

    Uses noise-based threshold with soft edges.
    When noiseValue < progress - softness: fully transitioned (1.0)
    When noiseValue > progress + softness: not transitioned (0.0)
    Between: smooth interpolation -/
def dissolveEdge (noiseValue progress softness : Float) : Float :=
  smoothstep (progress - softness) (progress + softness) noiseValue

/-- Calculate dissolve blend factor.

    Returns how much of the "to" image should be visible.
    0 = show "from", 1 = show "to" -/
def dissolveBlend (noiseValue progress softness : Float) : Float :=
  dissolveEdge noiseValue progress softness

--------------------------------------------------------------------------------
-- Wipe Transition
--------------------------------------------------------------------------------

/-- Calculate directional wipe projection.

    Projects UV coordinate onto wipe direction.
    angleDeg: wipe angle (0 = left-to-right, 90 = bottom-to-top)
    Returns value in approximately [0, 1] range. -/
def wipeProjection (uvX uvY angleDeg : Float) : Float :=
  let rad := angleDeg * Float.pi / 180.0
  let dirX := Float.cos rad
  let dirY := Float.sin rad
  -- UV relative to center (0.5, 0.5)
  let relX := uvX - 0.5
  let relY := uvY - 0.5
  -- Dot product + offset to get [0, 1] range
  (relX * dirX + relY * dirY) + 0.5

/-- Calculate wipe edge value.

    Uses directional threshold with soft edges.
    progress: 0 = show "from", 1 = show "to"
    softness: edge feathering amount -/
def wipeEdge (uvX uvY angleDeg progress softness : Float) : Float :=
  let d := wipeProjection uvX uvY angleDeg
  smoothstep (progress - softness) (progress + softness) d

/-- Calculate wipe blend factor.

    Returns how much of the "to" image should be visible.
    0 = show "from", 1 = show "to" -/
def wipeBlend (uvX uvY angleDeg progress softness : Float) : Float :=
  wipeEdge uvX uvY angleDeg progress softness

--------------------------------------------------------------------------------
-- Radial Wipe
--------------------------------------------------------------------------------

/-- Calculate radial wipe distance from center.

    Used for iris/circular wipe transitions.
    centerX, centerY: wipe center (typically 0.5, 0.5)
    Returns normalized distance. -/
def radialDistance (uvX uvY centerX centerY : Float) : Float :=
  let dx := uvX - centerX
  let dy := uvY - centerY
  Float.sqrt (dx * dx + dy * dy)

/-- Calculate radial wipe edge value.

    Expands or contracts from center point.
    maxRadius: radius at which transition completes (typically ~0.707 for corners)
    invert: true for iris-in (shrinking), false for iris-out (expanding) -/
def radialWipeEdge (uvX uvY centerX centerY progress softness maxRadius : Float) (invert : Bool) : Float :=
  let dist := radialDistance uvX uvY centerX centerY
  let normalizedDist := dist / maxRadius
  let threshold := if invert then 1.0 - progress else progress
  smoothstep (threshold - softness) (threshold + softness) normalizedDist

--------------------------------------------------------------------------------
-- Clock Wipe
--------------------------------------------------------------------------------

/-- Calculate angle from center (in radians, 0 = right, counter-clockwise). -/
def angleFromCenter (uvX uvY centerX centerY : Float) : Float :=
  let dx := uvX - centerX
  let dy := uvY - centerY
  Float.atan2 dy dx

/-- Calculate clock wipe edge value.

    Sweeps around center point like a clock hand.
    startAngleDeg: angle where wipe starts (0 = right)
    clockwise: true for clockwise sweep -/
def clockWipeEdge (uvX uvY centerX centerY startAngleDeg progress softness : Float) (clockwise : Bool) : Float :=
  let angle := angleFromCenter uvX uvY centerX centerY
  let startRad := startAngleDeg * Float.pi / 180.0
  -- Normalize angle relative to start
  let relAngle := angle - startRad
  -- Wrap to [0, 2π]
  let twoPi := 2.0 * Float.pi
  let wrapped := relAngle - twoPi * Float.floor (relAngle / twoPi)
  let normalizedAngle := wrapped / twoPi
  -- Apply direction
  let directedAngle := if clockwise then 1.0 - normalizedAngle else normalizedAngle
  smoothstep (progress - softness) (progress + softness) directedAngle

--------------------------------------------------------------------------------
-- Linear Interpolation (for transition blending)
--------------------------------------------------------------------------------

/-- Linear interpolation between two values. -/
def lerp (a b t : Float) : Float :=
  a + (b - a) * t

/-- Linear interpolation for RGB colors. -/
def lerpColor (r1 g1 b1 r2 g2 b2 t : Float) : Float × Float × Float :=
  (lerp r1 r2 t, lerp g1 g2 t, lerp b1 b2 t)

/-- Linear interpolation for RGBA colors. -/
def lerpColorAlpha (r1 g1 b1 a1 r2 g2 b2 a2 t : Float) : Float × Float × Float × Float :=
  (lerp r1 r2 t, lerp g1 g2 t, lerp b1 b2 t, lerp a1 a2 t)

end Lattice.Services.Shader.Transition
