/-
  Lattice.Services.Distort.Ripple - Ripple Distortion Mathematics

  Pure mathematical functions for ripple/wave distortion:
  - Concentric wave calculation
  - Decay/falloff functions
  - Radial displacement

  Source: ui/src/services/effects/distortRenderer.ts (lines 1209-1324)
-/

namespace Lattice.Services.Distort.Ripple

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Ripple configuration -/
structure RippleConfig where
  centerX : Float      -- Center X (0-1 normalized)
  centerY : Float      -- Center Y (0-1 normalized)
  radius : Float       -- Maximum radius of effect (pixels)
  wavelength : Float   -- Distance between wave peaks (pixels)
  amplitude : Float    -- Maximum displacement (pixels)
  phase : Float        -- Phase offset (radians, for animation)
  decay : Float        -- Falloff exponent (0-1)
deriving Repr, Inhabited

/-- Ripple displacement result -/
structure RippleResult where
  srcX : Float
  srcY : Float
  inEffect : Bool      -- Whether pixel is within ripple radius
deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Wave Calculation
--------------------------------------------------------------------------------

/-- Calculate ripple wave value at a distance.

    Uses sine wave with phase offset.

    @param dist Distance from center (pixels)
    @param wavelength Distance between peaks (pixels)
    @param phase Phase offset (radians)
    @return Wave value in [-1, 1] -/
def rippleWave (dist wavelength phase : Float) : Float :=
  if wavelength < 0.0001 then 0.0
  else Float.sin ((dist / wavelength) * 2.0 * Float.pi + phase)

--------------------------------------------------------------------------------
-- Decay/Falloff
--------------------------------------------------------------------------------

/-- Calculate decay factor based on distance from center.

    Uses power function for smooth falloff.

    @param dist Distance from center
    @param radius Maximum effect radius
    @param decay Decay exponent (higher = faster falloff)
    @return Falloff factor in [0, 1] -/
def decayFactor (dist radius decay : Float) : Float :=
  if radius <= 0.0 then 0.0
  else if dist >= radius then 0.0
  else Float.pow (1.0 - dist / radius) decay

/-- Linear falloff (simple version).

    @param dist Distance from center
    @param radius Maximum radius
    @return Linear falloff in [0, 1] -/
def linearFalloff (dist radius : Float) : Float :=
  if radius <= 0.0 then 0.0
  else Float.max 0.0 (1.0 - dist / radius)

/-- Smooth falloff using smoothstep.

    @param dist Distance from center
    @param radius Maximum radius
    @return Smooth falloff in [0, 1] -/
def smoothFalloff (dist radius : Float) : Float :=
  if radius <= 0.0 then 0.0
  else
    let t := Float.max 0.0 (Float.min 1.0 (1.0 - dist / radius))
    t * t * (3.0 - 2.0 * t)

--------------------------------------------------------------------------------
-- Radial Displacement
--------------------------------------------------------------------------------

/-- Calculate unit direction vector from center to point.

    @param dx X distance from center
    @param dy Y distance from center
    @param dist Total distance (pre-computed)
    @return (nx, ny) unit direction vector -/
def unitDirection (dx dy dist : Float) : Float × Float :=
  if dist < 0.0001 then (0.0, 0.0)
  else (dx / dist, dy / dist)

/-- Apply radial displacement along direction from center.

    @param x Current X
    @param y Current Y
    @param nx Unit direction X
    @param ny Unit direction Y
    @param displacement Displacement amount (signed)
    @return (newX, newY) displaced position -/
def radialDisplace (x y nx ny displacement : Float) : Float × Float :=
  (x - nx * displacement, y - ny * displacement)

--------------------------------------------------------------------------------
-- Ripple Effect
--------------------------------------------------------------------------------

/-- Calculate ripple displacement for a single pixel.

    @param x Pixel X coordinate
    @param y Pixel Y coordinate
    @param config Ripple configuration
    @param width Image width (for center conversion)
    @param height Image height (for center conversion)
    @return Displaced source coordinates -/
def calculateRipple (x y : Float) (config : RippleConfig) (width height : Float) : RippleResult :=
  let centerXPixels := config.centerX * width
  let centerYPixels := config.centerY * height
  let dx := x - centerXPixels
  let dy := y - centerYPixels
  let dist := Float.sqrt (dx * dx + dy * dy)

  -- Check if within effect radius
  if dist <= 0.0 || dist >= config.radius then
    { srcX := x, srcY := y, inEffect := false }
  else
    -- Calculate ripple displacement
    let wave := rippleWave dist config.wavelength config.phase
    let falloff := decayFactor dist config.radius config.decay
    let displacement := wave * config.amplitude * falloff

    -- Get radial direction and displace
    let (nx, ny) := unitDirection dx dy dist
    let (srcX, srcY) := radialDisplace x y nx ny displacement

    { srcX := srcX, srcY := srcY, inEffect := true }

--------------------------------------------------------------------------------
-- Multiple Ripple Sources
--------------------------------------------------------------------------------

/-- Combine displacement from multiple ripple sources.

    Uses additive blending of displacements.

    @param x Pixel X
    @param y Pixel Y
    @param configs Array of ripple configurations
    @param width Image width
    @param height Image height
    @return Combined displaced coordinates -/
def combineRipples (x y : Float) (configs : Array RippleConfig) (width height : Float) : Float × Float :=
  let (totalDx, totalDy) := configs.foldl (fun (accDx, accDy) config =>
    let result := calculateRipple x y config width height
    if result.inEffect then
      (accDx + (x - result.srcX), accDy + (y - result.srcY))
    else
      (accDx, accDy)
  ) (0.0, 0.0)
  (x - totalDx, y - totalDy)

--------------------------------------------------------------------------------
-- Animation Helpers
--------------------------------------------------------------------------------

/-- Convert degrees to radians for phase.

    @param degrees Phase in degrees
    @return Phase in radians -/
def phaseToRadians (degrees : Float) : Float :=
  degrees * Float.pi / 180.0

/-- Calculate animated phase for looping.

    @param time Current time (0-1 normalized over loop period)
    @param loops Number of complete wave cycles per period
    @return Phase in radians -/
def animatedPhase (time : Float) (loops : Nat) : Float :=
  time * Float.ofNat loops * 2.0 * Float.pi

end Lattice.Services.Distort.Ripple
