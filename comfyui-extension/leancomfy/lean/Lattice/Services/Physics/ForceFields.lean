/-
  Lattice.Services.Physics.ForceFields - Force Field Calculations

  Pure mathematical functions for force field calculations:
  - Gravity (constant direction)
  - Wind (with turbulence noise)
  - Attraction/Repulsion (point forces with falloff)
  - Explosion (instantaneous radial impulse)
  - Buoyancy (submerged depth-based)
  - Vortex (tangential + inward)
  - Drag (linear and quadratic)

  All functions are total and deterministic.

  Source: ui/src/services/physics/PhysicsEngine.ts (ForceFieldProcessor)
-/

namespace Lattice.Services.Physics.ForceFields

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Force field type enumeration -/
inductive ForceFieldType
  | gravity
  | wind
  | attraction
  | explosion
  | buoyancy
  | vortex
  | drag
  deriving Repr, Inhabited, BEq

/-- Force calculation result -/
inductive ForceResult
  | forceApplied (fx fy : Float)     -- Force to apply
  | impulseApplied (ix iy : Float)   -- Impulse (direct velocity change)
  | noForce                          -- Force doesn't apply
  deriving Repr, Inhabited, BEq

--------------------------------------------------------------------------------
-- Gravity
--------------------------------------------------------------------------------

/-- Calculate gravity force.

    Simple constant directional force scaled by mass.

    @param gx Gravity X component
    @param gy Gravity Y component
    @param mass Body mass
    @return (force X, force Y) -/
def calculateGravity (gx gy mass : Float) : Float × Float :=
  (gx * mass, gy * mass)

--------------------------------------------------------------------------------
-- Wind
--------------------------------------------------------------------------------

/-- Calculate wind force with turbulence.

    Combines base wind direction with noise-based turbulence.

    @param baseX Base wind X component
    @param baseY Base wind Y component
    @param noiseX Noise X offset
    @param noiseY Noise Y offset
    @param turbulence Turbulence strength
    @return (force X, force Y) -/
def calculateWind (baseX baseY noiseX noiseY turbulence : Float) : Float × Float :=
  (baseX + noiseX * turbulence, baseY + noiseY * turbulence)

--------------------------------------------------------------------------------
-- Attraction/Repulsion
--------------------------------------------------------------------------------

/-- Falloff type for attraction forces -/
inductive FalloffType
  | linear
  | quadratic
  | constant
  deriving Repr, Inhabited, BEq

/-- Calculate attraction force toward a point.

    @param cx Field center X
    @param cy Field center Y
    @param px Body position X
    @param py Body position Y
    @param strength Force strength (negative = repulsion)
    @param radius Falloff radius (0 = infinite range)
    @param mass Body mass
    @param falloff Falloff type
    @return Some (fx, fy) if in range, none otherwise -/
def calculateAttraction (cx cy px py strength radius mass : Float) (falloff : FalloffType) :
    Option (Float × Float) :=
  let dx := cx - px
  let dy := cy - py
  let distSq := dx * dx + dy * dy
  let dist := Float.sqrt distSq

  -- Out of radius check
  if radius > 0.0 && dist > radius then
    none
  -- Too close check (avoid singularity)
  else if dist < 1.0 then
    none
  else
    let forceMag := match falloff with
      | FalloffType.linear =>
          if radius > 0.0 then strength * (radius - dist) / radius
          else strength
      | FalloffType.quadratic =>
          if distSq > 0.0001 then strength / distSq
          else strength
      | FalloffType.constant => strength
    let dirX := dx / dist
    let dirY := dy / dist
    some (dirX * forceMag * mass, dirY * forceMag * mass)

--------------------------------------------------------------------------------
-- Explosion
--------------------------------------------------------------------------------

/-- Calculate explosion impulse.

    Radial impulse with linear falloff from center.

    @param ex Explosion center X
    @param ey Explosion center Y
    @param px Body position X
    @param py Body position Y
    @param strength Impulse strength
    @param radius Effect radius
    @return Some (impulseX, impulseY) if in range, none otherwise -/
def calculateExplosion (ex ey px py strength radius : Float) : Option (Float × Float) :=
  let dx := px - ex
  let dy := py - ey
  let dist := Float.sqrt (dx * dx + dy * dy)

  if dist > radius || dist < 1.0 then
    none
  else
    let falloff := 1.0 - dist / radius
    let nx := if dist > 0.0001 then dx / dist else 1.0
    let ny := if dist > 0.0001 then dy / dist else 0.0
    some (nx * strength * falloff, ny * strength * falloff)

--------------------------------------------------------------------------------
-- Buoyancy
--------------------------------------------------------------------------------

/-- Calculate buoyancy force.

    Simulates fluid buoyancy and drag for submerged bodies.

    @param surfaceLevel Y coordinate of fluid surface
    @param bodyY Body Y position
    @param density Fluid density
    @param mass Body mass
    @param radius Body radius (for submerged volume)
    @param velX Body X velocity
    @param velY Body Y velocity
    @param linearDrag Linear drag coefficient
    @return Some (fx, fy) if submerged, none otherwise -/
def calculateBuoyancy (surfaceLevel bodyY density mass radius velX velY linearDrag : Float) :
    Option (Float × Float) :=
  let submergedDepth := bodyY - surfaceLevel
  if submergedDepth <= 0.0 then
    none
  else
    let submergedRatio := Float.min 1.0 (submergedDepth / (radius * 2.0))
    let buoyancyForce := -density * submergedRatio * mass * 980.0
    let dragX := -linearDrag * velX * submergedRatio
    let dragY := -linearDrag * velY * submergedRatio
    some (dragX, buoyancyForce + dragY)

--------------------------------------------------------------------------------
-- Vortex
--------------------------------------------------------------------------------

/-- Calculate vortex force.

    Combines tangential (swirl) force with inward pull.

    @param cx Vortex center X
    @param cy Vortex center Y
    @param px Body position X
    @param py Body position Y
    @param tangentialStrength Tangential force strength
    @param inwardStrength Inward pull strength
    @param radius Effect radius
    @param mass Body mass
    @return Some (fx, fy) if in range, none otherwise -/
def calculateVortex (cx cy px py tangentialStrength inwardStrength radius mass : Float) :
    Option (Float × Float) :=
  let dx := px - cx
  let dy := py - cy
  let dist := Float.sqrt (dx * dx + dy * dy)

  if dist > radius || dist < 1.0 then
    none
  else
    let falloff := 1.0 - dist / radius
    let nx := dx / dist
    let ny := dy / dist
    -- Tangent vector (perpendicular to normal)
    let tx := -ny
    let ty := nx
    -- Tangential force (swirl)
    let tangentialX := tx * tangentialStrength * falloff * mass
    let tangentialY := ty * tangentialStrength * falloff * mass
    -- Inward force (pull toward center)
    let inwardX := -nx * inwardStrength * falloff * mass
    let inwardY := -ny * inwardStrength * falloff * mass
    some (tangentialX + inwardX, tangentialY + inwardY)

--------------------------------------------------------------------------------
-- Drag
--------------------------------------------------------------------------------

/-- Calculate drag force.

    Combines linear and quadratic drag components.
    F_drag = -linear * v - quadratic * |v| * v

    @param velX Body X velocity
    @param velY Body Y velocity
    @param linear Linear drag coefficient
    @param quadratic Quadratic drag coefficient
    @return Some (fx, fy) if significant velocity, none otherwise -/
def calculateDrag (velX velY linear quadratic : Float) : Option (Float × Float) :=
  let speed := Float.sqrt (velX * velX + velY * velY)
  if speed < 0.01 then
    none
  else
    let nx := velX / speed
    let ny := velY / speed
    let dragMag := linear * speed + quadratic * speed * speed
    some (-nx * dragMag, -ny * dragMag)

--------------------------------------------------------------------------------
-- Utility Functions
--------------------------------------------------------------------------------

/-- Linear falloff from 1 at center to 0 at radius.

    @param dist Distance from center
    @param radius Falloff radius
    @return Falloff factor in [0, 1] -/
def falloffLinear (dist radius : Float) : Float :=
  if radius <= 0.0 then 1.0
  else if dist >= radius then 0.0
  else 1.0 - dist / radius

/-- Quadratic (inverse square) falloff.

    @param dist Distance from center
    @return Falloff factor (1 / dist^2, clamped to 1 when dist < 1) -/
def falloffQuadratic (dist : Float) : Float :=
  if dist < 1.0 then 1.0
  else 1.0 / (dist * dist)

/-- Check if position is within radius of center.

    @param cx Center X
    @param cy Center Y
    @param px Position X
    @param py Position Y
    @param radius Check radius
    @return True if within radius -/
def inBoundsRadius (cx cy px py radius : Float) : Bool :=
  let dx := px - cx
  let dy := py - cy
  dx * dx + dy * dy <= radius * radius

/-- Combine multiple force results into single force.

    @param forces Array of force results
    @return Combined (fx, fy) -/
def combineForces (forces : Array ForceResult) : Float × Float :=
  forces.foldl (init := (0.0, 0.0)) fun acc result =>
    match result with
    | ForceResult.forceApplied fx fy => (acc.1 + fx, acc.2 + fy)
    | ForceResult.impulseApplied _ _ => acc  -- Impulses handled separately
    | ForceResult.noForce => acc

/-- Extract impulses from force results.

    @param forces Array of force results
    @return Combined (impulseX, impulseY) -/
def combineImpulses (forces : Array ForceResult) : Float × Float :=
  forces.foldl (init := (0.0, 0.0)) fun acc result =>
    match result with
    | ForceResult.forceApplied _ _ => acc  -- Forces handled separately
    | ForceResult.impulseApplied ix iy => (acc.1 + ix, acc.2 + iy)
    | ForceResult.noForce => acc

end Lattice.Services.Physics.ForceFields
