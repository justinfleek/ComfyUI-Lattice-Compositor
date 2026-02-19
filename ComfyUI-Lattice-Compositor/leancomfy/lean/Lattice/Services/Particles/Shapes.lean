/-
  Lattice.Services.Particles.Shapes - Particle Emitter Shape Distributions

  Pure mathematical functions for particle emission positions based on
  emitter shape. Provides uniform distributions within various geometric
  shapes for particle spawning.

  Supported shapes:
  - Point: Single point emission
  - Line: Linear emission perpendicular to direction
  - Circle: Filled or edge-only circular emission
  - Ring: Donut-shaped emission (inner/outer radius)
  - Box: Rectangular emission (filled or perimeter)
  - Sphere: 3D sphere projected to 2D (surface or volume)
  - Cone: Conical emission along direction

  All shapes use deterministic random values (0-1) as input to ensure
  reproducible particle spawning with seeded RNG.

  Source: ui/src/services/particleSystem.ts
-/

namespace Lattice.Services.Particles.Shapes

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Result of spawn position calculation -/
structure SpawnResult where
  x : Float           -- X position (normalized 0-1)
  y : Float           -- Y position (normalized 0-1)
  direction : Option Float  -- Optional direction override (degrees)
  deriving Repr, Inhabited

/-- Box perimeter edge for edge emission -/
inductive BoxEdge
  | top
  | right
  | bottom
  | left
  deriving Repr, Inhabited, BEq

--------------------------------------------------------------------------------
-- Point Emission
--------------------------------------------------------------------------------

/-- Emit from a single point. -/
def emitPoint (emitterX emitterY : Float) : SpawnResult :=
  { x := emitterX, y := emitterY, direction := none }

--------------------------------------------------------------------------------
-- Line Emission
--------------------------------------------------------------------------------

/-- Emit from a line perpendicular to emitter direction.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param direction Emitter direction in degrees
    @param halfWidth Half-width of the line
    @param t Random value (0-1) for position along line
    @return Spawn position on the line -/
def emitLine (emitterX emitterY direction halfWidth t : Float) : SpawnResult :=
  let dirRad := direction * Float.pi / 180.0
  -- Perpendicular to direction
  let perpX := -Float.sin dirRad
  let perpY := Float.cos dirRad
  let offset := (t - 0.5) * halfWidth * 2.0
  { x := emitterX + perpX * offset
  , y := emitterY + perpY * offset
  , direction := none }

--------------------------------------------------------------------------------
-- Circle Emission
--------------------------------------------------------------------------------

/-- Emit from a filled circle with uniform area distribution.

    Uses sqrt(random) to ensure uniform distribution over area.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param radius Circle radius
    @param randomAngle Random value (0-1) for angle
    @param randomRadius Random value (0-1) for radius
    @return Spawn position in circle -/
def emitCircleFilled (emitterX emitterY radius randomAngle randomRadius : Float) : SpawnResult :=
  let angle := randomAngle * Float.pi * 2.0
  -- sqrt for uniform area distribution
  let r := radius * Float.sqrt randomRadius
  { x := emitterX + Float.cos angle * r
  , y := emitterY + Float.sin angle * r
  , direction := none }

/-- Emit from circle edge only.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param radius Circle radius
    @param randomAngle Random value (0-1) for angle
    @return Spawn position on circle edge -/
def emitCircleEdge (emitterX emitterY radius randomAngle : Float) : SpawnResult :=
  let angle := randomAngle * Float.pi * 2.0
  { x := emitterX + Float.cos angle * radius
  , y := emitterY + Float.sin angle * radius
  , direction := none }

--------------------------------------------------------------------------------
-- Ring Emission
--------------------------------------------------------------------------------

/-- Emit from a ring (donut) with uniform area distribution.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param innerRadius Inner radius of ring
    @param outerRadius Outer radius of ring
    @param randomAngle Random value (0-1) for angle
    @param randomRadius Random value (0-1) for radius
    @return Spawn position in ring -/
def emitRing (emitterX emitterY innerRadius outerRadius randomAngle randomRadius : Float) : SpawnResult :=
  let angle := randomAngle * Float.pi * 2.0
  -- Uniform distribution in ring area
  let innerSq := innerRadius * innerRadius
  let outerSq := outerRadius * outerRadius
  let r := Float.sqrt (randomRadius * (outerSq - innerSq) + innerSq)
  { x := emitterX + Float.cos angle * r
  , y := emitterY + Float.sin angle * r
  , direction := none }

--------------------------------------------------------------------------------
-- Box Emission
--------------------------------------------------------------------------------

/-- Emit from a filled box.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param width Box width
    @param height Box height
    @param randomX Random value (0-1) for X position
    @param randomY Random value (0-1) for Y position
    @return Spawn position in box -/
def emitBoxFilled (emitterX emitterY width height randomX randomY : Float) : SpawnResult :=
  { x := emitterX + (randomX - 0.5) * width
  , y := emitterY + (randomY - 0.5) * height
  , direction := none }

/-- Determine which edge of a box a perimeter position falls on.

    @param t Normalized position along perimeter (0-1)
    @param width Box width
    @param height Box height
    @return Edge and position on that edge -/
def boxEdgeFromT (t width height : Float) : BoxEdge × Float :=
  let perimeter := 2.0 * (width + height)
  let pos := t * perimeter
  if pos < width then
    (BoxEdge.top, pos)
  else if pos < width + height then
    (BoxEdge.right, pos - width)
  else if pos < 2.0 * width + height then
    (BoxEdge.bottom, pos - width - height)
  else
    (BoxEdge.left, pos - 2.0 * width - height)

/-- Emit from box perimeter (edges only).

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param width Box width
    @param height Box height
    @param randomT Random value (0-1) for position along perimeter
    @return Spawn position on box edge -/
def emitBoxEdge (emitterX emitterY width height randomT : Float) : SpawnResult :=
  let halfW := width / 2.0
  let halfH := height / 2.0
  let (edge, edgePos) := boxEdgeFromT randomT width height
  match edge with
  | BoxEdge.top =>
      { x := emitterX - halfW + edgePos, y := emitterY - halfH, direction := none }
  | BoxEdge.right =>
      { x := emitterX + halfW, y := emitterY - halfH + edgePos, direction := none }
  | BoxEdge.bottom =>
      { x := emitterX + halfW - edgePos, y := emitterY + halfH, direction := none }
  | BoxEdge.left =>
      { x := emitterX - halfW, y := emitterY + halfH - edgePos, direction := none }

--------------------------------------------------------------------------------
-- Sphere Emission (3D projected to 2D)
--------------------------------------------------------------------------------

/-- Emit from sphere surface.

    Uses spherical coordinates with uniform distribution.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param radius Sphere radius
    @param randomTheta Random value (0-1) for theta angle
    @param randomPhi Random value (0-1) for phi angle (uses acos for uniform)
    @return Spawn position on sphere surface (XY projection) -/
def emitSphereSurface (emitterX emitterY radius randomTheta randomPhi : Float) : SpawnResult :=
  let theta := randomTheta * Float.pi * 2.0
  -- Uniform distribution on sphere surface
  let phi := Float.acos (2.0 * randomPhi - 1.0)
  { x := emitterX + Float.sin phi * Float.cos theta * radius
  , y := emitterY + Float.sin phi * Float.sin theta * radius
  , direction := none }

/-- Emit from sphere volume using rejection sampling.

    Takes pre-sampled point that passed rejection test.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param radius Sphere radius
    @param unitX Normalized X coordinate (-1 to 1, inside unit sphere)
    @param unitY Normalized Y coordinate (-1 to 1, inside unit sphere)
    @return Spawn position inside sphere (XY projection) -/
def emitSphereVolume (emitterX emitterY radius unitX unitY : Float) : SpawnResult :=
  { x := emitterX + unitX * radius
  , y := emitterY + unitY * radius
  , direction := none }

--------------------------------------------------------------------------------
-- Cone Emission
--------------------------------------------------------------------------------

/-- Emit from a cone volume.

    Cone opens along the emitter direction from the emitter position.

    @param emitterX Emitter center X
    @param emitterY Emitter center Y
    @param direction Emitter direction in degrees
    @param coneAngle Half-angle of cone in degrees
    @param coneRadius Maximum radius at cone end
    @param coneLength Length of cone
    @param randomT Random value (0-1) for position along cone length
    @param randomTheta Random value (0-1) for angle around cone axis
    @return Spawn position in cone -/
def emitCone (emitterX emitterY direction coneAngle coneRadius coneLength randomT randomTheta : Float) : SpawnResult :=
  let coneAngleRad := coneAngle * Float.pi / 180.0
  let theta := randomTheta * Float.pi * 2.0
  -- Radius grows along cone
  let radiusAtT := randomT * coneRadius * Float.tan coneAngleRad
  -- Position in cone's local space
  let localX := Float.cos theta * radiusAtT
  let localY := randomT * coneLength
  -- Rotate to emitter direction
  let dirRad := direction * Float.pi / 180.0
  let cosDir := Float.cos dirRad
  let sinDir := Float.sin dirRad
  { x := emitterX + localX * cosDir - localY * sinDir
  , y := emitterY + localX * sinDir + localY * cosDir
  , direction := none }

--------------------------------------------------------------------------------
-- Collision Response
--------------------------------------------------------------------------------

/-- Elastic collision response between two particles.

    Returns new velocities for both particles.

    @param p1x Particle 1 X position
    @param p1y Particle 1 Y position
    @param v1x Particle 1 X velocity
    @param v1y Particle 1 Y velocity
    @param p2x Particle 2 X position
    @param p2y Particle 2 Y position
    @param v2x Particle 2 X velocity
    @param v2y Particle 2 Y velocity
    @param damping Collision damping factor
    @return ((new v1x, new v1y), (new v2x, new v2y)) -/
def elasticCollision (p1x p1y v1x v1y p2x p2y v2x v2y damping : Float) :
    (Float × Float) × (Float × Float) :=
  let dx := p2x - p1x
  let dy := p2y - p1y
  let dist := Float.sqrt (dx * dx + dy * dy)

  if dist < 0.0001 then
    -- Particles at same position, no collision response
    ((v1x, v1y), (v2x, v2y))
  else
    let nx := dx / dist
    let ny := dy / dist
    -- Relative velocity
    let dvx := v1x - v2x
    let dvy := v1y - v2y
    -- Velocity component along collision normal
    let dvDotN := dvx * nx + dvy * ny
    -- Only respond if moving towards each other
    if dvDotN <= 0.0 then
      ((v1x, v1y), (v2x, v2y))
    else
      -- Apply impulse
      let impulseX := dvDotN * nx * damping
      let impulseY := dvDotN * ny * damping
      ((v1x - impulseX, v1y - impulseY), (v2x + impulseX, v2y + impulseY))

/-- Calculate particle separation to prevent overlap.

    @param p1x Particle 1 X position
    @param p1y Particle 1 Y position
    @param p2x Particle 2 X position
    @param p2y Particle 2 Y position
    @param minDist Minimum distance (sum of radii)
    @return ((new p1x, new p1y), (new p2x, new p2y)) -/
def separateParticles (p1x p1y p2x p2y minDist : Float) :
    (Float × Float) × (Float × Float) :=
  let dx := p2x - p1x
  let dy := p2y - p1y
  let dist := Float.sqrt (dx * dx + dy * dy)

  if dist >= minDist || dist < 0.0001 then
    -- No overlap or coincident
    ((p1x, p1y), (p2x, p2y))
  else
    let overlap := minDist - dist
    let nx := dx / dist
    let ny := dy / dist
    let halfOverlap := overlap * 0.5
    ((p1x - nx * halfOverlap, p1y - ny * halfOverlap),
     (p2x + nx * halfOverlap, p2y + ny * halfOverlap))

end Lattice.Services.Particles.Shapes
