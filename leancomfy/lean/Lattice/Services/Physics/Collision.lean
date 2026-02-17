/-
  Lattice.Services.Physics.Collision - Collision Detection Algorithms

  Pure mathematical functions for collision detection between shapes:
  - Circle vs Circle
  - Circle vs Box (AABB)
  - Box vs Box (AABB)

  Returns collision manifold with:
  - Contact normal (from A to B)
  - Penetration depth
  - Contact point

  All functions are deterministic and side-effect free.

  Source: ui/src/services/physics/PhysicsEngine.ts
-/

namespace Lattice.Services.Physics.Collision

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- 2D Vector (duplicated for independence, could import from VectorMath) -/
structure Vec2 where
  x : Float
  y : Float
  deriving Repr, Inhabited, BEq

/-- Collision manifold containing contact information -/
structure CollisionManifold where
  /-- Contact normal (pointing from body A to body B) -/
  normalX : Float
  normalY : Float
  /-- Penetration depth (positive when overlapping) -/
  depth : Float
  /-- Contact point (world coordinates) -/
  contactX : Float
  contactY : Float
  deriving Repr, Inhabited

--------------------------------------------------------------------------------
-- Vector Helpers (internal)
--------------------------------------------------------------------------------

private def vecLength (x y : Float) : Float :=
  Float.sqrt (x * x + y * y)

private def vecLengthSq (x y : Float) : Float :=
  x * x + y * y

private def vecNormalize (x y : Float) : Float × Float :=
  let len := vecLength x y
  if len < 0.0001 then
    (0.0, 0.0)
  else
    (x / len, y / len)

--------------------------------------------------------------------------------
-- Circle vs Circle
--------------------------------------------------------------------------------

/-- Test collision between two circles.

    @param x1 Center X of circle 1
    @param y1 Center Y of circle 1
    @param r1 Radius of circle 1
    @param x2 Center X of circle 2
    @param y2 Center Y of circle 2
    @param r2 Radius of circle 2
    @return Some manifold if collision, none otherwise -/
def circleVsCircle (x1 y1 r1 x2 y2 r2 : Float) : Option CollisionManifold :=
  let dx := x2 - x1
  let dy := y2 - y1
  let distSq := vecLengthSq dx dy
  let minDist := r1 + r2

  -- No collision if distance >= sum of radii
  if distSq >= minDist * minDist then
    none
  else
    let dist := Float.sqrt distSq
    -- Normal from circle 1 to circle 2
    let (nx, ny) := if dist > 0.0001 then
                      (dx / dist, dy / dist)
                    else
                      (1.0, 0.0)  -- Default normal for coincident centers
    let depth := minDist - dist
    -- Contact point is on the surface of circle 1, along the normal
    let contactX := x1 + nx * r1
    let contactY := y1 + ny * r1
    some { normalX := nx
         , normalY := ny
         , depth := depth
         , contactX := contactX
         , contactY := contactY }

--------------------------------------------------------------------------------
-- Circle vs Box (AABB)
--------------------------------------------------------------------------------

/-- Test collision between a circle and an axis-aligned box.

    @param cx Circle center X
    @param cy Circle center Y
    @param cr Circle radius
    @param bx Box center X
    @param by Box center Y
    @param bw Box half-width
    @param bh Box half-height
    @param boxAngle Box rotation angle (radians)
    @return Some manifold if collision, none otherwise -/
def circleVsBox (cx cy cr bx by bw bh boxAngle : Float) : Option CollisionManifold :=
  -- Transform circle center to box local space
  let cosA := Float.cos (-boxAngle)
  let sinA := Float.sin (-boxAngle)
  let dx := cx - bx
  let dy := cy - by
  let localX := dx * cosA - dy * sinA
  let localY := dx * sinA + dy * cosA

  -- Find closest point on box to circle center (in local space)
  let closestX := Float.max (-bw) (Float.min bw localX)
  let closestY := Float.max (-bh) (Float.min bh localY)

  -- Check if circle center is inside box
  let isInside := localX == closestX && localY == closestY

  -- Calculate distance from circle center to closest point
  let diffX := localX - closestX
  let diffY := localY - closestY
  let distSq := vecLengthSq diffX diffY

  if isInside then
    -- Circle center inside box - push out along shortest axis
    let dxEdge := bw - Float.abs localX
    let dyEdge := bh - Float.abs localY
    let (localNormalX, localNormalY, dist) :=
      if dxEdge < dyEdge then
        (if localX > 0.0 then 1.0 else -1.0, 0.0, dxEdge)
      else
        (0.0, if localY > 0.0 then 1.0 else -1.0, dyEdge)
    let depth := cr + dist
    -- Transform normal back to world space
    let worldNormalX := localNormalX * Float.cos boxAngle - localNormalY * Float.sin boxAngle
    let worldNormalY := localNormalX * Float.sin boxAngle + localNormalY * Float.cos boxAngle
    -- Contact point on circle surface
    let contactX := cx - worldNormalX * cr
    let contactY := cy - worldNormalY * cr
    some { normalX := -worldNormalX  -- Flip for inside case
         , normalY := -worldNormalY
         , depth := depth
         , contactX := contactX
         , contactY := contactY }
  else if distSq < cr * cr then
    -- Circle overlaps box edge
    let dist := Float.sqrt distSq
    let (localNormalX, localNormalY) :=
      if dist > 0.0001 then
        (diffX / dist, diffY / dist)
      else
        (1.0, 0.0)
    let depth := cr - dist
    -- Transform normal back to world space
    let worldNormalX := localNormalX * Float.cos boxAngle - localNormalY * Float.sin boxAngle
    let worldNormalY := localNormalX * Float.sin boxAngle + localNormalY * Float.cos boxAngle
    -- Contact point on circle surface
    let contactX := cx - worldNormalX * cr
    let contactY := cy - worldNormalY * cr
    some { normalX := worldNormalX
         , normalY := worldNormalY
         , depth := depth
         , contactX := contactX
         , contactY := contactY }
  else
    none

--------------------------------------------------------------------------------
-- Box vs Box (AABB - axis aligned only)
--------------------------------------------------------------------------------

/-- Test collision between two axis-aligned boxes.

    @param x1 Center X of box 1
    @param y1 Center Y of box 1
    @param w1 Half-width of box 1
    @param h1 Half-height of box 1
    @param x2 Center X of box 2
    @param y2 Center Y of box 2
    @param w2 Half-width of box 2
    @param h2 Half-height of box 2
    @return Some manifold if collision, none otherwise -/
def boxVsBox (x1 y1 w1 h1 x2 y2 w2 h2 : Float) : Option CollisionManifold :=
  let dx := x2 - x1
  let dy := y2 - y1
  let overlapX := w1 + w2 - Float.abs dx
  let overlapY := h1 + h2 - Float.abs dy

  -- No collision if no overlap on either axis
  if overlapX <= 0.0 || overlapY <= 0.0 then
    none
  else
    -- Use minimum overlap axis as collision normal
    let (nx, ny, depth) :=
      if overlapX < overlapY then
        (if dx > 0.0 then 1.0 else -1.0, 0.0, overlapX)
      else
        (0.0, if dy > 0.0 then 1.0 else -1.0, overlapY)

    -- Contact point at center of overlap region
    let contactX := x1 + nx * w1
    let contactY := y1 + ny * h1

    some { normalX := nx
         , normalY := ny
         , depth := depth
         , contactX := contactX
         , contactY := contactY }

--------------------------------------------------------------------------------
-- Separating Axis Test (SAT) for Oriented Boxes
--------------------------------------------------------------------------------

/-- Project a box onto an axis and return min/max values.

    @param cx Box center X
    @param cy Box center Y
    @param hw Half-width
    @param hh Half-height
    @param angle Box rotation angle
    @param axisX Axis X component
    @param axisY Axis Y component
    @return (min projection, max projection) -/
def projectBoxOnAxis (cx cy hw hh angle axisX axisY : Float) : Float × Float :=
  -- Get the four corners of the box
  let cosA := Float.cos angle
  let sinA := Float.sin angle

  -- Local corners: (+hw, +hh), (-hw, +hh), (-hw, -hh), (+hw, -hh)
  -- Transform to world space and project

  let corner1X := cx + hw * cosA - hh * sinA
  let corner1Y := cy + hw * sinA + hh * cosA
  let corner2X := cx - hw * cosA - hh * sinA
  let corner2Y := cy - hw * sinA + hh * cosA
  let corner3X := cx - hw * cosA + hh * sinA
  let corner3Y := cy - hw * sinA - hh * cosA
  let corner4X := cx + hw * cosA + hh * sinA
  let corner4Y := cy + hw * sinA - hh * cosA

  let p1 := corner1X * axisX + corner1Y * axisY
  let p2 := corner2X * axisX + corner2Y * axisY
  let p3 := corner3X * axisX + corner3Y * axisY
  let p4 := corner4X * axisX + corner4Y * axisY

  let minP := Float.min (Float.min p1 p2) (Float.min p3 p4)
  let maxP := Float.max (Float.max p1 p2) (Float.max p3 p4)

  (minP, maxP)

/-- Test collision between two oriented boxes using SAT.

    @param x1 Center X of box 1
    @param y1 Center Y of box 1
    @param w1 Half-width of box 1
    @param h1 Half-height of box 1
    @param a1 Rotation angle of box 1
    @param x2 Center X of box 2
    @param y2 Center Y of box 2
    @param w2 Half-width of box 2
    @param h2 Half-height of box 2
    @param a2 Rotation angle of box 2
    @return Some manifold if collision, none otherwise -/
def obbVsObb (x1 y1 w1 h1 a1 x2 y2 w2 h2 a2 : Float) : Option CollisionManifold :=
  -- Get the four potential separating axes (two per box)
  let axis1X := Float.cos a1
  let axis1Y := Float.sin a1
  let axis2X := -Float.sin a1
  let axis2Y := Float.cos a1
  let axis3X := Float.cos a2
  let axis3Y := Float.sin a2
  let axis4X := -Float.sin a2
  let axis4Y := Float.cos a2

  -- Test each axis
  let axes := [(axis1X, axis1Y), (axis2X, axis2Y), (axis3X, axis3Y), (axis4X, axis4Y)]

  -- Find minimum overlap
  let rec testAxes (axs : List (Float × Float)) (minOverlap : Float) (minAxis : Float × Float) :
      Option (Float × Float × Float) :=
    match axs with
    | [] => some (minOverlap, minAxis.1, minAxis.2)
    | (ax, ay) :: rest =>
        let (min1, max1) := projectBoxOnAxis x1 y1 w1 h1 a1 ax ay
        let (min2, max2) := projectBoxOnAxis x2 y2 w2 h2 a2 ax ay
        let overlap := Float.min (max1 - min2) (max2 - min1)
        if overlap <= 0.0 then
          none  -- Separating axis found, no collision
        else if overlap < minOverlap then
          testAxes rest overlap (ax, ay)
        else
          testAxes rest minOverlap minAxis

  match testAxes axes 1000000.0 (1.0, 0.0) with
  | none => none
  | some (depth, nx, ny) =>
      -- Ensure normal points from box 1 to box 2
      let dx := x2 - x1
      let dy := y2 - y1
      let dot := dx * nx + dy * ny
      let (finalNx, finalNy) := if dot < 0.0 then (-nx, -ny) else (nx, ny)
      let contactX := (x1 + x2) / 2.0
      let contactY := (y1 + y2) / 2.0
      some { normalX := finalNx
           , normalY := finalNy
           , depth := depth
           , contactX := contactX
           , contactY := contactY }

end Lattice.Services.Physics.Collision
