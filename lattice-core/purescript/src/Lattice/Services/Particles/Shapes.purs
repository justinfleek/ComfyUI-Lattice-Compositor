-- | Lattice.Services.Particles.Shapes - Particle Emitter Shape Distributions
-- |
-- | Pure mathematical functions for particle emission positions based on
-- | emitter shape. Provides uniform distributions within various geometric
-- | shapes for particle spawning.
-- |
-- | Supported shapes:
-- | - Point: Single point emission
-- | - Line: Linear emission perpendicular to direction
-- | - Circle: Filled or edge-only circular emission
-- | - Ring: Donut-shaped emission (inner/outer radius)
-- | - Box: Rectangular emission (filled or perimeter)
-- | - Sphere: 3D sphere projected to 2D (surface or volume)
-- | - Cone: Conical emission along direction
-- |
-- | All shapes use deterministic random values (0-1) as input to ensure
-- | reproducible particle spawning with seeded RNG.
-- |
-- | Source: ui/src/services/particleSystem.ts

module Lattice.Services.Particles.Shapes
  ( SpawnResult
  , BoxEdge(..)
  , emitPoint
  , emitLine
  , emitCircleFilled
  , emitCircleEdge
  , emitRing
  , emitBoxFilled
  , emitBoxEdge
  , boxEdgeFromT
  , emitSphereSurface
  , emitSphereVolume
  , emitCone
  , elasticCollision
  , separateParticles
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (acos, cos, pi, sin, sqrt, tan)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Result of spawn position calculation
type SpawnResult =
  { x :: Number           -- ^ X position (normalized 0-1)
  , y :: Number           -- ^ Y position (normalized 0-1)
  , direction :: Maybe Number  -- ^ Optional direction override (degrees)
  }

-- | Box perimeter edge for edge emission
data BoxEdge = TopEdge | RightEdge | BottomEdge | LeftEdge

derive instance eqBoxEdge :: Eq BoxEdge

-- ────────────────────────────────────────────────────────────────────────────
-- Point Emission
-- ────────────────────────────────────────────────────────────────────────────

-- | Emit from a single point.
emitPoint :: Number -> Number -> SpawnResult
emitPoint emitterX emitterY =
  { x: emitterX, y: emitterY, direction: Nothing }

-- ────────────────────────────────────────────────────────────────────────────
-- Line Emission
-- ────────────────────────────────────────────────────────────────────────────

-- | Emit from a line perpendicular to emitter direction.
emitLine :: Number -> Number -> Number -> Number -> Number -> SpawnResult
emitLine emitterX emitterY direction halfWidth t =
  let dirRad = direction * pi / 180.0
      -- Perpendicular to direction
      perpX = -sin dirRad
      perpY = cos dirRad
      offset = (t - 0.5) * halfWidth * 2.0
  in { x: emitterX + perpX * offset, y: emitterY + perpY * offset, direction: Nothing }

-- ────────────────────────────────────────────────────────────────────────────
-- Circle Emission
-- ────────────────────────────────────────────────────────────────────────────

-- | Emit from a filled circle with uniform area distribution.
-- |
-- | Uses sqrt(random) to ensure uniform distribution over area.
emitCircleFilled :: Number -> Number -> Number -> Number -> Number -> SpawnResult
emitCircleFilled emitterX emitterY radius randomAngle randomRadius =
  let angle = randomAngle * pi * 2.0
      r = radius * sqrt randomRadius  -- sqrt for uniform area
  in { x: emitterX + cos angle * r, y: emitterY + sin angle * r, direction: Nothing }

-- | Emit from circle edge only.
emitCircleEdge :: Number -> Number -> Number -> Number -> SpawnResult
emitCircleEdge emitterX emitterY radius randomAngle =
  let angle = randomAngle * pi * 2.0
  in { x: emitterX + cos angle * radius, y: emitterY + sin angle * radius, direction: Nothing }

-- ────────────────────────────────────────────────────────────────────────────
-- Ring Emission
-- ────────────────────────────────────────────────────────────────────────────

-- | Emit from a ring (donut) with uniform area distribution.
emitRing :: Number -> Number -> Number -> Number -> Number -> Number -> SpawnResult
emitRing emitterX emitterY innerRadius outerRadius randomAngle randomRadius =
  let angle = randomAngle * pi * 2.0
      innerSq = innerRadius * innerRadius
      outerSq = outerRadius * outerRadius
      r = sqrt (randomRadius * (outerSq - innerSq) + innerSq)
  in { x: emitterX + cos angle * r, y: emitterY + sin angle * r, direction: Nothing }

-- ────────────────────────────────────────────────────────────────────────────
-- Box Emission
-- ────────────────────────────────────────────────────────────────────────────

-- | Emit from a filled box.
emitBoxFilled :: Number -> Number -> Number -> Number -> Number -> Number -> SpawnResult
emitBoxFilled emitterX emitterY width height randomX randomY =
  { x: emitterX + (randomX - 0.5) * width
  , y: emitterY + (randomY - 0.5) * height
  , direction: Nothing }

-- | Determine which edge of a box a perimeter position falls on.
boxEdgeFromT :: Number -> Number -> Number -> Tuple BoxEdge Number
boxEdgeFromT t width height =
  let perimeter = 2.0 * (width + height)
      pos = t * perimeter
  in if pos < width then Tuple TopEdge pos
     else if pos < width + height then Tuple RightEdge (pos - width)
     else if pos < 2.0 * width + height then Tuple BottomEdge (pos - width - height)
     else Tuple LeftEdge (pos - 2.0 * width - height)

-- | Emit from box perimeter (edges only).
emitBoxEdge :: Number -> Number -> Number -> Number -> Number -> SpawnResult
emitBoxEdge emitterX emitterY width height randomT =
  let halfW = width / 2.0
      halfH = height / 2.0
      Tuple edge edgePos = boxEdgeFromT randomT width height
  in case edge of
       TopEdge    -> { x: emitterX - halfW + edgePos, y: emitterY - halfH, direction: Nothing }
       RightEdge  -> { x: emitterX + halfW, y: emitterY - halfH + edgePos, direction: Nothing }
       BottomEdge -> { x: emitterX + halfW - edgePos, y: emitterY + halfH, direction: Nothing }
       LeftEdge   -> { x: emitterX - halfW, y: emitterY + halfH - edgePos, direction: Nothing }

-- ────────────────────────────────────────────────────────────────────────────
-- Sphere Emission (3D projected to 2D)
-- ────────────────────────────────────────────────────────────────────────────

-- | Emit from sphere surface.
-- |
-- | Uses spherical coordinates with uniform distribution.
emitSphereSurface :: Number -> Number -> Number -> Number -> Number -> SpawnResult
emitSphereSurface emitterX emitterY radius randomTheta randomPhi =
  let theta = randomTheta * pi * 2.0
      phi = acos (2.0 * randomPhi - 1.0)  -- Uniform on sphere
  in { x: emitterX + sin phi * cos theta * radius
     , y: emitterY + sin phi * sin theta * radius
     , direction: Nothing }

-- | Emit from sphere volume using rejection sampling.
-- |
-- | Takes pre-sampled point that passed rejection test.
emitSphereVolume :: Number -> Number -> Number -> Number -> Number -> SpawnResult
emitSphereVolume emitterX emitterY radius unitX unitY =
  { x: emitterX + unitX * radius, y: emitterY + unitY * radius, direction: Nothing }

-- ────────────────────────────────────────────────────────────────────────────
-- Cone Emission
-- ────────────────────────────────────────────────────────────────────────────

-- | Emit from a cone volume.
-- |
-- | Cone opens along the emitter direction from the emitter position.
emitCone :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> SpawnResult
emitCone emitterX emitterY direction coneAngle coneRadius coneLength randomT randomTheta =
  let coneAngleRad = coneAngle * pi / 180.0
      theta = randomTheta * pi * 2.0
      radiusAtT = randomT * coneRadius * tan coneAngleRad
      -- Position in cone's local space
      localX = cos theta * radiusAtT
      localY = randomT * coneLength
      -- Rotate to emitter direction
      dirRad = direction * pi / 180.0
      cosDir = cos dirRad
      sinDir = sin dirRad
  in { x: emitterX + localX * cosDir - localY * sinDir
     , y: emitterY + localX * sinDir + localY * cosDir
     , direction: Nothing }

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Response
-- ────────────────────────────────────────────────────────────────────────────

-- | Elastic collision response between two particles.
-- |
-- | Returns new velocities for both particles.
elasticCollision :: Number -> Number -> Number -> Number
                 -> Number -> Number -> Number -> Number
                 -> Number
                 -> Tuple (Tuple Number Number) (Tuple Number Number)
elasticCollision p1x p1y v1x v1y p2x p2y v2x v2y damping =
  let dx = p2x - p1x
      dy = p2y - p1y
      dist = sqrt (dx * dx + dy * dy)
  in if dist < 0.0001 then
       Tuple (Tuple v1x v1y) (Tuple v2x v2y)  -- Same position
     else
       let nx = dx / dist
           ny = dy / dist
           dvx = v1x - v2x
           dvy = v1y - v2y
           dvDotN = dvx * nx + dvy * ny
       in if dvDotN <= 0.0 then
            Tuple (Tuple v1x v1y) (Tuple v2x v2y)  -- Moving apart
          else
            let impulseX = dvDotN * nx * damping
                impulseY = dvDotN * ny * damping
            in Tuple (Tuple (v1x - impulseX) (v1y - impulseY))
                     (Tuple (v2x + impulseX) (v2y + impulseY))

-- | Calculate particle separation to prevent overlap.
separateParticles :: Number -> Number -> Number -> Number -> Number
                  -> Tuple (Tuple Number Number) (Tuple Number Number)
separateParticles p1x p1y p2x p2y minDist =
  let dx = p2x - p1x
      dy = p2y - p1y
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= minDist || dist < 0.0001 then
       Tuple (Tuple p1x p1y) (Tuple p2x p2y)
     else
       let overlap = minDist - dist
           nx = dx / dist
           ny = dy / dist
           halfOverlap = overlap * 0.5
       in Tuple (Tuple (p1x - nx * halfOverlap) (p1y - ny * halfOverlap))
                (Tuple (p2x + nx * halfOverlap) (p2y + ny * halfOverlap))
