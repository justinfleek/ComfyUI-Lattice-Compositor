{-|
Module      : Lattice.Services.Particles.Shapes
Description : Particle Emitter Shape Distributions
Copyright   : (c) Lattice Team, 2026
License     : MIT

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
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.Shapes
  ( -- * Types
    SpawnResult(..)
  , BoxEdge(..)
    -- * Point Emission
  , emitPoint
    -- * Line Emission
  , emitLine
    -- * Circle Emission
  , emitCircleFilled
  , emitCircleEdge
    -- * Ring Emission
  , emitRing
    -- * Box Emission
  , emitBoxFilled
  , emitBoxEdge
  , boxEdgeFromT
    -- * Sphere Emission
  , emitSphereSurface
  , emitSphereVolume
    -- * Cone Emission
  , emitCone
    -- * Collision Response
  , elasticCollision
  , separateParticles
  ) where

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Result of spawn position calculation
data SpawnResult = SpawnResult
  { srX :: Double           -- ^ X position (normalized 0-1)
  , srY :: Double           -- ^ Y position (normalized 0-1)
  , srDirection :: Maybe Double  -- ^ Optional direction override (degrees)
  } deriving (Show, Eq)

-- | Box perimeter edge for edge emission
data BoxEdge = TopEdge | RightEdge | BottomEdge | LeftEdge
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Point Emission
--------------------------------------------------------------------------------

-- | Emit from a single point.
emitPoint :: Double -> Double -> SpawnResult
emitPoint emitterX emitterY =
  SpawnResult emitterX emitterY Nothing

--------------------------------------------------------------------------------
-- Line Emission
--------------------------------------------------------------------------------

-- | Emit from a line perpendicular to emitter direction.
emitLine :: Double -> Double -> Double -> Double -> Double -> SpawnResult
emitLine emitterX emitterY direction halfWidth t =
  let dirRad = direction * pi / 180
      -- Perpendicular to direction
      perpX = -sin dirRad
      perpY = cos dirRad
      offset = (t - 0.5) * halfWidth * 2
  in SpawnResult (emitterX + perpX * offset) (emitterY + perpY * offset) Nothing

--------------------------------------------------------------------------------
-- Circle Emission
--------------------------------------------------------------------------------

-- | Emit from a filled circle with uniform area distribution.
--
-- Uses sqrt(random) to ensure uniform distribution over area.
emitCircleFilled :: Double -> Double -> Double -> Double -> Double -> SpawnResult
emitCircleFilled emitterX emitterY radius randomAngle randomRadius =
  let angle = randomAngle * pi * 2
      r = radius * sqrt randomRadius  -- sqrt for uniform area
  in SpawnResult (emitterX + cos angle * r) (emitterY + sin angle * r) Nothing

-- | Emit from circle edge only.
emitCircleEdge :: Double -> Double -> Double -> Double -> SpawnResult
emitCircleEdge emitterX emitterY radius randomAngle =
  let angle = randomAngle * pi * 2
  in SpawnResult (emitterX + cos angle * radius) (emitterY + sin angle * radius) Nothing

--------------------------------------------------------------------------------
-- Ring Emission
--------------------------------------------------------------------------------

-- | Emit from a ring (donut) with uniform area distribution.
emitRing :: Double -> Double -> Double -> Double -> Double -> Double -> SpawnResult
emitRing emitterX emitterY innerRadius outerRadius randomAngle randomRadius =
  let angle = randomAngle * pi * 2
      innerSq = innerRadius * innerRadius
      outerSq = outerRadius * outerRadius
      r = sqrt (randomRadius * (outerSq - innerSq) + innerSq)
  in SpawnResult (emitterX + cos angle * r) (emitterY + sin angle * r) Nothing

--------------------------------------------------------------------------------
-- Box Emission
--------------------------------------------------------------------------------

-- | Emit from a filled box.
emitBoxFilled :: Double -> Double -> Double -> Double -> Double -> Double -> SpawnResult
emitBoxFilled emitterX emitterY width height randomX randomY =
  SpawnResult (emitterX + (randomX - 0.5) * width)
              (emitterY + (randomY - 0.5) * height)
              Nothing

-- | Determine which edge of a box a perimeter position falls on.
boxEdgeFromT :: Double -> Double -> Double -> (BoxEdge, Double)
boxEdgeFromT t width height =
  let perimeter = 2 * (width + height)
      pos = t * perimeter
  in if pos < width then (TopEdge, pos)
     else if pos < width + height then (RightEdge, pos - width)
     else if pos < 2 * width + height then (BottomEdge, pos - width - height)
     else (LeftEdge, pos - 2 * width - height)

-- | Emit from box perimeter (edges only).
emitBoxEdge :: Double -> Double -> Double -> Double -> Double -> SpawnResult
emitBoxEdge emitterX emitterY width height randomT =
  let halfW = width / 2
      halfH = height / 2
      (edge, edgePos) = boxEdgeFromT randomT width height
  in case edge of
       TopEdge    -> SpawnResult (emitterX - halfW + edgePos) (emitterY - halfH) Nothing
       RightEdge  -> SpawnResult (emitterX + halfW) (emitterY - halfH + edgePos) Nothing
       BottomEdge -> SpawnResult (emitterX + halfW - edgePos) (emitterY + halfH) Nothing
       LeftEdge   -> SpawnResult (emitterX - halfW) (emitterY + halfH - edgePos) Nothing

--------------------------------------------------------------------------------
-- Sphere Emission (3D projected to 2D)
--------------------------------------------------------------------------------

-- | Emit from sphere surface.
--
-- Uses spherical coordinates with uniform distribution.
emitSphereSurface :: Double -> Double -> Double -> Double -> Double -> SpawnResult
emitSphereSurface emitterX emitterY radius randomTheta randomPhi =
  let theta = randomTheta * pi * 2
      phi = acos (2 * randomPhi - 1)  -- Uniform on sphere
  in SpawnResult (emitterX + sin phi * cos theta * radius)
                 (emitterY + sin phi * sin theta * radius)
                 Nothing

-- | Emit from sphere volume using rejection sampling.
--
-- Takes pre-sampled point that passed rejection test.
emitSphereVolume :: Double -> Double -> Double -> Double -> Double -> SpawnResult
emitSphereVolume emitterX emitterY radius unitX unitY =
  SpawnResult (emitterX + unitX * radius) (emitterY + unitY * radius) Nothing

--------------------------------------------------------------------------------
-- Cone Emission
--------------------------------------------------------------------------------

-- | Emit from a cone volume.
--
-- Cone opens along the emitter direction from the emitter position.
emitCone :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> SpawnResult
emitCone emitterX emitterY direction coneAngle coneRadius coneLength randomT randomTheta =
  let coneAngleRad = coneAngle * pi / 180
      theta = randomTheta * pi * 2
      radiusAtT = randomT * coneRadius * tan coneAngleRad
      -- Position in cone's local space
      localX = cos theta * radiusAtT
      localY = randomT * coneLength
      -- Rotate to emitter direction
      dirRad = direction * pi / 180
      cosDir = cos dirRad
      sinDir = sin dirRad
  in SpawnResult (emitterX + localX * cosDir - localY * sinDir)
                 (emitterY + localX * sinDir + localY * cosDir)
                 Nothing

--------------------------------------------------------------------------------
-- Collision Response
--------------------------------------------------------------------------------

-- | Elastic collision response between two particles.
--
-- Returns new velocities for both particles.
elasticCollision :: Double -> Double -> Double -> Double
                 -> Double -> Double -> Double -> Double
                 -> Double
                 -> ((Double, Double), (Double, Double))
elasticCollision p1x p1y v1x v1y p2x p2y v2x v2y damping =
  let dx = p2x - p1x
      dy = p2y - p1y
      dist = sqrt (dx * dx + dy * dy)
  in if dist < 0.0001 then
       ((v1x, v1y), (v2x, v2y))  -- Same position
     else
       let nx = dx / dist
           ny = dy / dist
           dvx = v1x - v2x
           dvy = v1y - v2y
           dvDotN = dvx * nx + dvy * ny
       in if dvDotN <= 0 then
            ((v1x, v1y), (v2x, v2y))  -- Moving apart
          else
            let impulseX = dvDotN * nx * damping
                impulseY = dvDotN * ny * damping
            in ((v1x - impulseX, v1y - impulseY),
                (v2x + impulseX, v2y + impulseY))

-- | Calculate particle separation to prevent overlap.
separateParticles :: Double -> Double -> Double -> Double -> Double
                  -> ((Double, Double), (Double, Double))
separateParticles p1x p1y p2x p2y minDist =
  let dx = p2x - p1x
      dy = p2y - p1y
      dist = sqrt (dx * dx + dy * dy)
  in if dist >= minDist || dist < 0.0001 then
       ((p1x, p1y), (p2x, p2y))
     else
       let overlap = minDist - dist
           nx = dx / dist
           ny = dy / dist
           halfOverlap = overlap * 0.5
       in ((p1x - nx * halfOverlap, p1y - ny * halfOverlap),
           (p2x + nx * halfOverlap, p2y + ny * halfOverlap))
