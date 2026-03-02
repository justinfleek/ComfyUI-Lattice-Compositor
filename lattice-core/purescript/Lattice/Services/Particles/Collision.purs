-- | Lattice.Services.Particles.Collision - Spatial Hashing and Collision Detection
-- |
-- | Pure mathematical functions for particle collision:
-- | - Spatial hash grid construction
-- | - Broad-phase neighbor queries
-- | - Collision detection and response
-- | - Environment collision (floor, ceiling, walls)
-- |
-- | All functions are total and deterministic.
-- |
-- | Source: ui/src/services/particleSystem.ts (handleParticleCollisions)

module Lattice.Services.Particles.Collision
  ( CollisionConfig(..)
  , CollisionResponse(..)
  , CollisionResult(..)
  , cellKey
  , collisionDistance
  , checkPairCollision
  , bounceResponse
  , separateOverlap
  , checkFloorCollision
  , checkCeilingCollision
  , checkWallCollision
  , applyEnvironmentCollision
  ) where

import Prelude

import Data.Int (floor)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (max, min, sqrt)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Collision response type
data CollisionResponse
  = ResponseBounce
  | ResponseAbsorb
  | ResponseExplode

derive instance eqCollisionResponse :: Eq CollisionResponse

instance showCollisionResponse :: Show CollisionResponse where
  show ResponseBounce = "ResponseBounce"
  show ResponseAbsorb = "ResponseAbsorb"
  show ResponseExplode = "ResponseExplode"

-- | Collision configuration
type CollisionConfig =
  { enabled :: Boolean
  , particleCollision :: Boolean
  , particleRadius :: Number
  , damping :: Number
  , response :: CollisionResponse
  , floorEnabled :: Boolean
  , floorY :: Number
  , ceilingEnabled :: Boolean
  , ceilingY :: Number
  , wallsEnabled :: Boolean
  , bounciness :: Number
  , friction :: Number
  , cellSize :: Number
  }

-- | Result of a collision check
type CollisionResult =
  { collided :: Boolean
  , newVx1 :: Number
  , newVy1 :: Number
  , newVx2 :: Number
  , newVy2 :: Number
  , newX1 :: Number
  , newY1 :: Number
  , newX2 :: Number
  , newY2 :: Number
  , p1Killed :: Boolean
  , p2Killed :: Boolean
  }

-- ────────────────────────────────────────────────────────────────────────────
-- Spatial Hashing
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate cell key from position.
cellKey :: Number -> Number -> Number -> Tuple Int Int
cellKey x y cellSize =
  let
    safeCellSize = max 0.001 cellSize
    cx = floor (x / safeCellSize)
    cy = floor (y / safeCellSize)
  in
    Tuple cx cy

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Detection
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate collision distance between two particles.
collisionDistance :: Number -> Number -> Number -> Number
collisionDistance size1 size2 radiusMult =
  (size1 / 1000.0 * radiusMult) + (size2 / 1000.0 * radiusMult)

-- | Check if two particles are colliding.
-- |
-- | Returns (distance, nx, ny) if colliding.
checkPairCollision
  :: Number -> Number -> Number  -- p1: x, y, size
  -> Number -> Number -> Number  -- p2: x, y, size
  -> Number                      -- radius multiplier
  -> Maybe { dist :: Number, nx :: Number, ny :: Number }
checkPairCollision x1 y1 s1 x2 y2 s2 radiusMult =
  let
    dx = x2 - x1
    dy = y2 - y1
    distSq = dx * dx + dy * dy
    minDist = collisionDistance s1 s2 radiusMult
  in
    if distSq < minDist * minDist && distSq > 0.000001
    then
      let
        dist = sqrt distSq
        nx = dx / dist
        ny = dy / dist
      in
        Just { dist, nx, ny }
    else
      Nothing

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Response
-- ────────────────────────────────────────────────────────────────────────────

-- | Elastic bounce collision response.
bounceResponse
  :: Number -> Number -> Number -> Number  -- p1: vx, vy, x, y
  -> Number -> Number -> Number -> Number  -- p2: vx, vy, x, y
  -> Number -> Number                      -- normal: nx, ny
  -> Number -> Number                      -- minDist, damping
  -> CollisionResult
bounceResponse vx1 vy1 x1 y1 vx2 vy2 x2 y2 nx ny minDist damping =
  let
    dvx = vx1 - vx2
    dvy = vy1 - vy2
    dvDotN = dvx * nx + dvy * ny
  in
    if dvDotN > 0.0  -- Moving towards each other
    then
      let
        impulseX = dvDotN * nx * damping
        impulseY = dvDotN * ny * damping
        dist = sqrt ((x2 - x1) * (x2 - x1) + (y2 - y1) * (y2 - y1))
        overlap = if dist > 0.0001 then minDist - dist else 0.0
      in
        { collided: true
        , newVx1: vx1 - impulseX
        , newVy1: vy1 - impulseY
        , newVx2: vx2 + impulseX
        , newVy2: vy2 + impulseY
        , newX1: x1 - nx * overlap * 0.5
        , newY1: y1 - ny * overlap * 0.5
        , newX2: x2 + nx * overlap * 0.5
        , newY2: y2 + ny * overlap * 0.5
        , p1Killed: false
        , p2Killed: false
        }
    else
      noCollision vx1 vy1 x1 y1 vx2 vy2 x2 y2

-- | No collision result helper.
noCollision :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number -> CollisionResult
noCollision vx1 vy1 x1 y1 vx2 vy2 x2 y2 =
  { collided: false
  , newVx1: vx1
  , newVy1: vy1
  , newVx2: vx2
  , newVy2: vy2
  , newX1: x1
  , newY1: y1
  , newX2: x2
  , newY2: y2
  , p1Killed: false
  , p2Killed: false
  }

-- | Calculate separation to resolve overlap.
separateOverlap
  :: Number -> Number -> Number -> Number  -- x1, y1, x2, y2
  -> Number                                -- minDist
  -> Tuple (Tuple Number Number) (Tuple Number Number)  -- new positions
separateOverlap x1 y1 x2 y2 minDist =
  let
    dx = x2 - x1
    dy = y2 - y1
    dist = sqrt (dx * dx + dy * dy)
  in
    if dist < minDist && dist > 0.0001
    then
      let
        overlap = minDist - dist
        nx = dx / dist
        ny = dy / dist
      in
        Tuple
          (Tuple (x1 - nx * overlap * 0.5) (y1 - ny * overlap * 0.5))
          (Tuple (x2 + nx * overlap * 0.5) (y2 + ny * overlap * 0.5))
    else
      Tuple (Tuple x1 y1) (Tuple x2 y2)

-- ────────────────────────────────────────────────────────────────────────────
-- Environment Collision
-- ────────────────────────────────────────────────────────────────────────────

-- | Check and respond to floor collision.
checkFloorCollision
  :: Number -> Number -> Number -> Number  -- x, y, vx, vy
  -> Number -> Number -> Number            -- floorY, bounciness, friction
  -> Tuple (Tuple Number Number) (Tuple Number Number)  -- new (x, y), (vx, vy)
checkFloorCollision x y vx vy floorY bounciness friction =
  if y > floorY
  then Tuple (Tuple x floorY) (Tuple (vx * (1.0 - friction)) (-vy * bounciness))
  else Tuple (Tuple x y) (Tuple vx vy)

-- | Check and respond to ceiling collision.
checkCeilingCollision
  :: Number -> Number -> Number -> Number
  -> Number -> Number -> Number
  -> Tuple (Tuple Number Number) (Tuple Number Number)
checkCeilingCollision x y vx vy ceilingY bounciness friction =
  if y < ceilingY
  then Tuple (Tuple x ceilingY) (Tuple (vx * (1.0 - friction)) (-vy * bounciness))
  else Tuple (Tuple x y) (Tuple vx vy)

-- | Check and respond to wall collisions.
checkWallCollision
  :: Number -> Number -> Number -> Number
  -> Number -> Number
  -> Tuple (Tuple Number Number) (Tuple Number Number)
checkWallCollision x y vx vy bounciness friction
  | x < 0.0 = Tuple (Tuple 0.0 y) (Tuple (-vx * bounciness) (vy * (1.0 - friction)))
  | x > 1.0 = Tuple (Tuple 1.0 y) (Tuple (-vx * bounciness) (vy * (1.0 - friction)))
  | otherwise = Tuple (Tuple x y) (Tuple vx vy)

-- | Apply all environment collisions based on config.
applyEnvironmentCollision
  :: CollisionConfig
  -> Number -> Number -> Number -> Number
  -> Tuple (Tuple Number Number) (Tuple Number Number)
applyEnvironmentCollision cfg x y vx vy =
  let
    Tuple (Tuple x1 y1) (Tuple vx1 vy1) =
      if cfg.floorEnabled
      then checkFloorCollision x y vx vy cfg.floorY cfg.bounciness cfg.friction
      else Tuple (Tuple x y) (Tuple vx vy)

    Tuple (Tuple x2 y2) (Tuple vx2 vy2) =
      if cfg.ceilingEnabled
      then checkCeilingCollision x1 y1 vx1 vy1 cfg.ceilingY cfg.bounciness cfg.friction
      else Tuple (Tuple x1 y1) (Tuple vx1 vy1)

    Tuple (Tuple x3 y3) (Tuple vx3 vy3) =
      if cfg.wallsEnabled
      then checkWallCollision x2 y2 vx2 vy2 cfg.bounciness cfg.friction
      else Tuple (Tuple x2 y2) (Tuple vx2 vy2)
  in
    Tuple (Tuple x3 y3) (Tuple vx3 vy3)
