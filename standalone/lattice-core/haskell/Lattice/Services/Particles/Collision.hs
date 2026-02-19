{-|
Module      : Lattice.Services.Particles.Collision
Description : Spatial Hashing and Collision Detection
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for particle collision:
- Spatial hash grid construction
- Broad-phase neighbor queries
- Narrow-phase collision detection
- Collision response (bounce, absorb, explode)
- Environment collision (floor, ceiling, walls)

All functions are total and deterministic.

Source: ui/src/services/particleSystem.ts (handleParticleCollisions, handleEnvironmentCollisions)
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Particles.Collision
  ( -- * Types
    SpatialCell(..)
  , CollisionConfig(..)
  , CollisionResponse(..)
  , CollisionResult(..)
  , EnvironmentBounds(..)
    -- * Spatial Hashing
  , cellKey
  , buildSpatialGrid
  , getNeighborCells
  , cellNeighborKeys
    -- * Collision Detection
  , checkPairCollision
  , detectCollisions
  , collisionDistance
    -- * Collision Response
  , bounceResponse
  , absorbResponse
  , separateOverlap
    -- * Environment Collision
  , checkFloorCollision
  , checkCeilingCollision
  , checkWallCollision
  , applyEnvironmentCollision
  ) where

import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)

-- ────────────────────────────────────────────────────────────────────────────
-- Types
-- ────────────────────────────────────────────────────────────────────────────

-- | Spatial hash cell containing particle indices
data SpatialCell = SpatialCell
  { scParticleIds :: [Int]  -- ^ Particle IDs in this cell
  } deriving (Show, Eq)

-- | Collision response type
data CollisionResponse
  = ResponseBounce   -- ^ Elastic bounce with damping
  | ResponseAbsorb   -- ^ Larger particle absorbs smaller
  | ResponseExplode  -- ^ Both particles die (trigger sub-emitters)
  deriving (Show, Eq)

-- | Collision configuration
data CollisionConfig = CollisionConfig
  { ccEnabled :: Bool
  , ccParticleCollision :: Bool
  , ccParticleRadius :: Double     -- ^ Collision radius multiplier
  , ccDamping :: Double            -- ^ Energy loss on bounce (0-1)
  , ccResponse :: CollisionResponse
  , ccFloorEnabled :: Bool
  , ccFloorY :: Double             -- ^ Floor Y position (normalized)
  , ccCeilingEnabled :: Bool
  , ccCeilingY :: Double           -- ^ Ceiling Y position
  , ccWallsEnabled :: Bool
  , ccBounciness :: Double         -- ^ Wall bounce factor
  , ccFriction :: Double           -- ^ Surface friction
  , ccCellSize :: Double           -- ^ Spatial hash cell size
  } deriving (Show, Eq)

-- | Result of a collision check
data CollisionResult = CollisionResult
  { crCollided :: Bool
  , crNewVx1 :: Double   -- ^ New velocity X for particle 1
  , crNewVy1 :: Double   -- ^ New velocity Y for particle 1
  , crNewVx2 :: Double   -- ^ New velocity X for particle 2
  , crNewVy2 :: Double   -- ^ New velocity Y for particle 2
  , crNewX1 :: Double    -- ^ New position X for particle 1
  , crNewY1 :: Double    -- ^ New position Y for particle 1
  , crNewX2 :: Double    -- ^ New position X for particle 2
  , crNewY2 :: Double    -- ^ New position Y for particle 2
  , crP1Killed :: Bool   -- ^ Whether particle 1 should die
  , crP2Killed :: Bool   -- ^ Whether particle 2 should die
  } deriving (Show, Eq)

-- | Environment boundary configuration
data EnvironmentBounds = EnvironmentBounds
  { ebMinX :: Double
  , ebMaxX :: Double
  , ebMinY :: Double
  , ebMaxY :: Double
  } deriving (Show, Eq)

-- ────────────────────────────────────────────────────────────────────────────
-- Spatial Hashing
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate cell key from position.
--
-- @param x X position (normalized 0-1)
-- @param y Y position
-- @param cellSize Cell size (normalized)
-- @return (cellX, cellY) integer coordinates
cellKey :: Double -> Double -> Double -> (Int, Int)
cellKey x y cellSize =
  let cx = floor (x / max 0.001 cellSize)
      cy = floor (y / max 0.001 cellSize)
  in (cx, cy)

-- | Build spatial hash grid from particle positions.
--
-- @param particles List of (id, x, y) tuples
-- @param cellSize Hash cell size
-- @return Map from cell key to particle IDs
buildSpatialGrid :: [(Int, Double, Double)] -> Double -> Map (Int, Int) [Int]
buildSpatialGrid particles cellSize =
  foldr insertParticle Map.empty particles
  where
    insertParticle (pid, x, y) grid =
      let key = cellKey x y cellSize
      in Map.insertWith (++) key [pid] grid

-- | Get all neighbor cell keys (including self).
cellNeighborKeys :: (Int, Int) -> [(Int, Int)]
cellNeighborKeys (cx, cy) =
  [ (cx + dx, cy + dy)
  | dx <- [-1, 0, 1]
  , dy <- [-1, 0, 1]
  ]

-- | Get particle IDs from neighboring cells.
getNeighborCells :: Map (Int, Int) [Int] -> (Int, Int) -> [Int]
getNeighborCells grid key =
  concatMap (lookupCell grid) (cellNeighborKeys key)
  where
    lookupCell g k = Map.findWithDefault [] k g

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Detection
-- ────────────────────────────────────────────────────────────────────────────

-- | Calculate collision distance between two particles.
--
-- @param size1 Particle 1 size
-- @param size2 Particle 2 size
-- @param radiusMult Collision radius multiplier
-- @return Minimum separation distance
collisionDistance :: Double -> Double -> Double -> Double
collisionDistance size1 size2 radiusMult =
  (size1 / 1000 * radiusMult) + (size2 / 1000 * radiusMult)

-- | Check if two particles are colliding.
--
-- @return (isColliding, distance, normalX, normalY)
checkPairCollision
  :: Double -> Double -> Double  -- ^ Particle 1: x, y, size
  -> Double -> Double -> Double  -- ^ Particle 2: x, y, size
  -> Double                      -- ^ Radius multiplier
  -> Maybe (Double, Double, Double)  -- ^ (distance, nx, ny)
checkPairCollision x1 y1 s1 x2 y2 s2 radiusMult =
  let dx = x2 - x1
      dy = y2 - y1
      distSq = dx * dx + dy * dy
      minDist = collisionDistance s1 s2 radiusMult
  in if distSq < minDist * minDist && distSq > 0.000001
     then
       let dist = sqrt distSq
           nx = dx / dist
           ny = dy / dist
       in Just (dist, nx, ny)
     else Nothing

-- | Detect all collisions for a particle against neighbors.
--
-- Returns list of (neighborId, distance, nx, ny).
detectCollisions
  :: Int -> Double -> Double -> Double  -- ^ This particle: id, x, y, size
  -> [(Int, Double, Double, Double)]    -- ^ Neighbors: id, x, y, size
  -> Double                             -- ^ Radius multiplier
  -> [(Int, Double, Double, Double)]    -- ^ Collisions: id, dist, nx, ny
detectCollisions pid x y size neighbors radiusMult =
  [ (nid, dist, nx, ny)
  | (nid, nx', ny', nsize) <- neighbors
  , nid > pid  -- Only check each pair once
  , Just (dist, nx, ny) <- [checkPairCollision x y size nx' ny' nsize radiusMult]
  ]

-- ────────────────────────────────────────────────────────────────────────────
-- Collision Response
-- ────────────────────────────────────────────────────────────────────────────

-- | Elastic bounce collision response.
--
-- Exchanges momentum along collision normal with damping.
bounceResponse
  :: Double -> Double -> Double -> Double  -- ^ P1: vx, vy, x, y
  -> Double -> Double -> Double -> Double  -- ^ P2: vx, vy, x, y
  -> Double -> Double                      -- ^ Normal: nx, ny
  -> Double -> Double                      -- ^ minDist, damping
  -> CollisionResult
bounceResponse vx1 vy1 x1 y1 vx2 vy2 x2 y2 nx ny minDist damping =
  let dvx = vx1 - vx2
      dvy = vy1 - vy2
      dvDotN = dvx * nx + dvy * ny
  in if dvDotN > 0  -- Moving towards each other
     then
       let impulseX = dvDotN * nx * damping
           impulseY = dvDotN * ny * damping
           -- Separate to prevent overlap
           dist = sqrt ((x2-x1)*(x2-x1) + (y2-y1)*(y2-y1))
           overlap = if dist > 0.0001 then minDist - dist else 0
       in CollisionResult
            { crCollided = True
            , crNewVx1 = vx1 - impulseX
            , crNewVy1 = vy1 - impulseY
            , crNewVx2 = vx2 + impulseX
            , crNewVy2 = vy2 + impulseY
            , crNewX1 = x1 - nx * overlap * 0.5
            , crNewY1 = y1 - ny * overlap * 0.5
            , crNewX2 = x2 + nx * overlap * 0.5
            , crNewY2 = y2 + ny * overlap * 0.5
            , crP1Killed = False
            , crP2Killed = False
            }
     else noCollision vx1 vy1 x1 y1 vx2 vy2 x2 y2

-- | Absorb collision response (larger eats smaller).
absorbResponse
  :: Double -> Double  -- ^ Sizes: s1, s2
  -> Double -> Double -> Double -> Double  -- ^ P1: vx, vy, x, y
  -> Double -> Double -> Double -> Double  -- ^ P2: vx, vy, x, y
  -> CollisionResult
absorbResponse s1 s2 vx1 vy1 x1 y1 vx2 vy2 x2 y2 =
  if s1 > s2
  then CollisionResult True vx1 vy1 vx2 vy2 x1 y1 x2 y2 False True
  else CollisionResult True vx1 vy1 vx2 vy2 x1 y1 x2 y2 True False

-- | No collision result helper.
noCollision :: Double -> Double -> Double -> Double -> Double -> Double -> Double -> Double -> CollisionResult
noCollision vx1 vy1 x1 y1 vx2 vy2 x2 y2 =
  CollisionResult False vx1 vy1 vx2 vy2 x1 y1 x2 y2 False False

-- | Calculate separation to resolve overlap.
separateOverlap
  :: Double -> Double -> Double -> Double  -- ^ Positions: x1, y1, x2, y2
  -> Double                                -- ^ Minimum distance
  -> (Double, Double, Double, Double)      -- ^ New positions
separateOverlap x1 y1 x2 y2 minDist =
  let dx = x2 - x1
      dy = y2 - y1
      dist = sqrt (dx * dx + dy * dy)
  in if dist < minDist && dist > 0.0001
     then
       let overlap = minDist - dist
           nx = dx / dist
           ny = dy / dist
       in (x1 - nx * overlap * 0.5, y1 - ny * overlap * 0.5,
           x2 + nx * overlap * 0.5, y2 + ny * overlap * 0.5)
     else (x1, y1, x2, y2)

-- ────────────────────────────────────────────────────────────────────────────
-- Environment Collision
-- ────────────────────────────────────────────────────────────────────────────

-- | Check and respond to floor collision.
checkFloorCollision
  :: Double -> Double -> Double -> Double  -- ^ x, y, vx, vy
  -> Double -> Double -> Double            -- ^ floorY, bounciness, friction
  -> (Double, Double, Double, Double)      -- ^ newX, newY, newVx, newVy
checkFloorCollision x y vx vy floorY bounciness friction =
  if y > floorY
  then (x, floorY, vx * (1 - friction), -vy * bounciness)
  else (x, y, vx, vy)

-- | Check and respond to ceiling collision.
checkCeilingCollision
  :: Double -> Double -> Double -> Double  -- ^ x, y, vx, vy
  -> Double -> Double -> Double            -- ^ ceilingY, bounciness, friction
  -> (Double, Double, Double, Double)
checkCeilingCollision x y vx vy ceilingY bounciness friction =
  if y < ceilingY
  then (x, ceilingY, vx * (1 - friction), -vy * bounciness)
  else (x, y, vx, vy)

-- | Check and respond to wall collisions.
checkWallCollision
  :: Double -> Double -> Double -> Double  -- ^ x, y, vx, vy
  -> Double -> Double                      -- ^ bounciness, friction
  -> (Double, Double, Double, Double)
checkWallCollision x y vx vy bounciness friction
  | x < 0 = (0, y, -vx * bounciness, vy * (1 - friction))
  | x > 1 = (1, y, -vx * bounciness, vy * (1 - friction))
  | otherwise = (x, y, vx, vy)

-- | Apply all environment collisions based on config.
applyEnvironmentCollision
  :: CollisionConfig
  -> Double -> Double -> Double -> Double  -- ^ x, y, vx, vy
  -> (Double, Double, Double, Double)
applyEnvironmentCollision cfg x y vx vy =
  let (x1, y1, vx1, vy1) =
        if ccFloorEnabled cfg
        then checkFloorCollision x y vx vy (ccFloorY cfg) (ccBounciness cfg) (ccFriction cfg)
        else (x, y, vx, vy)
      (x2, y2, vx2, vy2) =
        if ccCeilingEnabled cfg
        then checkCeilingCollision x1 y1 vx1 vy1 (ccCeilingY cfg) (ccBounciness cfg) (ccFriction cfg)
        else (x1, y1, vx1, vy1)
      (x3, y3, vx3, vy3) =
        if ccWallsEnabled cfg
        then checkWallCollision x2 y2 vx2 vy2 (ccBounciness cfg) (ccFriction cfg)
        else (x2, y2, vx2, vy2)
  in (x3, y3, vx3, vy3)
