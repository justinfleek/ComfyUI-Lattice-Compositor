-- | Lattice.Services.Physics.Collision - Collision Detection Algorithms
-- |
-- | Pure mathematical functions for collision detection between shapes:
-- | - Circle vs Circle
-- | - Circle vs Box (AABB)
-- | - Box vs Box (AABB)
-- |
-- | Returns collision manifold with:
-- | - Contact normal (from A to B)
-- | - Penetration depth
-- | - Contact point
-- |
-- | All functions are deterministic and side-effect free.
-- |
-- | Source: ui/src/services/physics/PhysicsEngine.ts

module Lattice.Services.Physics.Collision
  ( CollisionManifold
  , circleVsCircle
  , circleVsBox
  , boxVsBox
  , projectBoxOnAxis
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Math (abs, cos, max, min, sin, sqrt)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Collision manifold containing contact information
type CollisionManifold =
  { normalX :: Number    -- ^ Normal X (from A to B)
  , normalY :: Number    -- ^ Normal Y
  , depth :: Number      -- ^ Penetration depth
  , contactX :: Number   -- ^ Contact point X
  , contactY :: Number   -- ^ Contact point Y
  }

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

vecLengthSq :: Number -> Number -> Number
vecLengthSq x y = x * x + y * y

--------------------------------------------------------------------------------
-- Circle vs Circle
--------------------------------------------------------------------------------

-- | Test collision between two circles.
-- |
-- | Returns Nothing if no collision, Just manifold if collision.
circleVsCircle :: Number -> Number -> Number -> Number -> Number -> Number
               -> Maybe CollisionManifold
circleVsCircle x1 y1 r1 x2 y2 r2 =
  let dx = x2 - x1
      dy = y2 - y1
      distSq = vecLengthSq dx dy
      minDist = r1 + r2
  in if distSq >= minDist * minDist
     then Nothing
     else let dist = sqrt distSq
              Tuple nx ny = if dist > 0.0001
                            then Tuple (dx / dist) (dy / dist)
                            else Tuple 1.0 0.0
              depth = minDist - dist
              contactX = x1 + nx * r1
              contactY = y1 + ny * r1
          in Just { normalX: nx, normalY: ny, depth, contactX, contactY }

--------------------------------------------------------------------------------
-- Circle vs Box
--------------------------------------------------------------------------------

-- | Test collision between a circle and an axis-aligned box.
circleVsBox :: Number -> Number -> Number -> Number -> Number -> Number -> Number -> Number
            -> Maybe CollisionManifold
circleVsBox cx cy cr bx by bw bh boxAngle =
  let cosA = cos (-boxAngle)
      sinA = sin (-boxAngle)
      dx = cx - bx
      dy = cy - by
      localX = dx * cosA - dy * sinA
      localY = dx * sinA + dy * cosA

      closestX = max (-bw) (min bw localX)
      closestY = max (-bh) (min bh localY)

      isInside = localX == closestX && localY == closestY

      diffX = localX - closestX
      diffY = localY - closestY
      distSq = vecLengthSq diffX diffY

  in if isInside
     then let dxEdge = bw - abs localX
              dyEdge = bh - abs localY
              { localNX, localNY, dist: distInside } =
                if dxEdge < dyEdge
                then { localNX: if localX > 0.0 then 1.0 else -1.0, localNY: 0.0, dist: dxEdge }
                else { localNX: 0.0, localNY: if localY > 0.0 then 1.0 else -1.0, dist: dyEdge }
              depth = cr + distInside
              worldNX = localNX * cos boxAngle - localNY * sin boxAngle
              worldNY = localNX * sin boxAngle + localNY * cos boxAngle
              contactX = cx - worldNX * cr
              contactY = cy - worldNY * cr
          in Just { normalX: -worldNX, normalY: -worldNY, depth, contactX, contactY }
     else if distSq < cr * cr
          then let dist = sqrt distSq
                   Tuple localNX localNY = if dist > 0.0001
                                           then Tuple (diffX / dist) (diffY / dist)
                                           else Tuple 1.0 0.0
                   depth = cr - dist
                   worldNX = localNX * cos boxAngle - localNY * sin boxAngle
                   worldNY = localNX * sin boxAngle + localNY * cos boxAngle
                   contactX = cx - worldNX * cr
                   contactY = cy - worldNY * cr
               in Just { normalX: worldNX, normalY: worldNY, depth, contactX, contactY }
          else Nothing

--------------------------------------------------------------------------------
-- Box vs Box (AABB)
--------------------------------------------------------------------------------

-- | Test collision between two axis-aligned boxes.
boxVsBox :: Number -> Number -> Number -> Number
         -> Number -> Number -> Number -> Number
         -> Maybe CollisionManifold
boxVsBox x1 y1 w1 h1 x2 y2 w2 h2 =
  let dx = x2 - x1
      dy = y2 - y1
      overlapX = w1 + w2 - abs dx
      overlapY = h1 + h2 - abs dy
  in if overlapX <= 0.0 || overlapY <= 0.0
     then Nothing
     else let { nx, ny, depth } =
                if overlapX < overlapY
                then { nx: if dx > 0.0 then 1.0 else -1.0, ny: 0.0, depth: overlapX }
                else { nx: 0.0, ny: if dy > 0.0 then 1.0 else -1.0, depth: overlapY }
              contactX = x1 + nx * w1
              contactY = y1 + ny * h1
          in Just { normalX: nx, normalY: ny, depth, contactX, contactY }

--------------------------------------------------------------------------------
-- Oriented Box Projection
--------------------------------------------------------------------------------

-- | Project a box onto an axis and return (min, max).
projectBoxOnAxis :: Number -> Number -> Number -> Number -> Number
                 -> Number -> Number -> Tuple Number Number
projectBoxOnAxis cx cy hw hh angle axisX axisY =
  let cosA = cos angle
      sinA = sin angle
      corner1X = cx + hw * cosA - hh * sinA
      corner1Y = cy + hw * sinA + hh * cosA
      corner2X = cx - hw * cosA - hh * sinA
      corner2Y = cy - hw * sinA + hh * cosA
      corner3X = cx - hw * cosA + hh * sinA
      corner3Y = cy - hw * sinA - hh * cosA
      corner4X = cx + hw * cosA + hh * sinA
      corner4Y = cy + hw * sinA - hh * cosA
      p1 = corner1X * axisX + corner1Y * axisY
      p2 = corner2X * axisX + corner2Y * axisY
      p3 = corner3X * axisX + corner3Y * axisY
      p4 = corner4X * axisX + corner4Y * axisY
      minP = min (min p1 p2) (min p3 p4)
      maxP = max (max p1 p2) (max p3 p4)
  in Tuple minP maxP
