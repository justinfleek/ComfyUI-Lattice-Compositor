{-|
{-# LANGUAGE OverloadedStrings #-}
Module      : Lattice.Services.Physics.Collision
Description : Collision Detection Algorithms
Copyright   : (c) Lattice Team, 2026
License     : MIT

Pure mathematical functions for collision detection between shapes:
- Circle vs Circle
- Circle vs Box (AABB)
- Box vs Box (AABB)
- Oriented Box vs Oriented Box (SAT)

Returns collision manifold with:
- Contact normal (from A to B)
- Penetration depth
- Contact point

All functions are deterministic and side-effect free.

Source: ui/src/services/physics/PhysicsEngine.ts
-}

{-# LANGUAGE StrictData #-}

module Lattice.Services.Physics.Collision
  ( -- * Types
    CollisionManifold(..)
    -- * Collision Tests
  , circleVsCircle
  , circleVsBox
  , boxVsBox
  , obbVsObb
  , projectBoxOnAxis
  ) where

import Data.Maybe (listToMaybe, catMaybes)
import Data.List (minimumBy)
import Data.Ord (comparing)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Collision manifold containing contact information
data CollisionManifold = CollisionManifold
  { cmNormalX :: Double   -- ^ Normal X (from A to B)
  , cmNormalY :: Double   -- ^ Normal Y
  , cmDepth :: Double     -- ^ Penetration depth
  , cmContactX :: Double  -- ^ Contact point X
  , cmContactY :: Double  -- ^ Contact point Y
  } deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

vecLength :: Double -> Double -> Double
vecLength x y = sqrt (x * x + y * y)

vecLengthSq :: Double -> Double -> Double
vecLengthSq x y = x * x + y * y

--------------------------------------------------------------------------------
-- Circle vs Circle
--------------------------------------------------------------------------------

-- | Test collision between two circles.
--
-- Returns Nothing if no collision, Just manifold if collision.
circleVsCircle :: Double  -- ^ Circle 1 center X
               -> Double  -- ^ Circle 1 center Y
               -> Double  -- ^ Circle 1 radius
               -> Double  -- ^ Circle 2 center X
               -> Double  -- ^ Circle 2 center Y
               -> Double  -- ^ Circle 2 radius
               -> Maybe CollisionManifold
circleVsCircle x1 y1 r1 x2 y2 r2 =
  let dx = x2 - x1
      dy = y2 - y1
      distSq = vecLengthSq dx dy
      minDist = r1 + r2
  in if distSq >= minDist * minDist
     then Nothing
     else let dist = sqrt distSq
              (nx, ny) = if dist > 0.0001
                         then (dx / dist, dy / dist)
                         else (1, 0)
              depth = minDist - dist
              contactX = x1 + nx * r1
              contactY = y1 + ny * r1
          in Just $ CollisionManifold nx ny depth contactX contactY

--------------------------------------------------------------------------------
-- Circle vs Box
--------------------------------------------------------------------------------

-- | Test collision between a circle and an axis-aligned box.
circleVsBox :: Double  -- ^ Circle center X
            -> Double  -- ^ Circle center Y
            -> Double  -- ^ Circle radius
            -> Double  -- ^ Box center X
            -> Double  -- ^ Box center Y
            -> Double  -- ^ Box half-width
            -> Double  -- ^ Box half-height
            -> Double  -- ^ Box rotation angle
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
              (localNX, localNY, dist) =
                if dxEdge < dyEdge
                then (if localX > 0 then 1 else -1, 0, dxEdge)
                else (0, if localY > 0 then 1 else -1, dyEdge)
              depth = cr + dist
              worldNX = localNX * cos boxAngle - localNY * sin boxAngle
              worldNY = localNX * sin boxAngle + localNY * cos boxAngle
              contactX = cx - worldNX * cr
              contactY = cy - worldNY * cr
          in Just $ CollisionManifold (-worldNX) (-worldNY) depth contactX contactY
     else if distSq < cr * cr
          then let dist = sqrt distSq
                   (localNX, localNY) = if dist > 0.0001
                                        then (diffX / dist, diffY / dist)
                                        else (1, 0)
                   depth = cr - dist
                   worldNX = localNX * cos boxAngle - localNY * sin boxAngle
                   worldNY = localNX * sin boxAngle + localNY * cos boxAngle
                   contactX = cx - worldNX * cr
                   contactY = cy - worldNY * cr
               in Just $ CollisionManifold worldNX worldNY depth contactX contactY
          else Nothing

--------------------------------------------------------------------------------
-- Box vs Box (AABB)
--------------------------------------------------------------------------------

-- | Test collision between two axis-aligned boxes.
boxVsBox :: Double  -- ^ Box 1 center X
         -> Double  -- ^ Box 1 center Y
         -> Double  -- ^ Box 1 half-width
         -> Double  -- ^ Box 1 half-height
         -> Double  -- ^ Box 2 center X
         -> Double  -- ^ Box 2 center Y
         -> Double  -- ^ Box 2 half-width
         -> Double  -- ^ Box 2 half-height
         -> Maybe CollisionManifold
boxVsBox x1 y1 w1 h1 x2 y2 w2 h2 =
  let dx = x2 - x1
      dy = y2 - y1
      overlapX = w1 + w2 - abs dx
      overlapY = h1 + h2 - abs dy
  in if overlapX <= 0 || overlapY <= 0
     then Nothing
     else let (nx, ny, depth) =
                if overlapX < overlapY
                then (if dx > 0 then 1 else -1, 0, overlapX)
                else (0, if dy > 0 then 1 else -1, overlapY)
              contactX = x1 + nx * w1
              contactY = y1 + ny * h1
          in Just $ CollisionManifold nx ny depth contactX contactY

--------------------------------------------------------------------------------
-- Oriented Box vs Oriented Box (SAT)
--------------------------------------------------------------------------------

-- | Project a box onto an axis and return (min, max).
projectBoxOnAxis :: Double  -- ^ Center X
                 -> Double  -- ^ Center Y
                 -> Double  -- ^ Half-width
                 -> Double  -- ^ Half-height
                 -> Double  -- ^ Rotation angle
                 -> Double  -- ^ Axis X
                 -> Double  -- ^ Axis Y
                 -> (Double, Double)
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
  in (minimum [p1, p2, p3, p4], maximum [p1, p2, p3, p4])

-- | Test collision between two oriented boxes using SAT.
obbVsObb :: Double -> Double -> Double -> Double -> Double  -- ^ Box 1
         -> Double -> Double -> Double -> Double -> Double  -- ^ Box 2
         -> Maybe CollisionManifold
obbVsObb x1 y1 w1 h1 a1 x2 y2 w2 h2 a2 =
  let axes = [ (cos a1, sin a1)
             , (-sin a1, cos a1)
             , (cos a2, sin a2)
             , (-sin a2, cos a2)
             ]

      testAxis (ax, ay) =
        let (min1, max1) = projectBoxOnAxis x1 y1 w1 h1 a1 ax ay
            (min2, max2) = projectBoxOnAxis x2 y2 w2 h2 a2 ax ay
            overlap = min (max1 - min2) (max2 - min1)
        in if overlap <= 0
           then Nothing
           else Just (overlap, ax, ay)

      results = catMaybes $ map testAxis axes

  in if length results < 4
     then Nothing  -- Separating axis found
     else let (depth, nx, ny) = minimumBy (comparing (\(d,_,_) -> d)) results
              dx = x2 - x1
              dy = y2 - y1
              dot = dx * nx + dy * ny
              (finalNx, finalNy) = if dot < 0 then (-nx, -ny) else (nx, ny)
              contactX = (x1 + x2) / 2
              contactY = (y1 + y2) / 2
          in Just $ CollisionManifold finalNx finalNy depth contactX contactY
