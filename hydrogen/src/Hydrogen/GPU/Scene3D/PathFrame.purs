-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // gpu // scene3d // path frame
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathFrame — Frenet frame, normal, and curvature computation.
-- |
-- | ## Design
-- | Computes local coordinate frames along curves for:
-- | - Camera paths (look-at direction)
-- | - Ribbon/tube extrusion
-- | - Motion along paths
-- | - Curvature analysis

module Hydrogen.GPU.Scene3D.PathFrame
  ( -- * Frenet Frame
    FrenetFrame
  , evalPathFrame
  , evalPathNormal
  
  -- * Curvature
  , evalPathCurvature
  
  -- * Second Derivative (for curvature)
  , evalCubicBezierSecondDerivative
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (||)
  , negate
  , bind
  , pure
  , otherwise
  )

import Data.Array (length, index)
import Data.Int (toNumber, floor, rem) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3
  , vec3UnitY
  , vec3UnitZ
  , addVec3
  , subtractVec3
  , scaleVec3
  , normalizeVec3Safe
  , crossVec3
  , dotVec3
  , lengthVec3
  )

import Hydrogen.GPU.Scene3D.Path (Path3D, SplineType(BezierSpline))
import Hydrogen.GPU.Scene3D.PathEval (evalPath, evalPathTangent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // frenet frame
-- ═════════════════════════════════════════════════════════════════════════════

-- | Frenet-Serret frame at a point on the curve.
-- |
-- | The frame provides a local coordinate system that follows the curve:
-- | - tangent: Direction of travel (T)
-- | - normal: Direction of curvature (N), perpendicular to T
-- | - binormal: B = T × N, completes the right-handed frame
-- |
-- | Used for: camera paths, ribbon extrusion, tube geometry, motion along path.
type FrenetFrame =
  { position :: Vec3 Number    -- Point on curve
  , tangent :: Vec3 Number     -- Unit tangent (T)
  , normal :: Vec3 Number      -- Unit normal (N)
  , binormal :: Vec3 Number    -- Unit binormal (B = T × N)
  }

-- | Evaluate the Frenet frame at a point on the path.
-- |
-- | ## Algorithm
-- | Uses the tangent and an "up" reference vector to compute a stable frame.
-- | When tangent is nearly parallel to up, falls back to alternative reference.
-- |
-- | This avoids the "twist" discontinuity problem of true Frenet frames.
evalPathFrame :: Path3D -> Number -> Maybe FrenetFrame
evalPathFrame path t = do
  pos <- evalPath path t
  tan <- evalPathTangent path t
  
  let
    -- Use world Y as default up reference
    up = vec3UnitY
    
    -- If tangent is nearly parallel to Y, use Z instead
    dotUp = dotVec3 tan up
    refVec = if dotUp > 0.99 || dotUp < (-0.99)
             then vec3UnitZ
             else up
    
    -- Compute stable normal via cross products
    -- binormal = normalize(tangent × up)
    -- normal = binormal × tangent
    binormal = normalizeVec3Safe (crossVec3 tan refVec)
    normal = crossVec3 binormal tan
  
  pure { position: pos, tangent: tan, normal: normal, binormal: binormal }

-- | Evaluate the normal vector at a point on the path.
-- |
-- | Returns the normal from the Frenet frame.
evalPathNormal :: Path3D -> Number -> Maybe (Vec3 Number)
evalPathNormal path t = do
  frame <- evalPathFrame path t
  pure frame.normal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // second derivative
-- ═════════════════════════════════════════════════════════════════════════════

-- | Second derivative of cubic Bezier (un-normalized).
-- |
-- | ## Formula
-- | B''(t) = 6(1-t)(p2-2p1+p0) + 6t(p3-2p2+p1)
evalCubicBezierSecondDerivative :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalCubicBezierSecondDerivative p0 p1 p2 p3 t =
  let
    mt = 1.0 - t
    
    -- Second difference vectors
    d0 = addVec3 (subtractVec3 p2 (scaleVec3 2.0 p1)) p0
    d1 = addVec3 (subtractVec3 p3 (scaleVec3 2.0 p2)) p1
  in
    addVec3 (scaleVec3 (6.0 * mt) d0) (scaleVec3 (6.0 * t) d1)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // curvature
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate curvature at a point on the path.
-- |
-- | Curvature κ measures how sharply the curve bends.
-- | κ = |T'| / |r'| = |r' × r''| / |r'|³
-- |
-- | ## Returns
-- | - 0 for straight lines
-- | - Higher values for sharper bends
-- | - Radius of curvature = 1/κ
evalPathCurvature :: Path3D -> Number -> Maybe Number
evalPathCurvature path t =
  case path.splineType of
    BezierSpline -> evalBezierPathCurvature path t
    _ -> Just 0.0  -- Other spline types: implement as needed

-- | Internal: Curvature for Bezier paths.
evalBezierPathCurvature :: Path3D -> Number -> Maybe Number
evalBezierPathCurvature path t = do
  let
    pts = path.points
    n = length pts
  
  if n < 2 then Nothing else do
    let
      numSegments = if path.closed then n else n - 1
      segmentFloat = t * toNumber numSegments
      segIdx = clampInt 0 (numSegments - 1) (floorToInt segmentFloat)
      localT = segmentFloat - toNumber segIdx
    
    i1 <- getPointIndex path.closed n segIdx
    i2 <- getPointIndex path.closed n (segIdx + 1)
    
    pt1 <- index pts i1
    pt2 <- index pts i2
    
    let
      p0 = pt1.position
      p1 = addVec3 p0 pt1.handleOut.offset
      p2 = addVec3 pt2.position pt2.handleIn.offset
      p3 = pt2.position
      
      -- First derivative (velocity, not normalized)
      firstDeriv = evalCubicBezierFirstDerivRaw p0 p1 p2 p3 localT
      -- Second derivative
      secondDeriv = evalCubicBezierSecondDerivative p0 p1 p2 p3 localT
      
      -- κ = |r' × r''| / |r'|³
      crossProd = crossVec3 firstDeriv secondDeriv
      crossLen = lengthVec3 crossProd
      velocityLen = lengthVec3 firstDeriv
      velocityCubed = velocityLen * velocityLen * velocityLen
    
    if velocityCubed < 0.000001
      then pure 0.0
      else pure (crossLen / velocityCubed)

-- | First derivative of Bezier WITHOUT normalization.
evalCubicBezierFirstDerivRaw :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalCubicBezierFirstDerivRaw p0 p1 p2 p3 t =
  let
    t2 = t * t
    mt = 1.0 - t
    mt2 = mt * mt
    
    c0 = 3.0 * mt2
    c1 = 6.0 * mt * t
    c2 = 3.0 * t2
    
    v0 = subtractVec3 p1 p0
    v1 = subtractVec3 p2 p1
    v2 = subtractVec3 p3 p2
  in
    addVec3 (addVec3 (scaleVec3 c0 v0) (scaleVec3 c1 v1)) (scaleVec3 c2 v2)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get point index with wrapping/clamping.
getPointIndex :: Boolean -> Int -> Int -> Maybe Int
getPointIndex closed n i
  | closed = Just (modInt (modInt i n + n) n)
  | i < 0 = Just 0
  | i > n - 1 = Just (n - 1)
  | otherwise = Just i

-- | Convert Int to Number.
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Floor Number to Int.
floorToInt :: Number -> Int
floorToInt = Int.floor

-- | Integer modulo.
modInt :: Int -> Int -> Int
modInt = Int.rem

-- | Clamp Int to range.
clampInt :: Int -> Int -> Int -> Int
clampInt lo hi x
  | x < lo = lo
  | x > hi = hi
  | otherwise = x
