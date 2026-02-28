-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // gpu // scene3d // path eval
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | PathEval — Core spline evaluation functions.
-- |
-- | ## Design
-- | All functions are pure math. No state, no effects.
-- | Given control points and parameter t, compute position and tangent.
-- |
-- | ## Spline Types
-- | - Linear: straight line segments
-- | - Bezier: cubic Bezier with explicit handles  
-- | - Catmull-Rom: smooth curve through all points
-- | - Hermite: position + velocity at each point
-- |
-- | ## Related Modules
-- | - PathFrame: Frenet frame, normal, curvature
-- | - PathArcLength: Arc-length parameterization, sampling
-- | - PathMetrics: Validation, endpoints, sinuosity

module Hydrogen.GPU.Scene3D.PathEval
  ( -- * Path Evaluation
    evalPath
  , evalPathTangent
  
  -- * Bezier Primitives
  , evalCubicBezier
  , evalCubicBezierTangent
  
  -- * Catmull-Rom Primitives
  , evalCatmullRom
  , evalCatmullRomTangent
  
  -- * Bezier Subdivision
  , subdivideCubicBezier
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

-- | Prelude: Arithmetic vocabulary for polynomial spline evaluation.
import Prelude
  ( (+)
  , (-)
  , (*)
  , (<)
  , (>=)
  , (==)
  , negate
  , otherwise
  , bind
  )

import Data.Array (length, index)
import Data.Int (toNumber, floor, rem) as Int
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Schema.Dimension.Vector.Vec3 
  ( Vec3
  , vec3
  , addVec3
  , subtractVec3
  , scaleVec3
  , normalizeVec3
  , lerpVec3
  )

import Hydrogen.GPU.Scene3D.Path 
  ( Path3D
  , ControlPoint
  , SplineType(LinearSpline, BezierSpline, CatmullRomSpline, HermiteSpline)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // linear interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation between two points.
-- |
-- | t = 0 → p0, t = 1 → p1
evalLinear :: Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalLinear p0 p1 t =
  addVec3 (scaleVec3 (1.0 - t) p0) (scaleVec3 t p1)

-- | Tangent of linear segment (constant).
evalLinearTangent :: Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalLinearTangent p0 p1 _ =
  normalizeVec3 (subtractVec3 p1 p0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // cubic bezier
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate cubic Bezier curve at parameter t.
-- |
-- | ## Parameters
-- | - p0: Start point
-- | - p1: First control point (handle out from p0)
-- | - p2: Second control point (handle in to p3)
-- | - p3: End point
-- | - t: Parameter in [0, 1]
-- |
-- | ## Formula
-- | B(t) = (1-t)³p0 + 3(1-t)²t·p1 + 3(1-t)t²·p2 + t³·p3
evalCubicBezier :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalCubicBezier p0 p1 p2 p3 t =
  let
    t2 = t * t
    t3 = t2 * t
    mt = 1.0 - t
    mt2 = mt * mt
    mt3 = mt2 * mt
    
    c0 = mt3
    c1 = 3.0 * mt2 * t
    c2 = 3.0 * mt * t2
    c3 = t3
  in
    addVec3 (addVec3 (addVec3 
      (scaleVec3 c0 p0) 
      (scaleVec3 c1 p1)) 
      (scaleVec3 c2 p2)) 
      (scaleVec3 c3 p3)

-- | Tangent (first derivative) of cubic Bezier at parameter t.
-- |
-- | ## Formula
-- | B'(t) = 3(1-t)²(p1-p0) + 6(1-t)t(p2-p1) + 3t²(p3-p2)
evalCubicBezierTangent :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalCubicBezierTangent p0 p1 p2 p3 t =
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
    normalizeVec3 (addVec3 (addVec3 
      (scaleVec3 c0 v0) 
      (scaleVec3 c1 v1)) 
      (scaleVec3 c2 v2))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // catmull-rom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate Catmull-Rom spline at parameter t.
-- |
-- | ## Parameters
-- | - p0: Previous point (for tangent calculation)
-- | - p1: Start of segment
-- | - p2: End of segment
-- | - p3: Next point (for tangent calculation)
-- | - tension: Controls curve tightness (0.5 = standard Catmull-Rom)
-- | - t: Parameter in [0, 1] for segment p1→p2
evalCatmullRom :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Number -> Vec3 Number
evalCatmullRom p0 p1 p2 p3 tension t =
  let
    t2 = t * t
    t3 = t2 * t
    tau = tension
    
    c0 = negate tau * t3 + 2.0 * tau * t2 - tau * t
    c1 = (2.0 - tau) * t3 + (tau - 3.0) * t2 + 1.0
    c2 = (tau - 2.0) * t3 + (3.0 - 2.0 * tau) * t2 + tau * t
    c3 = tau * t3 - tau * t2
  in
    addVec3 (addVec3 (addVec3 
      (scaleVec3 c0 p0) 
      (scaleVec3 c1 p1)) 
      (scaleVec3 c2 p2)) 
      (scaleVec3 c3 p3)

-- | Tangent of Catmull-Rom spline at parameter t.
evalCatmullRomTangent :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Number -> Vec3 Number
evalCatmullRomTangent p0 p1 p2 p3 tension t =
  let
    t2 = t * t
    tau = tension
    
    dc0 = negate 3.0 * tau * t2 + 4.0 * tau * t - tau
    dc1 = 3.0 * (2.0 - tau) * t2 + 2.0 * (tau - 3.0) * t
    dc2 = 3.0 * (tau - 2.0) * t2 + 2.0 * (3.0 - 2.0 * tau) * t + tau
    dc3 = 3.0 * tau * t2 - 2.0 * tau * t
  in
    normalizeVec3 (addVec3 (addVec3 (addVec3 
      (scaleVec3 dc0 p0) 
      (scaleVec3 dc1 p1)) 
      (scaleVec3 dc2 p2)) 
      (scaleVec3 dc3 p3))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // hermite
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate Hermite spline at parameter t.
evalHermite :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalHermite p0 m0 p1 m1 t =
  let
    t2 = t * t
    t3 = t2 * t
    
    h00 = 2.0 * t3 - 3.0 * t2 + 1.0
    h10 = t3 - 2.0 * t2 + t
    h01 = negate 2.0 * t3 + 3.0 * t2
    h11 = t3 - t2
  in
    addVec3 (addVec3 (addVec3 
      (scaleVec3 h00 p0) 
      (scaleVec3 h10 m0)) 
      (scaleVec3 h01 p1)) 
      (scaleVec3 h11 m1)

-- | Tangent of Hermite spline at parameter t.
evalHermiteTangent :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number -> Number -> Vec3 Number
evalHermiteTangent p0 m0 p1 m1 t =
  let
    t2 = t * t
    
    dh00 = 6.0 * t2 - 6.0 * t
    dh10 = 3.0 * t2 - 4.0 * t + 1.0
    dh01 = negate 6.0 * t2 + 6.0 * t
    dh11 = 3.0 * t2 - 2.0 * t
  in
    normalizeVec3 (addVec3 (addVec3 (addVec3 
      (scaleVec3 dh00 p0) 
      (scaleVec3 dh10 m0)) 
      (scaleVec3 dh01 p1)) 
      (scaleVec3 dh11 m1))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate a Path3D at global parameter t.
-- |
-- | ## Parameters
-- | - path: The path to evaluate
-- | - t: Global parameter in [0, 1] spanning entire path
-- |
-- | ## Returns
-- | Nothing if path has no points.
evalPath :: Path3D -> Number -> Maybe (Vec3 Number)
evalPath path t =
  let
    pts = path.points
    n = length pts
  in
    if n < 2 then
      case index pts 0 of
        Just pt -> Just pt.position
        Nothing -> Nothing
    else
      evalPathSegmented path.splineType path.tension path.closed pts n t

-- | Evaluate path tangent at global parameter t.
evalPathTangent :: Path3D -> Number -> Maybe (Vec3 Number)
evalPathTangent path t =
  let
    pts = path.points
    n = length pts
  in
    if n < 2 then
      if n == 1 then Just (vec3 1.0 0.0 0.0) else Nothing
    else
      evalPathTangentSegmented path.splineType path.tension path.closed pts n t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // segmented evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Internal: Evaluate path split into segments.
evalPathSegmented :: SplineType -> Number -> Boolean -> Array ControlPoint -> Int -> Number -> Maybe (Vec3 Number)
evalPathSegmented splineType tension closed pts n t =
  let
    numSegments = if closed then n else n - 1
    segmentFloat = t * toNumber numSegments
    segmentIndex = clampInt 0 (numSegments - 1) (floorToInt segmentFloat)
    localT = segmentFloat - toNumber segmentIndex
  in
    evalSegmentAt splineType tension closed pts n segmentIndex localT

-- | Internal: Evaluate tangent split into segments.
evalPathTangentSegmented :: SplineType -> Number -> Boolean -> Array ControlPoint -> Int -> Number -> Maybe (Vec3 Number)
evalPathTangentSegmented splineType tension closed pts n t =
  let
    numSegments = if closed then n else n - 1
    segmentFloat = t * toNumber numSegments
    segmentIndex = clampInt 0 (numSegments - 1) (floorToInt segmentFloat)
    localT = segmentFloat - toNumber segmentIndex
  in
    evalTangentAt splineType tension closed pts n segmentIndex localT

-- | Internal: Evaluate position at specific segment.
evalSegmentAt :: SplineType -> Number -> Boolean -> Array ControlPoint -> Int -> Int -> Number -> Maybe (Vec3 Number)
evalSegmentAt splineType tension closed pts n segIdx localT = do
  i0 <- getPointIndex closed n (segIdx - 1)
  i1 <- getPointIndex closed n segIdx
  i2 <- getPointIndex closed n (segIdx + 1)
  i3 <- getPointIndex closed n (segIdx + 2)
  
  pt0 <- index pts i0
  pt1 <- index pts i1
  pt2 <- index pts i2
  pt3 <- index pts i3
  
  let
    p0 = pt0.position
    p1 = pt1.position
    p2 = pt2.position
    p3 = pt3.position
  
  case splineType of
    LinearSpline ->
      Just (evalLinear p1 p2 localT)
    
    BezierSpline ->
      let
        handle1Out = addVec3 p1 pt1.handleOut.offset
        handle2In = addVec3 p2 pt2.handleIn.offset
      in
        Just (evalCubicBezier p1 handle1Out handle2In p2 localT)
    
    CatmullRomSpline ->
      Just (evalCatmullRom p0 p1 p2 p3 tension localT)
    
    HermiteSpline ->
      let
        m0 = pt1.handleOut.offset
        m1 = pt2.handleIn.offset
      in
        Just (evalHermite p1 m0 p2 m1 localT)

-- | Internal: Evaluate tangent at specific segment.
evalTangentAt :: SplineType -> Number -> Boolean -> Array ControlPoint -> Int -> Int -> Number -> Maybe (Vec3 Number)
evalTangentAt splineType tension closed pts n segIdx localT = do
  i0 <- getPointIndex closed n (segIdx - 1)
  i1 <- getPointIndex closed n segIdx
  i2 <- getPointIndex closed n (segIdx + 1)
  i3 <- getPointIndex closed n (segIdx + 2)
  
  pt0 <- index pts i0
  pt1 <- index pts i1
  pt2 <- index pts i2
  pt3 <- index pts i3
  
  let
    p0 = pt0.position
    p1 = pt1.position
    p2 = pt2.position
    p3 = pt3.position
  
  case splineType of
    LinearSpline ->
      Just (evalLinearTangent p1 p2 localT)
    
    BezierSpline ->
      let
        handle1Out = addVec3 p1 pt1.handleOut.offset
        handle2In = addVec3 p2 pt2.handleIn.offset
      in
        Just (evalCubicBezierTangent p1 handle1Out handle2In p2 localT)
    
    CatmullRomSpline ->
      Just (evalCatmullRomTangent p0 p1 p2 p3 tension localT)
    
    HermiteSpline ->
      let
        m0 = pt1.handleOut.offset
        m1 = pt2.handleIn.offset
      in
        Just (evalHermiteTangent p1 m0 p2 m1 localT)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bezier subdivision
-- ═════════════════════════════════════════════════════════════════════════════

-- | Subdivide a cubic Bezier curve at parameter t using de Casteljau's algorithm.
-- |
-- | Returns two sets of control points: (left curve, right curve)
subdivideCubicBezier 
  :: Vec3 Number -> Vec3 Number -> Vec3 Number -> Vec3 Number 
  -> Number 
  -> { left :: { p0 :: Vec3 Number, p1 :: Vec3 Number, p2 :: Vec3 Number, p3 :: Vec3 Number }
     , right :: { p0 :: Vec3 Number, p1 :: Vec3 Number, p2 :: Vec3 Number, p3 :: Vec3 Number }
     }
subdivideCubicBezier p0 p1 p2 p3 t =
  let
    q0 = lerpVec3 t p0 p1
    q1 = lerpVec3 t p1 p2
    q2 = lerpVec3 t p2 p3
    
    r0 = lerpVec3 t q0 q1
    r1 = lerpVec3 t q1 q2
    
    s = lerpVec3 t r0 r1
  in
    { left: { p0: p0, p1: q0, p2: r0, p3: s }
    , right: { p0: s, p1: r1, p2: q2, p3: p3 }
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get point index with wrapping/clamping.
getPointIndex :: Boolean -> Int -> Int -> Maybe Int
getPointIndex closed n i
  | closed = Just (modInt (modInt i n + n) n)
  | i < 0 = Just 0
  | i >= n = Just (n - 1)
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
  | x >= hi = hi
  | otherwise = x
