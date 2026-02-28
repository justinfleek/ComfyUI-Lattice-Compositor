-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // schema // geometry // spline // helpers
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Spline Helpers: Mathematical utilities for spline evaluation.
-- |
-- | Contains internal functions for:
-- | - Catmull-Rom evaluation (Barry-Goldman algorithm)
-- | - B-Spline evaluation (cubic uniform basis)
-- | - Bezier conversion
-- | - Numerical utilities (exp, log, pow)

module Hydrogen.Schema.Geometry.Spline.Helpers
  ( -- * Evaluation
    catmullRomEvaluate
  , catmullRomTangentEvaluate
  , bSplineEvaluate
  , bSplineTangentEvaluate
  
    -- * Conversion
  , catmullRomToBezier
  , bSplineToBezier
  
    -- * Math Utilities
  , clamp01
  , wrapIndex
  , toNumber
  , epsilon
  , pow
  , exp
  , log
  
    -- * Array Building
  , buildArray
  , buildIntArray
  
    -- * Geometry Utilities
  , origin
  , initialBounds
  , mergeBounds
  ) where

import Prelude
  ( (+)
  , (-)
  , (*)
  , (/)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (==)
  , otherwise
  , negate
  , min
  , max
  , show
  )

import Data.Array (snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Int (toNumber) as Int
import Data.EuclideanRing (mod) as Ring
import Data.Number (sqrt)

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2)
import Hydrogen.Schema.Geometry.Bezier (CubicBezier, cubicBezier)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // catmull-rom evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate Catmull-Rom segment at local parameter t ∈ [0, 1].
-- |
-- | Uses centripetal parameterization with alpha = tension.
-- | - alpha = 0.0: Uniform (standard Catmull-Rom, can have cusps)
-- | - alpha = 0.5: Centripetal (prevents cusps and self-intersection)
-- | - alpha = 1.0: Chordal (follows chord lengths exactly)
-- |
-- | The centripetal variant is mathematically superior for most use cases
-- | as it guarantees no cusps or self-intersections while still being smooth.
catmullRomEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Number -> Point2D
catmullRomEvaluate t (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) alpha =
  let
    -- Compute knot intervals using |P_{i+1} - P_i|^alpha
    -- This is the key to centripetal parameterization
    d01 = chordLength p0 p1 alpha
    d12 = chordLength p1 p2 alpha
    d23 = chordLength p2 p3 alpha
    
    -- Knot values (cumulative)
    t0 = 0.0
    t1 = t0 + d01
    t2 = t1 + d12
    t3 = t2 + d23
    
    -- Map input t ∈ [0,1] to knot interval [t1, t2]
    tKnot = t1 + t * (t2 - t1)
    
    -- Barry-Goldman pyramid algorithm for Catmull-Rom
    -- This is a recursive interpolation scheme
    
    -- First level: linear interpolation between adjacent points
    a1x = interpolateKnot t0 t1 tKnot p0.x p1.x
    a1y = interpolateKnot t0 t1 tKnot p0.y p1.y
    a2x = interpolateKnot t1 t2 tKnot p1.x p2.x
    a2y = interpolateKnot t1 t2 tKnot p1.y p2.y
    a3x = interpolateKnot t2 t3 tKnot p2.x p3.x
    a3y = interpolateKnot t2 t3 tKnot p2.y p3.y
    
    -- Second level
    b1x = interpolateKnot t0 t2 tKnot a1x a2x
    b1y = interpolateKnot t0 t2 tKnot a1y a2y
    b2x = interpolateKnot t1 t3 tKnot a2x a3x
    b2y = interpolateKnot t1 t3 tKnot a2y a3y
    
    -- Third level (final point)
    cx = interpolateKnot t1 t2 tKnot b1x b2x
    cy = interpolateKnot t1 t2 tKnot b1y b2y
  in
    point2D cx cy

-- | Tangent of Catmull-Rom segment at local parameter t.
-- |
-- | Computed via numerical differentiation of the Barry-Goldman algorithm.
-- | Uses central difference for accuracy.
catmullRomTangentEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Number -> Vector2D
catmullRomTangentEvaluate t pp0 pp1 pp2 pp3 alpha =
  let
    -- Use central difference for derivative
    h = 0.0001
    t1 = max 0.0 (t - h)
    t2 = min 1.0 (t + h)
    actualH = (t2 - t1) / 2.0
    
    (Point2D pMinus) = catmullRomEvaluate t1 pp0 pp1 pp2 pp3 alpha
    (Point2D pPlus) = catmullRomEvaluate t2 pp0 pp1 pp2 pp3 alpha
    
    -- Scale by knot interval to get proper velocity
    (Point2D p1) = pp1
    (Point2D p2) = pp2
    d12 = chordLength p1 p2 alpha
    
    dx = (pPlus.x - pMinus.x) / (2.0 * actualH) * d12
    dy = (pPlus.y - pMinus.y) / (2.0 * actualH) * d12
  in
    vec2 dx dy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // b-spline evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate B-spline segment at local parameter t ∈ [0, 1].
-- |
-- | Uses cubic uniform B-spline basis.
bSplineEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Point2D
bSplineEvaluate t (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) =
  let
    t2 = t * t
    t3 = t2 * t
    mt = 1.0 - t
    mt3 = mt * mt * mt
    
    -- B-spline basis functions (cubic uniform)
    -- N0 = (1-t)³/6
    -- N1 = (3t³ - 6t² + 4)/6
    -- N2 = (-3t³ + 3t² + 3t + 1)/6
    -- N3 = t³/6
    
    b0 = mt3 / 6.0
    b1 = (3.0 * t3 - 6.0 * t2 + 4.0) / 6.0
    b2 = (negate 3.0 * t3 + 3.0 * t2 + 3.0 * t + 1.0) / 6.0
    b3 = t3 / 6.0
    
    x = b0 * p0.x + b1 * p1.x + b2 * p2.x + b3 * p3.x
    y = b0 * p0.y + b1 * p1.y + b2 * p2.y + b3 * p3.y
  in
    point2D x y

-- | Tangent of B-spline segment at local parameter t.
bSplineTangentEvaluate :: Number -> Point2D -> Point2D -> Point2D -> Point2D -> Vector2D
bSplineTangentEvaluate t (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) =
  let
    t2 = t * t
    mt = 1.0 - t
    mt2 = mt * mt
    
    -- Derivatives of B-spline basis functions
    -- N0' = -3(1-t)²/6 = -(1-t)²/2
    -- N1' = (9t² - 12t)/6 = (3t² - 4t)/2
    -- N2' = (-9t² + 6t + 3)/6 = (-3t² + 2t + 1)/2
    -- N3' = 3t²/6 = t²/2
    
    db0 = negate mt2 / 2.0
    db1 = (3.0 * t2 - 4.0 * t) / 2.0
    db2 = (negate 3.0 * t2 + 2.0 * t + 1.0) / 2.0
    db3 = t2 / 2.0
    
    dx = db0 * p0.x + db1 * p1.x + db2 * p2.x + db3 * p3.x
    dy = db0 * p0.y + db1 * p1.y + db2 * p2.y + db3 * p3.y
  in
    vec2 dx dy

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // bezier conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert Catmull-Rom segment to equivalent cubic Bezier.
-- |
-- | The Bezier control points are derived from the Catmull-Rom tangents
-- | at the endpoints.
catmullRomToBezier :: Point2D -> Point2D -> Point2D -> Point2D -> Number -> CubicBezier
catmullRomToBezier (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) _ =
  let
    -- Catmull-Rom goes from p1 to p2
    -- Tangent at p1: 0.5 * (p2 - p0)
    -- Tangent at p2: 0.5 * (p3 - p1)
    
    -- Bezier control points: P0, P0 + T0/3, P1 - T1/3, P1
    t0x = 0.5 * (p2.x - p0.x)
    t0y = 0.5 * (p2.y - p0.y)
    t1x = 0.5 * (p3.x - p1.x)
    t1y = 0.5 * (p3.y - p1.y)
    
    bp0 = point2D p1.x p1.y
    bp1 = point2D (p1.x + t0x / 3.0) (p1.y + t0y / 3.0)
    bp2 = point2D (p2.x - t1x / 3.0) (p2.y - t1y / 3.0)
    bp3 = point2D p2.x p2.y
  in
    cubicBezier bp0 bp1 bp2 bp3

-- | Convert B-spline segment to equivalent cubic Bezier.
-- |
-- | B-spline to Bezier conversion uses the de Boor algorithm.
bSplineToBezier :: Point2D -> Point2D -> Point2D -> Point2D -> CubicBezier
bSplineToBezier (Point2D p0) (Point2D p1) (Point2D p2) (Point2D p3) =
  let
    -- B-spline to Bezier conversion matrix (for uniform cubic):
    -- B0 = (P0 + 4P1 + P2) / 6
    -- B1 = (4P1 + 2P2) / 6 = (2P1 + P2) / 3
    -- B2 = (2P1 + 4P2) / 6 = (P1 + 2P2) / 3
    -- B3 = (P1 + 4P2 + P3) / 6
    
    bp0 = point2D
      ((p0.x + 4.0 * p1.x + p2.x) / 6.0)
      ((p0.y + 4.0 * p1.y + p2.y) / 6.0)
    
    bp1 = point2D
      ((2.0 * p1.x + p2.x) / 3.0)
      ((2.0 * p1.y + p2.y) / 3.0)
    
    bp2 = point2D
      ((p1.x + 2.0 * p2.x) / 3.0)
      ((p1.y + 2.0 * p2.y) / 3.0)
    
    bp3 = point2D
      ((p1.x + 4.0 * p2.x + p3.x) / 6.0)
      ((p1.y + 4.0 * p2.y + p3.y) / 6.0)
  in
    cubicBezier bp0 bp1 bp2 bp3

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // chord utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute chord length raised to power alpha.
-- |
-- | |P1 - P0|^alpha where alpha controls the parameterization type.
chordLength :: { x :: Number, y :: Number } -> { x :: Number, y :: Number } -> Number -> Number
chordLength p0 p1 alpha =
  let
    dx = p1.x - p0.x
    dy = p1.y - p0.y
    distSq = dx * dx + dy * dy
  in
    -- Handle degenerate case (coincident points)
    if distSq < epsilon then epsilon
    -- For alpha = 0.5, we want sqrt(dist) = dist^0.5 = (distSq)^0.25
    -- For alpha = 1.0, we want dist = (distSq)^0.5
    -- General: dist^alpha = (distSq)^(alpha/2)
    else pow distSq (alpha / 2.0)

-- | Linear interpolation in knot space.
-- |
-- | Given knots ti and tj, and values vi and vj, compute value at t.
interpolateKnot :: Number -> Number -> Number -> Number -> Number -> Number
interpolateKnot ti tj t vi vj =
  let denom = tj - ti
  in if denom < epsilon then vi
     else vi + (t - ti) / denom * (vj - vi)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // math utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Power function using exp/log.
-- |
-- | Computes x^y for positive x.
pow :: Number -> Number -> Number
pow x y =
  if x <= 0.0 then 0.0
  else exp (y * log x)

-- | Exponential function
exp :: Number -> Number
exp x = expImpl x

-- | Natural logarithm
log :: Number -> Number
log x = logImpl x

-- | Log implementation using series expansion
-- | ln(x) = 2 * sum_{n=0}^∞ (1/(2n+1)) * ((x-1)/(x+1))^(2n+1)
logImpl :: Number -> Number
logImpl x =
  if x <= 0.0 then negate 1.0e308  -- -infinity approximation
  else if x < 0.5 then
    -- Range reduction: ln(x) = ln(x/e^k) + k for appropriate k
    let k = logEstimate x
        xReduced = x / expImpl k
    in logSeries xReduced + k
  else if x > 2.0 then
    let k = logEstimate x
        xReduced = x / expImpl k
    in logSeries xReduced + k
  else logSeries x

-- | Estimate log for range reduction
logEstimate :: Number -> Number
logEstimate x = 
  if x > 1.0 then logEstimatePositive x 0.0
  else negate (logEstimatePositive (1.0 / x) 0.0)

logEstimatePositive :: Number -> Number -> Number
logEstimatePositive x acc =
  if x < 2.718281828 then acc
  else logEstimatePositive (x / 2.718281828) (acc + 1.0)

-- | Log series for x near 1
logSeries :: Number -> Number
logSeries x =
  let
    y = (x - 1.0) / (x + 1.0)
    y2 = y * y
  in 2.0 * y * (1.0 + y2 / 3.0 + y2 * y2 / 5.0 + y2 * y2 * y2 / 7.0 + 
                y2 * y2 * y2 * y2 / 9.0 + y2 * y2 * y2 * y2 * y2 / 11.0)

-- | Exp implementation using series expansion
-- | e^x = sum_{n=0}^∞ x^n / n!
expImpl :: Number -> Number
expImpl x =
  if x > 700.0 then 1.0e308  -- overflow protection
  else if x < negate 700.0 then 0.0  -- underflow protection
  else if x < 0.0 then 1.0 / expImpl (negate x)
  else if x > 1.0 then
    -- Range reduction: e^x = (e^(x/n))^n
    let n = Int.toNumber (floorInt x + 1)
        xSmall = x / n
        eSmall = expSeries xSmall
    in powNumber eSmall (floorInt x + 1)
  else expSeries x

-- | Floor for Number -> Int
floorInt :: Number -> Int
floorInt n = 
  if n < 0.0 then negate (floorIntPositive (negate n))
  else floorIntPositive n

floorIntPositive :: Number -> Int
floorIntPositive n =
  floorIntImpl n 0

floorIntImpl :: Number -> Int -> Int
floorIntImpl n acc =
  if Int.toNumber acc > n then acc - 1
  else if Int.toNumber (acc + 1) > n then acc
  else floorIntImpl n (acc + 1)

-- | Exp series for |x| < 1
expSeries :: Number -> Number
expSeries x =
  let
    x2 = x * x
    x3 = x2 * x
    x4 = x3 * x
    x5 = x4 * x
    x6 = x5 * x
    x7 = x6 * x
    x8 = x7 * x
  in 1.0 + x + x2 / 2.0 + x3 / 6.0 + x4 / 24.0 + x5 / 120.0 + 
     x6 / 720.0 + x7 / 5040.0 + x8 / 40320.0

-- | Number power by repeated squaring
powNumber :: Number -> Int -> Number
powNumber base n =
  if n <= 0 then 1.0
  else if wrapIndex n 2 == 0 then
    let half = powNumber base (n / 2)
    in half * half
  else base * powNumber base (n - 1)

-- | Small epsilon for numerical stability
epsilon :: Number
epsilon = 1.0e-10

-- | Clamp value to [0, 1]
-- |
-- | All inputs are assumed finite (no NaN, no Infinity).
-- | The guards cover the complete bounded range.
clamp01 :: Number -> Number
clamp01 n
  | n < 0.0 = 0.0
  | n > 1.0 = 1.0
  | otherwise = n  -- n is in [0, 1]

-- | Integer to Number conversion
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Modulo for integers (using EuclideanRing)
wrapIndex :: Int -> Int -> Int
wrapIndex a b = Ring.mod a b

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // array building
-- ═════════════════════════════════════════════════════════════════════════════

-- | Build array from function
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build array of integers [0, 1, ..., n-1].
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n (\i -> Just i)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // geometry utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Origin point for fallbacks
origin :: Point2D
origin = point2D 0.0 0.0

-- | Initial bounding box (will be overwritten by first real bounds)
initialBounds :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
initialBounds = 
  { minX: 1.0e308
  , minY: 1.0e308
  , maxX: negate 1.0e308
  , maxY: negate 1.0e308
  }

-- | Merge two bounding boxes
mergeBounds 
  :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
mergeBounds a b =
  { minX: min a.minX b.minX
  , minY: min a.minY b.minY
  , maxX: max a.maxX b.maxX
  , maxY: max a.maxY b.maxY
  }
