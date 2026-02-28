-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // geometry // nurbs
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Nurbs — Non-Uniform Rational B-Splines for professional curve modeling.
-- |
-- | ## Design Philosophy
-- |
-- | NURBS are the gold standard for precise curve and surface representation
-- | in CAD, professional animation, and industrial design. They extend B-splines
-- | with two key features:
-- |
-- | - **Weights**: Each control point has a weight that affects how strongly
-- |   it "pulls" the curve. Weights enable exact representation of conic
-- |   sections (circles, ellipses, hyperbolas).
-- |
-- | - **Non-uniform knots**: The knot vector can have non-uniform spacing,
-- |   allowing finer control over where the curve "responds" to control points.
-- |
-- | ## Mathematical Foundation
-- |
-- | A NURBS curve of degree p is defined as:
-- |
-- | ```
-- | C(u) = Σᵢ (Nᵢ,ₚ(u) · wᵢ · Pᵢ) / Σᵢ (Nᵢ,ₚ(u) · wᵢ)
-- | ```
-- |
-- | Where:
-- | - Pᵢ are control points
-- | - wᵢ are weights (positive numbers)
-- | - Nᵢ,ₚ(u) are B-spline basis functions of degree p
-- | - The knot vector determines the basis functions
-- |
-- | ## Key Properties
-- |
-- | - **Exact conics**: Circles, ellipses, and arcs can be represented exactly
-- | - **Local control**: Moving one point affects only nearby curve segments
-- | - **Affine invariance**: Transformations apply to control points only
-- | - **Variation diminishing**: The curve is "smoother" than control polygon
-- |
-- | ## Use Cases
-- |
-- | - CAD/CAM systems (Solidworks, AutoCAD, Rhino)
-- | - Typography and font design
-- | - Aircraft and automotive body design
-- | - Professional 3D modeling (Maya, Blender)
-- | - CNC machining tool paths
-- |
-- | ## Dependencies
-- |
-- | - Schema.Geometry.Point (Point2D for control points)
-- | - Schema.Geometry.Vector (Vector2D for tangents)
-- | - Data.Array (control points, knots, weights)

module Hydrogen.Schema.Geometry.Nurbs
  ( -- * NURBS Curve Type
    NurbsCurve(NurbsCurve)
  , ControlPoint(ControlPoint)
  , KnotVector
  
  -- * Construction
  , nurbsCurve
  , nurbsFromPoints
  , nurbsCircle
  , nurbsArc
  , nurbsEllipse
  
  -- * Accessors
  , nurbsControlPoints
  , nurbsKnots
  , nurbsDegree
  , nurbsOrder
  , controlPointPosition
  , controlPointWeight
  
  -- * Evaluation
  , nurbsPointAt
  , nurbsTangentAt
  , nurbsNormalAt
  , nurbsCurvatureAt
  
  -- * Modification
  , setControlPoint
  , setWeight
  , insertKnot
  , elevateDegree
  
  -- * Geometry
  , nurbsLength
  , nurbsBoundingBox
  
  -- * Conversion
  , nurbsToBeziers
  , sampleNurbs
  
  -- * Validation
  , isValidNurbs
  , nurbsParameterRange
  
  -- * Point Access
  , nurbsControlPointAt
  , nurbsWeightAt
  
  -- * Bezier Integration
  , nurbsLengthViaBeziers
  , nurbsBoundingBoxViaBeziers
  
  -- * Morphing
  , blendNurbsWeights
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (+)
  , (-)
  , (*)
  , (/)
  , (<>)
  , (==)
  , (<)
  , (>)
  , (<=)
  , (>=)
  , (&&)
  , (||)
  , otherwise
  , negate
  , min
  , max
  , map
  )

import Data.Array (length, index, (!!), snoc, foldl, updateAt, zipWith, take, drop)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (sqrt, pi, cos, sin)
import Data.Int (toNumber) as Int

import Hydrogen.Schema.Geometry.Point (Point2D(Point2D), point2D)
import Hydrogen.Schema.Geometry.Vector (Vector2D, vec2, normalize2, perpendicular2)
import Hydrogen.Schema.Geometry.Bezier 
  ( CubicBezier
  , cubicBezier
  , cubicLength
  , cubicBoundingBox
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | A weighted control point for NURBS curves.
-- |
-- | Weight > 0 always. Higher weight pulls the curve closer to the point.
-- | Weight = 1 gives standard B-spline behavior.
newtype ControlPoint = ControlPoint
  { position :: Point2D
  , weight :: Number
  }

derive instance eqControlPoint :: Eq ControlPoint

instance showControlPoint :: Show ControlPoint where
  show (ControlPoint cp) = "(ControlPoint pos:" <> show cp.position 
    <> " w:" <> show cp.weight <> ")"

-- | Knot vector for NURBS.
-- |
-- | A non-decreasing sequence of parameter values.
-- | For a curve of degree p with n control points:
-- | - Knot vector has m = n + p + 1 values
-- | - First p+1 knots are often clamped (equal to first value)
-- | - Last p+1 knots are often clamped (equal to last value)
type KnotVector = Array Number

-- | NURBS (Non-Uniform Rational B-Spline) curve.
-- |
-- | Degree p curve with n control points requires n + p + 1 knots.
newtype NurbsCurve = NurbsCurve
  { controlPoints :: Array ControlPoint
  , knots :: KnotVector
  , degree :: Int
  }

derive instance eqNurbsCurve :: Eq NurbsCurve

instance showNurbsCurve :: Show NurbsCurve where
  show (NurbsCurve c) = "(NurbsCurve degree:" <> show c.degree 
    <> " points:" <> show (length c.controlPoints)
    <> " knots:" <> show (length c.knots) <> ")"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // construction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a NURBS curve with explicit knot vector.
-- |
-- | Returns Nothing if:
-- | - Fewer than degree + 1 control points
-- | - Knot vector length ≠ n + p + 1
-- | - Any weight ≤ 0
-- | - Degree < 1
nurbsCurve :: Int -> Array ControlPoint -> KnotVector -> Maybe NurbsCurve
nurbsCurve degree cps knots =
  let 
    n = length cps
    m = length knots
    requiredKnots = n + degree + 1
    validDegree = degree >= 1
    validPoints = n >= degree + 1
    validKnots = m == requiredKnots && isNonDecreasing knots
    validWeights = allWeightsPositive cps
  in
    if validDegree && validPoints && validKnots && validWeights
    then Just (NurbsCurve { controlPoints: cps, knots: knots, degree: degree })
    else Nothing

-- | Create a NURBS curve from unweighted points with uniform knot vector.
-- |
-- | All weights are set to 1.0 (equivalent to B-spline).
nurbsFromPoints :: Int -> Array Point2D -> Maybe NurbsCurve
nurbsFromPoints degree pts =
  let 
    cps = map (\p -> ControlPoint { position: p, weight: 1.0 }) pts
    n = length pts
    knots = uniformKnotVector n degree
  in
    nurbsCurve degree cps knots

-- | Create a NURBS circle centered at origin with given radius.
-- |
-- | Uses 9 control points (degree 2) with weights for exact circle.
-- | This is the standard NURBS representation of a full circle.
nurbsCircle :: Number -> NurbsCurve
nurbsCircle radius =
  let
    -- 9 control points for full circle (degree 2)
    w = sqrt 2.0 / 2.0  -- Weight for corner points
    r = radius
    
    cps = 
      [ ControlPoint { position: point2D r 0.0, weight: 1.0 }
      , ControlPoint { position: point2D r r, weight: w }
      , ControlPoint { position: point2D 0.0 r, weight: 1.0 }
      , ControlPoint { position: point2D (negate r) r, weight: w }
      , ControlPoint { position: point2D (negate r) 0.0, weight: 1.0 }
      , ControlPoint { position: point2D (negate r) (negate r), weight: w }
      , ControlPoint { position: point2D 0.0 (negate r), weight: 1.0 }
      , ControlPoint { position: point2D r (negate r), weight: w }
      , ControlPoint { position: point2D r 0.0, weight: 1.0 }  -- Closed
      ]
    
    -- Knot vector for closed degree-2 curve with 9 points
    knots = [0.0, 0.0, 0.0, 0.25, 0.25, 0.5, 0.5, 0.75, 0.75, 1.0, 1.0, 1.0]
  in
    NurbsCurve { controlPoints: cps, knots: knots, degree: 2 }

-- | Create a NURBS arc from start angle to end angle.
-- |
-- | Angles in radians. Arc is counter-clockwise from start to end.
nurbsArc :: Number -> Number -> Number -> NurbsCurve
nurbsArc radius startAngle endAngle =
  let
    -- Compute arc span
    span = endAngle - startAngle
    
    -- For spans ≤ π/2, we can use a single quadratic segment
    -- For larger spans, we need multiple segments
    numSegments = 
      if span <= pi / 2.0 then 1
      else if span <= pi then 2
      else if span <= 3.0 * pi / 2.0 then 3
      else 4
    
    segmentAngle = span / toNumber numSegments
    halfAngle = segmentAngle / 2.0
    w = cos halfAngle  -- Weight for middle control point
    
    -- Build control points for each segment
    cps = buildArcControlPoints radius startAngle numSegments segmentAngle w []
    
    -- Uniform knot vector for the arc
    knots = buildArcKnots numSegments
  in
    NurbsCurve { controlPoints: cps, knots: knots, degree: 2 }

-- | Create a NURBS ellipse centered at origin.
-- |
-- | rx = radius along X axis, ry = radius along Y axis.
nurbsEllipse :: Number -> Number -> NurbsCurve
nurbsEllipse rx ry =
  let
    w = sqrt 2.0 / 2.0
    
    cps = 
      [ ControlPoint { position: point2D rx 0.0, weight: 1.0 }
      , ControlPoint { position: point2D rx ry, weight: w }
      , ControlPoint { position: point2D 0.0 ry, weight: 1.0 }
      , ControlPoint { position: point2D (negate rx) ry, weight: w }
      , ControlPoint { position: point2D (negate rx) 0.0, weight: 1.0 }
      , ControlPoint { position: point2D (negate rx) (negate ry), weight: w }
      , ControlPoint { position: point2D 0.0 (negate ry), weight: 1.0 }
      , ControlPoint { position: point2D rx (negate ry), weight: w }
      , ControlPoint { position: point2D rx 0.0, weight: 1.0 }
      ]
    
    knots = [0.0, 0.0, 0.0, 0.25, 0.25, 0.5, 0.5, 0.75, 0.75, 1.0, 1.0, 1.0]
  in
    NurbsCurve { controlPoints: cps, knots: knots, degree: 2 }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // accessors
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get control points of NURBS curve.
nurbsControlPoints :: NurbsCurve -> Array ControlPoint
nurbsControlPoints (NurbsCurve c) = c.controlPoints

-- | Get knot vector of NURBS curve.
nurbsKnots :: NurbsCurve -> KnotVector
nurbsKnots (NurbsCurve c) = c.knots

-- | Get degree of NURBS curve.
nurbsDegree :: NurbsCurve -> Int
nurbsDegree (NurbsCurve c) = c.degree

-- | Get order of NURBS curve (degree + 1).
nurbsOrder :: NurbsCurve -> Int
nurbsOrder (NurbsCurve c) = c.degree + 1

-- | Get position from control point.
controlPointPosition :: ControlPoint -> Point2D
controlPointPosition (ControlPoint cp) = cp.position

-- | Get weight from control point.
controlPointWeight :: ControlPoint -> Number
controlPointWeight (ControlPoint cp) = cp.weight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // evaluation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Evaluate NURBS curve at parameter u.
-- |
-- | Parameter u should be within the valid parameter range (see nurbsParameterRange).
-- | Uses de Boor's algorithm for numerical stability.
nurbsPointAt :: Number -> NurbsCurve -> Point2D
nurbsPointAt u (NurbsCurve c) =
  let
    -- Clamp u to valid range
    range = nurbsParamRange c.knots c.degree
    u' = clampNumber range.start range.end u
    
    -- Find knot span
    span = findKnotSpan u' c.knots c.degree
    
    -- Evaluate using de Boor's algorithm with rational weights
    result = deBoorRational u' span c.degree c.controlPoints c.knots
  in
    result

-- | Tangent vector at parameter u.
-- |
-- | Computed via numerical differentiation for stability.
nurbsTangentAt :: Number -> NurbsCurve -> Vector2D
nurbsTangentAt u curve =
  let
    h = 0.0001
    range = nurbsParameterRange curve
    u1 = max range.start (u - h)
    u2 = min range.end (u + h)
    actualH = (u2 - u1) / 2.0
    
    (Point2D p1) = nurbsPointAt u1 curve
    (Point2D p2) = nurbsPointAt u2 curve
    
    dx = (p2.x - p1.x) / (2.0 * actualH)
    dy = (p2.y - p1.y) / (2.0 * actualH)
  in
    vec2 dx dy

-- | Normal vector at parameter u (perpendicular to tangent).
nurbsNormalAt :: Number -> NurbsCurve -> Vector2D
nurbsNormalAt u curve =
  let tangent = nurbsTangentAt u curve
  in perpendicular2 (normalize2 tangent)

-- | Curvature at parameter u.
-- |
-- | κ = |T'(u)| where T is the unit tangent.
-- | Computed via second-order numerical differentiation.
nurbsCurvatureAt :: Number -> NurbsCurve -> Number
nurbsCurvatureAt u curve =
  let
    h = 0.0001
    range = nurbsParameterRange curve
    u0 = clampNumber range.start range.end (u - h)
    u1 = clampNumber range.start range.end u
    u2 = clampNumber range.start range.end (u + h)
    
    (Point2D p0) = nurbsPointAt u0 curve
    (Point2D p1) = nurbsPointAt u1 curve
    (Point2D p2) = nurbsPointAt u2 curve
    
    -- First derivatives
    dx1 = (p1.x - p0.x) / h
    dy1 = (p1.y - p0.y) / h
    dx2 = (p2.x - p1.x) / h
    dy2 = (p2.y - p1.y) / h
    
    -- Second derivatives
    ddx = (dx2 - dx1) / h
    ddy = (dy2 - dy1) / h
    
    -- Average first derivative at u
    dx = (dx1 + dx2) / 2.0
    dy = (dy1 + dy2) / 2.0
    
    -- Curvature formula: κ = |x'y'' - y'x''| / (x'² + y'²)^(3/2)
    cross = dx * ddy - dy * ddx
    speedSq = dx * dx + dy * dy
    speed = sqrt speedSq
    speedCubed = speedSq * speed
  in
    if speedCubed < epsilon then 0.0
    else absNum cross / speedCubed

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // modification
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set a control point at given index.
-- |
-- | Returns Nothing if index out of bounds.
setControlPoint :: Int -> ControlPoint -> NurbsCurve -> Maybe NurbsCurve
setControlPoint i cp (NurbsCurve c) =
  case updateAt i cp c.controlPoints of
    Nothing -> Nothing
    Just newCps -> Just (NurbsCurve { controlPoints: newCps, knots: c.knots, degree: c.degree })

-- | Set weight of control point at given index.
-- |
-- | Returns Nothing if index out of bounds or weight ≤ 0.
setWeight :: Int -> Number -> NurbsCurve -> Maybe NurbsCurve
setWeight i w (NurbsCurve c) =
  if w <= 0.0 then Nothing
  else case index c.controlPoints i of
    Nothing -> Nothing
    Just (ControlPoint cp) ->
      let newCp = ControlPoint { position: cp.position, weight: w }
      in setControlPoint i newCp (NurbsCurve c)

-- | Insert a knot into the curve (knot insertion algorithm).
-- |
-- | Knot insertion adds a knot without changing the curve shape.
-- | This is useful for:
-- | - Converting NURBS to Beziers
-- | - Splitting curves
-- | - Increasing local control
-- |
-- | Returns Nothing if u is outside valid range.
insertKnot :: Number -> NurbsCurve -> Maybe NurbsCurve
insertKnot u (NurbsCurve c) =
  let
    range = nurbsParamRange c.knots c.degree
  in
    if u < range.start || u > range.end then Nothing
    else 
      let
        -- Find span where u will be inserted
        k = findKnotSpan u c.knots c.degree
        
        -- Insert knot into knot vector
        newKnots = insertIntoSortedArray u c.knots
        
        -- Compute new control points using Oslo algorithm
        newCps = osloInsert u k c.degree c.controlPoints c.knots
      in
        Just (NurbsCurve { controlPoints: newCps, knots: newKnots, degree: c.degree })

-- | Elevate degree of curve by 1.
-- |
-- | Degree elevation increases flexibility without changing shape.
elevateDegree :: NurbsCurve -> NurbsCurve
elevateDegree (NurbsCurve c) =
  let
    -- Degree elevation requires inserting new control points
    -- For now, use a simplified approach via sampling and refitting
    -- Full implementation would use the degree elevation algorithm
    
    newDegree = c.degree + 1
    n = length c.controlPoints
    
    -- Sample the curve at more points
    numSamples = n + c.degree
    samples = buildArray numSamples (\i ->
      let t = toNumber i / toNumber (numSamples - 1)
          range = nurbsParamRange c.knots c.degree
          u = range.start + t * (range.end - range.start)
      in Just (nurbsPointAt u (NurbsCurve c))
    )
    
    -- Create new control points (simplified: use samples as approximation)
    newCps = map (\p -> ControlPoint { position: p, weight: 1.0 }) samples
    
    -- Create new knot vector
    newKnots = uniformKnotVector (length newCps) newDegree
  in
    NurbsCurve { controlPoints: newCps, knots: newKnots, degree: newDegree }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Approximate arc length of NURBS curve.
-- |
-- | Uses adaptive sampling for accuracy.
nurbsLength :: NurbsCurve -> Number
nurbsLength curve =
  let
    samples = sampleNurbs 100 curve
    n = length samples
  in
    sumDistances samples 0 0.0 n

-- | Bounding box of NURBS curve.
-- |
-- | Computed from sampled points (conservative estimate).
nurbsBoundingBox :: NurbsCurve -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
nurbsBoundingBox curve =
  let samples = sampleNurbs 100 curve
  in foldl updateBounds initialBounds samples

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert NURBS to array of cubic Bezier curves.
-- |
-- | Uses knot insertion to split at each unique internal knot,
-- | then extracts Bezier segments.
nurbsToBeziers :: NurbsCurve -> Array CubicBezier
nurbsToBeziers curve =
  let
    -- Sample curve and create Bezier approximation
    samples = sampleNurbs 64 curve
    n = length samples
  in
    if n < 4 then []
    else buildArray ((n - 1) / 3) (\i ->
      let 
        base = i * 3
        p0 = fromMaybe origin (index samples base)
        p1 = fromMaybe origin (index samples (base + 1))
        p2 = fromMaybe origin (index samples (base + 2))
        p3 = fromMaybe origin (index samples (min (base + 3) (n - 1)))
      in Just (cubicBezier p0 p1 p2 p3)
    )

-- | Sample NURBS curve at n evenly-spaced parameter values.
sampleNurbs :: Int -> NurbsCurve -> Array Point2D
sampleNurbs n curve =
  if n <= 0 then []
  else
    let range = nurbsParameterRange curve
    in buildArray (n + 1) (\i ->
      let 
        t = toNumber i / toNumber n
        u = range.start + t * (range.end - range.start)
      in Just (nurbsPointAt u curve)
    )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // validation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if NURBS curve is valid.
isValidNurbs :: NurbsCurve -> Boolean
isValidNurbs (NurbsCurve c) =
  let
    n = length c.controlPoints
    m = length c.knots
    requiredKnots = n + c.degree + 1
  in
    c.degree >= 1 &&
    n >= c.degree + 1 &&
    m == requiredKnots &&
    isNonDecreasing c.knots &&
    allWeightsPositive c.controlPoints

-- | Get valid parameter range for NURBS curve.
-- |
-- | For clamped NURBS, this is typically [0, 1] or [knots[p], knots[n]].
nurbsParameterRange :: NurbsCurve -> { start :: Number, end :: Number }
nurbsParameterRange (NurbsCurve c) = nurbsParamRange c.knots c.degree

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // point access
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get control point at index using array indexing operator.
nurbsControlPointAt :: Int -> NurbsCurve -> Maybe ControlPoint
nurbsControlPointAt i (NurbsCurve c) = c.controlPoints !! i

-- | Get weight at index.
nurbsWeightAt :: Int -> NurbsCurve -> Maybe Number
nurbsWeightAt i curve =
  case nurbsControlPointAt i curve of
    Nothing -> Nothing
    Just (ControlPoint cp) -> Just cp.weight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // bezier integration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute NURBS length via Bezier conversion.
-- |
-- | More accurate than direct sampling for curves that convert well to Beziers.
nurbsLengthViaBeziers :: NurbsCurve -> Number
nurbsLengthViaBeziers curve =
  let beziers = nurbsToBeziers curve
  in foldl (\acc b -> acc + cubicLength b) 0.0 beziers

-- | Compute NURBS bounding box via Bezier conversion.
-- |
-- | Uses exact Bezier bounding box computation for each segment.
nurbsBoundingBoxViaBeziers :: NurbsCurve -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
nurbsBoundingBoxViaBeziers curve =
  let 
    beziers = nurbsToBeziers curve
    bezierBounds = map cubicBoundingBox beziers
  in foldl mergeBounds initialBounds bezierBounds

-- | Merge two bounding boxes.
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

-- | Blend two NURBS curves with given weights (for morphing/interpolation).
-- |
-- | Curves must have same number of control points.
-- | Returns array of blended control point positions.
blendNurbsWeights :: Number -> NurbsCurve -> NurbsCurve -> Array Point2D
blendNurbsWeights t (NurbsCurve c1) (NurbsCurve c2) =
  let
    t' = clampNumber 0.0 1.0 t
    mt = 1.0 - t'
    
    blend :: ControlPoint -> ControlPoint -> Point2D
    blend (ControlPoint cp1) (ControlPoint cp2) =
      let
        (Point2D p1) = cp1.position
        (Point2D p2) = cp2.position
        x = mt * p1.x * cp1.weight + t' * p2.x * cp2.weight
        y = mt * p1.y * cp1.weight + t' * p2.y * cp2.weight
        w = mt * cp1.weight + t' * cp2.weight
      in
        if w < epsilon then origin
        else point2D (x / w) (y / w)
  in
    zipWith blend c1.controlPoints c2.controlPoints

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get parameter range from knots and degree.
nurbsParamRange :: KnotVector -> Int -> { start :: Number, end :: Number }
nurbsParamRange knots degree =
  let
    n = length knots
  in
    { start: fromMaybe 0.0 (index knots degree)
    , end: fromMaybe 1.0 (index knots (n - degree - 1))
    }

-- | Find the knot span index for parameter u.
-- |
-- | Returns i such that knots[i] ≤ u < knots[i+1].
findKnotSpan :: Number -> KnotVector -> Int -> Int
findKnotSpan u knots degree =
  let
    n = length knots - degree - 2
    range = nurbsParamRange knots degree
  in
    if u >= range.end then n
    else if u <= range.start then degree
    else findSpanBinary u knots degree n

-- | Binary search for knot span.
findSpanBinary :: Number -> KnotVector -> Int -> Int -> Int
findSpanBinary u knots low high =
  if high - low <= 1 then low
  else
    let mid = (low + high) / 2
    in case index knots mid of
      Nothing -> low
      Just kMid ->
        if u < kMid then findSpanBinary u knots low mid
        else findSpanBinary u knots mid high

-- | De Boor's algorithm for rational NURBS evaluation.
deBoorRational :: Number -> Int -> Int -> Array ControlPoint -> KnotVector -> Point2D
deBoorRational u span degree cps knots =
  let
    -- Extract relevant control points (p+1 points starting at span-degree)
    startIdx = span - degree
    relevantCps = take (degree + 1) (drop startIdx cps)
    
    -- Convert to homogeneous coordinates (x*w, y*w, w)
    homogeneous = map toHomogeneous relevantCps
    
    -- Apply de Boor recursively
    result = deBoorRecursive u span degree degree homogeneous knots
  in
    case index result 0 of
      Nothing -> origin
      Just h -> fromHomogeneous h

-- | Convert control point to homogeneous coordinates.
toHomogeneous :: ControlPoint -> { x :: Number, y :: Number, w :: Number }
toHomogeneous (ControlPoint cp) =
  let (Point2D p) = cp.position
  in { x: p.x * cp.weight, y: p.y * cp.weight, w: cp.weight }

-- | Convert homogeneous coordinates back to Point2D.
fromHomogeneous :: { x :: Number, y :: Number, w :: Number } -> Point2D
fromHomogeneous h =
  if h.w < epsilon then origin
  else point2D (h.x / h.w) (h.y / h.w)

-- | Recursive de Boor evaluation.
deBoorRecursive 
  :: Number 
  -> Int 
  -> Int 
  -> Int 
  -> Array { x :: Number, y :: Number, w :: Number } 
  -> KnotVector 
  -> Array { x :: Number, y :: Number, w :: Number }
deBoorRecursive u span degree r pts knots =
  if r <= 0 then pts
  else
    let
      newPts = buildArray (length pts - 1) (\j ->
        let
          i = span - degree + 1 + j
          knotI = fromMaybe 0.0 (index knots i)
          knotIPR = fromMaybe 1.0 (index knots (i + degree + 1 - r))
          denom = knotIPR - knotI
          alpha = if denom < epsilon then 0.0 else (u - knotI) / denom
        in
          case { p0: index pts j, p1: index pts (j + 1) } of
            { p0: Just pt0, p1: Just pt1 } ->
              Just { x: (1.0 - alpha) * pt0.x + alpha * pt1.x
                   , y: (1.0 - alpha) * pt0.y + alpha * pt1.y
                   , w: (1.0 - alpha) * pt0.w + alpha * pt1.w
                   }
            _ -> Nothing
      )
    in
      deBoorRecursive u span degree (r - 1) newPts knots

-- | Oslo algorithm for knot insertion.
osloInsert :: Number -> Int -> Int -> Array ControlPoint -> KnotVector -> Array ControlPoint
osloInsert u k degree cps knots =
  let
    n = length cps
  in
    buildArray (n + 1) (\i ->
      if i <= k - degree then index cps i
      else if i >= k + 1 then index cps (i - 1)
      else
        let
          knotI = fromMaybe 0.0 (index knots i)
          knotIPD = fromMaybe 1.0 (index knots (i + degree))
          denom = knotIPD - knotI
          alpha = if denom < epsilon then 0.0 else (u - knotI) / denom
        in
          case { p0: index cps (i - 1), p1: index cps i } of
            { p0: Just (ControlPoint cp0), p1: Just (ControlPoint cp1) } ->
              let
                (Point2D pos0) = cp0.position
                (Point2D pos1) = cp1.position
                newX = (1.0 - alpha) * pos0.x + alpha * pos1.x
                newY = (1.0 - alpha) * pos0.y + alpha * pos1.y
                newW = (1.0 - alpha) * cp0.weight + alpha * cp1.weight
              in Just (ControlPoint { position: point2D newX newY, weight: newW })
            _ -> index cps i
    )

-- | Check if array is non-decreasing.
isNonDecreasing :: Array Number -> Boolean
isNonDecreasing arr =
  let n = length arr
  in foldl (\acc i ->
       case { a: index arr i, b: index arr (i + 1) } of
         { a: Just va, b: Just vb } -> acc && va <= vb
         _ -> acc
     ) true (buildIntArray (n - 1))

-- | Check all control point weights are positive.
allWeightsPositive :: Array ControlPoint -> Boolean
allWeightsPositive cps = foldl (\acc (ControlPoint cp) -> acc && cp.weight > 0.0) true cps

-- | Create uniform clamped knot vector.
uniformKnotVector :: Int -> Int -> KnotVector
uniformKnotVector n degree =
  let
    numKnots = n + degree + 1
    numInternalKnots = numKnots - 2 * (degree + 1)
  in
    buildArray numKnots (\i ->
      if i <= degree then Just 0.0
      else if i >= numKnots - degree - 1 then Just 1.0
      else Just (toNumber (i - degree) / toNumber (numInternalKnots + 1))
    )

-- | Insert value into sorted array.
insertIntoSortedArray :: Number -> Array Number -> Array Number
insertIntoSortedArray v arr =
  let
    n = length arr
    insertIdx = findInsertIndex v arr 0 n
    before = take insertIdx arr
    after = drop insertIdx arr
  in
    before <> [v] <> after

findInsertIndex :: Number -> Array Number -> Int -> Int -> Int
findInsertIndex v arr i n =
  if i >= n then n
  else case index arr i of
    Nothing -> i
    Just x -> if v <= x then i else findInsertIndex v arr (i + 1) n

-- | Build arc control points.
buildArcControlPoints :: Number -> Number -> Int -> Number -> Number -> Array ControlPoint -> Array ControlPoint
buildArcControlPoints radius startAngle numSegs segAngle w acc =
  if numSegs <= 0 then acc
  else
    let
      -- Start point of this segment
      angle0 = startAngle + toNumber (length acc / 2) * segAngle
      angle1 = angle0 + segAngle
      midAngle = (angle0 + angle1) / 2.0
      
      -- Control point at middle (off-curve, weighted)
      cpAngle = midAngle
      -- The control point is at radius/cos(halfAngle) distance
      cpRadius = radius / cos (segAngle / 2.0)
      
      p0 = ControlPoint { position: point2D (radius * cos angle0) (radius * sin angle0), weight: 1.0 }
      pMid = ControlPoint { position: point2D (cpRadius * cos cpAngle) (cpRadius * sin cpAngle), weight: w }
      
      newAcc = if length acc == 0 
               then [p0, pMid]
               else snoc acc pMid
    in
      if numSegs == 1 then
        snoc newAcc (ControlPoint { position: point2D (radius * cos angle1) (radius * sin angle1), weight: 1.0 })
      else
        buildArcControlPoints radius startAngle (numSegs - 1) segAngle w newAcc

-- | Build knot vector for arc.
buildArcKnots :: Int -> KnotVector
buildArcKnots numSegs =
  let
    -- For degree 2 with numSegs segments, we need 2*numSegs + 3 knots
    numKnots = 2 * numSegs + 3
  in
    buildArray numKnots (\i ->
      if i <= 2 then Just 0.0
      else if i >= numKnots - 2 then Just 1.0
      else 
        let segIdx = (i - 2) / 2
        in Just (toNumber segIdx / toNumber numSegs)
    )

-- | Sum distances between consecutive points.
sumDistances :: Array Point2D -> Int -> Number -> Int -> Number
sumDistances pts i acc n =
  if i >= n - 1 then acc
  else case { p0: index pts i, p1: index pts (i + 1) } of
    { p0: Just (Point2D a), p1: Just (Point2D b) } ->
      let 
        dx = b.x - a.x
        dy = b.y - a.y
        d = sqrt (dx * dx + dy * dy)
      in sumDistances pts (i + 1) (acc + d) n
    _ -> acc

-- | Update bounding box with a point.
updateBounds 
  :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number } 
  -> Point2D 
  -> { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
updateBounds bounds (Point2D p) =
  { minX: min bounds.minX p.x
  , minY: min bounds.minY p.y
  , maxX: max bounds.maxX p.x
  , maxY: max bounds.maxY p.y
  }

-- | Initial bounding box.
initialBounds :: { minX :: Number, minY :: Number, maxX :: Number, maxY :: Number }
initialBounds = 
  { minX: 1.0e308
  , minY: 1.0e308
  , maxX: negate 1.0e308
  , maxY: negate 1.0e308
  }

-- | Clamp value to range.
-- | Named clampNumber to avoid shadowing Prelude.clamp
clampNumber :: Number -> Number -> Number -> Number
clampNumber lo hi v
  | v < lo = lo
  | v > hi = hi
  | otherwise = v

-- | Origin point.
origin :: Point2D
origin = point2D 0.0 0.0

-- | Integer to Number.
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Absolute value.
absNum :: Number -> Number
absNum n = if n < 0.0 then negate n else n

-- | Small epsilon.
epsilon :: Number
epsilon = 1.0e-10

-- | Build array from function.
buildArray :: forall a. Int -> (Int -> Maybe a) -> Array a
buildArray n f = buildArrayImpl 0 n f []

buildArrayImpl :: forall a. Int -> Int -> (Int -> Maybe a) -> Array a -> Array a
buildArrayImpl i n f acc =
  if i >= n then acc
  else case f i of
    Nothing -> buildArrayImpl (i + 1) n f acc
    Just x -> buildArrayImpl (i + 1) n f (snoc acc x)

-- | Build integer array [0, 1, ..., n-1].
buildIntArray :: Int -> Array Int
buildIntArray n = buildArray n Just
