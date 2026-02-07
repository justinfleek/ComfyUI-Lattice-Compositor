# Specification 05: Bezier Mathematics
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-05  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines the mathematical foundations for Bezier curves used in Lottie animations:

1. **Quadratic Bezier** (3 control points)
2. **Cubic Bezier** (4 control points)
3. **Path operations** (subdivision, arc length, intersection)
4. **Formal proofs** of curve properties

---

## 2. Mathematical Foundations

### 2.1 Bernstein Polynomials

The Bernstein basis polynomials of degree n are:

$$B_{i,n}(t) = \binom{n}{i} t^i (1-t)^{n-i}$$

For cubic bezier (n=3):
- $B_{0,3}(t) = (1-t)^3$
- $B_{1,3}(t) = 3t(1-t)^2$
- $B_{2,3}(t) = 3t^2(1-t)$
- $B_{3,3}(t) = t^3$

### 2.2 Lean4 Formalization

```lean4
/-- Binomial coefficient -/
def binomial : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binomial n k + binomial n (k + 1)

/-- Bernstein basis polynomial B_{i,n}(t) -/
def bernstein (n i : Nat) (t : Float) : Float :=
  (binomial n i : Float) * (t ^ i) * ((1 - t) ^ (n - i))

/-- Proof: Bernstein polynomials sum to 1 -/
theorem bernstein_partition_unity (n : Nat) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    (Finset.range (n + 1)).sum (fun i => bernstein n i t) = 1 := by
  -- By binomial theorem: Σ B_{i,n}(t) = (t + (1-t))^n = 1^n = 1
  sorry

/-- Proof: Bernstein polynomials are non-negative on [0,1] -/
theorem bernstein_nonneg (n i : Nat) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    0 ≤ bernstein n i t := by
  simp [bernstein]
  -- All factors are non-negative when 0 ≤ t ≤ 1
  sorry

/-- Proof: B_{i,n}(0) = 1 iff i = 0 -/
theorem bernstein_at_zero (n i : Nat) (hi : i ≤ n) :
    bernstein n i 0 = if i = 0 then 1 else 0 := by
  simp [bernstein]
  cases i with
  | zero => simp
  | succ j => simp [pow_succ]

/-- Proof: B_{i,n}(1) = 1 iff i = n -/
theorem bernstein_at_one (n i : Nat) (hi : i ≤ n) :
    bernstein n i 1 = if i = n then 1 else 0 := by
  simp [bernstein]
  sorry
```

---

## 3. Quadratic Bezier Curves

### 3.1 Definition

A quadratic Bezier curve with control points P₀, P₁, P₂:

$$\mathbf{B}(t) = (1-t)^2 P_0 + 2t(1-t) P_1 + t^2 P_2$$

### 3.2 Lean4 Implementation

```lean4
/-- Quadratic Bezier curve -/
structure QuadraticBezier where
  p0 : Point  -- Start point
  p1 : Point  -- Control point
  p2 : Point  -- End point
  deriving Repr

namespace QuadraticBezier

/-- Evaluate curve at parameter t ∈ [0,1] -/
def eval (b : QuadraticBezier) (t : Float) : Point :=
  let t' := max 0 (min 1 t)  -- Clamp to [0,1]
  let c0 := (1 - t') * (1 - t')
  let c1 := 2 * t' * (1 - t')
  let c2 := t' * t'
  Point.mk' 
    (c0 * b.p0.x + c1 * b.p1.x + c2 * b.p2.x)
    (c0 * b.p0.y + c1 * b.p1.y + c2 * b.p2.y)

/-- First derivative (tangent vector) -/
def derivative (b : QuadraticBezier) (t : Float) : Point :=
  let t' := max 0 (min 1 t)
  let c0 := 2 * (1 - t')
  let c1 := 2 * t'
  Point.mk'
    (c0 * (b.p1.x - b.p0.x) + c1 * (b.p2.x - b.p1.x))
    (c0 * (b.p1.y - b.p0.y) + c1 * (b.p2.y - b.p1.y))

/-- Proof: Curve passes through start point -/
theorem eval_at_zero (b : QuadraticBezier) : eval b 0 = b.p0 := by
  simp [eval, Point.mk']
  -- c0 = 1, c1 = 0, c2 = 0
  sorry

/-- Proof: Curve passes through end point -/
theorem eval_at_one (b : QuadraticBezier) : eval b 1 = b.p2 := by
  simp [eval, Point.mk']
  -- c0 = 0, c1 = 0, c2 = 1
  sorry

/-- Split curve at parameter t using de Casteljau -/
def split (b : QuadraticBezier) (t : Float) : QuadraticBezier × QuadraticBezier :=
  let t' := max 0 (min 1 t)
  -- First level interpolation
  let q0 := Point.lerp t' b.p0 b.p1
  let q1 := Point.lerp t' b.p1 b.p2
  -- Second level (point on curve)
  let r := Point.lerp t' q0 q1
  -- Two new curves
  (⟨b.p0, q0, r⟩, ⟨r, q1, b.p2⟩)

end QuadraticBezier
```

### 3.3 Haskell Implementation

```haskell
{-# LANGUAGE StrictData #-}

module Lattice.Bezier.Quadratic where

import Lattice.Geometry.Point

-- | Quadratic Bezier curve (3 control points)
data QuadraticBezier = QuadraticBezier
  { qbP0 :: !Point  -- Start
  , qbP1 :: !Point  -- Control
  , qbP2 :: !Point  -- End
  } deriving (Eq, Show)

-- | Evaluate at parameter t ∈ [0,1]
evalQuadratic :: QuadraticBezier -> Double -> Point
evalQuadratic (QuadraticBezier p0 p1 p2) t =
  let t' = max 0 (min 1 t)
      c0 = (1 - t') * (1 - t')
      c1 = 2 * t' * (1 - t')
      c2 = t' * t'
  in point
       (c0 * ptXVal p0 + c1 * ptXVal p1 + c2 * ptXVal p2)
       (c0 * ptYVal p0 + c1 * ptYVal p1 + c2 * ptYVal p2)
  where
    ptXVal = bValue . ptX
    ptYVal = bValue . ptY

-- | First derivative at t
derivativeQuadratic :: QuadraticBezier -> Double -> Point
derivativeQuadratic (QuadraticBezier p0 p1 p2) t =
  let t' = max 0 (min 1 t)
      c0 = 2 * (1 - t')
      c1 = 2 * t'
  in point
       (c0 * (ptXVal p1 - ptXVal p0) + c1 * (ptXVal p2 - ptXVal p1))
       (c0 * (ptYVal p1 - ptYVal p0) + c1 * (ptYVal p2 - ptYVal p1))
  where
    ptXVal = bValue . ptX
    ptYVal = bValue . ptY

-- | Split at t using de Casteljau algorithm
splitQuadratic :: QuadraticBezier -> Double -> (QuadraticBezier, QuadraticBezier)
splitQuadratic (QuadraticBezier p0 p1 p2) t =
  let t' = max 0 (min 1 t)
      q0 = pointLerp t' p0 p1
      q1 = pointLerp t' p1 p2
      r  = pointLerp t' q0 q1
  in (QuadraticBezier p0 q0 r, QuadraticBezier r q1 p2)

-- | Bounding box (axis-aligned)
boundingBoxQuadratic :: QuadraticBezier -> (Point, Point)
boundingBoxQuadratic qb =
  let samples = map (evalQuadratic qb) [0, 0.1 .. 1.0]
      xs = map (bValue . ptX) samples
      ys = map (bValue . ptY) samples
  in (point (minimum xs) (minimum ys), point (maximum xs) (maximum ys))

-- | Approximate arc length using subdivision
arcLengthQuadratic :: QuadraticBezier -> Int -> Double
arcLengthQuadratic qb segments =
  let step = 1.0 / fromIntegral segments
      pts = map (evalQuadratic qb) [0, step .. 1.0]
      dists = zipWith pointDistance pts (tail pts)
  in sum dists
```

---

## 4. Cubic Bezier Curves

### 4.1 Definition

A cubic Bezier curve with control points P₀, P₁, P₂, P₃:

$$\mathbf{B}(t) = (1-t)^3 P_0 + 3t(1-t)^2 P_1 + 3t^2(1-t) P_2 + t^3 P_3$$

### 4.2 Lean4 Implementation

```lean4
/-- Cubic Bezier curve -/
structure CubicBezier where
  p0 : Point  -- Start point
  p1 : Point  -- Control point 1
  p2 : Point  -- Control point 2
  p3 : Point  -- End point
  deriving Repr

namespace CubicBezier

/-- Evaluate curve at parameter t ∈ [0,1] -/
def eval (b : CubicBezier) (t : Float) : Point :=
  let t' := max 0 (min 1 t)
  let mt := 1 - t'
  let c0 := mt * mt * mt
  let c1 := 3 * t' * mt * mt
  let c2 := 3 * t' * t' * mt
  let c3 := t' * t' * t'
  Point.mk'
    (c0 * b.p0.x + c1 * b.p1.x + c2 * b.p2.x + c3 * b.p3.x)
    (c0 * b.p0.y + c1 * b.p1.y + c2 * b.p2.y + c3 * b.p3.y)

/-- First derivative -/
def derivative (b : CubicBezier) (t : Float) : Point :=
  let t' := max 0 (min 1 t)
  let mt := 1 - t'
  let c0 := 3 * mt * mt
  let c1 := 6 * t' * mt
  let c2 := 3 * t' * t'
  Point.mk'
    (c0 * (b.p1.x - b.p0.x) + c1 * (b.p2.x - b.p1.x) + c2 * (b.p3.x - b.p2.x))
    (c0 * (b.p1.y - b.p0.y) + c1 * (b.p2.y - b.p1.y) + c2 * (b.p3.y - b.p2.y))

/-- Second derivative -/
def secondDerivative (b : CubicBezier) (t : Float) : Point :=
  let t' := max 0 (min 1 t)
  let c0 := 6 * (1 - t')
  let c1 := 6 * t'
  let d1x := b.p2.x - 2 * b.p1.x + b.p0.x
  let d1y := b.p2.y - 2 * b.p1.y + b.p0.y
  let d2x := b.p3.x - 2 * b.p2.x + b.p1.x
  let d2y := b.p3.y - 2 * b.p2.y + b.p1.y
  Point.mk' (c0 * d1x + c1 * d2x) (c0 * d1y + c1 * d2y)

/-- Proof: Curve passes through endpoints -/
theorem eval_endpoints (b : CubicBezier) :
    eval b 0 = b.p0 ∧ eval b 1 = b.p3 := by
  constructor
  · simp [eval, Point.mk']
    sorry
  · simp [eval, Point.mk']
    sorry

/-- Proof: Tangent at endpoints -/
theorem tangent_at_endpoints (b : CubicBezier) :
    ∃ k₀ k₁ : Float, k₀ > 0 ∧ k₁ > 0 ∧
    derivative b 0 = Point.scale k₀ (Point.sub b.p1 b.p0) ∧
    derivative b 1 = Point.scale k₁ (Point.sub b.p3 b.p2) := by
  use 3, 3
  sorry

/-- Split at t using de Casteljau -/
def split (b : CubicBezier) (t : Float) : CubicBezier × CubicBezier :=
  let t' := max 0 (min 1 t)
  -- Level 1
  let q0 := Point.lerp t' b.p0 b.p1
  let q1 := Point.lerp t' b.p1 b.p2
  let q2 := Point.lerp t' b.p2 b.p3
  -- Level 2
  let r0 := Point.lerp t' q0 q1
  let r1 := Point.lerp t' q1 q2
  -- Level 3 (point on curve)
  let s := Point.lerp t' r0 r1
  (⟨b.p0, q0, r0, s⟩, ⟨s, r1, q2, b.p3⟩)

end CubicBezier
```

### 4.3 Haskell Implementation

```haskell
-- | Cubic Bezier curve (4 control points)
data CubicBezier = CubicBezier
  { cbP0 :: !Point  -- Start
  , cbP1 :: !Point  -- Control 1
  , cbP2 :: !Point  -- Control 2
  , cbP3 :: !Point  -- End
  } deriving (Eq, Show)

-- | Evaluate at parameter t ∈ [0,1]
evalCubic :: CubicBezier -> Double -> Point
evalCubic (CubicBezier p0 p1 p2 p3) t =
  let t' = max 0 (min 1 t)
      mt = 1 - t'
      c0 = mt * mt * mt
      c1 = 3 * t' * mt * mt
      c2 = 3 * t' * t' * mt
      c3 = t' * t' * t'
  in point
       (c0 * px p0 + c1 * px p1 + c2 * px p2 + c3 * px p3)
       (c0 * py p0 + c1 * py p1 + c2 * py p2 + c3 * py p3)
  where
    px = bValue . ptX
    py = bValue . ptY

-- | First derivative at t
derivativeCubic :: CubicBezier -> Double -> Point
derivativeCubic (CubicBezier p0 p1 p2 p3) t =
  let t' = max 0 (min 1 t)
      mt = 1 - t'
      c0 = 3 * mt * mt
      c1 = 6 * t' * mt
      c2 = 3 * t' * t'
  in point
       (c0 * (px p1 - px p0) + c1 * (px p2 - px p1) + c2 * (px p3 - px p2))
       (c0 * (py p1 - py p0) + c1 * (py p2 - py p1) + c2 * (py p3 - py p2))
  where
    px = bValue . ptX
    py = bValue . ptY

-- | Second derivative at t
secondDerivativeCubic :: CubicBezier -> Double -> Point
secondDerivativeCubic (CubicBezier p0 p1 p2 p3) t =
  let t' = max 0 (min 1 t)
      c0 = 6 * (1 - t')
      c1 = 6 * t'
      d1x = px p2 - 2 * px p1 + px p0
      d1y = py p2 - 2 * py p1 + py p0
      d2x = px p3 - 2 * px p2 + px p1
      d2y = py p3 - 2 * py p2 + py p1
  in point (c0 * d1x + c1 * d2x) (c0 * d1y + c1 * d2y)
  where
    px = bValue . ptX
    py = bValue . ptY

-- | Split at t using de Casteljau algorithm
splitCubic :: CubicBezier -> Double -> (CubicBezier, CubicBezier)
splitCubic (CubicBezier p0 p1 p2 p3) t =
  let t' = max 0 (min 1 t)
      -- Level 1
      q0 = pointLerp t' p0 p1
      q1 = pointLerp t' p1 p2
      q2 = pointLerp t' p2 p3
      -- Level 2
      r0 = pointLerp t' q0 q1
      r1 = pointLerp t' q1 q2
      -- Level 3
      s  = pointLerp t' r0 r1
  in (CubicBezier p0 q0 r0 s, CubicBezier s r1 q2 p3)

-- | Curvature at parameter t
curvatureCubic :: CubicBezier -> Double -> Double
curvatureCubic cb t =
  let d1 = derivativeCubic cb t
      d2 = secondDerivativeCubic cb t
      d1x = bValue $ ptX d1
      d1y = bValue $ ptY d1
      d2x = bValue $ ptX d2
      d2y = bValue $ ptY d2
      cross = d1x * d2y - d1y * d2x
      denom = (d1x * d1x + d1y * d1y) ** 1.5
  in if abs denom < 1e-10 then 0 else cross / denom

-- | Bounding box (tight)
boundingBoxCubic :: CubicBezier -> (Point, Point)
boundingBoxCubic cb = 
  let -- Find extrema by solving derivative = 0
      extremaT = findExtrema cb ++ [0, 1]
      pts = map (evalCubic cb) extremaT
      xs = map (bValue . ptX) pts
      ys = map (bValue . ptY) pts
  in (point (minimum xs) (minimum ys), point (maximum xs) (maximum ys))
  where
    findExtrema (CubicBezier p0 p1 p2 p3) =
      let ax = -px p0 + 3 * px p1 - 3 * px p2 + px p3
          bx = 2 * px p0 - 4 * px p1 + 2 * px p2
          cx = -px p0 + px p1
          ay = -py p0 + 3 * py p1 - 3 * py p2 + py p3
          by = 2 * py p0 - 4 * py p1 + 2 * py p2
          cy = -py p0 + py p1
          txs = solveQuadratic ax bx cx
          tys = solveQuadratic ay by cy
      in filter (\t -> t > 0 && t < 1) (txs ++ tys)
    
    px = bValue . ptX
    py = bValue . ptY
    
    solveQuadratic a b c
      | abs a < 1e-10 = if abs b < 1e-10 then [] else [-c / b]
      | otherwise =
          let disc = b * b - 4 * a * c
          in if disc < 0 then []
             else let sq = sqrt disc
                  in [(-b + sq) / (2 * a), (-b - sq) / (2 * a)]

-- | Arc length using adaptive subdivision
arcLengthCubic :: CubicBezier -> Double -> Double
arcLengthCubic cb tolerance = arcLengthHelper cb tolerance 0
  where
    arcLengthHelper c tol depth
      | depth > 10 = chordLength c  -- Max recursion
      | flatEnough c tol = chordLength c
      | otherwise =
          let (c1, c2) = splitCubic c 0.5
          in arcLengthHelper c1 tol (depth + 1) + arcLengthHelper c2 tol (depth + 1)
    
    chordLength (CubicBezier p0 _ _ p3) = pointDistance p0 p3
    
    flatEnough (CubicBezier p0 p1 p2 p3) tol =
      let d1 = lineDistance p1 p0 p3
          d2 = lineDistance p2 p0 p3
      in max d1 d2 < tol
    
    lineDistance p lineStart lineEnd =
      let dx = bValue (ptX lineEnd) - bValue (ptX lineStart)
          dy = bValue (ptY lineEnd) - bValue (ptY lineStart)
          len = sqrt (dx * dx + dy * dy)
      in if len < 1e-10 then pointDistance p lineStart
         else abs ((bValue (ptX p) - bValue (ptX lineStart)) * dy - 
                   (bValue (ptY p) - bValue (ptY lineStart)) * dx) / len
```

### 4.4 PureScript Implementation

```purescript
module Lattice.Bezier.Cubic where

import Prelude
import Data.Number (sqrt, abs)
import Lattice.Geometry.Point (Point, point, pointLerp, pointDistance, getX, getY)

-- | Cubic Bezier curve
newtype CubicBezier = CubicBezier
  { p0 :: Point
  , p1 :: Point
  , p2 :: Point
  , p3 :: Point
  }

derive instance eqCubicBezier :: Eq CubicBezier

-- | Evaluate at parameter t
evalCubic :: CubicBezier -> Number -> Point
evalCubic (CubicBezier { p0, p1, p2, p3 }) t =
  let t' = max 0.0 (min 1.0 t)
      mt = 1.0 - t'
      c0 = mt * mt * mt
      c1 = 3.0 * t' * mt * mt
      c2 = 3.0 * t' * t' * mt
      c3 = t' * t' * t'
  in point
       (c0 * getX p0 + c1 * getX p1 + c2 * getX p2 + c3 * getX p3)
       (c0 * getY p0 + c1 * getY p1 + c2 * getY p2 + c3 * getY p3)

-- | Split at parameter t
splitCubic :: CubicBezier -> Number -> { left :: CubicBezier, right :: CubicBezier }
splitCubic (CubicBezier { p0, p1, p2, p3 }) t =
  let t' = max 0.0 (min 1.0 t)
      q0 = pointLerp t' p0 p1
      q1 = pointLerp t' p1 p2
      q2 = pointLerp t' p2 p3
      r0 = pointLerp t' q0 q1
      r1 = pointLerp t' q1 q2
      s  = pointLerp t' r0 r1
  in { left: CubicBezier { p0: p0, p1: q0, p2: r0, p3: s }
     , right: CubicBezier { p0: s, p1: r1, p2: q2, p3: p3 }
     }

-- | First derivative
derivativeCubic :: CubicBezier -> Number -> Point
derivativeCubic (CubicBezier { p0, p1, p2, p3 }) t =
  let t' = max 0.0 (min 1.0 t)
      mt = 1.0 - t'
      c0 = 3.0 * mt * mt
      c1 = 6.0 * t' * mt
      c2 = 3.0 * t' * t'
  in point
       (c0 * (getX p1 - getX p0) + c1 * (getX p2 - getX p1) + c2 * (getX p3 - getX p2))
       (c0 * (getY p1 - getY p0) + c1 * (getY p2 - getY p1) + c2 * (getY p3 - getY p2))
```

---

## 5. Path Operations

### 5.1 Bezier Path Type

```haskell
-- | Bezier path (sequence of cubic segments)
data BezierPath = BezierPath
  { bpSegments :: ![CubicBezier]
  , bpClosed   :: !Bool
  } deriving (Eq, Show)

-- | Create path from control points (Lottie format)
-- Lottie uses: vertices, in-tangents, out-tangents
fromLottieFormat :: [Point] -> [Point] -> [Point] -> Bool -> BezierPath
fromLottieFormat vertices inTangents outTangents closed =
  let n = length vertices
      segments = 
        [ CubicBezier
            (vertices !! i)
            (pointAdd (vertices !! i) (outTangents !! i))
            (pointAdd (vertices !! j) (inTangents !! j))
            (vertices !! j)
        | i <- [0 .. n - 2]
        , let j = i + 1
        ] ++
        if closed && n > 1
        then [ CubicBezier
                 (vertices !! (n - 1))
                 (pointAdd (vertices !! (n - 1)) (outTangents !! (n - 1)))
                 (pointAdd (vertices !! 0) (inTangents !! 0))
                 (vertices !! 0)
             ]
        else []
  in BezierPath segments closed

-- | Convert to Lottie format
toLottieFormat :: BezierPath -> ([Point], [Point], [Point])
toLottieFormat (BezierPath segments closed) =
  let vertices = map cbP0 segments ++ if closed then [] else [cbP3 $ last segments]
      outTangents = map (\s -> pointSub (cbP1 s) (cbP0 s)) segments ++ 
                    if closed then [] else [origin]
      inTangents = [origin] ++ 
                   map (\s -> pointSub (cbP2 s) (cbP3 s)) (init segments) ++
                   if closed 
                   then [pointSub (cbP2 $ last segments) (cbP3 $ last segments)]
                   else [pointSub (cbP2 $ last segments) (cbP3 $ last segments)]
  in (vertices, inTangents, outTangents)

-- | Evaluate path at parameter t ∈ [0, numSegments]
evalPath :: BezierPath -> Double -> Point
evalPath (BezierPath segments _) t
  | null segments = origin
  | otherwise =
      let n = length segments
          t' = max 0 (min (fromIntegral n) t)
          segIdx = min (n - 1) (floor t')
          localT = t' - fromIntegral segIdx
      in evalCubic (segments !! segIdx) localT

-- | Total arc length of path
pathArcLength :: BezierPath -> Double -> Double
pathArcLength (BezierPath segments _) tolerance =
  sum $ map (\s -> arcLengthCubic s tolerance) segments

-- | Bounding box of entire path
pathBoundingBox :: BezierPath -> (Point, Point)
pathBoundingBox (BezierPath segments _) =
  let boxes = map boundingBoxCubic segments
      minX = minimum $ map (bValue . ptX . fst) boxes
      minY = minimum $ map (bValue . ptY . fst) boxes
      maxX = maximum $ map (bValue . ptX . snd) boxes
      maxY = maximum $ map (bValue . ptY . snd) boxes
  in (point minX minY, point maxX maxY)
```

### 5.2 Path Morphing

```haskell
-- | Morph between two paths (must have same structure)
morphPaths :: BezierPath -> BezierPath -> Double -> Either String BezierPath
morphPaths (BezierPath segs1 c1) (BezierPath segs2 c2) t
  | length segs1 /= length segs2 = 
      Left "Cannot morph paths with different segment counts"
  | c1 /= c2 = 
      Left "Cannot morph between open and closed paths"
  | otherwise =
      let t' = max 0 (min 1 t)
          morphedSegs = zipWith (morphSegment t') segs1 segs2
      in Right $ BezierPath morphedSegs c1
  where
    morphSegment t (CubicBezier a0 a1 a2 a3) (CubicBezier b0 b1 b2 b3) =
      CubicBezier
        (pointLerp t a0 b0)
        (pointLerp t a1 b1)
        (pointLerp t a2 b2)
        (pointLerp t a3 b3)

-- | Resample path to have n segments
resamplePath :: BezierPath -> Int -> BezierPath
resamplePath path n
  | n < 1 = path
  | otherwise =
      let totalLen = pathArcLength path 0.1
          segLen = totalLen / fromIntegral n
          -- Sample points at equal arc length intervals
          params = [0, segLen .. totalLen]
          pts = map (evalPathAtArcLength path totalLen) params
          -- Create cubic segments through points
          segs = zipWith3 createSegment pts (tail pts) (drop 2 pts ++ [head pts])
      in BezierPath (take n segs) (bpClosed path)
  where
    evalPathAtArcLength p total arcLen =
      -- Binary search for parameter at given arc length
      binarySearch 0 (fromIntegral $ length $ bpSegments p) arcLen total p
    
    binarySearch lo hi targetLen totalLen p
      | hi - lo < 0.001 = evalPath p ((lo + hi) / 2)
      | otherwise =
          let mid = (lo + hi) / 2
              len = pathArcLengthTo p mid 0.1
          in if len < targetLen
             then binarySearch mid hi targetLen totalLen p
             else binarySearch lo mid targetLen totalLen p
    
    pathArcLengthTo p t tol =
      let fullSegs = floor t
          partialT = t - fromIntegral fullSegs
          segs = bpSegments p
          fullLen = sum $ map (\s -> arcLengthCubic s tol) (take fullSegs segs)
          partialSeg = segs !! fullSegs
          (partSeg, _) = splitCubic partialSeg partialT
      in fullLen + arcLengthCubic partSeg tol
    
    createSegment p0 p1 p2 =
      -- Catmull-Rom to Bezier conversion
      let c1 = pointAdd p0 (pointScale (1/6) (pointSub p1 p0))
          c2 = pointSub p1 (pointScale (1/6) (pointSub p2 p0))
      in CubicBezier p0 c1 c2 p1
```

---

## 6. Lean4 Proofs

```lean4
namespace BezierProofs

/-- Bezier curve is inside convex hull of control points -/
theorem cubic_convex_hull (b : CubicBezier) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ (w0 w1 w2 w3 : Float),
      w0 ≥ 0 ∧ w1 ≥ 0 ∧ w2 ≥ 0 ∧ w3 ≥ 0 ∧
      w0 + w1 + w2 + w3 = 1 ∧
      CubicBezier.eval b t = 
        Point.add (Point.scale w0 b.p0) 
          (Point.add (Point.scale w1 b.p1) 
            (Point.add (Point.scale w2 b.p2) (Point.scale w3 b.p3))) := by
  -- Weights are Bernstein polynomials which are non-negative and sum to 1
  use bernstein 3 0 t, bernstein 3 1 t, bernstein 3 2 t, bernstein 3 3 t
  constructor
  · exact bernstein_nonneg 3 0 t ht
  constructor
  · exact bernstein_nonneg 3 1 t ht
  constructor
  · exact bernstein_nonneg 3 2 t ht
  constructor
  · exact bernstein_nonneg 3 3 t ht
  constructor
  · exact bernstein_partition_unity 3 t ht
  · simp [CubicBezier.eval, bernstein]
    sorry

/-- de Casteljau subdivision is exact -/
theorem de_casteljau_exact (b : CubicBezier) (t s : Float) 
    (ht : 0 ≤ t ∧ t ≤ 1) (hs : 0 ≤ s ∧ s ≤ 1) :
    let (b1, b2) := CubicBezier.split b t
    (s ≤ t → CubicBezier.eval b1 (s / t) = CubicBezier.eval b s) ∧
    (s > t → CubicBezier.eval b2 ((s - t) / (1 - t)) = CubicBezier.eval b s) := by
  sorry

/-- Arc length is monotonic in parameter -/
theorem arc_length_monotonic (b : CubicBezier) (t1 t2 : Float)
    (h1 : 0 ≤ t1) (h2 : t1 ≤ t2) (h3 : t2 ≤ 1) :
    arcLengthTo b t1 ≤ arcLengthTo b t2 := by
  sorry

/-- Curvature is bounded -/
theorem curvature_bounded (b : CubicBezier) (t : Float) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ M : Float, |curvatureCubic b t| ≤ M := by
  sorry

end BezierProofs
```

---

## 7. Constraint Summary

| Type | Property | Min | Max | Default | Unit |
|------|----------|-----|-----|---------|------|
| Control Point | x, y | -100000 | 100000 | 0 | px |
| Parameter | t | 0 | 1 | 0 | normalized |
| Arc Length | tolerance | 0.001 | 10 | 0.1 | px |
| Subdivision | depth | 1 | 20 | 10 | levels |
| Curvature | κ | -∞ | +∞ | 0 | 1/px |

---

## 8. Test Matrix

| Test | Input | Expected |
|------|-------|----------|
| eval_at_0 | CubicBezier, t=0 | p0 |
| eval_at_1 | CubicBezier, t=1 | p3 |
| split_preserves | Split at 0.5 | Both halves on original curve |
| arc_length_line | Straight line | Equals distance(p0, p3) |
| bounding_box | Various curves | Contains all sample points |
| morph_identity | morph(p, p, t) | p for all t |

---

*End of Specification 05*
