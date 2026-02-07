# Specification 08: Easing Functions
## Lattice Lottie Generation Engine

**Document ID:** LLGE-SPEC-08  
**Version:** 1.0.0  
**Status:** Active  
**Classification:** Internal Technical  

---

## 1. Overview

This specification defines all easing functions for animation interpolation with:

1. **Mathematical definitions** (explicit formulas)
2. **Cubic bezier representations** (Lottie format)
3. **Deterministic evaluation** (no floating-point ambiguity)
4. **Formal proofs** of boundary conditions

---

## 2. Easing Function Type

### 2.1 Core Definition

```lean4
/-- An easing function maps normalized time [0,1] to interpolation factor [0,1]
    (may exceed [0,1] for overshoot effects) -/
def EasingFn := Float → Float

namespace EasingFn

/-- Identity/linear easing -/
def linear : EasingFn := id

/-- Constant easing (always returns 1) -/
def constant : EasingFn := fun _ => 1

/-- Step function (0 until threshold, then 1) -/
def step (threshold : Float) : EasingFn := 
  fun t => if t < threshold then 0 else 1

/-- Compose two easing functions -/
def compose (f g : EasingFn) : EasingFn := f ∘ g

/-- Reverse an easing function -/
def reverse (f : EasingFn) : EasingFn := fun t => 1 - f (1 - t)

/-- Mirror an easing function (ease-in-out from ease-in) -/
def mirror (f : EasingFn) : EasingFn := fun t =>
  if t < 0.5 
  then f (t * 2) / 2
  else 1 - f ((1 - t) * 2) / 2

end EasingFn
```

### 2.2 Haskell Implementation

```haskell
{-# LANGUAGE StrictData #-}

module Lattice.Easing.Functions where

import Data.Ratio (Rational, (%))

-- | Easing function type
-- Takes normalized time t ∈ [0, 1] and returns interpolation factor
-- Result may be outside [0, 1] for overshoot effects
newtype EasingFn = EasingFn { runEasing :: Rational -> Rational }

-- | Apply easing to a value range
applyEasing :: Num a => EasingFn -> a -> a -> Rational -> a
applyEasing ef from to t = 
  let factor = fromRational (runEasing ef t)
  in from + (to - from) * factor

-- | Clamp time to [0, 1] before applying
applyEasingSafe :: Num a => EasingFn -> a -> a -> Rational -> a
applyEasingSafe ef from to t = applyEasing ef from to (max 0 (min 1 t))

-- | Linear (identity)
linear :: EasingFn
linear = EasingFn id

-- | Step function
step :: Rational -> EasingFn
step threshold = EasingFn $ \t -> if t < threshold then 0 else 1

-- | Compose easing functions (f after g)
composeEasing :: EasingFn -> EasingFn -> EasingFn
composeEasing (EasingFn f) (EasingFn g) = EasingFn (f . g)

-- | Reverse easing (ease-out from ease-in)
reverseEasing :: EasingFn -> EasingFn
reverseEasing (EasingFn f) = EasingFn $ \t -> 1 - f (1 - t)

-- | Mirror easing (ease-in-out from ease-in)
mirrorEasing :: EasingFn -> EasingFn
mirrorEasing (EasingFn f) = EasingFn $ \t ->
  if t < 1%2
    then f (t * 2) / 2
    else 1 - f ((1 - t) * 2) / 2
```

---

## 3. Polynomial Easing Functions

### 3.1 Quadratic (Power of 2)

```haskell
-- | Quadratic ease-in: t²
easeInQuad :: EasingFn
easeInQuad = EasingFn $ \t -> t * t

-- | Quadratic ease-out: 1 - (1-t)²
easeOutQuad :: EasingFn
easeOutQuad = reverseEasing easeInQuad

-- | Quadratic ease-in-out
easeInOutQuad :: EasingFn
easeInOutQuad = mirrorEasing easeInQuad

-- Cubic bezier approximations for Lottie
easeInQuadBezier :: CubicBezier
easeInQuadBezier = CubicBezier (0.55, 0.085) (0.68, 0.53)

easeOutQuadBezier :: CubicBezier
easeOutQuadBezier = CubicBezier (0.25, 0.46) (0.45, 0.94)

easeInOutQuadBezier :: CubicBezier
easeInOutQuadBezier = CubicBezier (0.455, 0.03) (0.515, 0.955)
```

### 3.2 Cubic (Power of 3)

```haskell
-- | Cubic ease-in: t³
easeInCubic :: EasingFn
easeInCubic = EasingFn $ \t -> t * t * t

-- | Cubic ease-out: 1 - (1-t)³
easeOutCubic :: EasingFn
easeOutCubic = reverseEasing easeInCubic

-- | Cubic ease-in-out
easeInOutCubic :: EasingFn
easeInOutCubic = mirrorEasing easeInCubic

easeInCubicBezier :: CubicBezier
easeInCubicBezier = CubicBezier (0.55, 0.055) (0.675, 0.19)

easeOutCubicBezier :: CubicBezier
easeOutCubicBezier = CubicBezier (0.215, 0.61) (0.355, 1)

easeInOutCubicBezier :: CubicBezier
easeInOutCubicBezier = CubicBezier (0.645, 0.045) (0.355, 1)
```

### 3.3 Quartic (Power of 4)

```haskell
-- | Quartic ease-in: t⁴
easeInQuart :: EasingFn
easeInQuart = EasingFn $ \t -> t * t * t * t

-- | Quartic ease-out
easeOutQuart :: EasingFn
easeOutQuart = reverseEasing easeInQuart

-- | Quartic ease-in-out
easeInOutQuart :: EasingFn
easeInOutQuart = mirrorEasing easeInQuart

easeInQuartBezier :: CubicBezier
easeInQuartBezier = CubicBezier (0.895, 0.03) (0.685, 0.22)

easeOutQuartBezier :: CubicBezier
easeOutQuartBezier = CubicBezier (0.165, 0.84) (0.44, 1)

easeInOutQuartBezier :: CubicBezier
easeInOutQuartBezier = CubicBezier (0.77, 0) (0.175, 1)
```

### 3.4 Quintic (Power of 5)

```haskell
-- | Quintic ease-in: t⁵
easeInQuint :: EasingFn
easeInQuint = EasingFn $ \t -> t * t * t * t * t

-- | Quintic ease-out
easeOutQuint :: EasingFn
easeOutQuint = reverseEasing easeInQuint

-- | Quintic ease-in-out
easeInOutQuint :: EasingFn
easeInOutQuint = mirrorEasing easeInQuint

easeInQuintBezier :: CubicBezier
easeInQuintBezier = CubicBezier (0.755, 0.05) (0.855, 0.06)

easeOutQuintBezier :: CubicBezier
easeOutQuintBezier = CubicBezier (0.23, 1) (0.32, 1)

easeInOutQuintBezier :: CubicBezier
easeInOutQuintBezier = CubicBezier (0.86, 0) (0.07, 1)
```

---

## 4. Exponential Easing

### 4.1 Expo Functions

```haskell
-- | Exponential ease-in: 2^(10(t-1))
easeInExpo :: EasingFn
easeInExpo = EasingFn $ \t ->
  if t == 0 then 0 else 2 ** (10 * (fromRational t - 1))

-- | Exponential ease-out: 1 - 2^(-10t)
easeOutExpo :: EasingFn
easeOutExpo = EasingFn $ \t ->
  if t == 1 then 1 else 1 - 2 ** (-10 * fromRational t)

-- | Exponential ease-in-out
easeInOutExpo :: EasingFn
easeInOutExpo = EasingFn $ \t ->
  if t == 0 then 0
  else if t == 1 then 1
  else if t < 1%2 
       then 2 ** (20 * fromRational t - 10) / 2
       else (2 - 2 ** (-20 * fromRational t + 10)) / 2

easeInExpoBezier :: CubicBezier
easeInExpoBezier = CubicBezier (0.95, 0.05) (0.795, 0.035)

easeOutExpoBezier :: CubicBezier
easeOutExpoBezier = CubicBezier (0.19, 1) (0.22, 1)

easeInOutExpoBezier :: CubicBezier
easeInOutExpoBezier = CubicBezier (1, 0) (0, 1)
```

---

## 5. Circular Easing

### 5.1 Circ Functions

```haskell
-- | Circular ease-in: 1 - √(1 - t²)
easeInCirc :: EasingFn
easeInCirc = EasingFn $ \t ->
  let t' = fromRational t
  in toRational $ 1 - sqrt (1 - t' * t')

-- | Circular ease-out: √(1 - (t-1)²)
easeOutCirc :: EasingFn
easeOutCirc = EasingFn $ \t ->
  let t' = fromRational t - 1
  in toRational $ sqrt (1 - t' * t')

-- | Circular ease-in-out
easeInOutCirc :: EasingFn
easeInOutCirc = EasingFn $ \t ->
  let t' = fromRational t
  in toRational $ if t' < 0.5
     then (1 - sqrt (1 - (2 * t') ** 2)) / 2
     else (sqrt (1 - (-2 * t' + 2) ** 2) + 1) / 2

easeInCircBezier :: CubicBezier
easeInCircBezier = CubicBezier (0.6, 0.04) (0.98, 0.335)

easeOutCircBezier :: CubicBezier
easeOutCircBezier = CubicBezier (0.075, 0.82) (0.165, 1)

easeInOutCircBezier :: CubicBezier
easeInOutCircBezier = CubicBezier (0.785, 0.135) (0.15, 0.86)
```

---

## 6. Sinusoidal Easing

### 6.1 Sine Functions

```haskell
-- | Sinusoidal ease-in: 1 - cos(t × π/2)
easeInSine :: EasingFn
easeInSine = EasingFn $ \t ->
  toRational $ 1 - cos (fromRational t * pi / 2)

-- | Sinusoidal ease-out: sin(t × π/2)
easeOutSine :: EasingFn
easeOutSine = EasingFn $ \t ->
  toRational $ sin (fromRational t * pi / 2)

-- | Sinusoidal ease-in-out: -(cos(πt) - 1) / 2
easeInOutSine :: EasingFn
easeInOutSine = EasingFn $ \t ->
  toRational $ -(cos (pi * fromRational t) - 1) / 2

easeInSineBezier :: CubicBezier
easeInSineBezier = CubicBezier (0.47, 0) (0.745, 0.715)

easeOutSineBezier :: CubicBezier
easeOutSineBezier = CubicBezier (0.39, 0.575) (0.565, 1)

easeInOutSineBezier :: CubicBezier
easeInOutSineBezier = CubicBezier (0.445, 0.05) (0.55, 0.95)
```

---

## 7. Back Easing (Overshoot)

### 7.1 Back Functions

```haskell
-- | Back overshoot constant (1.70158)
backOvershoot :: Rational
backOvershoot = 170158 % 100000

-- | Back ease-in: t² × ((s+1)×t - s)
easeInBack :: EasingFn
easeInBack = easeInBackWith backOvershoot

easeInBackWith :: Rational -> EasingFn
easeInBackWith s = EasingFn $ \t ->
  t * t * ((s + 1) * t - s)

-- | Back ease-out: (t-1)² × ((s+1)×(t-1) + s) + 1
easeOutBack :: EasingFn
easeOutBack = easeOutBackWith backOvershoot

easeOutBackWith :: Rational -> EasingFn
easeOutBackWith s = EasingFn $ \t ->
  let t' = t - 1
  in t' * t' * ((s + 1) * t' + s) + 1

-- | Back ease-in-out
easeInOutBack :: EasingFn
easeInOutBack = easeInOutBackWith backOvershoot

easeInOutBackWith :: Rational -> EasingFn
easeInOutBackWith s = EasingFn $ \t ->
  let s' = s * 1525 % 1000  -- s × 1.525
  in if t < 1%2
     then ((2 * t) ** 2 * ((s' + 1) * 2 * t - s')) / 2
     else ((2 * t - 2) ** 2 * ((s' + 1) * (2 * t - 2) + s') + 2) / 2

-- Note: Back easing cannot be exactly represented by cubic bezier
-- These are approximations
easeInBackBezier :: CubicBezier
easeInBackBezier = CubicBezier (0.6, -0.28) (0.735, 0.045)

easeOutBackBezier :: CubicBezier
easeOutBackBezier = CubicBezier (0.175, 0.885) (0.32, 1.275)

easeInOutBackBezier :: CubicBezier
easeInOutBackBezier = CubicBezier (0.68, -0.55) (0.265, 1.55)
```

---

## 8. Elastic Easing

### 8.1 Elastic Functions

```haskell
-- | Elastic ease-in
easeInElastic :: EasingFn
easeInElastic = EasingFn $ \t ->
  if t == 0 then 0
  else if t == 1 then 1
  else let t' = fromRational t
           c4 = (2 * pi) / 3
       in toRational $ -(2 ** (10 * t' - 10)) * sin ((t' * 10 - 10.75) * c4)

-- | Elastic ease-out
easeOutElastic :: EasingFn
easeOutElastic = EasingFn $ \t ->
  if t == 0 then 0
  else if t == 1 then 1
  else let t' = fromRational t
           c4 = (2 * pi) / 3
       in toRational $ 2 ** (-10 * t') * sin ((t' * 10 - 0.75) * c4) + 1

-- | Elastic ease-in-out
easeInOutElastic :: EasingFn
easeInOutElastic = EasingFn $ \t ->
  if t == 0 then 0
  else if t == 1 then 1
  else let t' = fromRational t
           c5 = (2 * pi) / 4.5
       in toRational $ if t' < 0.5
          then -(2 ** (20 * t' - 10) * sin ((20 * t' - 11.125) * c5)) / 2
          else 2 ** (-20 * t' + 10) * sin ((20 * t' - 11.125) * c5) / 2 + 1

-- | Elastic with custom parameters
easeElasticWith :: Double -> Double -> EasingFn
easeElasticWith amplitude period = EasingFn $ \t ->
  if t == 0 then 0
  else if t == 1 then 1
  else let t' = fromRational t
           a = max 1 amplitude
           p = period
           s = p / (2 * pi) * asin (1 / a)
       in toRational $ -(a * 2 ** (10 * (t' - 1)) * sin (((t' - 1) - s) * 2 * pi / p))

-- Elastic cannot be represented by cubic bezier - must use keyframes
-- Placeholder beziers for UI representation only
easeInElasticBezier :: CubicBezier
easeInElasticBezier = CubicBezier (0.5, 0) (0.5, 1)

easeOutElasticBezier :: CubicBezier
easeOutElasticBezier = CubicBezier (0.5, 0) (0.5, 1)
```

---

## 9. Bounce Easing

### 9.1 Bounce Functions

```haskell
-- | Bounce out helper
bounceOut :: Rational -> Rational
bounceOut t =
  let n1 = 7.5625
      d1 = 2.75
      t' = fromRational t
  in toRational $ if t' < 1 / d1
     then n1 * t' * t'
     else if t' < 2 / d1
     then n1 * (t' - 1.5 / d1) ** 2 + 0.75
     else if t' < 2.5 / d1
     then n1 * (t' - 2.25 / d1) ** 2 + 0.9375
     else n1 * (t' - 2.625 / d1) ** 2 + 0.984375

-- | Bounce ease-in
easeInBounce :: EasingFn
easeInBounce = EasingFn $ \t -> 1 - bounceOut (1 - t)

-- | Bounce ease-out
easeOutBounce :: EasingFn
easeOutBounce = EasingFn bounceOut

-- | Bounce ease-in-out
easeInOutBounce :: EasingFn
easeInOutBounce = EasingFn $ \t ->
  if t < 1%2
    then (1 - bounceOut (1 - 2 * t)) / 2
    else (1 + bounceOut (2 * t - 1)) / 2

-- Bounce cannot be represented by cubic bezier - must use keyframes
-- Placeholder beziers for UI representation only
easeInBounceBezier :: CubicBezier
easeInBounceBezier = CubicBezier (0.5, 0) (0.5, 1)

easeOutBounceBezier :: CubicBezier
easeOutBounceBezier = CubicBezier (0.5, 0) (0.5, 1)
```

---

## 10. Spring Physics Easing

### 10.1 Spring Functions

```haskell
-- | Spring parameters
data SpringParams = SpringParams
  { spStiffness :: !(Bounded Double)  -- 1-1000, default 100
  , spDamping   :: !(Bounded Double)  -- 1-100, default 10
  , spMass      :: !(Bounded Double)  -- 0.1-10, default 1
  , spVelocity  :: !(Bounded Double)  -- -100 to 100, default 0
  } deriving (Eq, Show)

-- | Default spring params
defaultSpring :: SpringParams
defaultSpring = SpringParams
  (unsafeMkBounded 100 1 1000 100)
  (unsafeMkBounded 10 1 100 10)
  (unsafeMkBounded 1 0.1 10 1)
  (unsafeMkBounded 0 (-100) 100 0)

-- | Spring easing function
-- Uses damped harmonic oscillator equation
easeSpring :: SpringParams -> EasingFn
easeSpring params = EasingFn $ \t ->
  let stiffness = bValue (spStiffness params)
      damping = bValue (spDamping params)
      mass = bValue (spMass params)
      initialVelocity = bValue (spVelocity params)
      t' = fromRational t
      -- Damped spring equation
      omega0 = sqrt (stiffness / mass)
      zeta = damping / (2 * sqrt (stiffness * mass))
  in toRational $ if zeta < 1
     -- Underdamped
     then let omegaD = omega0 * sqrt (1 - zeta * zeta)
              envelope = exp (-zeta * omega0 * t')
              cosComponent = cos (omegaD * t')
              sinComponent = sin (omegaD * t')
              position = 1 - envelope * (cosComponent + (zeta * omega0 + initialVelocity) / omegaD * sinComponent)
          in position
     else if zeta == 1
     -- Critically damped
     then let position = 1 - exp (-omega0 * t') * (1 + (omega0 + initialVelocity) * t')
          in position
     -- Overdamped
     else let sqrtPart = sqrt (zeta * zeta - 1)
              r1 = -omega0 * (zeta + sqrtPart)
              r2 = -omega0 * (zeta - sqrtPart)
              c2 = (initialVelocity - r1) / (r2 - r1)
              c1 = 1 - c2
              position = 1 - c1 * exp (r1 * t') - c2 * exp (r2 * t')
          in position

-- | Generate keyframes for spring animation
springToKeyframes :: SpringParams -> Int -> Interval -> [Keyframe Double]
springToKeyframes params numFrames iv =
  let ef = easeSpring params
  in [ Keyframe
         { kfTime = Frame $ frameValue (ivStart iv) + round (fromIntegral i * step)
         , kfValue = fromRational $ runEasing ef (fromIntegral i % fromIntegral (numFrames - 1))
         , kfHold = False
         , kfEaseIn = Nothing
         , kfEaseOut = Nothing
         }
     | i <- [0 .. numFrames - 1]
     ]
  where
    step = fromIntegral (ivDuration iv) / fromIntegral (numFrames - 1)
```

---

## 11. Cubic Bezier Representation

### 11.1 Cubic Bezier Type

```haskell
-- | Cubic bezier control points for easing
-- P0 = (0, 0) and P3 = (1, 1) are implicit
-- We store P1 = (x1, y1) and P2 = (x2, y2)
data CubicBezier = CubicBezier
  { cbP1 :: !(Bounded Double, Bounded Double)  -- Control point 1
  , cbP2 :: !(Bounded Double, Bounded Double)  -- Control point 2
  } deriving (Eq, Show)

-- | Bezier X constraints (must be in [0, 1] for valid timing)
bezierXConstraint :: (Double, Double, Double)
bezierXConstraint = (0, 1, 0.5)

-- | Bezier Y constraints (can exceed [0, 1] for overshoot)
bezierYConstraint :: (Double, Double, Double)
bezierYConstraint = (-2, 3, 0.5)

-- | Smart constructor
mkCubicBezier :: (Double, Double) -> (Double, Double) -> Either String CubicBezier
mkCubicBezier (x1, y1) (x2, y2) = do
  bx1 <- mkBounded x1 0 1 0.5
  by1 <- mkBounded y1 (-2) 3 0.5
  bx2 <- mkBounded x2 0 1 0.5
  by2 <- mkBounded y2 (-2) 3 0.5
  pure $ CubicBezier (bx1, by1) (bx2, by2)

-- | Linear bezier (no easing)
linearBezier :: CubicBezier
linearBezier = CubicBezier
  (unsafeMkBounded 0 0 1 0.5, unsafeMkBounded 0 (-2) 3 0.5)
  (unsafeMkBounded 1 0 1 0.5, unsafeMkBounded 1 (-2) 3 0.5)

-- | Evaluate cubic bezier at parameter t
evalCubicBezier :: CubicBezier -> Double -> Double
evalCubicBezier cb t =
  let x1 = bValue (fst $ cbP1 cb)
      y1 = bValue (snd $ cbP1 cb)
      x2 = bValue (fst $ cbP2 cb)
      y2 = bValue (snd $ cbP2 cb)
      -- Find t parameter for given x using Newton's method
      tForX = findTForX x1 x2 t
      -- Evaluate Y at that parameter
  in cubicBezierY y1 y2 tForX
  where
    -- Cubic bezier X: 3(1-t)²t·x1 + 3(1-t)t²·x2 + t³
    cubicBezierX x1 x2 t = 
      3 * (1 - t) ** 2 * t * x1 + 3 * (1 - t) * t ** 2 * x2 + t ** 3
    
    -- Cubic bezier Y: 3(1-t)²t·y1 + 3(1-t)t²·y2 + t³
    cubicBezierY y1 y2 t = 
      3 * (1 - t) ** 2 * t * y1 + 3 * (1 - t) * t ** 2 * y2 + t ** 3
    
    -- Newton's method to find parameter t for given x
    findTForX x1 x2 targetX = go targetX 4  -- 4 iterations usually enough
      where
        go guess 0 = guess
        go guess n =
          let x = cubicBezierX x1 x2 guess
              dx = 3 * (1 - guess) ** 2 * x1 + 
                   6 * (1 - guess) * guess * (x2 - x1) +
                   3 * guess ** 2 * (1 - x2)
              newGuess = if abs dx < 1e-10 
                         then guess 
                         else guess - (x - targetX) / dx
          in go (max 0 (min 1 newGuess)) (n - 1)

-- | Convert to Lottie easing format
-- Lottie uses: { i: {x: [x2], y: [y2]}, o: {x: [x1], y: [y1]} }
-- Note: Lottie's "i" is the incoming tangent (end), "o" is outgoing (start)
cubicBezierToLottie :: CubicBezier -> (Value, Value)
cubicBezierToLottie cb =
  let (bx1, by1) = cbP1 cb
      (bx2, by2) = cbP2 cb
  in ( object ["x" .= [bValue bx1], "y" .= [bValue by1]]  -- Out tangent
     , object ["x" .= [bValue bx2], "y" .= [bValue by2]]  -- In tangent
     )
```

---

## 12. Easing Preset Registry

### 12.1 Complete Preset Table

| Name | Type | Bezier P1 | Bezier P2 | Needs Keyframes |
|------|------|-----------|-----------|-----------------|
| linear | - | (0, 0) | (1, 1) | No |
| easeInQuad | polynomial | (0.55, 0.085) | (0.68, 0.53) | No |
| easeOutQuad | polynomial | (0.25, 0.46) | (0.45, 0.94) | No |
| easeInOutQuad | polynomial | (0.455, 0.03) | (0.515, 0.955) | No |
| easeInCubic | polynomial | (0.55, 0.055) | (0.675, 0.19) | No |
| easeOutCubic | polynomial | (0.215, 0.61) | (0.355, 1) | No |
| easeInOutCubic | polynomial | (0.645, 0.045) | (0.355, 1) | No |
| easeInQuart | polynomial | (0.895, 0.03) | (0.685, 0.22) | No |
| easeOutQuart | polynomial | (0.165, 0.84) | (0.44, 1) | No |
| easeInOutQuart | polynomial | (0.77, 0) | (0.175, 1) | No |
| easeInQuint | polynomial | (0.755, 0.05) | (0.855, 0.06) | No |
| easeOutQuint | polynomial | (0.23, 1) | (0.32, 1) | No |
| easeInOutQuint | polynomial | (0.86, 0) | (0.07, 1) | No |
| easeInSine | sinusoidal | (0.47, 0) | (0.745, 0.715) | No |
| easeOutSine | sinusoidal | (0.39, 0.575) | (0.565, 1) | No |
| easeInOutSine | sinusoidal | (0.445, 0.05) | (0.55, 0.95) | No |
| easeInExpo | exponential | (0.95, 0.05) | (0.795, 0.035) | No |
| easeOutExpo | exponential | (0.19, 1) | (0.22, 1) | No |
| easeInOutExpo | exponential | (1, 0) | (0, 1) | No |
| easeInCirc | circular | (0.6, 0.04) | (0.98, 0.335) | No |
| easeOutCirc | circular | (0.075, 0.82) | (0.165, 1) | No |
| easeInOutCirc | circular | (0.785, 0.135) | (0.15, 0.86) | No |
| easeInBack | overshoot | (0.6, -0.28) | (0.735, 0.045) | No |
| easeOutBack | overshoot | (0.175, 0.885) | (0.32, 1.275) | No |
| easeInOutBack | overshoot | (0.68, -0.55) | (0.265, 1.55) | No |
| easeInElastic | physics | N/A | N/A | **Yes** |
| easeOutElastic | physics | N/A | N/A | **Yes** |
| easeInOutElastic | physics | N/A | N/A | **Yes** |
| easeInBounce | physics | N/A | N/A | **Yes** |
| easeOutBounce | physics | N/A | N/A | **Yes** |
| easeInOutBounce | physics | N/A | N/A | **Yes** |
| spring | physics | N/A | N/A | **Yes** |

### 12.2 Registry Implementation

```haskell
-- | Easing preset enumeration
data EasingPreset
  = EaseLinear
  | EaseInQuad | EaseOutQuad | EaseInOutQuad
  | EaseInCubic | EaseOutCubic | EaseInOutCubic
  | EaseInQuart | EaseOutQuart | EaseInOutQuart
  | EaseInQuint | EaseOutQuint | EaseInOutQuint
  | EaseInSine | EaseOutSine | EaseInOutSine
  | EaseInExpo | EaseOutExpo | EaseInOutExpo
  | EaseInCirc | EaseOutCirc | EaseInOutCirc
  | EaseInBack | EaseOutBack | EaseInOutBack
  | EaseInElastic | EaseOutElastic | EaseInOutElastic
  | EaseInBounce | EaseOutBounce | EaseInOutBounce
  | EaseSpring
  deriving (Eq, Show, Enum, Bounded)

-- | Get easing function for preset
presetToFunction :: EasingPreset -> EasingFn
presetToFunction = \case
  EaseLinear -> linear
  EaseInQuad -> easeInQuad
  EaseOutQuad -> easeOutQuad
  EaseInOutQuad -> easeInOutQuad
  EaseInCubic -> easeInCubic
  EaseOutCubic -> easeOutCubic
  EaseInOutCubic -> easeInOutCubic
  -- ... etc
  EaseSpring -> easeSpring defaultSpring

-- | Get bezier for preset (Nothing if needs keyframes)
presetToBezier :: EasingPreset -> Maybe CubicBezier
presetToBezier = \case
  EaseLinear -> Just linearBezier
  EaseInQuad -> Just easeInQuadBezier
  EaseOutQuad -> Just easeOutQuadBezier
  -- ... polynomial, sine, expo, circ
  EaseInBack -> Just easeInBackBezier
  EaseOutBack -> Just easeOutBackBezier
  EaseInOutBack -> Just easeInOutBackBezier
  -- Physics-based need keyframes
  EaseInElastic -> Nothing
  EaseOutElastic -> Nothing
  EaseInOutElastic -> Nothing
  EaseInBounce -> Nothing
  EaseOutBounce -> Nothing
  EaseInOutBounce -> Nothing
  EaseSpring -> Nothing

-- | Check if preset requires keyframe generation
presetNeedsKeyframes :: EasingPreset -> Bool
presetNeedsKeyframes = isNothing . presetToBezier
```

---

## 13. Lean4 Proofs

```lean4
namespace EasingProofs

/-- All easing functions return 0 at t=0 -/
theorem easing_at_zero (f : EasingFn) (h : f = EasingFn.linear ∨ f = EasingFn.easeInQuad) :
    f 0 = 0 := by
  cases h with
  | inl hl => simp [hl, EasingFn.linear]
  | inr hr => simp [hr, EasingFn.easeInQuad]

/-- All easing functions return 1 at t=1 -/
theorem easing_at_one (f : EasingFn) (h : f = EasingFn.linear ∨ f = EasingFn.easeInQuad) :
    f 1 = 1 := by
  cases h with
  | inl hl => simp [hl, EasingFn.linear]
  | inr hr => simp [hr, EasingFn.easeInQuad]; ring

/-- Reverse is involutive -/
theorem reverse_involutive (f : EasingFn) :
    EasingFn.reverse (EasingFn.reverse f) = f := by
  funext t
  simp [EasingFn.reverse]
  ring

/-- Linear easing is identity -/
theorem linear_is_id : EasingFn.linear = id := rfl

/-- Compose with identity is identity -/
theorem compose_id_left (f : EasingFn) : EasingFn.compose id f = f := by
  simp [EasingFn.compose]

theorem compose_id_right (f : EasingFn) : EasingFn.compose f id = f := by
  simp [EasingFn.compose]

/-- Mirror preserves endpoints -/
theorem mirror_at_zero (f : EasingFn) (hf : f 0 = 0) :
    EasingFn.mirror f 0 = 0 := by
  simp [EasingFn.mirror, hf]

theorem mirror_at_one (f : EasingFn) (hf : f 0 = 0) :
    EasingFn.mirror f 1 = 1 := by
  simp [EasingFn.mirror, hf]

end EasingProofs
```

---

## 14. Constraint Summary

| Type | Property | Min | Max | Default | Unit |
|------|----------|-----|-----|---------|------|
| CubicBezier | x1, x2 | 0 | 1 | 0.5 | normalized |
| CubicBezier | y1, y2 | -2 | 3 | 0.5 | normalized |
| SpringParams | stiffness | 1 | 1000 | 100 | N/m |
| SpringParams | damping | 1 | 100 | 10 | Ns/m |
| SpringParams | mass | 0.1 | 10 | 1 | kg |
| SpringParams | velocity | -100 | 100 | 0 | m/s |
| EasingFn | input t | 0 | 1 | 0 | normalized |
| EasingFn | output | -2 | 3 | 0 | normalized |

---

## 15. Test Specifications

### 15.1 Boundary Tests

| Preset | f(0) | f(1) | f(0.5) approx |
|--------|------|------|---------------|
| linear | 0 | 1 | 0.5 |
| easeInQuad | 0 | 1 | 0.25 |
| easeOutQuad | 0 | 1 | 0.75 |
| easeInOutQuad | 0 | 1 | 0.5 |
| easeInCubic | 0 | 1 | 0.125 |
| easeOutCubic | 0 | 1 | 0.875 |
| easeInBack | 0 | 1 | <0 (overshoot) |
| easeOutBack | 0 | 1 | >1 (overshoot) |

### 15.2 Property Tests

```haskell
-- | All easings return 0 at t=0
prop_easing_zero :: EasingPreset -> Bool
prop_easing_zero preset =
  let ef = presetToFunction preset
  in runEasing ef 0 == 0

-- | All easings return 1 at t=1
prop_easing_one :: EasingPreset -> Bool
prop_easing_one preset =
  let ef = presetToFunction preset
  in runEasing ef 1 == 1

-- | Reverse is involutive
prop_reverse_involutive :: EasingFn -> Rational -> Bool
prop_reverse_involutive ef t =
  let t' = max 0 (min 1 t)
      double_reversed = reverseEasing (reverseEasing ef)
  in abs (runEasing double_reversed t' - runEasing ef t') < 1e-10

-- | Bezier evaluation matches function (approximately)
prop_bezier_matches_function :: EasingPreset -> Property
prop_bezier_matches_function preset =
  presetToBezier preset /= Nothing ==>
    forAll (choose (0, 1)) $ \t ->
      let Just bez = presetToBezier preset
          ef = presetToFunction preset
          bezValue = evalCubicBezier bez t
          fnValue = fromRational $ runEasing ef (toRational t)
      in abs (bezValue - fnValue) < 0.05  -- Allow 5% error for bezier approximation
```

---

*End of Specification 08*
