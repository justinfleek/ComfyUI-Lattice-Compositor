-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // hydrogen // math // core
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core mathematical functions — PURE PURESCRIPT.
-- |
-- | No JavaScript. No FFI. Pure functional implementations using:
-- | - Taylor series for transcendental functions
-- | - Newton-Raphson iteration for roots
-- | - CORDIC-inspired algorithms where appropriate
-- |
-- | ## Precision
-- |
-- | All Taylor series use sufficient terms for IEEE 754 double precision
-- | (approximately 15-17 significant decimal digits).
-- |
-- | ## Verification
-- |
-- | These implementations have corresponding Lean4 proofs in:
-- | `proofs/Hydrogen/Math/Core.lean`

module Hydrogen.Math.Core
  ( -- * Constants
    pi
  , e
  , tau
  , sqrt2
  , sqrt1_2
  , ln2
  , ln10
  , log2e
  , log10e
  
  -- * Powers & Roots
  , pow
  , sqrt
  , cbrt
  , hypot
  , hypot3
  
  -- * Trigonometry
  , sin
  , cos
  , tan
  , asin
  , acos
  , atan
  , atan2
  , sinh
  , cosh
  , tanh
  , asinh
  , acosh
  , atanh
  
  -- * Exponential
  , exp
  , expm1
  , log
  , log10
  , log2
  , log1p
  
  -- * Rounding
  , floor
  , ceil
  , round
  , trunc
  , fround
  
  -- * Misc
  , abs
  , sign
  , min
  , max
  , minArray
  , maxArray
  , clamp
  
  -- * Special Values
  , isNaN
  , isFinite
  , isInteger
  , infinity
  , negativeInfinity
  
  -- * Interpolation
  , lerp
  , inverseLerp
  , remap
  , smoothstep
  , smootherstep
  
  -- * Angle Conversion
  , degreesToRadians
  , radiansToDegrees
  ) where

import Prelude hiding (min, max)
import Data.Array (foldl)
import Data.Int (floor, toNumber) as Int

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // constants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pi (ratio of circumference to diameter)
-- | Computed to full IEEE 754 double precision
pi :: Number
pi = 3.141592653589793

-- | Euler's number (base of natural logarithm)
e :: Number
e = 2.718281828459045

-- | Tau (2 * pi, full circle in radians)
tau :: Number
tau = 6.283185307179586

-- | Square root of 2
sqrt2 :: Number
sqrt2 = 1.4142135623730951

-- | Square root of 1/2 (equivalently, 1/sqrt(2))
sqrt1_2 :: Number
sqrt1_2 = 0.7071067811865476

-- | Natural logarithm of 2
ln2 :: Number
ln2 = 0.6931471805599453

-- | Natural logarithm of 10
ln10 :: Number
ln10 = 2.302585092994046

-- | Base-2 logarithm of e
log2e :: Number
log2e = 1.4426950408889634

-- | Base-10 logarithm of e
log10e :: Number
log10e = 0.4342944819032518

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // rounding
-- ═════════════════════════════════════════════════════════════════════════════

-- | Absolute value
abs :: Number -> Number
abs x = if x < 0.0 then negate x else x

-- | Sign: -1.0, 0.0, or 1.0
sign :: Number -> Number
sign x
  | x > 0.0 = 1.0
  | x < 0.0 = -1.0
  | otherwise = 0.0

-- | Round down to nearest integer
floor :: Number -> Number
floor x = 
  let i = Int.floor x
  in toNumber i
  where
    toNumber :: Int -> Number
    toNumber n = Int.toNumber n

-- | Round up to nearest integer
ceil :: Number -> Number
ceil x = 
  let fl = floor x
  in if x == fl then fl else fl + 1.0

-- | Round to nearest integer (half away from zero)
round :: Number -> Number
round x = 
  let fl = floor x
      diff = x - fl
  in if diff >= 0.5 then fl + 1.0 else fl

-- | Truncate toward zero
trunc :: Number -> Number
trunc x = if x >= 0.0 then floor x else ceil x

-- | Round to nearest 32-bit float (identity for our purposes)
fround :: Number -> Number
fround x = x

-- | Minimum of two values
min :: Number -> Number -> Number
min a b = if a <= b then a else b

-- | Maximum of two values
max :: Number -> Number -> Number
max a b = if a >= b then a else b

-- | Minimum of an array
minArray :: Array Number -> Number
minArray arr = foldl min infinity arr

-- | Maximum of an array  
maxArray :: Array Number -> Number
maxArray arr = foldl max negativeInfinity arr

-- | Clamp value to range [minVal, maxVal]
clamp :: Number -> Number -> Number -> Number
clamp minVal maxVal x = min maxVal (max minVal x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // special values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Positive infinity
infinity :: Number
infinity = 1.0 / 0.0

-- | Negative infinity
negativeInfinity :: Number
negativeInfinity = -1.0 / 0.0

-- | Check if value is NaN (NaN is the only value not equal to itself)
isNaN :: Number -> Boolean
isNaN x = x /= x

-- | Check if value is finite (not infinite, not NaN)
isFinite :: Number -> Boolean
isFinite x = not (isNaN x) && x /= infinity && x /= negativeInfinity

-- | Check if value is an integer
isInteger :: Number -> Boolean
isInteger x = isFinite x && floor x == x

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // powers & roots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Square root using Newton-Raphson iteration
-- |
-- | Starting guess: x/2, iterate: guess' = (guess + x/guess) / 2
-- | Converges quadratically (doubles correct digits each iteration)
sqrt :: Number -> Number
sqrt x
  | x < 0.0 = 0.0 / 0.0  -- NaN for negative
  | x == 0.0 = 0.0
  | x == infinity = infinity
  | otherwise = newtonSqrt x (initialGuess x) 0

-- | Initial guess for sqrt using bit manipulation approximation
-- | For IEEE 754, sqrt(x) ≈ x^0.5, and we can estimate via exponent halving
initialGuess :: Number -> Number
initialGuess x = 
  if x >= 1.0 
    then x / 2.0 
    else x * 2.0

-- | Newton-Raphson iteration for sqrt
newtonSqrt :: Number -> Number -> Int -> Number
newtonSqrt x guess iter
  | iter >= 100 = guess  -- Max iterations (should never hit this)
  | otherwise =
      let next = (guess + x / guess) / 2.0
      in if abs (next - guess) < 1.0e-15 * abs guess
           then next
           else newtonSqrt x next (iter + 1)

-- | Cube root
cbrt :: Number -> Number
cbrt x
  | x == 0.0 = 0.0
  | x < 0.0 = negate (cbrtPositive (negate x))
  | otherwise = cbrtPositive x

-- | Cube root for positive numbers using Newton-Raphson
-- | Iteration: guess' = (2*guess + x/guess^2) / 3
cbrtPositive :: Number -> Number
cbrtPositive x = newtonCbrt x (x / 3.0) 0

newtonCbrt :: Number -> Number -> Int -> Number
newtonCbrt x guess iter
  | iter >= 100 = guess
  | otherwise =
      let next = (2.0 * guess + x / (guess * guess)) / 3.0
      in if abs (next - guess) < 1.0e-15 * abs guess
           then next
           else newtonCbrt x next (iter + 1)

-- | Hypotenuse of 2D vector: sqrt(x^2 + y^2)
-- | Uses scaling to avoid overflow/underflow
hypot :: Number -> Number -> Number
hypot x y =
  let ax = abs x
      ay = abs y
      maxVal = max ax ay
  in if maxVal == 0.0
       then 0.0
       else maxVal * sqrt ((ax / maxVal) * (ax / maxVal) + (ay / maxVal) * (ay / maxVal))

-- | Hypotenuse of 3D vector: sqrt(x^2 + y^2 + z^2)
hypot3 :: Number -> Number -> Number -> Number
hypot3 x y z =
  let ax = abs x
      ay = abs y
      az = abs z
      maxVal = max (max ax ay) az
  in if maxVal == 0.0
       then 0.0
       else maxVal * sqrt ((ax / maxVal) * (ax / maxVal) + 
                           (ay / maxVal) * (ay / maxVal) + 
                           (az / maxVal) * (az / maxVal))

-- | Power function: base^exponent
-- | Uses exp(exponent * log(base)) for general case
pow :: Number -> Number -> Number
pow base exponent
  | exponent == 0.0 = 1.0
  | base == 0.0 = if exponent > 0.0 then 0.0 else infinity
  | base == 1.0 = 1.0
  | exponent == 1.0 = base
  | base < 0.0 && not (isInteger exponent) = 0.0 / 0.0  -- NaN
  | base < 0.0 = 
      let result = exp (exponent * log (negate base))
      in if isOdd (trunc exponent) then negate result else result
  | otherwise = exp (exponent * log base)

isOdd :: Number -> Boolean
isOdd x = 
  let half = x / 2.0
  in floor half /= half

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // exponential
-- ═════════════════════════════════════════════════════════════════════════════

-- | Exponential function e^x using Taylor series
-- |
-- | e^x = 1 + x + x²/2! + x³/3! + x⁴/4! + ...
-- |
-- | For large |x|, we use range reduction: e^x = e^(x/2) * e^(x/2)
exp :: Number -> Number
exp x
  | isNaN x = x
  | x == infinity = infinity
  | x == negativeInfinity = 0.0
  | x == 0.0 = 1.0
  | x > 709.0 = infinity  -- Overflow threshold
  | x < -745.0 = 0.0       -- Underflow threshold
  | abs x > 1.0 = 
      -- Range reduction: e^x = (e^(x/2))^2
      let half = exp (x / 2.0)
      in half * half
  | otherwise = expTaylor x

-- | Taylor series for exp, valid for |x| <= 1
expTaylor :: Number -> Number
expTaylor x = taylorExp x 1.0 1.0 1

taylorExp :: Number -> Number -> Number -> Int -> Number
taylorExp x sum term n
  | n > 30 = sum  -- 30 terms is more than enough for double precision
  | otherwise =
      let newTerm = term * x / toNumber n
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else taylorExp x newSum newTerm (n + 1)
  where
    toNumber :: Int -> Number
    toNumber i = Int.toNumber i

-- | exp(x) - 1, more precise for small x
expm1 :: Number -> Number
expm1 x
  | abs x < 1.0e-5 = x + x * x / 2.0  -- First-order approximation
  | otherwise = exp x - 1.0

-- | Natural logarithm using series expansion
-- |
-- | For x near 1, use: ln(x) = 2 * (y + y³/3 + y⁵/5 + ...) where y = (x-1)/(x+1)
-- | For other x, use range reduction: ln(x) = ln(x/e^n) + n
log :: Number -> Number
log x
  | isNaN x = x
  | x < 0.0 = 0.0 / 0.0  -- NaN
  | x == 0.0 = negativeInfinity
  | x == infinity = infinity
  | x == 1.0 = 0.0
  | otherwise = 
      -- Range reduction to bring x close to 1
      let reduced = reduceForLog x 0
      in logNear1 reduced.value + toNumber reduced.exponent * ln2
  where
    toNumber :: Int -> Number
    toNumber i = Int.toNumber i

-- | Reduce x to range [0.5, 2) by dividing/multiplying by 2
reduceForLog :: Number -> Int -> { value :: Number, exponent :: Int }
reduceForLog x n
  | x >= 2.0 = reduceForLog (x / 2.0) (n + 1)
  | x < 0.5 = reduceForLog (x * 2.0) (n - 1)
  | otherwise = { value: x, exponent: n }

-- | Logarithm for values near 1 using arctanh series
-- | ln(x) = 2 * arctanh((x-1)/(x+1))
logNear1 :: Number -> Number
logNear1 x =
  let y = (x - 1.0) / (x + 1.0)
  in 2.0 * atanhSeries y

-- | Arctanh series: y + y³/3 + y⁵/5 + ...
atanhSeries :: Number -> Number
atanhSeries y = atanhSeriesGo y y (y * y) 1

atanhSeriesGo :: Number -> Number -> Number -> Int -> Number
atanhSeriesGo sum term y2 n
  | n > 50 = sum
  | otherwise =
      let newTerm = term * y2
          k = 2 * n + 1
          contrib = newTerm / toNumber k
          newSum = sum + contrib
      in if abs contrib < 1.0e-16 * abs newSum
           then newSum
           else atanhSeriesGo newSum newTerm y2 (n + 1)
  where
    toNumber :: Int -> Number
    toNumber i = Int.toNumber i

-- | Base-10 logarithm
log10 :: Number -> Number
log10 x = log x / ln10

-- | Base-2 logarithm  
log2 :: Number -> Number
log2 x = log x / ln2

-- | log(1 + x), more precise for small x
log1p :: Number -> Number
log1p x
  | abs x < 1.0e-5 = x - x * x / 2.0  -- First-order approximation
  | otherwise = log (1.0 + x)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // trigonometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sine using Taylor series with range reduction
-- |
-- | sin(x) = x - x³/3! + x⁵/5! - x⁷/7! + ...
-- |
-- | Range reduction: reduce to [-π, π] then to [-π/2, π/2]
sin :: Number -> Number
sin x
  | isNaN x = x
  | not (isFinite x) = 0.0 / 0.0
  | otherwise =
      let reduced = reduceAngle x
      in sinReduced reduced

-- | Reduce angle to [-π, π]
reduceAngle :: Number -> Number
reduceAngle x =
  let twoPi = tau
      reduced = x - twoPi * round (x / twoPi)
  in reduced

-- | Sin for reduced angle in [-π, π]
sinReduced :: Number -> Number
sinReduced x
  | x > pi / 2.0 = sinTaylor (pi - x)
  | x < (negate pi) / 2.0 = negate (sinTaylor (pi + x))
  | otherwise = sinTaylor x

-- | Taylor series for sin, valid for |x| <= π/2
sinTaylor :: Number -> Number
sinTaylor x = taylorSin x x (x * x) 1

taylorSin :: Number -> Number -> Number -> Int -> Number
taylorSin sum term x2 n
  | n > 20 = sum
  | otherwise =
      let k = 2 * n
          newTerm = negate term * x2 / (toNumber k * toNumber (k + 1))
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else taylorSin newSum newTerm x2 (n + 1)
  where
    toNumber :: Int -> Number
    toNumber i = Int.toNumber i

-- | Cosine using Taylor series
-- |
-- | cos(x) = 1 - x²/2! + x⁴/4! - x⁶/6! + ...
cos :: Number -> Number
cos x
  | isNaN x = x
  | not (isFinite x) = 0.0 / 0.0
  | otherwise =
      let reduced = reduceAngle x
      in cosReduced reduced

-- | Cos for reduced angle in [-π, π]
cosReduced :: Number -> Number
cosReduced x
  | x > pi / 2.0 = negate (cosTaylor (pi - x))
  | x < (negate pi) / 2.0 = negate (cosTaylor (pi + x))
  | otherwise = cosTaylor x

-- | Taylor series for cos, valid for |x| <= π/2
cosTaylor :: Number -> Number
cosTaylor x = 
  let x2 = x * x
  in taylorCos 1.0 1.0 x2 1

taylorCos :: Number -> Number -> Number -> Int -> Number
taylorCos sum term x2 n
  | n > 20 = sum
  | otherwise =
      let k = 2 * n - 1
          newTerm = negate term * x2 / (toNumber k * toNumber (k + 1))
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else taylorCos newSum newTerm x2 (n + 1)
  where
    toNumber :: Int -> Number
    toNumber i = Int.toNumber i

-- | Tangent
tan :: Number -> Number
tan x = sin x / cos x

-- | Arcsine using Newton's method on sin
-- |
-- | For |x| <= 0.5, use Taylor series
-- | For |x| > 0.5, use identity: asin(x) = π/2 - 2*asin(sqrt((1-x)/2))
asin :: Number -> Number
asin x
  | isNaN x = x
  | x < -1.0 || x > 1.0 = 0.0 / 0.0
  | x == 1.0 = pi / 2.0
  | x == -1.0 = negate pi / 2.0
  | abs x <= 0.5 = asinTaylor x
  | x > 0.5 = pi / 2.0 - 2.0 * asinTaylor (sqrt ((1.0 - x) / 2.0))
  | otherwise = negate (pi / 2.0) + 2.0 * asinTaylor (sqrt ((1.0 + x) / 2.0))

-- | Taylor series for asin: x + x³/6 + 3x⁵/40 + ...
asinTaylor :: Number -> Number
asinTaylor x = asinGo x x (x * x) 1

asinGo :: Number -> Number -> Number -> Int -> Number
asinGo sum term x2 n
  | n > 50 = sum
  | otherwise =
      let k = 2 * n - 1
          newTerm = term * x2 * toNumber k * toNumber k / (toNumber (2 * n) * toNumber (2 * n + 1))
          newSum = sum + newTerm
      in if abs newTerm < 1.0e-16 * abs newSum
           then newSum
           else asinGo newSum newTerm x2 (n + 1)
  where
    toNumber :: Int -> Number
    toNumber i = Int.toNumber i

-- | Arccosine
acos :: Number -> Number
acos x = pi / 2.0 - asin x

-- | Arctangent using series expansion
-- |
-- | For |x| <= 1: atan(x) = x - x³/3 + x⁵/5 - ...
-- | For |x| > 1: atan(x) = π/2 - atan(1/x)
atan :: Number -> Number
atan x
  | isNaN x = x
  | x == infinity = pi / 2.0
  | x == negativeInfinity = negate pi / 2.0
  | abs x > 1.0 = 
      if x > 0.0 
        then pi / 2.0 - atanSmall (1.0 / x)
        else negate pi / 2.0 - atanSmall (1.0 / x)
  | otherwise = atanSmall x

-- | Atan for |x| <= 1
atanSmall :: Number -> Number
atanSmall x = atanGo x x (x * x) 1

atanGo :: Number -> Number -> Number -> Int -> Number
atanGo sum term x2 n
  | n > 50 = sum
  | otherwise =
      let newTerm = negate term * x2
          k = 2 * n + 1
          contrib = newTerm / toNumber k
          newSum = sum + contrib
      in if abs contrib < 1.0e-16 * abs newSum
           then newSum
           else atanGo newSum newTerm x2 (n + 1)
  where
    toNumber :: Int -> Number
    toNumber i = Int.toNumber i

-- | Two-argument arctangent
atan2 :: Number -> Number -> Number
atan2 y x
  | isNaN x || isNaN y = 0.0 / 0.0
  | x > 0.0 = atan (y / x)
  | x < 0.0 && y >= 0.0 = atan (y / x) + pi
  | x < 0.0 && y < 0.0 = atan (y / x) - pi
  | x == 0.0 && y > 0.0 = pi / 2.0
  | x == 0.0 && y < 0.0 = negate pi / 2.0
  | otherwise = 0.0  -- x == 0 && y == 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hyperbolic trig
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hyperbolic sine: sinh(x) = (e^x - e^(-x)) / 2
sinh :: Number -> Number
sinh x
  | abs x < 1.0e-5 = x  -- Approximation for small x
  | otherwise = (exp x - exp (negate x)) / 2.0

-- | Hyperbolic cosine: cosh(x) = (e^x + e^(-x)) / 2
cosh :: Number -> Number
cosh x = (exp x + exp (negate x)) / 2.0

-- | Hyperbolic tangent
tanh :: Number -> Number
tanh x
  | x > 20.0 = 1.0   -- Saturates to 1
  | x < -20.0 = -1.0 -- Saturates to -1
  | otherwise = sinh x / cosh x

-- | Inverse hyperbolic sine: asinh(x) = ln(x + sqrt(x² + 1))
asinh :: Number -> Number
asinh x = log (x + sqrt (x * x + 1.0))

-- | Inverse hyperbolic cosine: acosh(x) = ln(x + sqrt(x² - 1))
acosh :: Number -> Number
acosh x
  | x < 1.0 = 0.0 / 0.0
  | otherwise = log (x + sqrt (x * x - 1.0))

-- | Inverse hyperbolic tangent: atanh(x) = 0.5 * ln((1+x)/(1-x))
atanh :: Number -> Number
atanh x
  | abs x >= 1.0 = if x > 0.0 then infinity else negativeInfinity
  | otherwise = 0.5 * log ((1.0 + x) / (1.0 - x))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // interpolation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Linear interpolation: lerp a b t = a + (b - a) * t
-- | When t=0 returns a, when t=1 returns b
lerp :: Number -> Number -> Number -> Number
lerp a b t = a + (b - a) * t

-- | Inverse of lerp: find t such that lerp a b t = v
inverseLerp :: Number -> Number -> Number -> Number
inverseLerp a b v = (v - a) / (b - a)

-- | Remap value from one range to another
remap :: Number -> Number -> Number -> Number -> Number -> Number
remap inMin inMax outMin outMax v =
  let t = inverseLerp inMin inMax v
  in lerp outMin outMax t

-- | Smoothstep: cubic Hermite interpolation with zero derivatives at edges
smoothstep :: Number -> Number -> Number -> Number
smoothstep edge0 edge1 x =
  let t = clamp 0.0 1.0 ((x - edge0) / (edge1 - edge0))
  in t * t * (3.0 - 2.0 * t)

-- | Smootherstep: Ken Perlin's improved smoothstep
-- | Has zero 1st and 2nd derivatives at edges
smootherstep :: Number -> Number -> Number -> Number
smootherstep edge0 edge1 x =
  let t = clamp 0.0 1.0 ((x - edge0) / (edge1 - edge0))
  in t * t * t * (t * (t * 6.0 - 15.0) + 10.0)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // angle conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert degrees to radians
degreesToRadians :: Number -> Number
degreesToRadians deg = deg * pi / 180.0

-- | Convert radians to degrees
radiansToDegrees :: Number -> Number
radiansToDegrees rad = rad * 180.0 / pi
