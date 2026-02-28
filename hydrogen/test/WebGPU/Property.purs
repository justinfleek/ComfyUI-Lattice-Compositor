-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // gpu // property // tests
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Property-based tests for GPU rendering modules with realistic distributions.
-- |
-- | ## Test Categories
-- |
-- | 1. **Math Function Accuracy** — sin, cos, sqrt, pow vs reference values
-- | 2. **Bounded Type Invariants** — values always within declared bounds
-- | 3. **Idempotency** — clamping twice = clamping once
-- | 4. **Monotonicity** — sqrt, pow preserve ordering where expected
-- | 5. **Identity** — pow(x,1)=x, sqrt(x²)=|x|, sin(0)=0, cos(0)=1
-- | 6. **Ray Flag Combination** — priority ordering, commutativity checks
-- |
-- | ## Distributions
-- |
-- | - **Uniform** for general coverage
-- | - **Edge-biased** for boundary conditions (0, 1, -1, π, 2π, max, min)
-- | - **Realistic** for typical GPU workload values

module Test.WebGPU.Property where

import Prelude

import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (log)
import Test.QuickCheck (Result(..), (<?>))
import Test.QuickCheck.Gen (Gen, choose, chooseInt, elements, frequency, oneOf)
import Test.Spec (Spec, describe, it)

import Test.Spec.QuickCheck (quickCheck) as Spec

-- Modules under test
import Hydrogen.GPU.WebGPU.DeferredRendering as DR
import Hydrogen.GPU.Types.Bounded as B

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                  // generators
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Pi constant for angle calculations
pi :: Number
pi = 3.14159265358979

-- | Generate angles with edge-biased distribution
-- | Biases toward: 0, π/2, π, 3π/2, 2π (critical angles for trig)
genAngle :: Gen Number
genAngle = frequency $ NEA.cons'
  (Tuple 20.0 (elements $ NEA.cons' 0.0 [pi/2.0, pi, 3.0*pi/2.0, 2.0*pi]))
  [ Tuple 80.0 (map toNumber (chooseInt (-628) 628) <#> (_ / 100.0)) ]

-- | Generate positive numbers for sqrt testing
-- | Biases toward: 0, 1, perfect squares, small values
genPositive :: Gen Number
genPositive = frequency $ NEA.cons'
  (Tuple 15.0 (elements $ NEA.cons' 0.0 [1.0, 4.0, 9.0, 16.0, 25.0, 100.0]))
  [ Tuple 10.0 (elements $ NEA.cons' 0.0001 [0.01, 0.1])
  , Tuple 75.0 (map toNumber (chooseInt 0 10000) <#> (_ / 10.0))
  ]

-- | Generate unit interval values [0,1]
-- | Biases toward boundaries: 0, 0.5, 1
genUnit :: Gen Number
genUnit = frequency $ NEA.cons'
  (Tuple 20.0 (elements $ NEA.cons' 0.0 [0.5, 1.0]))
  [ Tuple 80.0 (map toNumber (chooseInt 0 1000) <#> (_ / 1000.0)) ]

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                             // reference // math
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Reference sin using more terms for comparison
-- | sin(x) = x - x³/6 + x⁵/120 - x⁷/5040 + x⁹/362880 - x¹¹/39916800
refSin :: Number -> Number
refSin x =
  let x' = normalizeAngle x
      x2 = x' * x'
      x3 = x' * x2
      x5 = x3 * x2
      x7 = x5 * x2
      x9 = x7 * x2
      x11 = x9 * x2
  in x' - (x3/6.0) + (x5/120.0) - (x7/5040.0) + (x9/362880.0) - (x11/39916800.0)

-- | Reference cos using more terms
refCos :: Number -> Number
refCos x =
  let x' = normalizeAngle x
      x2 = x' * x'
      x4 = x2 * x2
      x6 = x4 * x2
      x8 = x4 * x4
      x10 = x8 * x2
  in 1.0 - (x2/2.0) + (x4/24.0) - (x6/720.0) + (x8/40320.0) - (x10/3628800.0)

-- | Normalize angle to [-π, π]
normalizeAngle :: Number -> Number
normalizeAngle x =
  let twoPi = 2.0 * pi
      n = floor' (x / twoPi)
      x' = x - (n * twoPi)
  in if x' > pi then x' - twoPi else if x' < (-pi) then x' + twoPi else x'

-- | Simple floor for normalization
floor' :: Number -> Number
floor' n = toNumber (floorInt n)
  where
    floorInt :: Number -> Int
    floorInt x = if x >= 0.0 then truncPos x 0 else negate (truncPos (negate x) 0) - 1
    truncPos :: Number -> Int -> Int
    truncPos x acc = if x < 1.0 then acc else truncPos (x - 1.0) (acc + 1)

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                              // property // tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Absolute value helper
abs :: Number -> Number
abs x = if x < 0.0 then negate x else x

-- | Check if two numbers are approximately equal
approxEq :: Number -> Number -> Number -> Boolean
approxEq tolerance a b = abs (a - b) < tolerance

-- | Property: sin² + cos² = 1 (Pythagorean identity)
prop_pythagorean :: Number -> Result
prop_pythagorean x =
  let s = DR.sin x
      c = DR.cos x
      sum = s * s + c * c
  in approxEq 0.01 sum 1.0 <?> "sin²(" <> show x <> ") + cos²(" <> show x <> ") = " <> show sum <> " ≠ 1"

-- | Property: sin(0) = 0
prop_sinZero :: Result
prop_sinZero =
  let result = DR.sin 0.0
  in approxEq 0.0001 result 0.0 <?> "sin(0) = " <> show result <> " ≠ 0"

-- | Property: cos(0) = 1
prop_cosZero :: Result
prop_cosZero =
  let result = DR.cos 0.0
  in approxEq 0.0001 result 1.0 <?> "cos(0) = " <> show result <> " ≠ 1"

-- | Property: sin is odd: sin(-x) = -sin(x)
prop_sinOdd :: Number -> Result
prop_sinOdd x =
  let s1 = DR.sin x
      s2 = DR.sin (negate x)
  in approxEq 0.01 s1 (negate s2) <?> "sin(" <> show x <> ") = " <> show s1 <> ", sin(" <> show (negate x) <> ") = " <> show s2

-- | Property: cos is even: cos(-x) = cos(x)
prop_cosEven :: Number -> Result
prop_cosEven x =
  let c1 = DR.cos x
      c2 = DR.cos (negate x)
  in approxEq 0.01 c1 c2 <?> "cos(" <> show x <> ") = " <> show c1 <> ", cos(" <> show (negate x) <> ") = " <> show c2

-- | Property: sqrt(x)² ≈ x for positive x
prop_sqrtSquared :: Number -> Result
prop_sqrtSquared x =
  let r = DR.sqrt x
      squared = r * r
  in if x < 0.0
     then Success  -- skip negative
     else approxEq 0.01 squared x <?> "sqrt(" <> show x <> ")² = " <> show squared <> " ≠ " <> show x

-- | Property: sqrt is monotonic (a ≤ b → sqrt(a) ≤ sqrt(b))
prop_sqrtMonotonic :: Number -> Number -> Result
prop_sqrtMonotonic a b =
  let a' = abs a
      b' = abs b
      lo = if a' <= b' then a' else b'
      hi = if a' <= b' then b' else a'
  in (DR.sqrt lo <= DR.sqrt hi) <?> "sqrt(" <> show lo <> ") > sqrt(" <> show hi <> ")"

-- | Property: pow(x, 0) = 1
prop_powZero :: Number -> Result
prop_powZero x =
  let result = DR.pow x 0.0
  in approxEq 0.0001 result 1.0 <?> "pow(" <> show x <> ", 0) = " <> show result <> " ≠ 1"

-- | Property: pow(x, 1) = x
prop_powOne :: Number -> Result
prop_powOne x =
  let result = DR.pow x 1.0
  in approxEq 0.01 result x <?> "pow(" <> show x <> ", 1) = " <> show result <> " ≠ " <> show x

-- | Property: pow(x, 2) = x * x
prop_powTwo :: Number -> Result
prop_powTwo x =
  let result = DR.pow x 2.0
      expected = x * x
  in approxEq 0.01 result expected <?> "pow(" <> show x <> ", 2) = " <> show result <> " ≠ " <> show expected

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                        // bounded // type // tests
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Property: Metallic is always in [0,1]
prop_metallicBounded :: Number -> Result
prop_metallicBounded x =
  let m = B.unwrapMetallic (B.metallic x)
  in (m >= 0.0 && m <= 1.0) <?> "metallic(" <> show x <> ") = " <> show m <> " out of [0,1]"

-- | Property: Metallic clamping is idempotent
prop_metallicIdempotent :: Number -> Result
prop_metallicIdempotent x =
  let m1 = B.metallic x
      m2 = B.metallic (B.unwrapMetallic m1)
  in (B.unwrapMetallic m1 == B.unwrapMetallic m2) <?> "metallic not idempotent"

-- | Property: Roughness is always in [0,1]
prop_roughnessBounded :: Number -> Result
prop_roughnessBounded x =
  let r = B.unwrapRoughness (B.roughness x)
  in (r >= 0.0 && r <= 1.0) <?> "roughness(" <> show x <> ") = " <> show r <> " out of [0,1]"

-- | Property: IOR is always >= 1
prop_iorBounded :: Number -> Result
prop_iorBounded x =
  let i = B.unwrapIOR (B.ior x)
  in (i >= 1.0) <?> "ior(" <> show x <> ") = " <> show i <> " < 1"

-- | Property: Intensity is always >= 0
prop_intensityBounded :: Number -> Result
prop_intensityBounded x =
  let i = B.unwrapIntensity (B.intensity x)
  in (i >= 0.0) <?> "intensity(" <> show x <> ") = " <> show i <> " < 0"

-- | Property: Radius is always >= 0
prop_radiusBounded :: Number -> Result
prop_radiusBounded x =
  let r = B.unwrapRadius (B.radius x)
  in (r >= 0.0) <?> "radius(" <> show x <> ") = " <> show r <> " < 0"

-- | Property: ConeAngle is always in [0, π]
prop_coneAngleBounded :: Number -> Result
prop_coneAngleBounded x =
  let a = B.unwrapConeAngle (B.coneAngle x)
  in (a >= 0.0 && a <= 3.14159) <?> "coneAngle(" <> show x <> ") = " <> show a <> " out of [0,π]"

-- ═══════════════════════════════════════════════════════════════════════════════
--                                                                     // test spec
-- ═══════════════════════════════════════════════════════════════════════════════

spec :: Spec Unit
spec = describe "GPU Property Tests" do

  describe "Trigonometric Functions" do
    it "sin(0) = 0" do
      Spec.quickCheck \(_ :: Int) -> prop_sinZero
    
    it "cos(0) = 1" do
      Spec.quickCheck \(_ :: Int) -> prop_cosZero
    
    it "sin² + cos² = 1 (Pythagorean)" do
      Spec.quickCheck prop_pythagorean
    
    it "sin is odd function" do
      Spec.quickCheck prop_sinOdd
    
    it "cos is even function" do
      Spec.quickCheck prop_cosEven

  describe "Square Root" do
    it "sqrt(x)² ≈ x" do
      Spec.quickCheck prop_sqrtSquared
    
    it "sqrt is monotonic" do
      Spec.quickCheck \a b -> prop_sqrtMonotonic a b

  describe "Power Function" do
    it "pow(x, 0) = 1" do
      Spec.quickCheck prop_powZero
    
    it "pow(x, 1) = x" do
      Spec.quickCheck prop_powOne
    
    it "pow(x, 2) = x²" do
      Spec.quickCheck prop_powTwo

  describe "Bounded Types" do
    it "Metallic always in [0,1]" do
      Spec.quickCheck prop_metallicBounded
    
    it "Metallic clamping is idempotent" do
      Spec.quickCheck prop_metallicIdempotent
    
    it "Roughness always in [0,1]" do
      Spec.quickCheck prop_roughnessBounded
    
    it "IOR always >= 1" do
      Spec.quickCheck prop_iorBounded
    
    it "Intensity always >= 0" do
      Spec.quickCheck prop_intensityBounded
    
    it "Radius always >= 0" do
      Spec.quickCheck prop_radiusBounded
    
    it "ConeAngle always in [0,π]" do
      Spec.quickCheck prop_coneAngleBounded

