-- | Port of ui/src/__tests__/services/easing.test.ts
-- |
-- | Tests all 31 easing functions for boundary values, output range,
-- | monotonicity, symmetry, overshoot behavior, and helper functions.

module Test.Lattice.Services.Easing (spec) where

import Prelude

import Data.Array ((..), filter, any)
import Data.Foldable (for_)
import Data.Int (toNumber) as Int
import Data.Number as Number
import Data.Tuple (Tuple(..))
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite)

import Lattice.Services.Easing
  ( EasingType(..)
  , applyEasing
  , applyEasingType
  , interpolateWithEasing
  , linear, easeInSine, easeOutSine, easeInOutSine
  , easeInQuad, easeOutQuad, easeInOutQuad
  , easeInCubic, easeOutCubic, easeInOutCubic
  , easeInQuart, easeOutQuart, easeInOutQuart
  , easeInQuint, easeOutQuint, easeInOutQuint
  , easeInExpo, easeOutExpo, easeInOutExpo
  , easeInCirc, easeOutCirc, easeInOutCirc
  , easeInBack, easeOutBack, easeInOutBack
  , easeInElastic, easeOutElastic, easeInOutElastic
  , easeInBounce, easeOutBounce, easeInOutBounce
  )

--------------------------------------------------------------------------------
-- Constants
--------------------------------------------------------------------------------

tolerance :: Number
tolerance = 1.0e-10

-- | All easing types paired with their functions
allEasings :: Array (Tuple String (Tuple EasingType (Number -> Number)))
allEasings =
  [ Tuple "linear" (Tuple EaseLinear linear)
  , Tuple "easeInSine" (Tuple EaseInSine easeInSine)
  , Tuple "easeOutSine" (Tuple EaseOutSine easeOutSine)
  , Tuple "easeInOutSine" (Tuple EaseInOutSine easeInOutSine)
  , Tuple "easeInQuad" (Tuple EaseInQuad easeInQuad)
  , Tuple "easeOutQuad" (Tuple EaseOutQuad easeOutQuad)
  , Tuple "easeInOutQuad" (Tuple EaseInOutQuad easeInOutQuad)
  , Tuple "easeInCubic" (Tuple EaseInCubic easeInCubic)
  , Tuple "easeOutCubic" (Tuple EaseOutCubic easeOutCubic)
  , Tuple "easeInOutCubic" (Tuple EaseInOutCubic easeInOutCubic)
  , Tuple "easeInQuart" (Tuple EaseInQuart easeInQuart)
  , Tuple "easeOutQuart" (Tuple EaseOutQuart easeOutQuart)
  , Tuple "easeInOutQuart" (Tuple EaseInOutQuart easeInOutQuart)
  , Tuple "easeInQuint" (Tuple EaseInQuint easeInQuint)
  , Tuple "easeOutQuint" (Tuple EaseOutQuint easeOutQuint)
  , Tuple "easeInOutQuint" (Tuple EaseInOutQuint easeInOutQuint)
  , Tuple "easeInExpo" (Tuple EaseInExpo easeInExpo)
  , Tuple "easeOutExpo" (Tuple EaseOutExpo easeOutExpo)
  , Tuple "easeInOutExpo" (Tuple EaseInOutExpo easeInOutExpo)
  , Tuple "easeInCirc" (Tuple EaseInCirc easeInCirc)
  , Tuple "easeOutCirc" (Tuple EaseOutCirc easeOutCirc)
  , Tuple "easeInOutCirc" (Tuple EaseInOutCirc easeInOutCirc)
  , Tuple "easeInBack" (Tuple EaseInBack easeInBack)
  , Tuple "easeOutBack" (Tuple EaseOutBack easeOutBack)
  , Tuple "easeInOutBack" (Tuple EaseInOutBack easeInOutBack)
  , Tuple "easeInElastic" (Tuple EaseInElastic easeInElastic)
  , Tuple "easeOutElastic" (Tuple EaseOutElastic easeOutElastic)
  , Tuple "easeInOutElastic" (Tuple EaseInOutElastic easeInOutElastic)
  , Tuple "easeInBounce" (Tuple EaseInBounce easeInBounce)
  , Tuple "easeOutBounce" (Tuple EaseOutBounce easeOutBounce)
  , Tuple "easeInOutBounce" (Tuple EaseInOutBounce easeInOutBounce)
  ]

-- | Overshoot easing names (go below 0 or above 1)
overshootNames :: Array String
overshootNames =
  [ "easeInBack", "easeOutBack", "easeInOutBack"
  , "easeInElastic", "easeOutElastic", "easeInOutElastic"
  ]

-- | Bounded easings stay in [0,1]
boundedEasings :: Array (Tuple String (Number -> Number))
boundedEasings = allEasings
  # filter (\(Tuple name _) -> not (name `elem` overshootNames))
  # map (\(Tuple name (Tuple _ fn)) -> Tuple name fn)
  where
    elem x xs = any (_ == x) xs

-- | Monotonic easings (no bounce, no elastic, no back)
monotonicEasings :: Array (Tuple String (Number -> Number))
monotonicEasings =
  [ Tuple "linear" linear
  , Tuple "easeInSine" easeInSine, Tuple "easeOutSine" easeOutSine, Tuple "easeInOutSine" easeInOutSine
  , Tuple "easeInQuad" easeInQuad, Tuple "easeOutQuad" easeOutQuad, Tuple "easeInOutQuad" easeInOutQuad
  , Tuple "easeInCubic" easeInCubic, Tuple "easeOutCubic" easeOutCubic, Tuple "easeInOutCubic" easeInOutCubic
  , Tuple "easeInQuart" easeInQuart, Tuple "easeOutQuart" easeOutQuart, Tuple "easeInOutQuart" easeInOutQuart
  , Tuple "easeInQuint" easeInQuint, Tuple "easeOutQuint" easeOutQuint, Tuple "easeInOutQuint" easeInOutQuint
  , Tuple "easeInExpo" easeInExpo, Tuple "easeOutExpo" easeOutExpo, Tuple "easeInOutExpo" easeInOutExpo
  , Tuple "easeInCirc" easeInCirc, Tuple "easeOutCirc" easeOutCirc, Tuple "easeInOutCirc" easeInOutCirc
  ]

-- | Helper: assert greater than or equal (with tolerance)
assertGte :: Number -> Number -> Aff Unit
assertGte expected actual =
  if actual >= expected - tolerance
    then pure unit
    else fail ("Expected " <> show actual <> " >= " <> show expected)

-- | Helper: assert less than or equal (with tolerance)
assertLte :: Number -> Number -> Aff Unit
assertLte expected actual =
  if actual <= expected + tolerance
    then pure unit
    else fail ("Expected " <> show actual <> " <= " <> show expected)

assertLt :: Number -> Number -> Aff Unit
assertLt expected actual =
  if actual < expected
    then pure unit
    else fail ("Expected " <> show actual <> " < " <> show expected)

assertGt :: Number -> Number -> Aff Unit
assertGt expected actual =
  if actual > expected
    then pure unit
    else fail ("Expected " <> show actual <> " > " <> show expected)

--------------------------------------------------------------------------------
-- Test Spec
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = do
  describe "Easing Functions" do
    boundaryTests
    boundedRangeTests
    specificEasingTests
    overshootTests
    helperFunctionTests
    monotonicityTests
    symmetryTests
    edgeCaseTests

boundaryTests :: Spec Unit
boundaryTests = do
  describe "All easing functions: f(0) = 0" do
    for_ allEasings \(Tuple name (Tuple _ fn)) ->
      it (name <> "(0) = 0") do
        assertCloseTo tolerance 0.0 (fn 0.0)

  describe "All easing functions: f(1) = 1" do
    for_ allEasings \(Tuple name (Tuple _ fn)) ->
      it (name <> "(1) = 1") do
        assertCloseTo tolerance 1.0 (fn 1.0)

boundedRangeTests :: Spec Unit
boundedRangeTests = do
  describe "Bounded easings stay in [0, 1] range" do
    let tValues = [0.0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0]
    for_ boundedEasings \(Tuple name fn) ->
      it (name <> " outputs in [0, 1] for all t in [0, 1]") do
        for_ tValues \t -> do
          let result = fn t
          assertGte 0.0 result
          assertLte 1.0 result

specificEasingTests :: Spec Unit
specificEasingTests = do
  describe "linear" do
    it "is the identity function" do
      linear 0.0 `shouldEqual` 0.0
      linear 0.5 `shouldEqual` 0.5
      linear 1.0 `shouldEqual` 1.0

  describe "easeInQuad" do
    it "is t squared" do
      assertCloseTo tolerance 0.25 (easeInQuad 0.5)

  describe "easeOutQuad" do
    it "is 1 - (1-t)^2" do
      assertCloseTo tolerance 0.75 (easeOutQuad 0.5)

  describe "easeInCubic" do
    it "is t cubed" do
      assertCloseTo tolerance 0.125 (easeInCubic 0.5)

  describe "easeInExpo" do
    it "returns 0 at t=0" do
      easeInExpo 0.0 `shouldEqual` 0.0
    it "is nearly 0 at small t" do
      assertLt 0.01 (easeInExpo 0.1)

  describe "easeOutExpo" do
    it "returns 1 at t=1" do
      easeOutExpo 1.0 `shouldEqual` 1.0
    it "approaches 1 quickly" do
      assertGt 0.95 (easeOutExpo 0.5)

  describe "easeInOutSine" do
    it "is symmetric around 0.5" do
      let at25 = easeInOutSine 0.25
      let at75 = easeInOutSine 0.75
      assertCloseTo 1.0e-5 1.0 (at25 + at75)
    it "is 0.5 at t=0.5" do
      assertCloseTo tolerance 0.5 (easeInOutSine 0.5)

  describe "easeOutBounce" do
    it "bounces up multiple times" do
      let at60 = easeOutBounce 0.6
      let at70 = easeOutBounce 0.7
      assertLt at70 at60
    it "stays in [0, 1] range" do
      let steps = map (\i -> 0.05 * (toNumber i)) (0 .. 20)
      for_ steps \t -> do
        let result = easeOutBounce t
        assertGte 0.0 result
        assertLte 1.0 result

overshootTests :: Spec Unit
overshootTests = do
  describe "easeInBack (overshoot)" do
    it "goes negative for small t" do
      assertLt 0.0 (easeInBack 0.25)
    it "returns exactly 0 at t=0" do
      easeInBack 0.0 `shouldEqual` 0.0
    it "returns exactly 1 at t=1" do
      easeInBack 1.0 `shouldEqual` 1.0

  describe "easeOutBack (overshoot)" do
    it "goes above 1 before settling" do
      assertGt 1.0 (easeOutBack 0.75)
    it "returns exactly 0 at t=0" do
      easeOutBack 0.0 `shouldEqual` 0.0
    it "returns exactly 1 at t=1" do
      easeOutBack 1.0 `shouldEqual` 1.0

  describe "easeInElastic (overshoot)" do
    it "oscillates below 0" do
      let values = map easeInElastic [0.1, 0.2, 0.3, 0.4, 0.5]
      if any (_ < 0.0) values
        then pure unit
        else fail "Expected easeInElastic to go below 0 at some point"
    it "returns exactly 0 at t=0" do
      easeInElastic 0.0 `shouldEqual` 0.0
    it "returns exactly 1 at t=1" do
      easeInElastic 1.0 `shouldEqual` 1.0

  describe "easeOutElastic (overshoot)" do
    it "oscillates above 1" do
      let values = map easeOutElastic [0.5, 0.6, 0.7, 0.8, 0.9]
      if any (_ > 1.0) values
        then pure unit
        else fail "Expected easeOutElastic to go above 1 at some point"

helperFunctionTests :: Spec Unit
helperFunctionTests = do
  describe "applyEasing" do
    it "clamps input below 0" do
      applyEasing EaseLinear (-0.5) `shouldEqual` 0.0
    it "clamps input above 1" do
      applyEasing EaseLinear 1.5 `shouldEqual` 1.0
    it "applies named easing correctly" do
      assertCloseTo tolerance 0.25 (applyEasing EaseInQuad 0.5)

  describe "interpolateWithEasing" do
    it "returns start at t=0" do
      interpolateWithEasing 10.0 20.0 0.0 EaseLinear `shouldEqual` 10.0
    it "returns end at t=1" do
      interpolateWithEasing 10.0 20.0 1.0 EaseLinear `shouldEqual` 20.0
    it "returns midpoint at t=0.5 for linear" do
      interpolateWithEasing 0.0 100.0 0.5 EaseLinear `shouldEqual` 50.0
    it "applies easing to interpolation" do
      assertCloseTo tolerance 25.0 (interpolateWithEasing 0.0 100.0 0.5 EaseInQuad)
    it "handles negative ranges" do
      interpolateWithEasing (-100.0) 100.0 0.5 EaseLinear `shouldEqual` 0.0
    it "handles reversed ranges (end < start)" do
      interpolateWithEasing 100.0 0.0 0.5 EaseLinear `shouldEqual` 50.0

monotonicityTests :: Spec Unit
monotonicityTests = do
  describe "Monotonicity of non-overshoot functions" do
    for_ monotonicEasings \(Tuple name fn) ->
      it (name <> " is monotonically increasing") do
        let steps = map (\i -> 0.01 * (toNumber i)) (0 .. 100)
        checkMonotonic fn steps 0.0
  where
    checkMonotonic :: (Number -> Number) -> Array Number -> Number -> Aff Unit
    checkMonotonic _ [] _ = pure unit
    checkMonotonic fn ts prev = case ts of
      [] -> pure unit
      _ -> do
        let t = unsafeHead ts
        let curr = fn t
        if curr >= prev - tolerance
          then checkMonotonic fn (unsafeTail ts) curr
          else fail ("Not monotonic at t=" <> show t <> ": " <> show curr <> " < " <> show prev)

    unsafeHead :: forall a. Array a -> a
    unsafeHead arr = case arr of
      _ -> unsafePartialHead arr

    unsafeTail :: forall a. Array a -> Array a
    unsafeTail arr = case arr of
      _ -> unsafePartialTail arr

symmetryTests :: Spec Unit
symmetryTests = do
  describe "Power Easing Symmetry" do
    let families =
          [ { name: "Quad", eIn: easeInQuad, eOut: easeOutQuad, eInOut: easeInOutQuad }
          , { name: "Cubic", eIn: easeInCubic, eOut: easeOutCubic, eInOut: easeInOutCubic }
          , { name: "Quart", eIn: easeInQuart, eOut: easeOutQuart, eInOut: easeInOutQuart }
          , { name: "Quint", eIn: easeInQuint, eOut: easeOutQuint, eInOut: easeInOutQuint }
          ]
    for_ families \fam -> do
      it (fam.name <> ": easeIn(t) + easeOut(1-t) = 1") do
        for_ [0.0, 0.25, 0.5, 0.75, 1.0] \t -> do
          let sum = fam.eIn t + fam.eOut (1.0 - t)
          assertCloseTo 1.0e-5 1.0 sum
      it (fam.name <> ": easeInOut(0.5) = 0.5") do
        assertCloseTo 1.0e-5 0.5 (fam.eInOut 0.5)

edgeCaseTests :: Spec Unit
edgeCaseTests = do
  describe "Edge cases" do
    it "handles t = 0.5 for all easings without producing NaN" do
      for_ allEasings \(Tuple name (Tuple _ fn)) -> do
        assertFinite (fn 0.5)

    it "handles rapid repeated calls" do
      let steps = map (\i -> (toNumber i) / 1000.0) (0 .. 999)
      for_ steps \t ->
        assertFinite (easeInOutCubic t)

    it "produces consistent results (deterministic)" do
      for_ allEasings \(Tuple name (Tuple _ fn)) -> do
        let result1 = fn 0.5
        let result2 = fn 0.5
        result1 `shouldEqual` result2

-- | Convert Int to Number
toNumber :: Int -> Number
toNumber = Int.toNumber

-- | Unsafe head (array guaranteed non-empty by caller)
foreign import unsafePartialHead :: forall a. Array a -> a
foreign import unsafePartialTail :: forall a. Array a -> Array a
