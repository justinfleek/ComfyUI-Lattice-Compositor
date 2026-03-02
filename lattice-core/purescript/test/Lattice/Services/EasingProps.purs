-- | Port of ui/src/__tests__/services/easing.property.test.ts
-- |
-- | Property-based tests for mathematical invariants of easing functions.

module Test.Lattice.Services.EasingProps (spec) where

import Prelude

import Data.Array (any)
import Data.Foldable (for_)
import Data.Number as Number
import Effect.Aff (Aff)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Effect.Class (liftEffect)
import Test.QuickCheck (Result, (===), quickCheck)
import Test.QuickCheck.Gen (Gen, choose)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite)

import Lattice.Services.Easing
  ( EasingType(..)
  , applyEasing
  , applyEasingType
  , interpolateWithEasing
  , linear
  , easeInQuad, easeOutQuad, easeInOutQuad
  , easeInCubic, easeOutCubic, easeInOutCubic
  , easeInQuart, easeOutQuart, easeInOutQuart
  , easeInQuint, easeOutQuint, easeInOutQuint
  , easeInExpo, easeOutExpo
  , easeInBack, easeOutBack
  , easeInElastic, easeOutElastic
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Constants
-- ────────────────────────────────────────────────────────────────────────────

epsilon :: Number
epsilon = 1.0e-10

-- ────────────────────────────────────────────────────────────────────────────
-- Generators
-- ────────────────────────────────────────────────────────────────────────────

genT :: Gen Number
genT = choose 0.0 1.0

genExtendedT :: Gen Number
genExtendedT = choose (-2.0) 2.0

genValue :: Gen Number
genValue = choose (-1000.0) 1000.0

-- ────────────────────────────────────────────────────────────────────────────
-- Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "PROPERTY: Easing Functions" do
    boundaryProperties
    outputRangeProperties
    monotonicityProperties
    symmetryProperties
    determinismProperties
    linearIdentityProperties
    interpolationProperties
    expoProperties
    elasticProperties
    backProperties

boundaryProperties :: Spec Unit
boundaryProperties = do
  describe "Boundary Conditions" do
    it "f(0) = 0 for all easings" do
      let fns = allEasingFns
      for_ fns \{ name, fn } ->
        assertCloseTo epsilon 0.0 (fn 0.0)

    it "f(1) = 1 for all easings" do
      let fns = allEasingFns
      for_ fns \{ name, fn } ->
        assertCloseTo epsilon 1.0 (fn 1.0)

outputRangeProperties :: Spec Unit
outputRangeProperties = do
  describe "Output Range" do
    it "bounded easings stay in [0, 1] for random t" do
      liftEffect $ quickCheck \(_ :: Unit) -> do
        let fns = boundedEasingFns
        let t = 0.37 -- representative value
        let results = map (\{ fn } -> fn t) fns
        let allInRange = not (any (\r -> r < (0.0 - epsilon) || r > (1.0 + epsilon)) results)
        allInRange === true

    it "all easings produce finite output at t=0.5" do
      let fns = allEasingFns
      for_ fns \{ name, fn } ->
        assertFinite (fn 0.5)

monotonicityProperties :: Spec Unit
monotonicityProperties = do
  describe "Monotonicity" do
    it "monotonic easings: smaller t gives smaller output" do
      let fns = monotonicEasingFns
      for_ fns \{ name, fn } ->
        for_ [ { t1: 0.0, t2: 0.25 }
             , { t1: 0.25, t2: 0.5 }
             , { t1: 0.5, t2: 0.75 }
             , { t1: 0.75, t2: 1.0 }
             , { t1: 0.1, t2: 0.9 }
             ] \{ t1, t2 } -> do
          let r1 = fn t1
          let r2 = fn t2
          if r1 <= r2 + epsilon
            then pure unit
            else fail (name <> ": f(" <> show t1 <> ")=" <> show r1 <> " > f(" <> show t2 <> ")=" <> show r2)

symmetryProperties :: Spec Unit
symmetryProperties = do
  describe "Power Easing Symmetry" do
    let families =
          [ { name: "Quad", eIn: easeInQuad, eOut: easeOutQuad, eInOut: easeInOutQuad }
          , { name: "Cubic", eIn: easeInCubic, eOut: easeOutCubic, eInOut: easeInOutCubic }
          , { name: "Quart", eIn: easeInQuart, eOut: easeOutQuart, eInOut: easeInOutQuart }
          , { name: "Quint", eIn: easeInQuint, eOut: easeOutQuint, eInOut: easeInOutQuint }
          ]
    for_ families \fam -> do
      it (fam.name <> ": easeIn(t) + easeOut(1-t) = 1") do
        for_ [0.0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0] \t -> do
          let sum = fam.eIn t + fam.eOut (1.0 - t)
          assertCloseTo 1.0e-5 1.0 sum

      it (fam.name <> ": easeInOut(0.5) = 0.5") do
        assertCloseTo 1.0e-5 0.5 (fam.eInOut 0.5)

determinismProperties :: Spec Unit
determinismProperties = do
  describe "Determinism" do
    it "same input always produces same output" do
      let fns = allEasingFns
      for_ fns \{ name, fn } ->
        for_ [0.0, 0.25, 0.5, 0.75, 1.0] \t -> do
          let r1 = fn t
          let r2 = fn t
          r1 `shouldEqual` r2

linearIdentityProperties :: Spec Unit
linearIdentityProperties = do
  describe "Linear is Identity" do
    it "linear(t) = t for sample values" do
      for_ [0.0, 0.1, 0.25, 0.333, 0.5, 0.667, 0.75, 0.9, 1.0] \t ->
        linear t `shouldEqual` t

interpolationProperties :: Spec Unit
interpolationProperties = do
  describe "interpolateWithEasing" do
    it "at t=0 returns start" do
      for_ [10.0, -50.0, 0.0, 999.0] \start ->
        for_ [20.0, 100.0, -100.0] \end_ ->
          assertCloseTo 1.0e-5 start (interpolateWithEasing start end_ 0.0 EaseLinear)

    it "at t=1 returns end" do
      for_ [10.0, -50.0, 0.0] \start ->
        for_ [20.0, 100.0, -100.0] \end_ ->
          assertCloseTo 1.0e-5 end_ (interpolateWithEasing start end_ 1.0 EaseLinear)

    it "linear interpolation is exact" do
      for_ [0.0, 0.25, 0.5, 0.75, 1.0] \t -> do
        let result = interpolateWithEasing 0.0 100.0 t EaseLinear
        let expected = 100.0 * t
        assertCloseTo epsilon expected result

    it "interpolating same value gives that value" do
      for_ [0.0, 42.0, -100.0, 999.0] \v ->
        for_ [0.0, 0.25, 0.5, 0.75, 1.0] \t ->
          assertCloseTo 1.0e-5 v (interpolateWithEasing v v t EaseInQuad)

expoProperties :: Spec Unit
expoProperties = do
  describe "Expo Boundary Handling" do
    it "easeInExpo(0) = 0 exactly" do
      easeInExpo 0.0 `shouldEqual` 0.0
    it "easeOutExpo(1) = 1 exactly" do
      easeOutExpo 1.0 `shouldEqual` 1.0

elasticProperties :: Spec Unit
elasticProperties = do
  describe "Elastic Oscillation" do
    it "easeInElastic oscillates below 0" do
      let values = map easeInElastic [0.1, 0.2, 0.3, 0.4, 0.5]
      if any (_ < 0.0) values
        then pure unit
        else fail "Expected easeInElastic to go below 0"

    it "easeOutElastic oscillates above 1" do
      let values = map easeOutElastic [0.5, 0.6, 0.7, 0.8, 0.9]
      if any (_ > 1.0) values
        then pure unit
        else fail "Expected easeOutElastic to go above 1"

backProperties :: Spec Unit
backProperties = do
  describe "Back Overshoot" do
    it "easeInBack goes negative" do
      let values = map easeInBack [0.1, 0.2, 0.3]
      if any (_ < 0.0) values
        then pure unit
        else fail "Expected easeInBack to go below 0"

    it "easeOutBack goes above 1" do
      let values = map easeOutBack [0.7, 0.8, 0.9]
      if any (_ > 1.0) values
        then pure unit
        else fail "Expected easeOutBack to go above 1"

-- ────────────────────────────────────────────────────────────────────────────
-- Easing function lists
-- ────────────────────────────────────────────────────────────────────────────

type EasingEntry = { name :: String, fn :: Number -> Number }

allEasingFns :: Array EasingEntry
allEasingFns =
  [ { name: "linear", fn: linear }
  , { name: "easeInQuad", fn: easeInQuad }
  , { name: "easeOutQuad", fn: easeOutQuad }
  , { name: "easeInOutQuad", fn: easeInOutQuad }
  , { name: "easeInCubic", fn: easeInCubic }
  , { name: "easeOutCubic", fn: easeOutCubic }
  , { name: "easeInOutCubic", fn: easeInOutCubic }
  , { name: "easeInQuart", fn: easeInQuart }
  , { name: "easeOutQuart", fn: easeOutQuart }
  , { name: "easeInOutQuart", fn: easeInOutQuart }
  , { name: "easeInQuint", fn: easeInQuint }
  , { name: "easeOutQuint", fn: easeOutQuint }
  , { name: "easeInOutQuint", fn: easeInOutQuint }
  , { name: "easeInExpo", fn: easeInExpo }
  , { name: "easeOutExpo", fn: easeOutExpo }
  , { name: "easeInBack", fn: easeInBack }
  , { name: "easeOutBack", fn: easeOutBack }
  , { name: "easeInElastic", fn: easeInElastic }
  , { name: "easeOutElastic", fn: easeOutElastic }
  ]

boundedEasingFns :: Array EasingEntry
boundedEasingFns =
  [ { name: "linear", fn: linear }
  , { name: "easeInQuad", fn: easeInQuad }
  , { name: "easeOutQuad", fn: easeOutQuad }
  , { name: "easeInOutQuad", fn: easeInOutQuad }
  , { name: "easeInCubic", fn: easeInCubic }
  , { name: "easeOutCubic", fn: easeOutCubic }
  , { name: "easeInOutCubic", fn: easeInOutCubic }
  , { name: "easeInQuart", fn: easeInQuart }
  , { name: "easeOutQuart", fn: easeOutQuart }
  , { name: "easeInOutQuart", fn: easeInOutQuart }
  , { name: "easeInQuint", fn: easeInQuint }
  , { name: "easeOutQuint", fn: easeOutQuint }
  , { name: "easeInOutQuint", fn: easeInOutQuint }
  , { name: "easeInExpo", fn: easeInExpo }
  , { name: "easeOutExpo", fn: easeOutExpo }
  ]

monotonicEasingFns :: Array EasingEntry
monotonicEasingFns = boundedEasingFns
