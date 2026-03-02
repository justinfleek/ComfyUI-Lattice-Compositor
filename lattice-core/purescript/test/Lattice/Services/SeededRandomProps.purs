-- | Port of ui/src/__tests__/services/SeededRandom.property.test.ts
-- |
-- | Property-based tests for SeededRandom invariants.

module Test.Lattice.Services.SeededRandomProps (spec) where

import Prelude

import Data.Array (all, length)
import Data.Array as Array
import Data.Foldable (for_, foldl)
import Data.Int (toNumber) as Int
import Data.Number as Number
import Data.Number (abs) as Math
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Math (pi, sqrt) as Math
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.QuickCheck (Result, (===), quickCheck)
import Test.QuickCheck.Gen (Gen, choose, chooseInt)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite)

import Lattice.Services.Particles.SeededRandom
  ( RngState(..), Point2D(..), Point3D(..)
  , create, reset, setSeed
  , getState, setState, getSeed
  , next, nextN
  , range, int, variance, bool
  , angle
  , inCircle, onSphere
  , gaussian
  )

-- ────────────────────────────────────────────────────────────────────────────
-- Helpers
-- ────────────────────────────────────────────────────────────────────────────

generateN :: Int -> RngState -> Tuple (Array Number) RngState
generateN n rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = next r
      in go (k - 1) (acc <> [v]) r'

advance :: Int -> RngState -> RngState
advance 0 rng = rng
advance n rng =
  let Tuple _ rng' = next rng
  in advance (n - 1) rng'

-- ────────────────────────────────────────────────────────────────────────────
-- Spec
-- ────────────────────────────────────────────────────────────────────────────

spec :: Spec Unit
spec = do
  describe "PROPERTY: SeededRandom" do
    determinismInvariants
    outputBounds
    mathematicalInvariants
    probabilityCorrectness
    seedOperations
    mulberry32Specific

determinismInvariants :: Spec Unit
determinismInvariants = do
  describe "DETERMINISM INVARIANTS" do
    it "same seed always produces identical first value" do
      -- Test with several representative seeds
      for_ [0.0, 1.0, 42.0, 12345.0, 999999.0, 2147483647.0] \seed -> do
        let rng1 = create seed
            rng2 = create seed
            Tuple v1 _ = next rng1
            Tuple v2 _ = next rng2
        v1 `shouldEqual` v2

    it "same seed produces identical sequence for various lengths" do
      for_ [1, 5, 10, 50, 100] \n ->
        for_ [42.0, 12345.0, 0.0] \seed -> do
          let rng1 = create seed
              rng2 = create seed
              Tuple seq1 _ = generateN n rng1
              Tuple seq2 _ = generateN n rng2
          seq1 `shouldEqual` seq2

    it "different seeds produce different sequences" do
      for_ [ { s1: 1.0, s2: 2.0 }
           , { s1: 42.0, s2: 43.0 }
           , { s1: 0.0, s2: 999.0 }
           ] \{ s1, s2 } -> do
        let rng1 = create s1
            rng2 = create s2
            Tuple seq1 _ = generateN 100 rng1
            Tuple seq2 _ = generateN 100 rng2
            pairs = Array.zip seq1 seq2
            diffs = Array.length (Array.filter (\(Tuple a b) -> a /= b) pairs)
        if diffs > 90
          then pure unit
          else fail ("Expected >90 differences, got " <> show diffs)

    it "reset always returns to start of sequence" do
      for_ [42.0, 12345.0, 0.0, 999.0] \seed ->
        for_ [1, 10, 50, 100] \skipCount -> do
          let rng0 = create seed
              Tuple firstVal _ = next rng0
              rng1 = advance skipCount rng0
              rng2 = reset rng1
              Tuple firstVal' _ = next rng2
          firstVal `shouldEqual` firstVal'

    it "checkpoint/restore produces identical continuation" do
      for_ [42.0, 12345.0] \seed ->
        for_ [5, 20, 50] \skipCount ->
          for_ [5, 20] \checkCount -> do
            let rng0 = create seed
                rng1 = advance skipCount rng0
                checkpoint = getState rng1
                Tuple expected rng2 = generateN checkCount rng1
                rng3 = advance 50 rng2
                rng4 = setState checkpoint rng3
                Tuple actual _ = generateN checkCount rng4
            expected `shouldEqual` actual

outputBounds :: Spec Unit
outputBounds = do
  describe "OUTPUT BOUNDS" do
    it "next() always returns value in [0, 1) for many seeds" do
      for_ [0.0, 1.0, 42.0, 12345.0, 2147483647.0] \seed -> do
        let rng = create seed
            Tuple values _ = generateN 100 rng
            allOk = all (\v -> v >= 0.0 && v < 1.0) values
        if allOk
          then pure unit
          else fail ("Bounds violation for seed " <> show seed)

    it "next() is never NaN or Infinity" do
      for_ [0.0, 42.0, 12345.0, 999999.0] \seed -> do
        let rng = create seed
            Tuple values _ = generateN 1000 rng
            allFinite = all Number.isFinite values
        if allFinite
          then pure unit
          else fail "Got NaN or Infinity"

    it "range(min, max) returns value in [min, max]" do
      for_ [ { lo: 0.0, hi: 100.0 }
           , { lo: -50.0, hi: 50.0 }
           , { lo: -1000.0, hi: -500.0 }
           ] \{ lo, hi } ->
        for_ [42.0, 12345.0] \seed -> do
          let rng = create seed
              Tuple v _ = range lo hi rng
          if v >= lo && v <= hi
            then pure unit
            else fail ("range out of bounds: " <> show v)

    it "angle() returns value in [0, 2*pi)" do
      let twoPi = Math.pi * 2.0
      for_ [42.0, 12345.0, 0.0, 999.0] \seed -> do
        let rng = create seed
            Tuple v _ = angle rng
        if v >= 0.0 && v < twoPi
          then pure unit
          else fail ("angle out of bounds: " <> show v)

mathematicalInvariants :: Spec Unit
mathematicalInvariants = do
  describe "MATHEMATICAL INVARIANTS" do
    it "inCircle() point is within unit circle" do
      for_ [42.0, 12345.0, 0.0, 999.0, 777.0] \seed -> do
        let rng = create seed
            Tuple (Point2D p) _ = inCircle rng
            distSq = p.x * p.x + p.y * p.y
        if distSq <= 1.0 + 1.0e-10
          then pure unit
          else fail ("Point outside unit circle, distSq=" <> show distSq)

    it "onSphere() point is on unit sphere surface" do
      for_ [42.0, 12345.0, 0.0, 999.0, 777.0] \seed -> do
        let rng = create seed
            Tuple (Point3D p) _ = onSphere rng
            dist = Math.sqrt (p.x * p.x + p.y * p.y + p.z * p.z)
        assertCloseTo 1.0e-5 1.0 dist

    it "variance(base, v) returns value within base +/- v" do
      for_ [ { base: 50.0, var: 10.0 }
           , { base: 0.0, var: 100.0 }
           , { base: -50.0, var: 5.0 }
           ] \{ base: b, var: v } ->
        for_ [42.0, 12345.0] \seed -> do
          let rng = create seed
              Tuple result _ = variance b v rng
          if result >= b - v && result <= b + v
            then pure unit
            else fail ("variance out of bounds: " <> show result)

    it "gaussian() always returns finite number" do
      for_ [42.0, 12345.0, 0.0, 999.0] \seed -> do
        let rng = create seed
            Tuple v _ = gaussian 0.0 1.0 rng
        assertFinite v

    it "gaussian(0, 1) produces values centered around 0" do
      for_ [42.0, 12345.0] \seed -> do
        let rng = create seed
            Tuple values _ = generateGaussianN 1000 0.0 1.0 rng
            sum = foldl (+) 0.0 values
            mean = sum / 1000.0
        if Math.abs mean < 0.2
          then pure unit
          else fail ("Mean not close to 0: " <> show mean)

probabilityCorrectness :: Spec Unit
probabilityCorrectness = do
  describe "PROBABILITY CORRECTNESS" do
    it "bool(0) always returns false" do
      for_ [42.0, 12345.0, 0.0] \seed -> do
        let rng = create seed
            Tuple v _ = bool 0.0 rng
        v `shouldEqual` false

    it "bool(1) always returns true" do
      for_ [42.0, 12345.0, 0.0] \seed -> do
        let rng = create seed
            Tuple v _ = bool 1.0 rng
        -- next() returns [0, 1), so v < 1.0 is always true
        v `shouldEqual` true

seedOperations :: Spec Unit
seedOperations = do
  describe "SEED OPERATIONS" do
    it "getSeed() returns constructor seed" do
      for_ [0.0, 42.0, 12345.0, 999999.0] \seed -> do
        let rng = create seed
        getSeed rng `shouldEqual` seed

    it "setSeed() updates seed and matches fresh instance" do
      for_ [ { s1: 42.0, s2: 999.0 }
           , { s1: 0.0, s2: 12345.0 }
           ] \{ s1, s2 } -> do
        let rng = create s1
            rng' = setSeed s2 rng
        getSeed rng' `shouldEqual` s2
        let Tuple v1 _ = next rng'
            Tuple v2 _ = next (create s2)
        v1 `shouldEqual` v2

mulberry32Specific :: Spec Unit
mulberry32Specific = do
  describe "MULBERRY32 SPECIFIC" do
    it "mulberry32 produces non-zero after reasonable iterations" do
      for_ [1.0, 42.0, 12345.0, 999.0] \seed -> do
        let rng = create seed
            Tuple values _ = generateN 100 rng
            hasNonZero = Array.any (\v -> v > 0.001) values
        if hasNonZero
          then pure unit
          else fail ("No non-zero values for seed " <> show seed)

    it "state advances on each call" do
      for_ [42.0, 12345.0] \seed -> do
        let rng = create seed
            states = collectStates 10 rng
            unique = Array.nub states
        if Array.length unique == 10
          then pure unit
          else fail "States not all unique"

    it "instances do not affect each other" do
      let rng1 = create 42.0
          rng2 = create 999.0
          Tuple _ rng1' = next rng1
          Tuple _ rng2' = next rng2
          -- Advance rng1 1000 times
          rng1'' = advance 1000 rng1'
          -- rng2 should be independent
          rng2Fresh = create 999.0
          Tuple _ rng2Fresh' = next rng2Fresh
          Tuple v2 _ = next rng2'
          Tuple v2Fresh _ = next rng2Fresh'
      v2 `shouldEqual` v2Fresh

-- ────────────────────────────────────────────────────────────────────────────
-- Additional helpers
-- ────────────────────────────────────────────────────────────────────────────

collectStates :: Int -> RngState -> Array Number
collectStates 0 _ = []
collectStates n rng =
  let s = getState rng
      Tuple _ rng' = next rng
  in [s] <> collectStates (n - 1) rng'

generateGaussianN :: Int -> Number -> Number -> RngState -> Tuple (Array Number) RngState
generateGaussianN n mean stdDev rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = gaussian mean stdDev r
      in go (k - 1) (acc <> [v]) r'
