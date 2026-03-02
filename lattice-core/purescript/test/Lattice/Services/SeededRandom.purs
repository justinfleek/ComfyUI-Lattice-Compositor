-- | Port of ui/src/__tests__/services/SeededRandom.test.ts
-- |
-- | Tests for the seeded random number generator (mulberry32 algorithm).
-- | Note: PureScript implementation is pure/functional (returns Tuple),
-- | while TypeScript was class-based/mutable. Tests thread state explicitly.

module Test.Lattice.Services.SeededRandom (spec) where

import Prelude

import Data.Array (replicate, foldl, any, all, length, (..))
import Data.Array as Array
import Data.Foldable (for_)
import Data.Int (toNumber) as Int
import Data.Number as Number
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Aff (Aff)
import Math (pi, sqrt) as Math
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Lattice.TestHelpers (assertCloseTo, assertFinite, assertInRange)

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

-- | Generate n random numbers, returning the final state and array of values
generateN :: Int -> RngState -> Tuple (Array Number) RngState
generateN n rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = next r
      in go (k - 1) (acc <> [v]) r'

-- | Advance the RNG n steps, discarding values
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
  describe "SeededRandom" do
    constructorTests
    resetTests
    setSeedTests
    stateCheckpointTests
    nextTests
    rangeTests
    intTests
    varianceTests
    boolTests
    angleTests
    inCircleTests
    onSphereTests
    gaussianTests
    determinismContract
    edgeCases

constructorTests :: Spec Unit
constructorTests = do
  describe "constructor" do
    it "creates with seed 12345" do
      let rng = create 12345.0
      getSeed rng `shouldEqual` 12345.0

    it "creates with custom seed" do
      let rng = create 42.0
      getSeed rng `shouldEqual` 42.0

    it "creates with seed 0" do
      let rng = create 0.0
      getSeed rng `shouldEqual` 0.0

resetTests :: Spec Unit
resetTests = do
  describe "reset" do
    it "reset returns to initial sequence" do
      let rng0 = create 12345.0
          Tuple v1 rng1 = next rng0
          Tuple v2 rng2 = next rng1
          Tuple v3 _ = next rng2
          -- Reset and regenerate
          rng0' = reset rng0
          Tuple v1' rng1' = next rng0'
          Tuple v2' rng2' = next rng1'
          Tuple v3' _ = next rng2'
      v1 `shouldEqual` v1'
      v2 `shouldEqual` v2'
      v3 `shouldEqual` v3'

    it "reset works after many calls" do
      let rng0 = create 12345.0
          Tuple firstVal _ = next rng0
          rng' = advance 10000 rng0
          rngReset = reset rng'
          Tuple firstVal' _ = next rngReset
      firstVal `shouldEqual` firstVal'

setSeedTests :: Spec Unit
setSeedTests = do
  describe "setSeed" do
    it "setSeed changes the sequence" do
      let rng0 = create 12345.0
          Tuple v1 _ = next rng0
          rng1 = setSeed 999.0 rng0
          Tuple v2 _ = next rng1
      -- Different seeds should produce different values
      if v1 == v2
        then fail "Expected different values for different seeds"
        else pure unit

    it "setSeed makes sequence match fresh instance" do
      let rng0 = create 12345.0
          rng1 = setSeed 999.0 rng0
          Tuple v1 _ = next rng1
          fresh = create 999.0
          Tuple v2 _ = next fresh
      v1 `shouldEqual` v2

stateCheckpointTests :: Spec Unit
stateCheckpointTests = do
  describe "getState / setState" do
    it "getState returns current internal state" do
      let rng = create 12345.0
          s = getState rng
      assertFinite s

    it "setState restores exact position in sequence" do
      let rng0 = create 12345.0
          -- Skip 2 calls
          rng1 = advance 2 rng0
          -- Checkpoint
          checkpoint = getState rng1
          -- Generate 3 expected values
          Tuple expected rng2 = generateN 3 rng1
          -- Advance 100 more
          rng3 = advance 100 rng2
          -- Restore
          rng4 = setState checkpoint rng3
          -- Generate again
          Tuple actual _ = generateN 3 rng4
      expected `shouldEqual` actual

nextTests :: Spec Unit
nextTests = do
  describe "next" do
    it "returns values in [0, 1)" do
      let rng = create 12345.0
          Tuple values _ = generateN 1000 rng
          allInRange = all (\v -> v >= 0.0 && v < 1.0) values
      if allInRange
        then pure unit
        else fail "Not all values in [0, 1)"

    it "produces deterministic sequence for same seed" do
      let rng1 = create 12345.0
          rng2 = create 12345.0
          Tuple seq1 _ = generateN 100 rng1
          Tuple seq2 _ = generateN 100 rng2
      seq1 `shouldEqual` seq2

    it "different seeds produce different sequences" do
      let rng1 = create 1.0
          rng2 = create 2.0
          Tuple seq1 _ = generateN 100 rng1
          Tuple seq2 _ = generateN 100 rng2
          -- Count matches
          pairs = Array.zip seq1 seq2
          matches = Array.length (Array.filter (\(Tuple a b) -> a == b) pairs)
      if matches < 5
        then pure unit
        else fail ("Expected < 5 matches, got " <> show matches)

rangeTests :: Spec Unit
rangeTests = do
  describe "range" do
    it "returns values in [min, max]" do
      let check _ r =
            let Tuple v r' = range 10.0 20.0 r
            in if v >= 10.0 && v <= 20.0
               then r'
               else r' -- will be caught by outer check
          rng = create 12345.0
          Tuple values _ = generateRangeN 1000 10.0 20.0 rng
          allOk = all (\v -> v >= 10.0 && v <= 20.0) values
      if allOk
        then pure unit
        else fail "range values out of bounds"

    it "handles negative range" do
      let rng = create 12345.0
          Tuple values _ = generateRangeN 100 (-100.0) (-50.0) rng
          allOk = all (\v -> v >= (-100.0) && v <= (-50.0)) values
      if allOk
        then pure unit
        else fail "negative range values out of bounds"

    it "returns min when min === max" do
      let rng = create 12345.0
          Tuple v _ = range 5.0 5.0 rng
      assertCloseTo 1.0e-10 5.0 v

intTests :: Spec Unit
intTests = do
  describe "int" do
    it "returns integers in [min, max] inclusive" do
      let rng = create 12345.0
          Tuple values _ = generateIntN 1000 1 6 rng
          allOk = all (\v -> v >= 1 && v <= 6) values
      if allOk
        then pure unit
        else fail "int values out of bounds"

    it "handles single value range" do
      let rng = create 12345.0
          Tuple v _ = int 5 5 rng
      v `shouldEqual` 5

varianceTests :: Spec Unit
varianceTests = do
  describe "variance" do
    it "stays within base +/- variance" do
      let rng = create 12345.0
          Tuple values _ = generateVarianceN 1000 50.0 10.0 rng
          allOk = all (\v -> v >= 40.0 && v <= 60.0) values
      if allOk
        then pure unit
        else fail "variance values out of bounds"

    it "handles zero variance" do
      let rng = create 12345.0
          Tuple v _ = variance 100.0 0.0 rng
      v `shouldEqual` 100.0

boolTests :: Spec Unit
boolTests = do
  describe "bool" do
    it "probability 0 always returns false" do
      let check rng =
            let Tuple v rng' = bool 0.0 rng
            in Tuple v rng'
          rng = create 12345.0
          Tuple results _ = generateBoolN 100 0.0 rng
          allFalse = all not results
      if allFalse
        then pure unit
        else fail "bool(0) returned true"

    it "probability 1 always returns true" do
      let rng = create 12345.0
          Tuple results _ = generateBoolN 100 1.0 rng
          allTrue = all identity results
      if allTrue
        then pure unit
        else fail "bool(1) returned false"

angleTests :: Spec Unit
angleTests = do
  describe "angle" do
    it "returns values in [0, 2*pi)" do
      let rng = create 12345.0
          twoPi = Math.pi * 2.0
          Tuple values _ = generateAngleN 1000 rng
          allOk = all (\v -> v >= 0.0 && v < twoPi) values
      if allOk
        then pure unit
        else fail "angle values out of bounds"

inCircleTests :: Spec Unit
inCircleTests = do
  describe "inCircle" do
    it "all points are within unit circle" do
      let rng = create 12345.0
          Tuple points _ = generateInCircleN 1000 rng
          allOk = all (\(Point2D p) -> p.x * p.x + p.y * p.y <= 1.0 + 1.0e-10) points
      if allOk
        then pure unit
        else fail "inCircle point outside unit circle"

onSphereTests :: Spec Unit
onSphereTests = do
  describe "onSphere" do
    it "all points are on unit sphere surface" do
      let rng = create 12345.0
          Tuple points _ = generateOnSphereN 1000 rng
          allOk = all (\(Point3D p) ->
            let dist = Math.sqrt (p.x * p.x + p.y * p.y + p.z * p.z)
            in dist >= 0.99 && dist <= 1.01) points
      if allOk
        then pure unit
        else fail "onSphere point not on unit sphere"

gaussianTests :: Spec Unit
gaussianTests = do
  describe "gaussian" do
    it "returns finite numbers" do
      let rng = create 12345.0
          Tuple values _ = generateGaussianN 1000 0.0 1.0 rng
          allOk = all Number.isFinite values
      if allOk
        then pure unit
        else fail "gaussian returned non-finite value"

    it "default mean is approximately 0" do
      let rng = create 12345.0
          Tuple values _ = generateGaussianN 10000 0.0 1.0 rng
          sum = foldl (+) 0.0 values
          mean = sum / 10000.0
      if Number.abs mean < 1.0
        then pure unit
        else fail ("Expected mean near 0, got " <> show mean)

determinismContract :: Spec Unit
determinismContract = do
  describe "DETERMINISM CONTRACT" do
    it "same seed produces identical all-method sequence" do
      let rng1 = create 42.0
          rng2 = create 42.0
          -- Exercise all methods on both RNGs identically
          Tuple nv1 r1a = next rng1
          Tuple nv2 r2a = next rng2
          Tuple rv1 r1b = range 0.0 100.0 r1a
          Tuple rv2 r2b = range 0.0 100.0 r2a
          Tuple iv1 r1c = int 0 10 r1b
          Tuple iv2 r2c = int 0 10 r2b
          Tuple vv1 r1d = variance 50.0 10.0 r1c
          Tuple vv2 r2d = variance 50.0 10.0 r2c
          Tuple bv1 r1e = bool 0.5 r1d
          Tuple bv2 r2e = bool 0.5 r2d
          Tuple av1 r1f = angle r1e
          Tuple av2 r2f = angle r2e
          Tuple (Point2D cv1) r1g = inCircle r1f
          Tuple (Point2D cv2) r2g = inCircle r2f
          Tuple (Point3D sv1) r1h = onSphere r1g
          Tuple (Point3D sv2) r2h = onSphere r2g
          Tuple gv1 _ = gaussian 0.0 1.0 r1h
          Tuple gv2 _ = gaussian 0.0 1.0 r2h
      nv1 `shouldEqual` nv2
      rv1 `shouldEqual` rv2
      iv1 `shouldEqual` iv2
      vv1 `shouldEqual` vv2
      bv1 `shouldEqual` bv2
      av1 `shouldEqual` av2
      cv1.x `shouldEqual` cv2.x
      cv1.y `shouldEqual` cv2.y
      sv1.x `shouldEqual` sv2.x
      sv1.y `shouldEqual` sv2.y
      sv1.z `shouldEqual` sv2.z
      gv1 `shouldEqual` gv2

    it "checkpoint restore produces identical continuation" do
      let rng0 = create 12345.0
          -- Skip 50
          rng1 = advance 50 rng0
          -- Checkpoint
          checkpoint = getState rng1
          -- Capture 100 expected
          Tuple expected rng2 = generateN 100 rng1
          -- Advance 1000 more
          rng3 = advance 1000 rng2
          -- Restore
          rng4 = setState checkpoint rng3
          -- Capture 100 actual
          Tuple actual _ = generateN 100 rng4
      expected `shouldEqual` actual

    it "reset produces identical sequence from start" do
      let rng0 = create 12345.0
          Tuple original rng1 = generateN 100 rng0
          -- Do random operations
          rng2 = advance 500 rng1
          -- Reset
          rng3 = reset rng2
          Tuple afterReset _ = generateN 100 rng3
      original `shouldEqual` afterReset

edgeCases :: Spec Unit
edgeCases = do
  describe "edge cases" do
    it "handles seed = 0" do
      let rng = create 0.0
          Tuple v _ = next rng
      assertFinite v
      if v >= 0.0 && v < 1.0
        then pure unit
        else fail "seed 0: value out of range"

    it "handles large number of iterations without degradation" do
      let rng = create 12345.0
          rng' = advance 100000 rng
          Tuple v _ = next rng'
      assertFinite v
      if v >= 0.0 && v < 1.0
        then pure unit
        else fail "degraded after many iterations"

-- ────────────────────────────────────────────────────────────────────────────
-- Bulk generation helpers
-- ────────────────────────────────────────────────────────────────────────────

generateRangeN :: Int -> Number -> Number -> RngState -> Tuple (Array Number) RngState
generateRangeN n lo hi rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = range lo hi r
      in go (k - 1) (acc <> [v]) r'

generateIntN :: Int -> Int -> Int -> RngState -> Tuple (Array Int) RngState
generateIntN n lo hi rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = int lo hi r
      in go (k - 1) (acc <> [v]) r'

generateVarianceN :: Int -> Number -> Number -> RngState -> Tuple (Array Number) RngState
generateVarianceN n base var rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = variance base var r
      in go (k - 1) (acc <> [v]) r'

generateBoolN :: Int -> Number -> RngState -> Tuple (Array Boolean) RngState
generateBoolN n prob rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = bool prob r
      in go (k - 1) (acc <> [v]) r'

generateAngleN :: Int -> RngState -> Tuple (Array Number) RngState
generateAngleN n rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = angle r
      in go (k - 1) (acc <> [v]) r'

generateInCircleN :: Int -> RngState -> Tuple (Array Point2D) RngState
generateInCircleN n rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = inCircle r
      in go (k - 1) (acc <> [v]) r'

generateOnSphereN :: Int -> RngState -> Tuple (Array Point3D) RngState
generateOnSphereN n rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = onSphere r
      in go (k - 1) (acc <> [v]) r'

generateGaussianN :: Int -> Number -> Number -> RngState -> Tuple (Array Number) RngState
generateGaussianN n mean stdDev rng = go n [] rng
  where
    go 0 acc r = Tuple acc r
    go k acc r =
      let Tuple v r' = gaussian mean stdDev r
      in go (k - 1) (acc <> [v]) r'
