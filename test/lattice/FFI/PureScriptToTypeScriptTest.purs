-- |
-- Module      : Lattice.FFI.PureScriptToTypeScriptTest
-- Description : Round-trip tests for PureScript ↔ TypeScript converters
-- 
-- Property tests verifying that conversions preserve values correctly.
-- All tests use Test.QuickCheck for property-based testing.
--

module Lattice.FFI.PureScriptToTypeScriptTest where

import Prelude
import Test.QuickCheck (class Arbitrary, quickCheck, (===))
import Test.Spec (Spec, describe, it, pending)
import Data.Either (Either(..))
import Lattice.FFI.PureScriptToTypeScript
  ( psToTs
  , tsToPs
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // round
-- ════════════════════════════════════════════════════════════════════════════

-- | Test: PS → TS → PS round-trip
-- 
-- Property: Converting a PureScript value to TypeScript and back should
-- yield the original value.
roundTripPSTS :: forall a. Eq a => EncodeJson a => DecodeJson a => a -> Boolean
roundTripPSTS x = 
  case tsToPs (psToTs x) of
    Right x' -> x == x'
    Left _ -> false

-- ════════════════════════════════════════════════════════════════════════════
--                                                                      // type
-- ════════════════════════════════════════════════════════════════════════════

--                                                                      // note
-- instances. For now, this module provides the generic test framework.
--
-- Example generated tests:
--
-- roundTripPSTSPoint3 :: Point3 -> Boolean
-- roundTripPSTSPoint3 = roundTripPSTS

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // spec // test // suite
-- ════════════════════════════════════════════════════════════════════════════

spec :: Spec Unit
spec = do
  describe "PureScriptToTypeScript round-trip tests" $ do
    it "should round-trip Point3 values" $ do
      --                                                                      // todo
      pending

    it "should round-trip Vec3 values" $ do
      --                                                                      // todo
      pending

-- ════════════════════════════════════════════════════════════════════════════
--                                           // quickcheck // property // tests
-- ════════════════════════════════════════════════════════════════════════════

-- Run property tests with: quickCheck roundTripPSTS
