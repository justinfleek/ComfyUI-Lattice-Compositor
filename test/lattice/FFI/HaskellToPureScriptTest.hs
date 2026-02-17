-- |
-- Module      : Lattice.FFI.HaskellToPureScriptTest
-- Description : Round-trip tests for Haskell ↔ PureScript converters
-- 
-- Property tests verifying that conversions preserve values correctly.
-- All tests use QuickCheck for property-based testing.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.FFI.HaskellToPureScriptTest where

import Test.QuickCheck
import Test.Hspec
import Data.Aeson
  ( ToJSON(..)
  , FromJSON(..)
  )
import Lattice.FFI.HaskellToPureScript
  ( hsToPs
  , psToHs
  )

-- ============================================================================
-- ROUND-TRIP PROPERTY TESTS
-- ============================================================================

-- | Test: HS → PS → HS round-trip
-- 
-- Property: Converting a Haskell value to PureScript and back should
-- yield the original value.
prop_roundTripHSPS :: (Eq a, ToJSON a, FromJSON a, Show a) => a -> Property
prop_roundTripHSPS x = 
  case psToHs (hsToPs x) of
    Right x' -> x === x'
    Left err -> property False
      -- TODO: Better error reporting

-- ============================================================================
-- TYPE-SPECIFIC TESTS
-- ============================================================================

-- NOTE: Type-specific tests will be generated from Lean4 Extractable
-- instances. For now, this module provides the generic test framework.
--
-- Example generated tests:
--
-- prop_roundTripHSPSPoint3 :: Point3 -> Property
-- prop_roundTripHSPSPoint3 = prop_roundTripHSPS

-- ============================================================================
-- HSPEC TEST SUITE
-- ============================================================================

spec :: Spec
spec = do
  describe "HaskellToPureScript round-trip tests" $ do
    it "should round-trip Point3 values" $ do
      -- TODO: Add specific test cases once Point3 is available
      pending

    it "should round-trip Vec3 values" $ do
      -- TODO: Add specific test cases once Vec3 is available
      pending

-- ============================================================================
-- QUICKCHECK PROPERTY TESTS
-- ============================================================================

-- Run property tests with: quickCheck prop_roundTripHSPS
