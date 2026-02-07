-- |
-- Module      : Lattice.State.DepthflowSpec
-- Description : Test suite for depthflow state management
--

module Lattice.State.DepthflowSpec (spec) where

import Data.Aeson (Number(..), Value(..))
import Lattice.State.Depthflow (sanitizeNumber)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, assertEqual)

-- ============================================================================
-- TEST SUITE
-- ============================================================================

spec :: TestTree
spec =
  testGroup
    "Lattice.State.Depthflow"
    [ testGroup
        "sanitizeNumber"
        [ testCase "sanitizeNumber - returns valid number" $ do
            let result = sanitizeNumber (Number 42.0) 0.0
            assertEqual "Should return valid number" 42.0 result
        , testCase "sanitizeNumber - returns default for String" $ do
            let result = sanitizeNumber (String "not a number") 5.0
            assertEqual "Should return default" 5.0 result
        , testCase "sanitizeNumber - returns default for Bool" $ do
            let result = sanitizeNumber (Bool True) 10.0
            assertEqual "Should return default" 10.0 result
        , testCase "sanitizeNumber - returns default for Null" $ do
            let result = sanitizeNumber Null 15.0
            assertEqual "Should return default" 15.0 result
        , testCase "sanitizeNumber - returns default for Object" $ do
            let result = sanitizeNumber (Object mempty) 20.0
            assertEqual "Should return default" 20.0 result
        , testCase "sanitizeNumber - returns default for Array" $ do
            let result = sanitizeNumber (Array []) 25.0
            assertEqual "Should return default" 25.0 result
        , testCase "sanitizeNumber - handles zero" $ do
            let result = sanitizeNumber (Number 0.0) 100.0
            assertEqual "Should return zero" 0.0 result
        , testCase "sanitizeNumber - handles negative numbers" $ do
            let result = sanitizeNumber (Number (-10.5)) 0.0
            assertEqual "Should return negative number" (-10.5) result
        , testCase "sanitizeNumber - handles large numbers" $ do
            let result = sanitizeNumber (Number 1000000.0) 0.0
            assertEqual "Should return large number" 1000000.0 result
        ]
    ]
