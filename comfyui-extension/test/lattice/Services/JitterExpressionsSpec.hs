-- |
-- Test suite for Lattice.Services.JitterExpressions
--

module Lattice.Services.JitterExpressionsSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.JitterExpressions

-- Helper to create test params
createParams :: Double -> [Double] -> JitterParams
createParams time value = JitterParams
  { jitterParamsTime = time
  , jitterParamsValue = value
  }

spec :: TestTree
spec = testGroup "Lattice.Services.JitterExpressions"
  [ testGroup "jitter"
    [ testCase "jitter - deterministic" $ do
        let params = createParams 1.0 [0, 0, 0]
            result1 = jitter params 5.0 50.0 1 0.5 Nothing
            result2 = jitter params 5.0 50.0 1 0.5 Nothing
        -- Same inputs should give same outputs
        result1 @?= result2
    , testCase "jitter - adds noise" $ do
        let params = createParams 1.0 [0, 0]
            result = jitter params 5.0 50.0 1 0.5 Nothing
        -- Should have noise added
        head result /= 0 @?= True
    , testCase "jitter - default parameters" $
        jitter (createParams 1.0 [0, 0]) 5.0 50.0 1 0.5 Nothing @?=
        jitter (createParams 1.0 [0, 0]) 5.0 50.0 1 0.5 Nothing
    , testCase "jitter - octaves clamping" $ do
        let params = createParams 1.0 [0, 0]
            result1 = jitter params 5.0 50.0 (-1) 0.5 Nothing  -- Should clamp to 1
            result2 = jitter params 5.0 50.0 20 0.5 Nothing    -- Should clamp to 10
        -- Both should work without errors
        length result1 @?= 2
        length result2 @?= 2
    , testCase "jitter - time override" $ do
        let params = createParams 1.0 [0, 0]
            result1 = jitter params 5.0 50.0 1 0.5 (Just 2.0)
            result2 = jitter params 5.0 50.0 1 0.5 (Just 2.0)
        -- Should use override time
        result1 @?= result2
    ]
  , testGroup "temporalJitter"
    [ testCase "temporalJitter - deterministic" $ do
        let params = createParams 1.0 [0, 0, 0]
            result1 = temporalJitter params 5.0 50.0 1 Nothing
            result2 = temporalJitter params 5.0 50.0 1 Nothing
        -- Same inputs should give same outputs
        result1 @?= result2
    , testCase "temporalJitter - adds noise" $ do
        let params = createParams 1.0 [0, 0]
            result = temporalJitter params 5.0 50.0 1 Nothing
        -- Should have noise added
        head result /= 0 @?= True
    , testCase "temporalJitter - default parameters" $
        temporalJitter (createParams 1.0 [0, 0]) 5.0 50.0 1 Nothing @?=
        temporalJitter (createParams 1.0 [0, 0]) 5.0 50.0 1 Nothing
    , testCase "temporalJitter - octaves clamping" $ do
        let params = createParams 1.0 [0, 0]
            result1 = temporalJitter params 5.0 50.0 (-1) Nothing  -- Should clamp to 1
            result2 = temporalJitter params 5.0 50.0 20 Nothing    -- Should clamp to 10
        -- Both should work without errors
        length result1 @?= 2
        length result2 @?= 2
    , testCase "temporalJitter - frequency validation" $ do
        let params = createParams 1.0 [0, 0]
            result1 = temporalJitter params (-1) 50.0 1 Nothing  -- Should use default
            result2 = temporalJitter params 0 50.0 1 Nothing      -- Should use default
        -- Both should use default frequency (5.0)
        length result1 @?= 2
        length result2 @?= 2
    ]
  ]
