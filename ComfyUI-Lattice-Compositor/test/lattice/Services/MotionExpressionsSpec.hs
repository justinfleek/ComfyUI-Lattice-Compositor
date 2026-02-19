-- |
-- Test suite for Lattice.Services.MotionExpressions
--

module Lattice.Services.MotionExpressionsSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.MotionExpressions

-- Helper to create test params
createParams :: Double -> Double -> [Double] -> [Double] -> Double -> MotionParams
createParams time keyTime value velocity fps = MotionParams
  { motionParamsTime = time
  , motionParamsKeyTime = keyTime
  , motionParamsValue = value
  , motionParamsVelocity = velocity
  , motionParamsFps = fps
  }

spec :: TestTree
spec = testGroup "Lattice.Services.MotionExpressions"
  [ testGroup "inertia"
    [ testCase "inertia - before keyframe" $
        inertia (createParams 0.0 1.0 [0, 0, 0] [1, 1, 1] 16) 0.1 2.0 2.0 @?= [0, 0, 0]
    , testCase "inertia - at keyframe" $
        inertia (createParams 1.0 1.0 [0, 0, 0] [1, 1, 1] 16) 0.1 2.0 2.0 @?= [0, 0, 0]
    , testCase "inertia - after keyframe" $ do
        let result = inertia (createParams 2.0 1.0 [0, 0, 0] [1, 1, 1] 16) 0.1 2.0 2.0
        length result @?= 3
        -- Should have oscillation added
        head result /= 0 @?= True
    , testCase "inertia - default parameters" $
        inertia (createParams 2.0 1.0 [0, 0] [1, 1] 16) 0.1 2.0 2.0 @?= inertia (createParams 2.0 1.0 [0, 0] [1, 1] 16) 0.1 2.0 2.0
    , testCase "inertia - mismatched array lengths" $ do
        let result = inertia (createParams 2.0 1.0 [0, 0] [1, 1, 1] 16) 0.1 2.0 2.0
        length result @?= 3  -- Should use max length
    ]
  , testGroup "bounce"
    [ testCase "bounce - before keyframe" $
        bounce (createParams 0.0 1.0 [0, 0, 0] [0, 0, 0] 16) 0.7 4000 @?= [0, 0, 0]
    , testCase "bounce - at keyframe" $
        bounce (createParams 1.0 1.0 [0, 0, 0] [0, 0, 0] 16) 0.7 4000 @?= [0, 0, 0]
    , testCase "bounce - after keyframe" $ do
        let result = bounce (createParams 2.0 1.0 [10, 10, 10] [0, 0, 0] 16) 0.7 4000
        length result @?= 3
        -- Should have bounce offset subtracted
        result !! 0 < 10 @?= True
    , testCase "bounce - default parameters" $
        bounce (createParams 2.0 1.0 [0, 0] [0, 0] 16) 0.7 4000 @?= bounce (createParams 2.0 1.0 [0, 0] [0, 0] 16) 0.7 4000
    , testCase "bounce - elasticity clamping" $ do
        let result1 = bounce (createParams 2.0 1.0 [0, 0] [0, 0] 16) (-1) 4000  -- Should clamp to 0
            result2 = bounce (createParams 2.0 1.0 [0, 0] [0, 0] 16) 2.0 4000   -- Should clamp to 1
        result1 @?= result2  -- Both should use clamped values
    ]
  , testGroup "elastic"
    [ testCase "elastic - before keyframe" $
        elastic (createParams 0.0 1.0 [0, 0, 0] [0, 0, 0] 16) 1.0 0.3 @?= [0, 0, 0]
    , testCase "elastic - at keyframe" $
        elastic (createParams 1.0 1.0 [0, 0, 0] [0, 0, 0] 16) 1.0 0.3 @?= [0, 0, 0]
    , testCase "elastic - after keyframe" $ do
        let result = elastic (createParams 2.0 1.0 [0, 0, 0] [0, 0, 0] 16) 1.0 0.3
        length result @?= 3
        -- Should have oscillation added
        head result /= 0 @?= True
    , testCase "elastic - default parameters" $
        elastic (createParams 2.0 1.0 [0, 0] [0, 0] 16) 1.0 0.3 @?= elastic (createParams 2.0 1.0 [0, 0] [0, 0] 16) 1.0 0.3
    , testCase "elastic - period validation" $
        elastic (createParams 2.0 1.0 [0, 0] [0, 0] 16) 1.0 (-1) @?= elastic (createParams 2.0 1.0 [0, 0] [0, 0] 16) 1.0 0.3  -- Should use default
    ]
  ]
