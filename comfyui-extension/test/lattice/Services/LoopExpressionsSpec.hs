-- |
-- Test suite for Lattice.Services.LoopExpressions
--

module Lattice.Services.LoopExpressionsSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.LoopExpressions

-- Helper to create test params
createParams :: Double -> Double -> Double -> [Double] -> [Double] -> [Double] -> [Double] -> LoopParams
createParams time startTime endTime value velocity startValue endValue = LoopParams
  { loopParamsTime = time
  , loopParamsStartTime = startTime
  , loopParamsEndTime = endTime
  , loopParamsValue = value
  , loopParamsVelocity = velocity
  , loopParamsStartValue = startValue
  , loopParamsEndValue = endValue
  }

spec :: TestTree
spec = testGroup "Lattice.Services.LoopExpressions"
  [ testGroup "repeatAfter"
    [ testCase "repeatAfter - before end time" $ do
        let (cycleTime, _) = repeatAfter (createParams 0.5 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopCycle
        cycleTime @?= 0.5  -- Should return current time
    , testCase "repeatAfter - cycle mode" $ do
        let (cycleTime, isReverse) = repeatAfter (createParams 2.5 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopCycle
        -- Duration is 1.0, elapsed is 1.5, so cycleTime should be 0.0 + 0.5 = 0.5
        abs (cycleTime - 0.5) < 0.01 @?= True
        isReverse @?= False
    , testCase "repeatAfter - pingpong mode forward" $ do
        let (cycleTime, isReverse) = repeatAfter (createParams 1.5 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopPingpong
        -- First cycle, should be forward
        isReverse @?= False
    , testCase "repeatAfter - pingpong mode reverse" $ do
        let (cycleTime, isReverse) = repeatAfter (createParams 2.5 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopPingpong
        -- Second cycle, should be reverse
        isReverse @?= True
    , testCase "repeatAfter - offset mode" $ do
        let (cycleTime, isReverse) = repeatAfter (createParams 2.5 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopOffset
        -- Should return cycle time
        abs (cycleTime - 0.5) < 0.01 @?= True
        isReverse @?= False
    , testCase "repeatAfter - continue mode" $ do
        let (cycleTime, isReverse) = repeatAfter (createParams 2.5 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopContinue
        cycleTime @?= 2.5  -- Should return current time
        isReverse @?= False
    ]
  , testGroup "repeatAfterOffset"
    [ testCase "repeatAfterOffset - single cycle" $ do
        let result = repeatAfterOffset (createParams 2.0 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) 1.0
        -- 1 cycle elapsed, so offset should be 1 * delta = 10
        result !! 0 @?= 10.0
    , testCase "repeatAfterOffset - multiple cycles" $ do
        let result = repeatAfterOffset (createParams 3.0 0.0 1.0 [0, 0] [0, 0] [0, 0] [10, 10]) 2.0
        -- 2 cycles elapsed, so offset should be 2 * delta = 20
        result !! 0 @?= 20.0
    ]
  , testGroup "repeatAfterContinue"
    [ testCase "repeatAfterContinue - with velocity" $ do
        let result = repeatAfterContinue (createParams 2.0 0.0 1.0 [0, 0] [1, 2] [0, 0] [10, 10]) 1.0
        -- Should add velocity * elapsed
        result !! 0 @?= 1.0
        result !! 1 @?= 2.0
    ]
  , testGroup "repeatBefore"
    [ testCase "repeatBefore - after start time" $ do
        let (cycleTime, _) = repeatBefore (createParams 1.5 1.0 2.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopCycle
        cycleTime @?= 1.5  -- Should return current time
    , testCase "repeatBefore - cycle mode" $ do
        let (cycleTime, isReverse) = repeatBefore (createParams 0.5 1.0 2.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopCycle
        -- Duration is 1.0, elapsed is 0.5, so cycleTime should be 2.0 - 0.5 = 1.5
        abs (cycleTime - 1.5) < 0.01 @?= True
        isReverse @?= False
    , testCase "repeatBefore - pingpong mode forward" $ do
        let (cycleTime, isReverse) = repeatBefore (createParams 0.5 1.0 2.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopPingpong
        -- First cycle going backward, should be reverse
        isReverse @?= True
    , testCase "repeatBefore - continue mode" $ do
        let (cycleTime, isReverse) = repeatBefore (createParams 0.5 1.0 2.0 [0, 0] [0, 0] [0, 0] [10, 10]) LoopContinue
        cycleTime @?= 0.5  -- Should return current time
        isReverse @?= False
    ]
  , testGroup "repeatBeforeOffset"
    [ testCase "repeatBeforeOffset - single cycle" $ do
        let result = repeatBeforeOffset (createParams 0.0 1.0 2.0 [0, 0] [0, 0] [0, 0] [10, 10]) 1.0
        -- 1 cycle elapsed, delta is start - end = 0 - 10 = -10, so offset should be -10
        result !! 0 @?= (-10.0)
    ]
  , testGroup "repeatBeforeContinue"
    [ testCase "repeatBeforeContinue - with velocity" $ do
        let result = repeatBeforeContinue (createParams 0.0 1.0 2.0 [10, 20] [1, 2] [0, 0] [10, 10]) 1.0
        -- Should subtract velocity * elapsed
        result !! 0 @?= 9.0  -- 10 - 1*1
        result !! 1 @?= 18.0  -- 20 - 2*1
    ]
  ]
