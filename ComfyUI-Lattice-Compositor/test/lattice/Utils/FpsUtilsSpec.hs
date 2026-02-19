-- |
-- Test suite for Lattice.Utils.FpsUtils
--

module Lattice.Utils.FpsUtilsSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Utils.FpsUtils

spec :: TestTree
spec = testGroup "Lattice.Utils.FpsUtils"
  [ testGroup "Constants"
    [ testCase "defaultFps" $
        defaultFps @?= 16.0
    , testCase "minFps" $
        minFps @?= 1.0
    , testCase "maxFps" $
        maxFps @?= 120.0
    ]
  , testGroup "Validation"
    [ testCase "validateFps - valid fps" $
        validateFps (Just 30.0) 16.0 @?= 30.0
    , testCase "validateFps - below minimum" $
        validateFps (Just 0.5) 16.0 @?= 1.0
    , testCase "validateFps - above maximum" $
        validateFps (Just 200.0) 16.0 @?= 120.0
    , testCase "validateFps - null" $
        validateFps Nothing 16.0 @?= 16.0
    , testCase "assertValidFps - valid fps" $
        case assertValidFps (Just 30.0) Nothing of
          Right fps -> fps @?= 30.0
          Left _ -> assertFailure "Should succeed"
    , testCase "assertValidFps - invalid fps" $
        case assertValidFps (Just 0.0) Nothing of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail"
    ]
  , testGroup "Safe Operations"
    [ testCase "safeDivideByFps - normal division" $
        safeDivideByFps 30.0 (Just 30.0) 0.0 @?= 1.0
    , testCase "safeDivideByFps - invalid fps" $
        safeDivideByFps 30.0 Nothing 0.0 @?= 30.0 / 16.0
    ]
  , testGroup "Frame/Time Conversion"
    [ testCase "frameToTime - normal conversion" $
        frameToTime 30.0 (Just 30.0) @?= 1.0
    , testCase "timeToFrame - normal conversion" $
        timeToFrame 1.0 (Just 30.0) @?= 30.0
    , testCase "frameToTime - roundtrip" $ do
        let fps = Just 24.0
            frame = 48.0
            time = frameToTime frame fps
            frame' = timeToFrame time fps
        frame' @?= frame
    ]
  , testGroup "Duration Calculations"
    [ testCase "calculateDuration - normal" $
        calculateDuration 60.0 (Just 30.0) @?= 2.0
    , testCase "calculateFrameCount - normal" $
        calculateFrameCount 2.0 (Just 30.0) @?= 60.0
    , testCase "calculateFrameCount - ceiling" $
        calculateFrameCount 1.5 (Just 30.0) @?= 45.0  -- 1.5 * 30 = 45
    ]
  ]
