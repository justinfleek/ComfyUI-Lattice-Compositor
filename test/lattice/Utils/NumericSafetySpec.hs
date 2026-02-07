-- |
-- Test suite for Lattice.Utils.NumericSafety
--

module Lattice.Utils.NumericSafetySpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Utils.NumericSafety
import Prelude hiding (pi)
import qualified Prelude as P

spec :: TestTree
spec = testGroup "Lattice.Utils.NumericSafety"
  [ testGroup "Basic Safety"
    [ testCase "ensureFinite - finite number" $
        ensureFinite 42.5 0.0 @?= 42.5
    , testCase "ensureFinite - NaN" $
        ensureFinite (0/0) 0.0 @?= 0.0
    , testCase "requireFinite - finite number" $
        case requireFinite 42.5 "test" of
          Right val -> val @?= 42.5
          Left _ -> assertFailure "Should succeed"
    , testCase "requireFinite - NaN" $
        case requireFinite (0/0) "test" of
          Left _ -> return ()
          Right _ -> assertFailure "Should fail for NaN"
    ]
  , testGroup "Safe Arithmetic"
    [ testCase "safeDivide - normal division" $
        safeDivide 10.0 2.0 0.0 @?= 5.0
    , testCase "safeDivide - division by zero" $
        safeDivide 10.0 0.0 0.0 @?= 0.0
    , testCase "safeMod - positive result" $
        safeMod 10.0 3.0 @?= 1.0
    , testCase "safeMod - negative dividend" $
        safeMod (-10.0) 3.0 @?= 2.0  -- JavaScript-style: always positive
    , testCase "safeSqrt - valid sqrt" $
        safeSqrt 4.0 0.0 @?= 2.0
    , testCase "safeSqrt - negative number" $
        safeSqrt (-4.0) 0.0 @?= 0.0
    ]
  , testGroup "Clamping"
    [ testCase "clamp - within range" $
        clamp 5.0 0.0 10.0 @?= 5.0
    , testCase "clamp - below minimum" $
        clamp (-5.0) 0.0 10.0 @?= 0.0
    , testCase "clamp - above maximum" $
        clamp 15.0 0.0 10.0 @?= 10.0
    , testCase "clamp01 - within range" $
        clamp01 0.5 @?= 0.5
    , testCase "clamp01 - below zero" $
        clamp01 (-0.5) @?= 0.0
    , testCase "clamp01 - above one" $
        clamp01 1.5 @?= 1.0
    ]
  , testGroup "Interpolation"
    [ testCase "safeLerp - normal lerp" $
        safeLerp 0.0 10.0 0.5 @?= 5.0
    , testCase "safeLerp - t=0" $
        safeLerp 0.0 10.0 0.0 @?= 0.0
    , testCase "safeLerp - t=1" $
        safeLerp 0.0 10.0 1.0 @?= 10.0
    , testCase "smoothStep - edge cases" $
        smoothStep 0.0 1.0 0.5 @?= 0.5
    ]
  , testGroup "Vector Safety"
    [ testCase "safeNormalize2D - unit vector" $
        safeNormalize2D 1.0 0.0 @?= (1.0, 0.0)
    , testCase "safeNormalize2D - zero vector" $
        safeNormalize2D 0.0 0.0 @?= (0.0, 0.0)
    , testCase "safeDistance2D - normal distance" $
        safeDistance2D 0.0 0.0 3.0 4.0 @?= 5.0
    ]
  , testGroup "Angle Normalization"
    [ testCase "normalizeAngleDegrees - within range" $
        normalizeAngleDegrees 45.0 @?= 45.0
    , testCase "normalizeAngleDegrees - negative" $
        normalizeAngleDegrees (-45.0) @?= 315.0
    , testCase "normalizeAngleDegrees - over 360" $
        normalizeAngleDegrees 405.0 @?= 45.0
    , testCase "degreesToRadians" $
        degreesToRadians 180.0 @?= P.pi
    , testCase "radiansToDegrees" $
        radiansToDegrees P.pi @?= 180.0
    ]
  ]
