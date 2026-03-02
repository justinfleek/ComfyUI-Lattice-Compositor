-- |
-- Test suite for Lattice.Utils.Validation
--

module Lattice.Utils.ValidationSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Utils.Validation

spec :: TestTree
spec = testGroup "Lattice.Utils.Validation"
  [ testGroup "Primitive Validation"
    [ testCase "validateString - valid string" $
        validateString "hello" @?= Ok "hello"
    , testCase "validateString - empty string" $
        validateString "" @?= Fail "String must not be empty"
    , testCase "validateFiniteNumber - valid number" $
        validateFiniteNumber 42.5 @?= Ok 42.5
    , testCase "validateFiniteNumber - NaN" $
        case validateFiniteNumber (0/0) of
          Fail _ -> return ()
          _ -> assertFailure "Should fail for NaN"
    , testCase "validateInteger - valid integer" $
        validateInteger 42 @?= Ok 42
    , testCase "validateInteger - non-integer" $
        case validateInteger 42.5 of
          Fail _ -> return ()
          _ -> assertFailure "Should fail for non-integer"
    , testCase "validateBoolean - valid boolean" $
        validateBoolean True @?= Ok True
    ]
  , testGroup "Array Validation"
    [ testCase "validateArray - valid array" $
        validateArray validateFiniteNumber [1, 2, 3] @?= Ok [1, 2, 3]
    , testCase "validateArray - invalid element" $
        case validateArray validateFiniteNumber [1, 0/0, 3] of
          Fail _ -> return ()
          _ -> assertFailure "Should fail for invalid element"
    , testCase "validateNumberArray - valid array" $
        validateNumberArray [1, 2, 3] @?= Ok [1, 2, 3]
    ]
  , testGroup "Object Validation"
    [ testCase "validateVec2 - valid Vec2" $
        validateVec2 1.0 2.0 @?= Ok (1.0, 2.0)
    , testCase "validateVec2 - invalid x" $
        case validateVec2 (0/0) 2.0 of
          Fail _ -> return ()
          _ -> assertFailure "Should fail for invalid x"
    , testCase "validateVec3 - valid Vec3" $
        validateVec3 1.0 2.0 3.0 @?= Ok (1.0, 2.0, 3.0)
    ]
  , testGroup "Optional Values"
    [ testCase "optional - present value" $
        optional (Ok "value") @?= Ok (Just "value")
    , testCase "optional - missing value" $
        optional (Fail "error") @?= Ok Nothing
    , testCase "withDefault - present value" $
        withDefault "default" (Ok "value") @?= Ok "value"
    , testCase "withDefault - missing value" $
        withDefault "default" (Fail "error") @?= Ok "default"
    ]
  , testGroup "Composition"
    [ testCase "validateSchema - all valid" $ do
        let schema = validateSchema
              [ ("name", validateString)
              , ("age", validateFiniteNumber)
              ]
            result = validateSchema schema [("name", "John"), ("age", 30)]
        case result of
          Ok obj -> length obj @?= 2
          Fail _ -> assertFailure "Should succeed"
    , testCase "validateAll - all valid" $
        validateAll [Ok 1, Ok 2, Ok 3] @?= Ok [1, 2, 3]
    , testCase "validateAll - one invalid" $
        case validateAll [Ok 1, Fail "error", Ok 3] of
          Fail _ -> return ()
          _ -> assertFailure "Should fail if any invalid"
    ]
  ]
