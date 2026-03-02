-- |
-- Test suite for Lattice.Services.ProjectValidation
--

module Lattice.Services.ProjectValidationSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.ProjectValidation
import Data.Aeson (Value(..), object, (.=), Array)
import qualified Data.Aeson as A
import qualified Data.HashMap.Strict as HM
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Text (Text)
import qualified Data.Text as T

spec :: TestTree
spec = testGroup "Lattice.Services.ProjectValidation"
  [ testGroup "calculateMaxDepth"
    [ testCase "calculateMaxDepth - flat object" $
        calculateMaxDepth (object [("a", A.String "test")]) 0 @?= 1
    , testCase "calculateMaxDepth - nested object" $
        calculateMaxDepth (object [("a", object [("b", A.String "test")])]) 0 @?= 2
    , testCase "calculateMaxDepth - array" $
        calculateMaxDepth (A.Array (V.fromList [A.String "test"])) 0 @?= 1
    , testCase "calculateMaxDepth - nested array" $
        calculateMaxDepth (A.Array (V.fromList [A.Array (V.fromList [A.String "test"])])) 0 @?= 2
    , testCase "calculateMaxDepth - primitive" $
        calculateMaxDepth (A.String "test") 0 @?= 0
    ]
  , testGroup "validateExpressions"
    [ testCase "validateExpressions - no expressions" $
        validateExpressions (object [("a", A.String "test")]) "" @?= []
    , testCase "validateExpressions - valid expression" $
        length (validateExpressions (object [("expression", A.String "time * 2")]) "") @?= 0
    , testCase "validateExpressions - dangerous pattern" $
        length (validateExpressions (object [("expression", A.String "eval('bad')")]) "") > 0 @?= True
    , testCase "validateExpressions - expression too long" $ do
        let longExpr = T.replicate 10001 "x"
        length (validateExpressions (object [("expression", A.String longExpr)]) "") > 0 @?= True
    ]
  , testGroup "validateSingleExpression"
    [ testCase "validateSingleExpression - valid" $
        validateSingleExpression "time * 2" "test.path" @?= []
    , testCase "validateSingleExpression - too long" $ do
        let longExpr = T.replicate 10001 "x"
        length (validateSingleExpression longExpr "test.path") > 0 @?= True
    , testCase "validateSingleExpression - dangerous pattern" $
        length (validateSingleExpression "eval('bad')" "test.path") > 0 @?= True
    ]
  , testGroup "validateNumericBounds"
    [ testCase "validateNumericBounds - valid fps" $
        validateNumericBounds (object [("fps", A.Number 30)]) "" defaultNumericBounds @?= []
    , testCase "validateNumericBounds - invalid fps" $
        length (validateNumericBounds (object [("fps", A.Number 500)]) "" defaultNumericBounds) > 0 @?= True
    , testCase "validateNumericBounds - NaN" $
        length (validateNumericBounds (object [("fps", A.Number (0/0))]) "" defaultNumericBounds) > 0 @?= True
    ]
  , testGroup "validatePaths"
    [ testCase "validatePaths - safe path" $
        validatePaths (object [("path", A.String "assets/image.png")]) "" @?= []
    , testCase "validatePaths - path traversal" $
        length (validatePaths (object [("path", A.String "../../etc/passwd")]) "") > 0 @?= True
    , testCase "validatePaths - http url" $
        validatePaths (object [("url", A.String "http://example.com")]) "" @?= []
    ]
  , testGroup "countLayers"
    [ testCase "countLayers - no layers" $
        countLayers (object [("a", A.String "test")]) @?= 0
    , testCase "countLayers - single layer" $
        countLayers (object [("layers", A.Array (V.fromList [object [("type", A.String "text")]]))]) @?= 1
    , testCase "countLayers - multiple layers" $
        countLayers (object [("layers", A.Array (V.fromList [object [], object []]))]) @?= 2
    ]
  , testGroup "validateStringLengths"
    [ testCase "validateStringLengths - valid string" $
        validateStringLengths (A.String "test") "" @?= []
    , testCase "validateStringLengths - too long" $ do
        let longStr = T.replicate 100001 "x"
        length (validateStringLengths (A.String longStr) "") > 0 @?= True
    ]
  , testGroup "validateArrayLengths"
    [ testCase "validateArrayLengths - valid array" $
        validateArrayLengths (A.Array (A.fromList [A.String "test"])) "" @?= []
    , testCase "validateArrayLengths - too long" $ do
        let longArr = A.Array (V.fromList (replicate 100001 (A.String "test")))
        length (validateArrayLengths longArr "") > 0 @?= True
    ]
  , testGroup "validateProjectId"
    [ testCase "validateProjectId - valid" $
        validateProjectId "project_123" @?= True
    , testCase "validateProjectId - empty" $
        validateProjectId "" @?= False
    , testCase "validateProjectId - too long" $ do
        let longId = T.replicate 256 "x"
        validateProjectId longId @?= False
    , testCase "validateProjectId - path traversal" $
        validateProjectId "../project" @?= False
    , testCase "validateProjectId - invalid chars" $
        validateProjectId "project@123" @?= False
    ]
  ]
