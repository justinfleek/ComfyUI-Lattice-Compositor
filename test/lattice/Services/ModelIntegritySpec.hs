-- |
-- Test suite for Lattice.Services.ModelIntegrity
--

module Lattice.Services.ModelIntegritySpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.ModelIntegrity
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as T

spec :: TestTree
spec = testGroup "Lattice.Services.ModelIntegrity"
  [ testGroup "computeHash"
    [ testCase "computeHash - empty string" $ do
        let hash = computeHash BS.empty
        -- SHA256 of empty string: e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
        T.length hash @?= 64
    , testCase "computeHash - hello world" $ do
        let hash = computeHash (BS.pack [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100])
        -- SHA256 of "hello world": b94d27b9934d3e08a52e52d7da7dabfac484efe37a5380ee9088f7ace2efcde9
        T.length hash @?= 64
        -- Verify it's hex (all lowercase)
        T.all (\c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) hash @?= True
    , testCase "computeHash - deterministic" $ do
        let input = BS.pack [1, 2, 3, 4, 5]
        let hash1 = computeHash input
        let hash2 = computeHash input
        hash1 @?= hash2
    ]
  , testGroup "verifyHash"
    [ testCase "verifyHash - matching hashes" $ do
        let hash = computeHash (BS.pack [1, 2, 3])
        verifyHash hash hash @?= True
    , testCase "verifyHash - different hashes" $ do
        let hash1 = computeHash (BS.pack [1, 2, 3])
        let hash2 = computeHash (BS.pack [4, 5, 6])
        verifyHash hash1 hash2 @?= False
    , testCase "verifyHash - case sensitive" $ do
        let hash = computeHash (BS.pack [1, 2, 3])
        let hashUpper = T.toUpper hash
        verifyHash hash hashUpper @?= False
    ]
  , testGroup "validateDecompositionParams"
    [ testCase "validateDecompositionParams - valid params" $ do
        case validateDecompositionParams 5 4.0 50 640 Nothing of
          Right params -> do
            paramsNumLayers params @?= 5
            paramsTrueCfgScale params @?= 4.0
            paramsNumInferenceSteps params @?= 50
            paramsResolution params @?= 640
            paramsSeed params @?= Nothing
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateDecompositionParams - num_layers too low" $ do
        case validateDecompositionParams 2 4.0 50 640 Nothing of
          Left err -> T.isInfixOf "num_layers" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateDecompositionParams - num_layers too high" $ do
        case validateDecompositionParams 9 4.0 50 640 Nothing of
          Left err -> T.isInfixOf "num_layers" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateDecompositionParams - cfg_scale zero" $ do
        case validateDecompositionParams 5 0.0 50 640 Nothing of
          Left err -> T.isInfixOf "true_cfg_scale" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateDecompositionParams - cfg_scale negative" $ do
        case validateDecompositionParams 5 (-1.0) 50 640 Nothing of
          Left err -> T.isInfixOf "true_cfg_scale" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateDecompositionParams - steps zero" $ do
        case validateDecompositionParams 5 4.0 0 640 Nothing of
          Left err -> T.isInfixOf "num_inference_steps" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateDecompositionParams - resolution invalid" $ do
        case validateDecompositionParams 5 4.0 50 800 Nothing of
          Left err -> T.isInfixOf "resolution" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateDecompositionParams - resolution 1024 valid" $ do
        case validateDecompositionParams 5 4.0 50 1024 Nothing of
          Right params -> paramsResolution params @?= 1024
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateDecompositionParams - seed negative" $ do
        case validateDecompositionParams 5 4.0 50 640 (Just (-1)) of
          Left err -> T.isInfixOf "seed" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateDecompositionParams - seed valid" $ do
        case validateDecompositionParams 5 4.0 50 640 (Just 42) of
          Right params -> paramsSeed params @?= Just 42
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateDecompositionParams - all edge cases" $ do
        -- Minimum valid
        case validateDecompositionParams 3 0.0001 1 640 Nothing of
          Right _ -> return ()
          Left err -> fail $ "Should be valid (min): " ++ T.unpack err
        -- Maximum valid
        case validateDecompositionParams 8 1000.0 1000 1024 (Just 999999) of
          Right _ -> return ()
          Left err -> fail $ "Should be valid (max): " ++ T.unpack err
    ]
  ]
