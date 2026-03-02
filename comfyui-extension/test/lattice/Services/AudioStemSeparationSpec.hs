-- |
-- Test suite for Lattice.Services.AudioStemSeparation
--

module Lattice.Services.AudioStemSeparationSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.AudioStemSeparation
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

spec :: TestTree
spec = testGroup "Lattice.Services.AudioStemSeparation"
  [ testGroup "getModelConfig"
    [ testCase "getModelConfig - htdemucs exists" $ do
        case getModelConfig "htdemucs" of
          Just model -> do
            modelId model @?= "htdemucs"
            modelDisplayName model @?= "HT-Demucs"
            modelRecommended model @?= True
            length (modelStems model) @?= 4
          Nothing -> fail "htdemucs model should exist"
    , testCase "getModelConfig - htdemucs_6s exists" $ do
        case getModelConfig "htdemucs_6s" of
          Just model -> do
            modelId model @?= "htdemucs_6s"
            length (modelStems model) @?= 6
            "guitar" `elem` modelStems model @?= True
            "piano" `elem` modelStems model @?= True
          Nothing -> fail "htdemucs_6s model should exist"
    , testCase "getModelConfig - unknown model" $ do
        getModelConfig "unknown_model" @?= Nothing
    , testCase "getModelConfig - all models have valid configs" $ do
        let allModels = ["htdemucs", "htdemucs_ft", "htdemucs_6s", "mdx_extra"]
        mapM_ (\name -> case getModelConfig name of
          Just _ -> return ()
          Nothing -> fail $ "Model " ++ T.unpack name ++ " should exist") allModels
    ]
  , testGroup "getAvailableModels"
    [ testCase "getAvailableModels - returns all models" $ do
        let models = getAvailableModels
        length models @?= 4
        mapM_ (\model -> modelId model `elem` ["htdemucs", "htdemucs_ft", "htdemucs_6s", "mdx_extra"] @?= True) models
    , testCase "getAvailableModels - all models have sample rate 44100" $ do
        let models = getAvailableModels
        mapM_ (\model -> modelSampleRate model @?= 44100) models
    , testCase "getAvailableModels - exactly one recommended model" $ do
        let models = getAvailableModels
        let recommended = filter modelRecommended models
        length recommended @?= 1
        modelId (head recommended) @?= "htdemucs"
    ]
  , testGroup "getAttributionInfo"
    [ testCase "getAttributionInfo - fill_nodes exists" $ do
        let attrib = getAttributionInfo
        case Map.lookup "fill_nodes" attrib of
          Just attr -> do
            attributionName attr @?= "ComfyUI_Fill-Nodes"
            attributionAuthor attr @?= "filliptm"
            attributionLicense attr @?= "MIT"
          Nothing -> fail "fill_nodes attribution should exist"
    , testCase "getAttributionInfo - demucs exists" $ do
        let attrib = getAttributionInfo
        case Map.lookup "demucs" attrib of
          Just attr -> do
            attributionName attr @?= "Demucs"
            attributionAuthor attr @?= "Facebook Research"
            attributionLicense attr @?= "MIT"
          Nothing -> fail "demucs attribution should exist"
    , testCase "getAttributionInfo - all attributions have valid data" $ do
        let attrib = getAttributionInfo
        Map.foldlWithKey (\acc k v ->
          if T.null (attributionName v) || T.null (attributionRepo v)
            then fail $ "Attribution " ++ T.unpack k ++ " has empty fields"
            else acc) () attrib
    ]
  , testGroup "validateStemSeparationParams"
    [ testCase "validateStemSeparationParams - valid params" $ do
        case validateStemSeparationParams "htdemucs" 10.0 0.1 Nothing of
          Right params -> do
            paramsModelName params @?= "htdemucs"
            paramsSegmentLength params @?= 10.0
            paramsOverlap params @?= 0.1
            paramsStemsToReturn params @?= Nothing
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateStemSeparationParams - unknown model" $ do
        case validateStemSeparationParams "unknown_model" 10.0 0.1 Nothing of
          Left err -> T.isInfixOf "Unknown model" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateStemSeparationParams - segment_length zero" $ do
        case validateStemSeparationParams "htdemucs" 0.0 0.1 Nothing of
          Left err -> T.isInfixOf "segment_length" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateStemSeparationParams - segment_length negative" $ do
        case validateStemSeparationParams "htdemucs" (-1.0) 0.1 Nothing of
          Left err -> T.isInfixOf "segment_length" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateStemSeparationParams - overlap negative" $ do
        case validateStemSeparationParams "htdemucs" 10.0 (-0.1) Nothing of
          Left err -> T.isInfixOf "overlap" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateStemSeparationParams - overlap too high" $ do
        case validateStemSeparationParams "htdemucs" 10.0 0.6 Nothing of
          Left err -> T.isInfixOf "overlap" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateStemSeparationParams - overlap at boundary 0.5" $ do
        case validateStemSeparationParams "htdemucs" 10.0 0.5 Nothing of
          Right params -> paramsOverlap params @?= 0.5
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateStemSeparationParams - valid stems" $ do
        case validateStemSeparationParams "htdemucs" 10.0 0.1 (Just ["vocals", "drums"]) of
          Right params -> do
            paramsStemsToReturn params @?= Just ["vocals", "drums"]
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateStemSeparationParams - invalid stem name" $ do
        case validateStemSeparationParams "htdemucs" 10.0 0.1 (Just ["invalid_stem"]) of
          Left err -> T.isInfixOf "Invalid stem names" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateStemSeparationParams - invalid stem for 6s model" $ do
        case validateStemSeparationParams "htdemucs_6s" 10.0 0.1 (Just ["guitar", "invalid"]) of
          Left err -> T.isInfixOf "Invalid stem names" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateStemSeparationParams - all stems valid for 6s model" $ do
        case validateStemSeparationParams "htdemucs_6s" 10.0 0.1 (Just ["drums", "bass", "other", "vocals", "guitar", "piano"]) of
          Right params -> length (maybe [] id (paramsStemsToReturn params)) @?= 6
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateStemSeparationParams - edge cases" $ do
        -- Minimum valid segment length
        case validateStemSeparationParams "htdemucs" 0.0001 0.0 Nothing of
          Right _ -> return ()
          Left err -> fail $ "Should be valid (min): " ++ T.unpack err
        -- Maximum valid overlap
        case validateStemSeparationParams "htdemucs" 10.0 0.5 Nothing of
          Right _ -> return ()
          Left err -> fail $ "Should be valid (max overlap): " ++ T.unpack err
    ]
  ]
