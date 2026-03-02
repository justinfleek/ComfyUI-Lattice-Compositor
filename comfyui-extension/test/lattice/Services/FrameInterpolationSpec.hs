-- |
-- Test suite for Lattice.Services.FrameInterpolation
--

module Lattice.Services.FrameInterpolationSpec (spec) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import Lattice.Services.FrameInterpolation
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

spec :: TestTree
spec = testGroup "Lattice.Services.FrameInterpolation"
  [ testGroup "getRIFEModelConfig"
    [ testCase "getRIFEModelConfig - rife-v4.6 exists" $ do
        case getRIFEModelConfig "rife-v4.6" of
          Just model -> do
            rifeModelId model @?= "rife-v4.6"
            rifeModelDisplayName model @?= "RIFE v4.6"
            rifeModelSupportsEnsemble model @?= True
            rifeModelRecommended model @?= True
          Nothing -> fail "rife-v4.6 model should exist"
    , testCase "getRIFEModelConfig - rife-v3.9 exists" $ do
        case getRIFEModelConfig "rife-v3.9" of
          Just model -> do
            rifeModelId model @?= "rife-v3.9"
            rifeModelSupportsEnsemble model @?= False
            rifeModelRecommended model @?= False
          Nothing -> fail "rife-v3.9 model should exist"
    , testCase "getRIFEModelConfig - film model exists" $ do
        case getRIFEModelConfig "film" of
          Just model -> do
            rifeModelId model @?= "film"
            rifeModelDisplayName model @?= "FILM"
          Nothing -> fail "film model should exist"
    , testCase "getRIFEModelConfig - unknown model" $ do
        getRIFEModelConfig "unknown_model" @?= Nothing
    , testCase "getRIFEModelConfig - all models have valid configs" $ do
        let allModels = ["rife-v4.6", "rife-v4.0", "rife-v3.9", "film"]
        mapM_ (\name -> case getRIFEModelConfig name of
          Just _ -> return ()
          Nothing -> fail $ "Model " ++ T.unpack name ++ " should exist") allModels
    ]
  , testGroup "getAvailableRIFEModels"
    [ testCase "getAvailableRIFEModels - returns all models" $ do
        let models = getAvailableRIFEModels
        length models @?= 4
        mapM_ (\model -> rifeModelId model `elem` ["rife-v4.6", "rife-v4.0", "rife-v3.9", "film"] @?= True) models
    , testCase "getAvailableRIFEModels - exactly one recommended model" $ do
        let models = getAvailableRIFEModels
        let recommended = filter rifeModelRecommended models
        length recommended @?= 1
        rifeModelId (head recommended) @?= "rife-v4.6"
    , testCase "getAvailableRIFEModels - ensemble support count" $ do
        let models = getAvailableRIFEModels
        let ensembleSupported = filter rifeModelSupportsEnsemble models
        length ensembleSupported @?= 2  -- rife-v4.6 and rife-v4.0
    ]
  , testGroup "getRIFEAttributionInfo"
    [ testCase "getRIFEAttributionInfo - fill_nodes exists" $ do
        let attrib = getRIFEAttributionInfo
        case Map.lookup "fill_nodes" attrib of
          Just attr -> do
            attributionName attr @?= "ComfyUI_Fill-Nodes"
            attributionAuthor attr @?= "filliptm"
            attributionLicense attr @?= "MIT"
          Nothing -> fail "fill_nodes attribution should exist"
    , testCase "getRIFEAttributionInfo - rife exists" $ do
        let attrib = getRIFEAttributionInfo
        case Map.lookup "rife" attrib of
          Just attr -> do
            attributionName attr @?= "RIFE (Real-time Intermediate Flow Estimation)"
            attributionAuthor attr @?= "Megvii Research"
            attributionLicense attr @?= "Apache 2.0"
          Nothing -> fail "rife attribution should exist"
    , testCase "getRIFEAttributionInfo - practical_rife exists" $ do
        let attrib = getRIFEAttributionInfo
        case Map.lookup "practical_rife" attrib of
          Just attr -> do
            attributionName attr @?= "Practical-RIFE"
            attributionAuthor attr @?= "hzwer"
          Nothing -> fail "practical_rife attribution should exist"
    ]
  , testGroup "validateInterpolationParams"
    [ testCase "validateInterpolationParams - valid params" $ do
        case validateInterpolationParams "rife-v4.6" 2 False Nothing of
          Right params -> do
            paramsModelName params @?= "rife-v4.6"
            paramsFactor params @?= 2
            paramsEnsemble params @?= False
            paramsSlowdown params @?= Nothing
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateInterpolationParams - unknown model" $ do
        case validateInterpolationParams "unknown_model" 2 False Nothing of
          Left err -> T.isInfixOf "Unknown model" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateInterpolationParams - invalid factor" $ do
        case validateInterpolationParams "rife-v4.6" 3 False Nothing of
          Left err -> T.isInfixOf "factor must be 2, 4, or 8" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateInterpolationParams - factor 4 valid" $ do
        case validateInterpolationParams "rife-v4.6" 4 False Nothing of
          Right params -> paramsFactor params @?= 4
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateInterpolationParams - factor 8 valid" $ do
        case validateInterpolationParams "rife-v4.6" 8 False Nothing of
          Right params -> paramsFactor params @?= 8
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateInterpolationParams - ensemble with supported model" $ do
        case validateInterpolationParams "rife-v4.6" 2 True Nothing of
          Right params -> paramsEnsemble params @?= True
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateInterpolationParams - ensemble with unsupported model" $ do
        case validateInterpolationParams "rife-v3.9" 2 True Nothing of
          Left err -> T.isInfixOf "does not support ensemble mode" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateInterpolationParams - slowdown valid" $ do
        case validateInterpolationParams "rife-v4.6" 2 False (Just 2.5) of
          Right params -> paramsSlowdown params @?= Just 2.5
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    , testCase "validateInterpolationParams - slowdown zero" $ do
        case validateInterpolationParams "rife-v4.6" 2 False (Just 0.0) of
          Left err -> T.isInfixOf "slowdown" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateInterpolationParams - slowdown negative" $ do
        case validateInterpolationParams "rife-v4.6" 2 False (Just (-1.0)) of
          Left err -> T.isInfixOf "slowdown" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateInterpolationParams - slowdown too high" $ do
        case validateInterpolationParams "rife-v4.6" 2 False (Just 9.0) of
          Left err -> T.isInfixOf "slowdown" err @?= True
          Right _ -> fail "Should have failed validation"
    , testCase "validateInterpolationParams - slowdown at boundary 8.0" $ do
        case validateInterpolationParams "rife-v4.6" 2 False (Just 8.0) of
          Right params -> paramsSlowdown params @?= Just 8.0
          Left err -> fail $ "Should be valid: " ++ T.unpack err
    ]
  , testGroup "slowdownToFactor"
    [ testCase "slowdownToFactor - <= 2.0 returns 2" $ do
        slowdownToFactor 1.0 @?= 2
        slowdownToFactor 2.0 @?= 2
        slowdownToFactor 0.5 @?= 2
    , testCase "slowdownToFactor - <= 4.0 returns 4" $ do
        slowdownToFactor 2.1 @?= 4
        slowdownToFactor 3.0 @?= 4
        slowdownToFactor 4.0 @?= 4
    , testCase "slowdownToFactor - > 4.0 returns 8" $ do
        slowdownToFactor 4.1 @?= 8
        slowdownToFactor 5.0 @?= 8
        slowdownToFactor 8.0 @?= 8
        slowdownToFactor 100.0 @?= 8
    , testCase "slowdownToFactor - boundary values" $ do
        slowdownToFactor 2.0 @?= 2
        slowdownToFactor 2.0001 @?= 4
        slowdownToFactor 4.0 @?= 4
        slowdownToFactor 4.0001 @?= 8
    ]
  ]
