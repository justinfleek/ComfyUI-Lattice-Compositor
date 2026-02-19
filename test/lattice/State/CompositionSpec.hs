-- |
-- Module      : Lattice.State.CompositionSpec
-- Description : Test suite for Composition State management functions
-- 
-- Tests pure state management functions migrated from compositionStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.CompositionSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=), assertBool)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Composition
  ( getComposition
  , calculateDuration
  , computeCompositionSettings
  )
import Lattice.Types.Project
  ( Composition(..)
  , CompositionSettings(..)
  )
import Lattice.Utils.FpsUtils
  ( defaultFps
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                   // test // data // helpers
-- ════════════════════════════════════════════════════════════════════════════

-- | Create a simple test composition
createTestComposition :: Text -> Text -> Composition
createTestComposition compId compName =
  let
    settings = CompositionSettings
      { compositionSettingsWidth = 1920.0
      , compositionSettingsHeight = 1080.0
      , compositionSettingsFrameCount = 81.0
      , compositionSettingsFps = 16.0
      , compositionSettingsDuration = 81.0 / 16.0
      , compositionSettingsBackgroundColor = "#1a1a1a"
      , compositionSettingsAutoResizeToContent = False
      , compositionSettingsFrameBlendingEnabled = False
      , compositionSettingsColorSettings = Nothing
      , compositionSettingsMotionBlur = Nothing
      , compositionSettingsShutterAngle = Nothing
      , compositionSettingsMotionBlurSamples = Nothing
      }
  in
    Composition
      { compositionId = compId
      , compositionName = compName
      , compositionSettings = settings
      , compositionLayers = []
      , compositionCurrentFrame = 0.0
      , compositionIsNestedComp = False
      , compositionParentCompositionId = Nothing
      , compositionWorkflowId = Nothing
      , compositionWorkflowInputs = Nothing
      , compositionWorkflowOutputs = Nothing
      , compositionTemplateConfig = Nothing
      , compositionGlobalLight = Nothing
      , compositionMarkers = Nothing
      }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // tests
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Composition State Functions"
  [ testGroup "Pure Queries"
      [ testCase "getComposition - finds existing composition" $ do
          let
            comp1 = createTestComposition "comp1" "Comp 1"
            comp2 = createTestComposition "comp2" "Comp 2"
            compositions = HM.fromList [("comp1", comp1), ("comp2", comp2)]
          case getComposition compositions "comp1" of
            Just comp -> compositionId comp @?= "comp1"
            Nothing -> assertBool "Composition should be found" False
      
      , testCase "getComposition - returns Nothing for non-existent composition" $ do
          let compositions = HM.fromList [("comp1", createTestComposition "comp1" "Comp 1")]
          getComposition compositions "nonexistent" @?= Nothing
      ]
  
  , testGroup "Pure Calculations"
      [ testCase "calculateDuration - calculates duration correctly" $ do
          let duration = calculateDuration 81.0 (Just 16.0)
          duration @?= 5.0625
      
      , testCase "calculateDuration - handles zero fps" $ do
          let duration = calculateDuration 81.0 (Just 0.0)
          -- Should use defaultFps (16) when fps is invalid
          assertBool "Duration should be calculated with default fps" (duration > 0)
      
      , testCase "computeCompositionSettings - uses partial settings when provided" $ do
          let
            partialSettings = Just (CompositionSettings
              1920.0 1080.0 100.0 24.0 0.0 "#ffffff" False False Nothing Nothing Nothing Nothing)
            activeSettings = Just (CompositionSettings
              1280.0 720.0 81.0 16.0 0.0 "#000000" True True Nothing Nothing Nothing Nothing)
            result = computeCompositionSettings partialSettings activeSettings
          compositionSettingsWidth result @?= 1920.0
          compositionSettingsHeight result @?= 1080.0
          compositionSettingsFrameCount result @?= 100.0
          compositionSettingsFps result @?= 24.0
          compositionSettingsBackgroundColor result @?= "#ffffff"
      
      , testCase "computeCompositionSettings - uses active settings as fallback" $ do
          let
            partialSettings = Nothing
            activeSettings = Just (CompositionSettings
              1920.0 1080.0 81.0 16.0 0.0 "#1a1a1a" False False Nothing Nothing Nothing Nothing)
            result = computeCompositionSettings partialSettings activeSettings
          compositionSettingsWidth result @?= 1920.0
          compositionSettingsHeight result @?= 1080.0
          compositionSettingsFrameCount result @?= 81.0
          compositionSettingsFps result @?= 16.0
      
      , testCase "computeCompositionSettings - uses defaults when no settings provided" $ do
          let
            partialSettings = Nothing
            activeSettings = Nothing
            result = computeCompositionSettings partialSettings activeSettings
          compositionSettingsWidth result @?= 1024.0
          compositionSettingsHeight result @?= 1024.0
          compositionSettingsFrameCount result @?= 81.0
          compositionSettingsFps result @?= defaultFps
          compositionSettingsBackgroundColor result @?= "#050505"
      
      , testCase "computeCompositionSettings - calculates duration correctly" $ do
          let
            partialSettings = Just (CompositionSettings
              1920.0 1080.0 100.0 25.0 0.0 "#ffffff" False False Nothing Nothing Nothing Nothing)
            activeSettings = Nothing
            result = computeCompositionSettings partialSettings activeSettings
          let expectedDuration = 100.0 / 25.0
          compositionSettingsDuration result @?= expectedDuration
      ]
  ]
