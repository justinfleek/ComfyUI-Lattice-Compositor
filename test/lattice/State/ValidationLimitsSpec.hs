-- |
-- Module      : Lattice.State.ValidationLimitsSpec
-- Description : Test suite for Validation Limits functions
-- 
-- Tests pure validation limits functions migrated from validationLimitsStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.ValidationLimitsSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

import Lattice.State.ValidationLimits
  ( getDefaultLimits
  , validateLimit
  , clampLimit
  , ValidationLimits(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // tests
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Validation Limits Functions"
  [ testGroup "Pure Constants"
      [ testCase "getDefaultLimits - returns default limits" $ do
          let limits = getDefaultLimits
          validationLimitsMaxDimension limits @?= 8192.0
          validationLimitsMaxFrameCount limits @?= 10000.0
          validationLimitsMaxArrayLength limits @?= 100000.0
          validationLimitsMaxParticles limits @?= 1000000.0
          validationLimitsMaxLayers limits @?= 1000.0
          validationLimitsMaxKeyframesPerProperty limits @?= 10000.0
          validationLimitsMaxStringLength limits @?= 100000.0
          validationLimitsMaxFPS limits @?= 120.0
      ]
  
  , testGroup "Pure Validation"
      [ testCase "validateLimit - returns True for valid limit" $ do
          validateLimit 5000.0 10000.0 @?= True
      
      , testCase "validateLimit - returns False for negative limit" $ do
          validateLimit (-10.0) 10000.0 @?= False
      
      , testCase "validateLimit - returns False for limit exceeding max" $ do
          validateLimit 15000.0 10000.0 @?= False
      
      , testCase "validateLimit - returns True for limit at boundaries" $ do
          validateLimit 0.0 10000.0 @?= True
          validateLimit 10000.0 10000.0 @?= True
      
      , testCase "clampLimit - clamps to valid range" $ do
          clampLimit 5000.0 10000.0 @?= 5000.0
          clampLimit (-10.0) 10000.0 @?= 0.0
          clampLimit 15000.0 10000.0 @?= 10000.0
      
      , testCase "clampLimit - handles boundary values" $ do
          clampLimit 0.0 10000.0 @?= 0.0
          clampLimit 10000.0 10000.0 @?= 10000.0
      ]
  ]
