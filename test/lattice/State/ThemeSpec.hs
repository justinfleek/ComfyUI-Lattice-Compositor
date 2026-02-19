-- |
-- Module      : Lattice.State.ThemeSpec
-- Description : Test suite for Theme State functions
-- 
-- Tests pure theme state functions migrated from themeStore.ts
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.ThemeSpec (spec) where

import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Data.Text (Text)
import qualified Data.Text as T

import Lattice.State.Theme
  ( themeGradient
  , themePrimary
  , themeSecondary
  , getGlowColor
  , ThemeName(..)
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // tests
-- ════════════════════════════════════════════════════════════════════════════

spec :: TestTree
spec = testGroup "Theme State Functions"
  [ testGroup "Pure Queries (Getters)"
      [ testCase "themeGradient - returns CSS variable for violet" $ do
          let result = themeGradient ThemeNameViolet
          result @?= T.pack "var(--lattice-theme-violet-gradient)"
      
      , testCase "themePrimary - returns CSS variable for ocean" $ do
          let result = themePrimary ThemeNameOcean
          result @?= T.pack "var(--lattice-theme-ocean-primary)"
      
      , testCase "themeSecondary - returns CSS variable for sunset" $ do
          let result = themeSecondary ThemeNameSunset
          result @?= T.pack "var(--lattice-theme-sunset-secondary)"
      ]
  
  , testGroup "Pure Constants"
      [ testCase "getGlowColor - returns glow color for violet" $ do
          let result = getGlowColor ThemeNameViolet
          result @?= T.pack "rgba(139, 92, 246, 0.3)"
      
      , testCase "getGlowColor - returns glow color for ocean" $ do
          let result = getGlowColor ThemeNameOcean
          result @?= T.pack "rgba(6, 182, 212, 0.3)"
      
      , testCase "getGlowColor - returns glow color for all themes" $ do
          getGlowColor ThemeNameViolet @?= T.pack "rgba(139, 92, 246, 0.3)"
          getGlowColor ThemeNameOcean @?= T.pack "rgba(6, 182, 212, 0.3)"
          getGlowColor ThemeNameSunset @?= T.pack "rgba(251, 113, 133, 0.3)"
          getGlowColor ThemeNameForest @?= T.pack "rgba(16, 185, 129, 0.3)"
          getGlowColor ThemeNameEmber @?= T.pack "rgba(239, 68, 68, 0.3)"
          getGlowColor ThemeNameMono @?= T.pack "rgba(107, 114, 128, 0.3)"
      ]
  ]
