-- |
-- Module      : Lattice.State.Composition
-- Description : Pure state management functions for composition store
-- 
-- Migrated from ui/src/stores/compositionStore.ts
-- Pure query and calculation functions extracted from Pinia store - no state mutation, no IO
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.State.Composition
  ( -- Pure queries
    getComposition
  -- Pure calculations
  , calculateDuration
  , computeCompositionSettings
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)
import qualified Data.Text as T
import Lattice.Types.Project
  ( Composition(..)
  , CompositionSettings(..)
  )
import Lattice.Utils.FpsUtils
  ( validateFps
  , defaultFps
  , calculateDuration
  )

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                           // pure // queries
-- ════════════════════════════════════════════════════════════════════════════

-- | Get a composition by ID from compositions map
-- Pure function: takes compositions map and composition ID, returns composition or Nothing
getComposition ::
  HashMap Text Composition ->
  Text ->
  Maybe Composition
getComposition compositions compId = HM.lookup compId compositions

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // pure // calculations
-- ════════════════════════════════════════════════════════════════════════════

-- Note: calculateDuration is imported from Lattice.Utils.FpsUtils

-- | Compute composition settings with validation and defaults
-- Pure function: takes partial settings and active comp settings, returns validated settings
computeCompositionSettings ::
  Maybe CompositionSettings ->
  Maybe CompositionSettings ->
  CompositionSettings
computeCompositionSettings mPartialSettings mActiveSettings =
  let
    -- Extract fps with validation
    fps = case (mPartialSettings, mActiveSettings) of
      (Just (CompositionSettings _ _ _ fpsVal _ _ _ _ _ _ _ _), _) ->
        if fpsVal > 0 then validateFps (Just fpsVal) defaultFps else getFpsFromActive
      (_, Just (CompositionSettings _ _ _ fpsVal _ _ _ _ _ _ _ _)) ->
        if fpsVal > 0 then validateFps (Just fpsVal) defaultFps else defaultFps
      _ -> defaultFps
      where
        getFpsFromActive = case mActiveSettings of
          Just (CompositionSettings _ _ _ activeFps _ _ _ _ _ _ _ _) ->
            if activeFps > 0 then validateFps (Just activeFps) defaultFps else defaultFps
          Nothing -> defaultFps
    
    -- Extract width with defaults
    width = case (mPartialSettings, mActiveSettings) of
      (Just (CompositionSettings w _ _ _ _ _ _ _ _ _ _ _), _) ->
        if w > 0 then w else getWidthFromActive
      (_, Just (CompositionSettings activeW _ _ _ _ _ _ _ _ _ _ _)) ->
        if activeW > 0 then activeW else 1024.0
      _ -> 1024.0
      where
        getWidthFromActive = case mActiveSettings of
          Just (CompositionSettings activeW _ _ _ _ _ _ _ _ _ _ _) ->
            if activeW > 0 then activeW else 1024.0
          Nothing -> 1024.0
    
    -- Extract height with defaults
    height = case (mPartialSettings, mActiveSettings) of
      (Just (CompositionSettings _ h _ _ _ _ _ _ _ _ _ _), _) ->
        if h > 0 then h else getHeightFromActive
      (_, Just (CompositionSettings _ activeH _ _ _ _ _ _ _ _ _ _)) ->
        if activeH > 0 then activeH else 1024.0
      _ -> 1024.0
      where
        getHeightFromActive = case mActiveSettings of
          Just (CompositionSettings _ activeH _ _ _ _ _ _ _ _ _ _) ->
            if activeH > 0 then activeH else 1024.0
          Nothing -> 1024.0
    
    -- Extract frameCount with defaults
    frameCount = case (mPartialSettings, mActiveSettings) of
      (Just (CompositionSettings _ _ fc _ _ _ _ _ _ _ _ _), _) ->
        if fc > 0 then fc else getFrameCountFromActive
      (_, Just (CompositionSettings _ _ activeFc _ _ _ _ _ _ _ _ _)) ->
        if activeFc > 0 then activeFc else 81.0
      _ -> 81.0
      where
        getFrameCountFromActive = case mActiveSettings of
          Just (CompositionSettings _ _ activeFc _ _ _ _ _ _ _ _ _) ->
            if activeFc > 0 then activeFc else 81.0
          Nothing -> 81.0
    
    -- Extract backgroundColor with defaults (field 6: w h fc fps dur bg ...)
    backgroundColor = case (mPartialSettings, mActiveSettings) of
      (Just (CompositionSettings _ _ _ _ _ bg _ _ _ _ _ _), _) ->
        if T.null bg then "#050505" else bg
      _ -> "#050505"
    
    -- Extract autoResizeToContent with defaults (field 7)
    autoResizeToContent = case mPartialSettings of
      Just (CompositionSettings _ _ _ _ _ _ arc _ _ _ _ _) -> arc
      Nothing -> False
    
    -- Extract frameBlendingEnabled with defaults (field 8)
    frameBlendingEnabled = case mPartialSettings of
      Just (CompositionSettings _ _ _ _ _ _ _ fbe _ _ _ _) -> fbe
      Nothing -> False
    
    -- Calculate duration using utility function
    duration = calculateDuration frameCount fps
    
    -- Create settings (other fields use defaults from CompositionSettings)
    settings = CompositionSettings
      { compositionSettingsWidth = width
      , compositionSettingsHeight = height
      , compositionSettingsFrameCount = frameCount
      , compositionSettingsFps = fps
      , compositionSettingsDuration = duration
      , compositionSettingsBackgroundColor = backgroundColor
      , compositionSettingsAutoResizeToContent = autoResizeToContent
      , compositionSettingsFrameBlendingEnabled = frameBlendingEnabled
      , compositionSettingsColorSettings = Nothing
      , compositionSettingsMotionBlur = Nothing
      , compositionSettingsShutterAngle = Nothing
      , compositionSettingsMotionBlurSamples = Nothing
      }
  in
    settings
