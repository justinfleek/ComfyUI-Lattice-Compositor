-- |
-- Module      : Lattice.Composables.ViewportGuides
-- Description : Pure viewport guide types and style computation
--
-- Ported from ui/src/composables/useViewportGuides.ts
-- Pure: SafeFrameBounds, ResolutionPreset, resolution presets, style records from bounds.
-- Projection (3D → screen) remains in UI; this module computes styles from projected bounds.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Composables.ViewportGuides
  ( -- Types
    SafeFrameBounds(..)
  , ResolutionPreset(..)
  , ResolutionGuide(..)
  , SafeFrameStyle(..)
  -- Constants
  , resolutionPresets
  -- Style from bounds (pure)
  , safeFrameLeftStyle
  , safeFrameRightStyle
  , safeFrameTopStyle
  , safeFrameBottomStyle
  , compositionBoundaryStyle
  -- Resolution crop geometry (pure)
  , resolutionCropBounds
  , resolutionGuideFromPreset
  ) where

import Data.Text (Text)
import qualified Data.Text as T

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Safe frame overlay bounds in screen pixels (left, top, right, bottom)
data SafeFrameBounds = SafeFrameBounds
  { safeFrameLeft :: Double
  , safeFrameTop :: Double
  , safeFrameRight :: Double
  , safeFrameBottom :: Double
  }
  deriving (Eq, Show)

-- | Standard resolution preset (name, dimensions, color)
data ResolutionPreset = ResolutionPreset
  { resolutionPresetName :: Text
  , resolutionPresetWidth :: Int
  , resolutionPresetHeight :: Int
  , resolutionPresetColor :: Text
  }
  deriving (Eq, Show)

-- | Resolution guide with computed style (visible, style fields for overlay)
data ResolutionGuide = ResolutionGuide
  { resolutionGuideName :: Text
  , resolutionGuideColor :: Text
  , resolutionGuideResolution :: Text
  , resolutionGuideVisible :: Bool
  , resolutionGuideLeft :: Double
  , resolutionGuideTop :: Double
  , resolutionGuideWidth :: Double
  , resolutionGuideHeight :: Double
  }
  deriving (Eq, Show)

-- | CSS-like style for one safe-frame overlay (left, top, width, height in px)
data SafeFrameStyle = SafeFrameStyle
  { safeFrameStyleLeft :: Text
  , safeFrameStyleTop :: Text
  , safeFrameStyleWidth :: Text
  , safeFrameStyleHeight :: Text
  }
  deriving (Eq, Show)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Standard resolution presets (480p, 720p, 1080p)
resolutionPresets :: [ResolutionPreset]
resolutionPresets =
  [ ResolutionPreset "480p" 854 480 "#F59E0B"
  , ResolutionPreset "720p" 1280 720 "#8B5CF6"
  , ResolutionPreset "1080p" 1920 1080 "#06B6D4"
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                 // safe // frame // styles // from // bounds
-- ════════════════════════════════════════════════════════════════════════════

-- | Left overlay: from 0 to bounds.left
safeFrameLeftStyle :: SafeFrameBounds -> SafeFrameStyle
safeFrameLeftStyle b = SafeFrameStyle
  { safeFrameStyleLeft = "0"
  , safeFrameStyleTop = "0"
  , safeFrameStyleWidth = pxStyle (max 0 (safeFrameLeft b))
  , safeFrameStyleHeight = "100%"
  }

-- | Right overlay: from bounds.right to right edge
safeFrameRightStyle :: SafeFrameBounds -> SafeFrameStyle
safeFrameRightStyle b = SafeFrameStyle
  { safeFrameStyleLeft = pxStyle (safeFrameRight b)
  , safeFrameStyleTop = "0"
  , safeFrameStyleWidth = "calc(100% - " <> pxStyle (safeFrameRight b) <> ")"
  , safeFrameStyleHeight = "100%"
  }

-- | Top overlay: from bounds.left to bounds.right, height bounds.top
safeFrameTopStyle :: SafeFrameBounds -> SafeFrameStyle
safeFrameTopStyle b = SafeFrameStyle
  { safeFrameStyleLeft = pxStyle (max 0 (safeFrameLeft b))
  , safeFrameStyleTop = "0"
  , safeFrameStyleWidth = pxStyle (safeFrameRight b - max 0 (safeFrameLeft b))
  , safeFrameStyleHeight = pxStyle (max 0 (safeFrameTop b))
  }

-- | Bottom overlay: from bounds.left to bounds.right, from bounds.bottom down
safeFrameBottomStyle :: SafeFrameBounds -> SafeFrameStyle
safeFrameBottomStyle b = SafeFrameStyle
  { safeFrameStyleLeft = pxStyle (max 0 (safeFrameLeft b))
  , safeFrameStyleTop = pxStyle (safeFrameBottom b)
  , safeFrameStyleWidth = pxStyle (safeFrameRight b - max 0 (safeFrameLeft b))
  , safeFrameStyleHeight = "calc(100% - " <> pxStyle (safeFrameBottom b) <> ")"
  }

-- | Composition boundary: single rect (left, top, width, height). Width/height must be > 0 to show.
compositionBoundaryStyle :: SafeFrameBounds -> Maybe SafeFrameStyle
compositionBoundaryStyle b
  | width <= 0 || height <= 0 = Nothing
  | otherwise = Just SafeFrameStyle
      { safeFrameStyleLeft = pxStyle (safeFrameLeft b)
      , safeFrameStyleTop = pxStyle (safeFrameTop b)
      , safeFrameStyleWidth = pxStyle width
      , safeFrameStyleHeight = pxStyle height
      }
  where
    width = safeFrameRight b - safeFrameLeft b
    height = safeFrameBottom b - safeFrameTop b

pxStyle :: Double -> Text
pxStyle d = T.pack (show (round d :: Int)) <> "px"

-- ════════════════════════════════════════════════════════════════════════════
--                                            // resolution // crop // geometry
-- ════════════════════════════════════════════════════════════════════════════

-- | Crop rect in composition space: center (compW/2, compH/2), half dimensions.
-- Returns (centerX, centerY, halfWidth, halfHeight) for a preset smaller than or equal to comp.
resolutionCropBounds
  :: Double  -- ^ composition width
  -> Double  -- ^ composition height
  -> Int     -- ^ preset width
  -> Int     -- ^ preset height
  -> Maybe (Double, Double, Double, Double)
resolutionCropBounds compW compH presetW presetH
  | compW <= 0 || compH <= 0 = Nothing
  | fromIntegral presetW > compW || fromIntegral presetH > compH = Nothing
  | otherwise =
      let centerX = compW / 2
          centerY = compH / 2
          halfW = fromIntegral presetW / 2
          halfH = fromIntegral presetH / 2
      in Just (centerX, centerY, halfW, halfH)

-- | Build a ResolutionGuide from a preset and projected screen rect (left, top, right, bottom).
-- Projection is done by the UI; this just fills the guide record.
resolutionGuideFromPreset
  :: ResolutionPreset
  -> Double  -- ^ projected left (screen px)
  -> Double  -- ^ projected top
  -> Double  -- ^ projected right
  -> Double  -- ^ projected bottom
  -> Maybe ResolutionGuide
resolutionGuideFromPreset preset left top right bottom
  | boxWidth <= 0 || boxHeight <= 0 = Nothing
  | otherwise = Just ResolutionGuide
      { resolutionGuideName = resolutionPresetName preset
      , resolutionGuideColor = resolutionPresetColor preset
      , resolutionGuideResolution =
          T.pack (show (resolutionPresetWidth preset)) <> "×" <> T.pack (show (resolutionPresetHeight preset))
      , resolutionGuideVisible = True
      , resolutionGuideLeft = left
      , resolutionGuideTop = top
      , resolutionGuideWidth = boxWidth
      , resolutionGuideHeight = boxHeight
      }
  where
    boxWidth = right - left
    boxHeight = bottom - top
