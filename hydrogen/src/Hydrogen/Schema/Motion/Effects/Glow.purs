-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // schema // motion // effects // glow
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Glow effect enums for motion graphics.
-- |
-- | Defines composite modes, color modes, looping, falloff, tonemapping,
-- | and bloom blend modes.

module Hydrogen.Schema.Motion.Effects.Glow
  ( -- * Glow Composite Mode
    GlowCompositeMode(..)
  , allGlowCompositeModes
  , glowCompositeModeToString
  , glowCompositeModeFromString
  
    -- * Glow Colors Mode
  , GlowColorsMode(..)
  , allGlowColorsModes
  , glowColorsModeToString
  , glowColorsModeFromString
  
    -- * Color Looping
  , ColorLooping(..)
  , allColorLoopings
  , colorLoopingToString
  , colorLoopingFromString
  
    -- * Falloff Mode
  , FalloffMode(..)
  , allFalloffModes
  , falloffModeToString
  , falloffModeFromString
  
    -- * Tonemap Mode
  , TonemapMode(..)
  , allTonemapModes
  , tonemapModeToString
  , tonemapModeFromString
  
    -- * Bloom Blend Mode
  , BloomBlendMode(..)
  , allBloomBlendModes
  , bloomBlendModeToString
  , bloomBlendModeFromString
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // glow // composite // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How glow is composited with source.
data GlowCompositeMode
  = GCMOnTop   -- ^ Glow on top of source
  | GCMBehind  -- ^ Glow behind source
  | GCMNone    -- ^ Glow only (no source)

derive instance eqGlowCompositeMode :: Eq GlowCompositeMode
derive instance ordGlowCompositeMode :: Ord GlowCompositeMode

instance showGlowCompositeMode :: Show GlowCompositeMode where
  show GCMOnTop = "GCMOnTop"
  show GCMBehind = "GCMBehind"
  show GCMNone = "GCMNone"

-- | All glow composite modes for enumeration
allGlowCompositeModes :: Array GlowCompositeMode
allGlowCompositeModes = [ GCMOnTop, GCMBehind, GCMNone ]

glowCompositeModeToString :: GlowCompositeMode -> String
glowCompositeModeToString GCMOnTop = "on-top"
glowCompositeModeToString GCMBehind = "behind"
glowCompositeModeToString GCMNone = "none"

glowCompositeModeFromString :: String -> Maybe GlowCompositeMode
glowCompositeModeFromString "on-top" = Just GCMOnTop
glowCompositeModeFromString "behind" = Just GCMBehind
glowCompositeModeFromString "none" = Just GCMNone
glowCompositeModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // glow // colors // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How glow colors are determined.
data GlowColorsMode
  = GCMOriginal  -- ^ Use original source colors
  | GCMAB        -- ^ Interpolate between A and B colors

derive instance eqGlowColorsMode :: Eq GlowColorsMode
derive instance ordGlowColorsMode :: Ord GlowColorsMode

instance showGlowColorsMode :: Show GlowColorsMode where
  show GCMOriginal = "GCMOriginal"
  show GCMAB = "GCMAB"

-- | All glow colors modes for enumeration
allGlowColorsModes :: Array GlowColorsMode
allGlowColorsModes = [ GCMOriginal, GCMAB ]

glowColorsModeToString :: GlowColorsMode -> String
glowColorsModeToString GCMOriginal = "original"
glowColorsModeToString GCMAB = "ab"

glowColorsModeFromString :: String -> Maybe GlowColorsMode
glowColorsModeFromString "original" = Just GCMOriginal
glowColorsModeFromString "ab" = Just GCMAB
glowColorsModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color // looping
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color cycling behavior for glow.
data ColorLooping
  = CLNone        -- ^ No looping
  | CLSawtoothAB  -- ^ Sawtooth A→B
  | CLSawtoothBA  -- ^ Sawtooth B→A
  | CLTriangle    -- ^ Triangle wave A→B→A

derive instance eqColorLooping :: Eq ColorLooping
derive instance ordColorLooping :: Ord ColorLooping

instance showColorLooping :: Show ColorLooping where
  show CLNone = "CLNone"
  show CLSawtoothAB = "CLSawtoothAB"
  show CLSawtoothBA = "CLSawtoothBA"
  show CLTriangle = "CLTriangle"

-- | All color looping modes for enumeration
allColorLoopings :: Array ColorLooping
allColorLoopings = [ CLNone, CLSawtoothAB, CLSawtoothBA, CLTriangle ]

colorLoopingToString :: ColorLooping -> String
colorLoopingToString CLNone = "none"
colorLoopingToString CLSawtoothAB = "sawtooth-ab"
colorLoopingToString CLSawtoothBA = "sawtooth-ba"
colorLoopingToString CLTriangle = "triangle"

colorLoopingFromString :: String -> Maybe ColorLooping
colorLoopingFromString "none" = Just CLNone
colorLoopingFromString "sawtooth-ab" = Just CLSawtoothAB
colorLoopingFromString "sawtooth-ba" = Just CLSawtoothBA
colorLoopingFromString "triangle" = Just CLTriangle
colorLoopingFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // falloff // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Intensity falloff mode.
data FalloffMode
  = FMInverseSquare  -- ^ 1/r² falloff (physically accurate)
  | FMGaussian       -- ^ Gaussian curve
  | FMExponential    -- ^ Exponential decay

derive instance eqFalloffMode :: Eq FalloffMode
derive instance ordFalloffMode :: Ord FalloffMode

instance showFalloffMode :: Show FalloffMode where
  show FMInverseSquare = "FMInverseSquare"
  show FMGaussian = "FMGaussian"
  show FMExponential = "FMExponential"

-- | All falloff modes for enumeration
allFalloffModes :: Array FalloffMode
allFalloffModes = [ FMInverseSquare, FMGaussian, FMExponential ]

falloffModeToString :: FalloffMode -> String
falloffModeToString FMInverseSquare = "inverse-square"
falloffModeToString FMGaussian = "gaussian"
falloffModeToString FMExponential = "exponential"

falloffModeFromString :: String -> Maybe FalloffMode
falloffModeFromString "inverse-square" = Just FMInverseSquare
falloffModeFromString "gaussian" = Just FMGaussian
falloffModeFromString "exponential" = Just FMExponential
falloffModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // tonemap // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | HDR tonemapping mode.
data TonemapMode
  = TMNone      -- ^ No tonemapping
  | TMACES      -- ^ ACES filmic
  | TMReinhard  -- ^ Reinhard tonemapping
  | TMHable     -- ^ Hable/Uncharted 2

derive instance eqTonemapMode :: Eq TonemapMode
derive instance ordTonemapMode :: Ord TonemapMode

instance showTonemapMode :: Show TonemapMode where
  show TMNone = "TMNone"
  show TMACES = "TMACES"
  show TMReinhard = "TMReinhard"
  show TMHable = "TMHable"

-- | All tonemap modes for enumeration
allTonemapModes :: Array TonemapMode
allTonemapModes = [ TMNone, TMACES, TMReinhard, TMHable ]

tonemapModeToString :: TonemapMode -> String
tonemapModeToString TMNone = "none"
tonemapModeToString TMACES = "aces"
tonemapModeToString TMReinhard = "reinhard"
tonemapModeToString TMHable = "hable"

tonemapModeFromString :: String -> Maybe TonemapMode
tonemapModeFromString "none" = Just TMNone
tonemapModeFromString "aces" = Just TMACES
tonemapModeFromString "reinhard" = Just TMReinhard
tonemapModeFromString "hable" = Just TMHable
tonemapModeFromString _ = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // bloom // blend // mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bloom effect blend mode.
data BloomBlendMode
  = BBMAdd       -- ^ Additive blend
  | BBMScreen    -- ^ Screen blend
  | BBMOverlay   -- ^ Overlay blend
  | BBMSoftLight -- ^ Soft light blend

derive instance eqBloomBlendMode :: Eq BloomBlendMode
derive instance ordBloomBlendMode :: Ord BloomBlendMode

instance showBloomBlendMode :: Show BloomBlendMode where
  show BBMAdd = "BBMAdd"
  show BBMScreen = "BBMScreen"
  show BBMOverlay = "BBMOverlay"
  show BBMSoftLight = "BBMSoftLight"

-- | All bloom blend modes for enumeration
allBloomBlendModes :: Array BloomBlendMode
allBloomBlendModes = [ BBMAdd, BBMScreen, BBMOverlay, BBMSoftLight ]

bloomBlendModeToString :: BloomBlendMode -> String
bloomBlendModeToString BBMAdd = "add"
bloomBlendModeToString BBMScreen = "screen"
bloomBlendModeToString BBMOverlay = "overlay"
bloomBlendModeToString BBMSoftLight = "soft-light"

bloomBlendModeFromString :: String -> Maybe BloomBlendMode
bloomBlendModeFromString "add" = Just BBMAdd
bloomBlendModeFromString "screen" = Just BBMScreen
bloomBlendModeFromString "overlay" = Just BBMOverlay
bloomBlendModeFromString "soft-light" = Just BBMSoftLight
bloomBlendModeFromString _ = Nothing
