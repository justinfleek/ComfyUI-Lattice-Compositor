{-# LANGUAGE OverloadedStrings #-}

{-|
Module      : Lattice.Utils.Icons
Description : Icon utilities
Copyright   : (c) Lattice, 2026
License     : MIT

Centralized icon mapping using Phosphor Icons.
Maps semantic names to Phosphor icon component names.

Source: lattice-core/lean/Lattice/Utils/Icons.lean
-}

module Lattice.Utils.Icons
  ( -- * Icon Name Mapping
    getIconName
    -- * Layer Type Icons
  , getLayerTypeIcon
    -- * Asset Type Icons
  , getAssetTypeIcon
    -- * Effect Category Icons
  , getEffectCategoryIcon
    -- * Stem Type Icons
  , getStemTypeIcon
  ) where

import Data.Text (Text)

-- ────────────────────────────────────────────────────────────────────────────
-- Icon Name Mapping
-- ────────────────────────────────────────────────────────────────────────────

-- | Get icon name for common UI elements
getIconName :: Text -> Text
getIconName name = case name of
  -- Tools
  "pen" -> "PhPen"
  "pencil" -> "PhPencilSimple"
  "hand" -> "PhHand"
  "magnifyingGlass" -> "PhMagnifyingGlass"
  "sparkle" -> "PhSparkle"
  "star" -> "PhStar"
  "starFilled" -> "PhStarFill"
  "cursor" -> "PhCursor"
  -- Files & Folders
  "folder" -> "PhFolder"
  "folderOpen" -> "PhFolderOpen"
  "file" -> "PhFile"
  "fileText" -> "PhFileText"
  "fileImage" -> "PhFileImage"
  "fileVideo" -> "PhFileVideo"
  "fileAudio" -> "PhFileAudio"
  "download" -> "PhDownloadSimple"
  "upload" -> "PhUploadSimple"
  "export" -> "PhExport"
  "import" -> "PhDownload"
  -- Media
  "image" -> "PhImage"
  "video" -> "PhVideoCamera"
  "film" -> "PhFilmStrip"
  "filmSlate" -> "PhFilmSlate"
  "camera" -> "PhCamera"
  "speaker" -> "PhSpeakerHigh"
  "speakerMute" -> "PhSpeakerSlash"
  "microphone" -> "PhMicrophone"
  "music" -> "PhMusicNote"
  "musicNotes" -> "PhMusicNotes"
  "waveform" -> "PhWaveform"
  -- Controls
  "play" -> "PhPlay"
  "pause" -> "PhPause"
  "stop" -> "PhStop"
  "skipBack" -> "PhSkipBack"
  "skipForward" -> "PhSkipForward"
  "rewind" -> "PhRewind"
  "fastForward" -> "PhFastForward"
  "loop" -> "PhRepeat"
  "shuffle" -> "PhShuffle"
  -- Visibility & Lock
  "eye" -> "PhEye"
  "eyeSlash" -> "PhEyeSlash"
  "lock" -> "PhLock"
  "lockOpen" -> "PhLockOpen"
  "lockKey" -> "PhLockKey"
  -- Actions
  "check" -> "PhCheck"
  "x" -> "PhX"
  "plus" -> "PhPlus"
  "minus" -> "PhMinus"
  "trash" -> "PhTrash"
  "copy" -> "PhCopy"
  "paste" -> "PhClipboard"
  "cut" -> "PhScissors"
  "undo" -> "PhArrowCounterClockwise"
  "redo" -> "PhArrowClockwise"
  "refresh" -> "PhArrowsClockwise"
  --                                                                   // ui // e
  "gear" -> "PhGear"
  "gearSix" -> "PhGearSix"
  "sliders" -> "PhSliders"
  "faders" -> "PhFaders"
  "warning" -> "PhWarning"
  "info" -> "PhInfo"
  "question" -> "PhQuestion"
  "link" -> "PhLink"
  "linkBreak" -> "PhLinkBreak"
  -- Shapes
  "square" -> "PhSquare"
  "circle" -> "PhCircle"
  "triangle" -> "PhTriangle"
  "polygon" -> "PhPolygon"
  "rectangle" -> "PhRectangle"
  "path" -> "PhPath"
  "bezierCurve" -> "PhBezierCurve"
  -- 3D & Layers
  "cube" -> "PhCube"
  "cubeTransparent" -> "PhCubeTransparent"
  "stack" -> "PhStack"
  "stackSimple" -> "PhStackSimple"
  "layers" -> "PhStackSimple"
  -- Text
  "textT" -> "PhTextT"
  "textAa" -> "PhTextAa"
  -- Navigation
  "arrowUp" -> "PhArrowUp"
  "arrowDown" -> "PhArrowDown"
  "arrowLeft" -> "PhArrowLeft"
  "arrowRight" -> "PhArrowRight"
  "caretUp" -> "PhCaretUp"
  "caretDown" -> "PhCaretDown"
  "caretLeft" -> "PhCaretLeft"
  "caretRight" -> "PhCaretRight"
  -- Timeline
  "keyframe" -> "PhDiamond"
  "marker" -> "PhMapPin"
  "ruler" -> "PhRuler"
  "clock" -> "PhClock"
  "timer" -> "PhTimer"
  -- Effects
  "magic" -> "PhMagicWand"
  "sparkles" -> "PhSparkle"
  "lightning" -> "PhLightning"
  "fire" -> "PhFire"
  "drop" -> "PhDrop"
  "wind" -> "PhWind"
  "cloud" -> "PhCloud"
  "sun" -> "PhSun"
  "moon" -> "PhMoon"
  -- Default
  _ -> "PhQuestion"

-- ────────────────────────────────────────────────────────────────────────────
-- Layer Type Icons
-- ────────────────────────────────────────────────────────────────────────────

-- | Get icon for a layer type
getLayerTypeIcon :: Text -> Text
getLayerTypeIcon layerType = case layerType of
  "image" -> "PhImage"
  "video" -> "PhFilmStrip"
  "text" -> "PhTextT"
  "solid" -> "PhSquare"
  "shape" -> "PhPath"
  "spline" -> "PhBezierCurve"
  "null" -> "PhCrosshair"
  "camera" -> "PhCamera"
  "light" -> "PhLightbulb"
  "particles" -> "PhSparkle"
  "audio" -> "PhSpeakerHigh"
  "precomp" -> "PhPackage"
  "nestedComp" -> "PhPackage"
  "adjustment" -> "PhSliders"
  "model" -> "PhCube"
  "pointcloud" -> "PhCloud"
  "depth" -> "PhWaves"
  "normal" -> "PhCompass"
  "generated" -> "PhRobot"
  "group" -> "PhFolder"
  "control" -> "PhCrosshair"
  "matte" -> "PhSelection"
  "path" -> "PhPath"
  "pose" -> "PhPerson"
  _ -> "PhQuestion"

-- ────────────────────────────────────────────────────────────────────────────
-- Asset Type Icons
-- ────────────────────────────────────────────────────────────────────────────

-- | Get icon for an asset type
getAssetTypeIcon :: Text -> Text
getAssetTypeIcon assetType = case assetType of
  "composition" -> "PhFilmSlate"
  "footage" -> "PhFilmStrip"
  "image" -> "PhImage"
  "audio" -> "PhSpeakerHigh"
  "folder" -> "PhFolder"
  "data" -> "PhChartBar"
  "svg" -> "PhVectorTwo"
  "environment" -> "PhSun"
  "model" -> "PhCube"
  _ -> "PhFile"

-- ────────────────────────────────────────────────────────────────────────────
-- Effect Category Icons
-- ────────────────────────────────────────────────────────────────────────────

-- | Get icon for an effect category
getEffectCategoryIcon :: Text -> Text
getEffectCategoryIcon category = case category of
  "blur" -> "PhCircleHalf"
  "color" -> "PhPalette"
  "distort" -> "PhWaveSine"
  "generate" -> "PhSparkle"
  "stylize" -> "PhPaintBrush"
  "time" -> "PhClock"
  "audio" -> "PhWaveform"
  "3d" -> "PhCube"
  _ -> "PhSparkle"

-- ────────────────────────────────────────────────────────────────────────────
-- Stem Type Icons
-- ────────────────────────────────────────────────────────────────────────────

-- | Get icon for an audio stem type
getStemTypeIcon :: Text -> Text
getStemTypeIcon stemType = case stemType of
  "vocals" -> "PhMicrophone"
  "drums" -> "PhDrum"
  "bass" -> "PhWaveSquare"
  "other" -> "PhMusicNote"
  "guitar" -> "PhGuitar"
  "piano" -> "PhPiano"
  _ -> "PhMusicNote"
