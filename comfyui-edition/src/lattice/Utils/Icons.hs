-- |
-- Module      : Lattice.Utils.Icons
-- Description : Icon name mappings for UI (Phosphor Icons).
-- Ported from ui/src/utils/icons.ts. Pure data, no forbidden patterns.
--

{-# LANGUAGE OverloadedStrings #-}

module Lattice.Utils.Icons
  ( iconName
  , layerTypeIcon
  , assetTypeIcon
  , stemTypeIcon
  , effectCategoryIcon
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Text (Text)

-- | Semantic name -> Phosphor component name. Lookup via 'iconName'.
iconNamesMap :: HashMap Text Text
iconNamesMap =
  HM.fromList
    [ ("pen", "PhPen")
    , ("pencil", "PhPencilSimple")
    , ("hand", "PhHand")
    , ("magnifyingGlass", "PhMagnifyingGlass")
    , ("sparkle", "PhSparkle")
    , ("star", "PhStar")
    , ("starFilled", "PhStarFill")
    , ("cursor", "PhCursor")
    , ("folder", "PhFolder")
    , ("folderOpen", "PhFolderOpen")
    , ("file", "PhFile")
    , ("fileText", "PhFileText")
    , ("fileImage", "PhFileImage")
    , ("fileVideo", "PhFileVideo")
    , ("fileAudio", "PhFileAudio")
    , ("download", "PhDownloadSimple")
    , ("upload", "PhUploadSimple")
    , ("export", "PhExport")
    , ("import", "PhDownload")
    , ("image", "PhImage")
    , ("video", "PhVideoCamera")
    , ("film", "PhFilmStrip")
    , ("filmSlate", "PhFilmSlate")
    , ("camera", "PhCamera")
    , ("speaker", "PhSpeakerHigh")
    , ("speakerMute", "PhSpeakerSlash")
    , ("microphone", "PhMicrophone")
    , ("music", "PhMusicNote")
    , ("musicNotes", "PhMusicNotes")
    , ("waveform", "PhWaveform")
    , ("piano", "PhPiano")
    , ("guitar", "PhGuitar")
    , ("drums", "PhDrum")
    , ("vocals", "PhMicrophone")
    , ("play", "PhPlay")
    , ("pause", "PhPause")
    , ("stop", "PhStop")
    , ("skipBack", "PhSkipBack")
    , ("skipForward", "PhSkipForward")
    , ("rewind", "PhRewind")
    , ("fastForward", "PhFastForward")
    , ("loop", "PhRepeat")
    , ("shuffle", "PhShuffle")
    , ("eye", "PhEye")
    , ("eyeSlash", "PhEyeSlash")
    , ("lock", "PhLock")
    , ("lockOpen", "PhLockOpen")
    , ("lockKey", "PhLockKey")
    , ("check", "PhCheck")
    , ("x", "PhX")
    , ("plus", "PhPlus")
    , ("minus", "PhMinus")
    , ("trash", "PhTrash")
    , ("copy", "PhCopy")
    , ("paste", "PhClipboard")
    , ("cut", "PhScissors")
    , ("undo", "PhArrowCounterClockwise")
    , ("redo", "PhArrowClockwise")
    , ("refresh", "PhArrowsClockwise")
    , ("gear", "PhGear")
    , ("gearSix", "PhGearSix")
    , ("sliders", "PhSliders")
    , ("faders", "PhFaders")
    , ("warning", "PhWarning")
    , ("info", "PhInfo")
    , ("question", "PhQuestion")
    , ("link", "PhLink")
    , ("linkBreak", "PhLinkBreak")
    , ("chain", "PhChain")
    , ("square", "PhSquare")
    , ("circle", "PhCircle")
    , ("triangle", "PhTriangle")
    , ("polygon", "PhPolygon")
    , ("rectangle", "PhRectangle")
    , ("path", "PhPath")
    , ("bezierCurve", "PhBezierCurve")
    , ("vectorTwo", "PhVectorTwo")
    , ("cube", "PhCube")
    , ("cubeTransparent", "PhCubeTransparent")
    , ("stack", "PhStack")
    , ("stackSimple", "PhStackSimple")
    , ("layers", "PhStackSimple")
    , ("textT", "PhTextT")
    , ("textAa", "PhTextAa")
    , ("textAlignLeft", "PhTextAlignLeft")
    , ("arrowUp", "PhArrowUp")
    , ("arrowDown", "PhArrowDown")
    , ("arrowLeft", "PhArrowLeft")
    , ("arrowRight", "PhArrowRight")
    , ("caretUp", "PhCaretUp")
    , ("caretDown", "PhCaretDown")
    , ("caretLeft", "PhCaretLeft")
    , ("caretRight", "PhCaretRight")
    , ("keyframe", "PhDiamond")
    , ("marker", "PhMapPin")
    , ("ruler", "PhRuler")
    , ("clock", "PhClock")
    , ("timer", "PhTimer")
    , ("magic", "PhMagicWand")
    , ("sparkles", "PhSparkle")
    , ("lightning", "PhLightning")
    , ("fire", "PhFire")
    , ("drop", "PhDrop")
    , ("wind", "PhWind")
    , ("cloud", "PhCloud")
    , ("sun", "PhSun")
    , ("sunDim", "PhSunDim")
    , ("moon", "PhMoon")
    , ("chartLine", "PhChartLine")
    , ("chartLineUp", "PhChartLineUp")
    , ("chartBar", "PhChartBar")
    , ("activity", "PhActivity")
    , ("pulse", "PhPulse")
    , ("robot", "PhRobot")
    , ("package", "PhPackage")
    , ("compass", "PhCompass")
    , ("waves", "PhWaves")
    , ("monitor", "PhMonitor")
    , ("desktop", "PhDesktop")
    , ("palette", "PhPalette")
    , ("paintBrush", "PhPaintBrush")
    , ("atom", "PhAtom")
    , ("circuitry", "PhCircuitry")
    , ("globe", "PhGlobeSimple")
    , ("target", "PhTarget")
    , ("crosshair", "PhCrosshair")
    , ("lightbulb", "PhLightbulb")
    , ("lamp", "PhLamp")
    , ("flashlight", "PhFlashlight")
    , ("eyedropper", "PhEyedropper")
    , ("selection", "PhSelection")
    , ("selectionAll", "PhSelectionAll")
    , ("boundingBox", "PhBoundingBox")
    , ("dice", "PhDice")
    , ("caretDoubleUp", "PhCaretDoubleUp")
    , ("caretDoubleDown", "PhCaretDoubleDown")
    , ("arrowsOut", "PhArrowsOut")
    , ("arrowsIn", "PhArrowsIn")
    , ("cornersOut", "PhCornersOut")
    , ("cornersIn", "PhCornersIn")
    ]

-- | Lookup semantic icon name. Returns default "PhCircle" when not found.
iconName :: Text -> Text
iconName k = HM.findWithDefault "PhCircle" k iconNamesMap

layerTypeIconMap :: HashMap Text Text
layerTypeIconMap =
  HM.fromList
    [ ("image", "PhImage")
    , ("video", "PhFilmStrip")
    , ("text", "PhTextT")
    , ("solid", "PhSquare")
    , ("shape", "PhPath")
    , ("spline", "PhBezierCurve")
    , ("null", "PhCrosshair")
    , ("camera", "PhCamera")
    , ("light", "PhLightbulb")
    , ("particles", "PhSparkle")
    , ("audio", "PhSpeakerHigh")
    , ("precomp", "PhPackage")
    , ("nestedComp", "PhPackage")
    , ("adjustment", "PhSliders")
    , ("model", "PhCube")
    , ("pointcloud", "PhCloud")
    , ("depth", "PhWaves")
    , ("normal", "PhCompass")
    , ("generated", "PhRobot")
    , ("group", "PhFolder")
    , ("control", "PhCrosshair")
    , ("matte", "PhSelection")
    , ("path", "PhPath")
    , ("pose", "PhPerson")
    ]

-- | Icon for layer type. Default "PhSquare".
layerTypeIcon :: Text -> Text
layerTypeIcon k = HM.findWithDefault "PhSquare" k layerTypeIconMap

assetTypeIconMap :: HashMap Text Text
assetTypeIconMap =
  HM.fromList
    [ ("composition", "PhFilmSlate")
    , ("footage", "PhFilmStrip")
    , ("image", "PhImage")
    , ("audio", "PhSpeakerHigh")
    , ("folder", "PhFolder")
    , ("data", "PhChartBar")
    , ("svg", "PhVectorTwo")
    , ("environment", "PhSun")
    , ("model", "PhCube")
    ]

-- | Icon for asset type. Default "PhFile".
assetTypeIcon :: Text -> Text
assetTypeIcon k = HM.findWithDefault "PhFile" k assetTypeIconMap

stemTypeIconMap :: HashMap Text Text
stemTypeIconMap =
  HM.fromList
    [ ("vocals", "PhMicrophone")
    , ("drums", "PhDrum")
    , ("bass", "PhWaveSquare")
    , ("other", "PhMusicNote")
    , ("guitar", "PhGuitar")
    , ("piano", "PhPiano")
    ]

-- | Icon for stem type. Default "PhMusicNote".
stemTypeIcon :: Text -> Text
stemTypeIcon k = HM.findWithDefault "PhMusicNote" k stemTypeIconMap

effectCategoryIconMap :: HashMap Text Text
effectCategoryIconMap =
  HM.fromList
    [ ("blur", "PhCircleHalf")
    , ("color", "PhPalette")
    , ("distort", "PhWaveSine")
    , ("generate", "PhSparkle")
    , ("stylize", "PhPaintBrush")
    , ("time", "PhClock")
    , ("audio", "PhWaveform")
    , ("3d", "PhCube")
    ]

-- | Icon for effect category. Default "PhSliders".
effectCategoryIcon :: Text -> Text
effectCategoryIcon k = HM.findWithDefault "PhSliders" k effectCategoryIconMap
