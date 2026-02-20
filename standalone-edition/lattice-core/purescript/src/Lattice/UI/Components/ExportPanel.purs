-- | Export Panel Component
-- |
-- | Export settings panel for rendering compositions to video or frame sequences.
-- | Supports:
-- | - Video export (H.264, VP9, VP8) via WebCodecs API
-- | - Frame sequence export (PNG, JPEG, WebP, TIFF, EXR, DPX)
-- | - Quality settings and progress tracking
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/ExportPanel.vue
module Lattice.UI.Components.ExportPanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , ExportMode(..)
  , VideoCodec(..)
  , FrameFormat(..)
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)
import Lattice.UI.Utils as Utils

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { outputWidth :: Int
  , outputHeight :: Int
  , frameRate :: Int
  , totalFrames :: Int
  , webCodecsSupported :: Boolean
  , backendAvailable :: Boolean
  }

data Output
  = StartExport ExportConfig
  | CancelExport
  | DownloadResult

data Query a
  = SetProgress ExportProgress a
  | SetComplete EncodedResult a
  | ResetExport a

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // export // types
-- ════════════════════════════════════════════════════════════════════════════

data ExportMode
  = ExportVideo
  | ExportSequence

derive instance eqExportMode :: Eq ExportMode

instance showExportMode :: Show ExportMode where
  show = case _ of
    ExportVideo -> "video"
    ExportSequence -> "sequence"

data VideoCodec
  = CodecAVC
  | CodecVP9
  | CodecVP8

derive instance eqVideoCodec :: Eq VideoCodec

instance showVideoCodec :: Show VideoCodec where
  show = case _ of
    CodecAVC -> "avc"
    CodecVP9 -> "vp9"
    CodecVP8 -> "vp8"

codecLabel :: VideoCodec -> String
codecLabel = case _ of
  CodecAVC -> "H.264 (MP4)"
  CodecVP9 -> "VP9 (WebM)"
  CodecVP8 -> "VP8 (WebM)"

data VideoQuality
  = QualityLow
  | QualityMedium
  | QualityHigh
  | QualityLossless

derive instance eqVideoQuality :: Eq VideoQuality

instance showVideoQuality :: Show VideoQuality where
  show = case _ of
    QualityLow -> "low"
    QualityMedium -> "medium"
    QualityHigh -> "high"
    QualityLossless -> "lossless"

qualityLabel :: VideoQuality -> String
qualityLabel = case _ of
  QualityLow -> "Low (smaller file)"
  QualityMedium -> "Medium"
  QualityHigh -> "High"
  QualityLossless -> "Lossless (largest)"

data FrameFormat
  = FormatPNG
  | FormatJPEG
  | FormatWebP
  | FormatTIFF
  | FormatEXR
  | FormatDPX

derive instance eqFrameFormat :: Eq FrameFormat

instance showFrameFormat :: Show FrameFormat where
  show = case _ of
    FormatPNG -> "png"
    FormatJPEG -> "jpeg"
    FormatWebP -> "webp"
    FormatTIFF -> "tiff"
    FormatEXR -> "exr"
    FormatDPX -> "dpx"

formatLabel :: FrameFormat -> String
formatLabel = case _ of
  FormatPNG -> "PNG (Lossless)"
  FormatJPEG -> "JPEG (Lossy)"
  FormatWebP -> "WebP (Modern)"
  FormatTIFF -> "TIFF 16-bit (Backend)"
  FormatEXR -> "OpenEXR HDR (Backend)"
  FormatDPX -> "DPX Film (Backend)"

formatRequiresBackend :: FrameFormat -> Boolean
formatRequiresBackend = case _ of
  FormatTIFF -> true
  FormatEXR -> true
  FormatDPX -> true
  _ -> false

formatDescription :: FrameFormat -> String
formatDescription = case _ of
  FormatPNG -> "Lossless compression, supports transparency"
  FormatJPEG -> "Small files, no transparency"
  FormatWebP -> "Modern format, good compression"
  FormatTIFF -> "High bit depth, professional workflows"
  FormatEXR -> "HDR, VFX industry standard"
  FormatDPX -> "Film/broadcast standard"

type ExportConfig =
  { mode :: ExportMode
  , codec :: VideoCodec
  , quality :: VideoQuality
  , format :: FrameFormat
  , sequenceQuality :: Int
  }

type ExportProgress =
  { framesEncoded :: Int
  , totalFrames :: Int
  , percentage :: Number
  , bytesWritten :: Int
  }

type EncodedResult =
  { size :: Int
  , filename :: String
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { input :: Input
  , exportMode :: ExportMode
  , selectedCodec :: VideoCodec
  , selectedQuality :: VideoQuality
  , sequenceFormat :: FrameFormat
  , sequenceQuality :: Int
  , isExporting :: Boolean
  , exportComplete :: Boolean
  , progress :: ExportProgress
  , result :: Maybe EncodedResult
  }

data Action
  = Initialize
  | Receive Input
  | SetExportMode ExportMode
  | SetCodec VideoCodec
  | SetQuality VideoQuality
  | SetFormat FrameFormat
  | SetSequenceQuality String
  | StartExportAction
  | CancelExportAction
  | DownloadAction

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input: input
  , exportMode: ExportVideo
  , selectedCodec: CodecAVC
  , selectedQuality: QualityHigh
  , sequenceFormat: FormatPNG
  , sequenceQuality: 95
  , isExporting: false
  , exportComplete: false
  , progress: { framesEncoded: 0, totalFrames: 0, percentage: 0.0, bytesWritten: 0 }
  , result: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-export-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Export Settings"
    ]
    [ renderHeader
    , renderContent state
    ]

renderHeader :: forall m. H.ComponentHTML Action Slots m
renderHeader =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.span 
        [ cls [ "panel-title" ]
        , HP.attr (HH.AttrName "style") titleStyle
        ] 
        [ HH.text "Export" ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ renderModeSection state
    , case state.exportMode of
        ExportVideo -> renderVideoSection state
        ExportSequence -> renderSequenceSection state
    , renderOutputSection state
    , if state.isExporting || state.exportComplete
        then renderProgressSection state
        else HH.text ""
    , renderActionsSection state
    , if not state.input.webCodecsSupported && state.exportMode == ExportVideo
        then renderWarning
        else HH.text ""
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                        // mode // section
-- ════════════════════════════════════════════════════════════════════════════

renderModeSection :: forall m. State -> H.ComponentHTML Action Slots m
renderModeSection state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div 
        [ cls [ "section-header" ]
        , HP.attr (HH.AttrName "style") sectionHeaderStyle
        ]
        [ HH.span 
            [ cls [ "section-title" ]
            , HP.id "export-mode-label"
            ] 
            [ HH.text "Export Mode" ]
        ]
    , HH.div 
        [ cls [ "mode-toggle" ]
        , HP.attr (HH.AttrName "style") modeToggleStyle
        , HP.attr (HH.AttrName "role") "group"
        , ARIA.labelledBy "export-mode-label"
        ]
        [ modeButton "Video" ExportVideo state
        , modeButton "Frame Sequence" ExportSequence state
        ]
    ]

modeButton :: forall m. String -> ExportMode -> State -> H.ComponentHTML Action Slots m
modeButton labelText mode state =
  let isActive = mode == state.exportMode
  in
  HH.button
    [ cls [ "mode-btn" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") (modeBtnStyle isActive)
    , HP.disabled state.isExporting
    , ARIA.pressed (show isActive)
    , HP.attr (HH.AttrName "data-state") (if isActive then "active" else "inactive")
    , HE.onClick \_ -> SetExportMode mode
    ]
    [ HH.text labelText ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // video // section
-- ════════════════════════════════════════════════════════════════════════════

renderVideoSection :: forall m. State -> H.ComponentHTML Action Slots m
renderVideoSection state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.span [ cls [ "section-title" ] ] [ HH.text "Video Format" ] ]
    , renderControlRow "Codec" (renderCodecSelect state)
    , renderControlRow "Quality" (renderQualitySelect state)
    ]

renderCodecSelect :: forall m. State -> H.ComponentHTML Action Slots m
renderCodecSelect state =
  HH.select
    [ cls [ "codec-select" ]
    , HP.attr (HH.AttrName "style") selectStyle
    , HP.disabled state.isExporting
    , HE.onValueChange \v -> SetCodec (parseCodec v)
    ]
    [ HH.option [ HP.value "avc", HP.selected (state.selectedCodec == CodecAVC) ] 
        [ HH.text (codecLabel CodecAVC) ]
    , HH.option [ HP.value "vp9", HP.selected (state.selectedCodec == CodecVP9) ] 
        [ HH.text (codecLabel CodecVP9) ]
    , HH.option [ HP.value "vp8", HP.selected (state.selectedCodec == CodecVP8) ] 
        [ HH.text (codecLabel CodecVP8) ]
    ]

parseCodec :: String -> VideoCodec
parseCodec = case _ of
  "vp9" -> CodecVP9
  "vp8" -> CodecVP8
  _ -> CodecAVC

renderQualitySelect :: forall m. State -> H.ComponentHTML Action Slots m
renderQualitySelect state =
  HH.select
    [ cls [ "quality-select" ]
    , HP.attr (HH.AttrName "style") selectStyle
    , HP.disabled state.isExporting
    , HE.onValueChange \v -> SetQuality (parseQuality v)
    ]
    [ HH.option [ HP.value "low", HP.selected (state.selectedQuality == QualityLow) ] 
        [ HH.text (qualityLabel QualityLow) ]
    , HH.option [ HP.value "medium", HP.selected (state.selectedQuality == QualityMedium) ] 
        [ HH.text (qualityLabel QualityMedium) ]
    , HH.option [ HP.value "high", HP.selected (state.selectedQuality == QualityHigh) ] 
        [ HH.text (qualityLabel QualityHigh) ]
    , HH.option [ HP.value "lossless", HP.selected (state.selectedQuality == QualityLossless) ] 
        [ HH.text (qualityLabel QualityLossless) ]
    ]

parseQuality :: String -> VideoQuality
parseQuality = case _ of
  "low" -> QualityLow
  "medium" -> QualityMedium
  "lossless" -> QualityLossless
  _ -> QualityHigh

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // sequence // section
-- ════════════════════════════════════════════════════════════════════════════

renderSequenceSection :: forall m. State -> H.ComponentHTML Action Slots m
renderSequenceSection state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.span [ cls [ "section-title" ] ] [ HH.text "Sequence Format" ] ]
    , renderControlRow "Format" (renderFormatSelect state)
    , if needsQualitySlider state.sequenceFormat
        then renderQualitySlider state
        else HH.text ""
    , renderFormatInfo state
    ]

renderFormatSelect :: forall m. State -> H.ComponentHTML Action Slots m
renderFormatSelect state =
  HH.select
    [ cls [ "format-select" ]
    , HP.attr (HH.AttrName "style") selectStyle
    , HP.disabled state.isExporting
    , HE.onValueChange \v -> SetFormat (parseFormat v)
    ]
    [ HH.option [ HP.value "png", HP.selected (state.sequenceFormat == FormatPNG) ] 
        [ HH.text (formatLabel FormatPNG) ]
    , HH.option [ HP.value "jpeg", HP.selected (state.sequenceFormat == FormatJPEG) ] 
        [ HH.text (formatLabel FormatJPEG) ]
    , HH.option [ HP.value "webp", HP.selected (state.sequenceFormat == FormatWebP) ] 
        [ HH.text (formatLabel FormatWebP) ]
    , HH.option 
        [ HP.value "tiff"
        , HP.selected (state.sequenceFormat == FormatTIFF)
        , HP.disabled (not state.input.backendAvailable)
        ] 
        [ HH.text (formatLabel FormatTIFF) ]
    , HH.option 
        [ HP.value "exr"
        , HP.selected (state.sequenceFormat == FormatEXR)
        , HP.disabled (not state.input.backendAvailable)
        ] 
        [ HH.text (formatLabel FormatEXR) ]
    , HH.option 
        [ HP.value "dpx"
        , HP.selected (state.sequenceFormat == FormatDPX)
        , HP.disabled (not state.input.backendAvailable)
        ] 
        [ HH.text (formatLabel FormatDPX) ]
    ]

parseFormat :: String -> FrameFormat
parseFormat = case _ of
  "jpeg" -> FormatJPEG
  "webp" -> FormatWebP
  "tiff" -> FormatTIFF
  "exr" -> FormatEXR
  "dpx" -> FormatDPX
  _ -> FormatPNG

needsQualitySlider :: FrameFormat -> Boolean
needsQualitySlider = case _ of
  FormatJPEG -> true
  FormatWebP -> true
  _ -> false

renderQualitySlider :: forall m. State -> H.ComponentHTML Action Slots m
renderQualitySlider state =
  HH.div
    [ cls [ "control-row" ]
    , HP.attr (HH.AttrName "style") controlRowStyle
    ]
    [ HH.label_ [ HH.text "Quality" ]
    , HH.input
        [ HP.type_ HP.InputRange
        , HP.attr (HH.AttrName "min") "1"
        , HP.attr (HH.AttrName "max") "100"
        , HP.value (show state.sequenceQuality)
        , HP.disabled state.isExporting
        , HP.attr (HH.AttrName "style") rangeStyle
        , HE.onValueInput SetSequenceQuality
        ]
    , HH.span 
        [ cls [ "quality-value" ]
        , HP.attr (HH.AttrName "style") qualityValueStyle
        ] 
        [ HH.text (show state.sequenceQuality <> "%") ]
    ]

renderFormatInfo :: forall m. State -> H.ComponentHTML Action Slots m
renderFormatInfo state =
  HH.div
    [ cls [ "format-info" ]
    , HP.attr (HH.AttrName "style") formatInfoStyle
    ]
    [ HH.div 
        [ cls [ "info-badge" ]
        , HP.attr (HH.AttrName "style") (infoBadgeStyle (formatRequiresBackend state.sequenceFormat))
        ]
        [ HH.text (if formatRequiresBackend state.sequenceFormat then "Backend Required" else "Browser Export") ]
    , HH.span 
        [ cls [ "format-desc" ]
        , HP.attr (HH.AttrName "style") formatDescStyle
        ] 
        [ HH.text (formatDescription state.sequenceFormat) ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // output // section
-- ════════════════════════════════════════════════════════════════════════════

renderOutputSection :: forall m. State -> H.ComponentHTML Action Slots m
renderOutputSection state =
  HH.div
    [ cls [ "control-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.div [ cls [ "section-header" ], HP.attr (HH.AttrName "style") sectionHeaderStyle ]
        [ HH.span [ cls [ "section-title" ] ] [ HH.text "Output" ] ]
    , HH.div 
        [ cls [ "info-grid" ]
        , HP.attr (HH.AttrName "style") infoGridStyle
        ]
        [ renderInfoItem "Size" (show state.input.outputWidth <> " x " <> show state.input.outputHeight)
        , renderInfoItem "Frame Rate" (show state.input.frameRate <> " fps")
        , renderInfoItem "Duration" (formatDuration state.input.totalFrames state.input.frameRate)
        , renderInfoItem "Total Frames" (show state.input.totalFrames)
        ]
    ]

renderInfoItem :: forall m. String -> String -> H.ComponentHTML Action Slots m
renderInfoItem label value =
  HH.div
    [ cls [ "info-item" ]
    , HP.attr (HH.AttrName "style") infoItemStyle
    ]
    [ HH.span [ cls [ "info-label" ], HP.attr (HH.AttrName "style") infoLabelStyle ] [ HH.text label ]
    , HH.span [ cls [ "info-value" ], HP.attr (HH.AttrName "style") infoValueStyle ] [ HH.text value ]
    ]

formatDuration :: Int -> Int -> String
formatDuration frames fps =
  let
    seconds = toNumber frames / toNumber fps
    m = floor (seconds / 60.0)
    s = seconds - (toNumber m * 60.0)
  in
    if m > 0
      then show m <> "m " <> formatNum s <> "s"
      else formatNum s <> "s"

toNumber :: Int -> Number
toNumber = Utils.toNumber

floor :: Number -> Int
floor = Utils.floor

formatNum :: Number -> String
formatNum = Utils.formatFixed 2

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // progress // section
-- ════════════════════════════════════════════════════════════════════════════

renderProgressSection :: forall m. State -> H.ComponentHTML Action Slots m
renderProgressSection state =
  HH.div
    [ cls [ "progress-section" ]
    , HP.attr (HH.AttrName "style") progressSectionStyle
    , HP.attr (HH.AttrName "role") "progressbar"
    , ARIA.valueNow (show state.progress.percentage)
    , ARIA.valueMin "0"
    , ARIA.valueMax "100"
    ]
    [ HH.div 
        [ cls [ "progress-header" ]
        , HP.attr (HH.AttrName "style") progressHeaderStyle
        ]
        [ HH.span_ [ HH.text (statusText state) ]
        , if state.isExporting
            then HH.span_ [ HH.text (formatNum state.progress.percentage <> "%") ]
            else HH.text ""
        ]
    , HH.div 
        [ cls [ "progress-bar" ]
        , HP.attr (HH.AttrName "style") progressBarStyle
        ]
        [ HH.div 
            [ cls [ "progress-fill" ]
            , HP.attr (HH.AttrName "style") (progressFillStyle state.progress.percentage)
            ] 
            []
        ]
    , if state.isExporting
        then HH.div 
              [ cls [ "progress-details" ]
              , HP.attr (HH.AttrName "style") progressDetailsStyle
              ]
              [ HH.span_ [ HH.text ("Frame " <> show state.progress.framesEncoded <> " / " <> show state.progress.totalFrames) ]
              , HH.span_ [ HH.text (formatBytes state.progress.bytesWritten) ]
              ]
        else HH.text ""
    ]

statusText :: State -> String
statusText state
  | state.exportComplete = "Export complete!"
  | state.isExporting = 
      if state.exportMode == ExportSequence 
        then "Rendering frames..."
        else "Encoding..."
  | otherwise = "Ready"

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // actions // section
-- ════════════════════════════════════════════════════════════════════════════

renderActionsSection :: forall m. State -> H.ComponentHTML Action Slots m
renderActionsSection state =
  HH.div
    [ cls [ "actions-section" ]
    , HP.attr (HH.AttrName "style") actionsSectionStyle
    ]
    [ if not state.isExporting
        then renderExportButton state
        else renderCancelButton
    , if state.exportComplete
        then renderDownloadButton state
        else HH.text ""
    ]

renderExportButton :: forall m. State -> H.ComponentHTML Action Slots m
renderExportButton state =
  let
    canExport = not state.isExporting && 
                (state.exportMode == ExportSequence || state.input.webCodecsSupported)
    labelText = if state.exportMode == ExportVideo then "Export Video" else "Export Frames"
  in
  HH.button
    [ cls [ "export-btn", "primary" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") primaryBtnStyle
    , HP.disabled (not canExport)
    , HE.onClick \_ -> StartExportAction
    ]
    [ HH.text labelText ]

renderCancelButton :: forall m. H.ComponentHTML Action Slots m
renderCancelButton =
  HH.button
    [ cls [ "export-btn", "cancel" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") cancelBtnStyle
    , HE.onClick \_ -> CancelExportAction
    ]
    [ HH.text "Cancel" ]

renderDownloadButton :: forall m. State -> H.ComponentHTML Action Slots m
renderDownloadButton state =
  let
    sizeText = case state.result of
      Just r -> " (" <> formatBytes r.size <> ")"
      Nothing -> ""
    labelText = if state.exportMode == ExportVideo 
      then "Download" <> sizeText
      else "Download ZIP" <> sizeText
  in
  HH.button
    [ cls [ "export-btn", "download" ]
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "style") downloadBtnStyle
    , HE.onClick \_ -> DownloadAction
    ]
    [ HH.text labelText ]

renderWarning :: forall m. H.ComponentHTML Action Slots m
renderWarning =
  HH.div
    [ cls [ "warning-message" ]
    , HP.attr (HH.AttrName "style") warningStyle
    , HP.attr (HH.AttrName "role") "alert"
    ]
    [ HH.span [ cls [ "warning-icon" ], HP.attr (HH.AttrName "aria-hidden") "true" ] [ HH.text "⚠️" ]
    , HH.span_ [ HH.text "WebCodecs API not supported in this browser. Video export unavailable." ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

renderControlRow :: forall m. String -> H.ComponentHTML Action Slots m -> H.ComponentHTML Action Slots m
renderControlRow label control =
  HH.div
    [ cls [ "control-row" ]
    , HP.attr (HH.AttrName "style") controlRowStyle
    ]
    [ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text label ]
    , control
    ]

formatBytes :: Int -> String
formatBytes bytes =
  if bytes == 0 then "0 B"
  else
    let
      k = 1024.0
      bytesN = toNumber bytes
      i = floor (log bytesN / log k)
      sizes = ["B", "KB", "MB", "GB"]
      size = case Array.index sizes i of
               Just s -> s
               Nothing -> "B"
      value = bytesN / (pow k (toNumber i))
    in
      formatNum value <> " " <> size

log :: Number -> Number
log = Utils.log

pow :: Number -> Number -> Number
pow = Utils.pow

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "background: var(--lattice-surface-1); border-radius: 8px; " <>
  "overflow: hidden; display: flex; flex-direction: column;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; justify-content: space-between; " <>
  "padding: 12px 16px; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

titleStyle :: String
titleStyle =
  "font-weight: 600; font-size: 14px; color: var(--lattice-text-primary);"

contentStyle :: String
contentStyle =
  "flex: 1; padding: 16px; display: flex; flex-direction: column; gap: 16px; " <>
  "overflow-y: auto; overflow-x: hidden;"

sectionStyle :: String
sectionStyle =
  "background: var(--lattice-surface-2); border-radius: 6px; padding: 12px;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "margin-bottom: 12px;"

modeToggleStyle :: String
modeToggleStyle =
  "display: flex; gap: 4px; background: var(--lattice-surface-1); " <>
  "border-radius: 6px; padding: 4px;"

modeBtnStyle :: Boolean -> String
modeBtnStyle active =
  "flex: 1; padding: 8px 16px; border: none; border-radius: 4px; " <>
  "background: " <> (if active then "var(--lattice-accent)" else "transparent") <> "; " <>
  "color: " <> (if active then "white" else "var(--lattice-text-secondary)") <> "; " <>
  "font-size: 13px; font-weight: 500; cursor: pointer;"

controlRowStyle :: String
controlRowStyle =
  "display: flex; align-items: center; gap: 12px; margin-bottom: 8px;"

labelStyle :: String
labelStyle =
  "min-width: 80px; font-size: 13px; color: var(--lattice-text-primary);"

selectStyle :: String
selectStyle =
  "flex: 1; padding: 6px 10px; background: var(--lattice-surface-1); " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 4px; " <>
  "color: var(--lattice-text-primary); font-size: 13px;"

rangeStyle :: String
rangeStyle =
  "flex: 1; height: 4px; background: var(--lattice-surface-1); " <>
  "border-radius: 2px; cursor: pointer;"

qualityValueStyle :: String
qualityValueStyle =
  "min-width: 40px; text-align: right; font-size: 13px; color: var(--lattice-text-primary);"

formatInfoStyle :: String
formatInfoStyle =
  "display: flex; align-items: center; gap: 8px; margin-top: 8px; " <>
  "padding-top: 8px; border-top: 1px solid var(--lattice-border-subtle);"

infoBadgeStyle :: Boolean -> String
infoBadgeStyle requiresBackend =
  let
    (bg, fg) = if requiresBackend
      then ("rgba(234, 179, 8, 0.2)", "#eab308")
      else ("rgba(34, 197, 94, 0.2)", "#22c55e")
  in
    "padding: 2px 8px; border-radius: 4px; font-size: 11px; " <>
    "font-weight: 600; text-transform: uppercase; " <>
    "background: " <> bg <> "; color: " <> fg <> ";"

formatDescStyle :: String
formatDescStyle =
  "font-size: 12px; color: var(--lattice-text-secondary);"

infoGridStyle :: String
infoGridStyle =
  "display: grid; grid-template-columns: 1fr 1fr; gap: 8px;"

infoItemStyle :: String
infoItemStyle =
  "display: flex; justify-content: space-between; font-size: 13px;"

infoLabelStyle :: String
infoLabelStyle =
  "color: var(--lattice-text-secondary);"

infoValueStyle :: String
infoValueStyle =
  "color: var(--lattice-text-primary); font-weight: 500;"

progressSectionStyle :: String
progressSectionStyle =
  "background: var(--lattice-surface-2); border-radius: 6px; padding: 12px;"

progressHeaderStyle :: String
progressHeaderStyle =
  "display: flex; justify-content: space-between; margin-bottom: 8px; " <>
  "font-size: 13px; color: var(--lattice-text-primary);"

progressBarStyle :: String
progressBarStyle =
  "height: 8px; background: var(--lattice-surface-1); " <>
  "border-radius: 4px; overflow: hidden;"

progressFillStyle :: Number -> String
progressFillStyle percentage =
  "height: 100%; background: linear-gradient(90deg, #4f46e5, #7c3aed); " <>
  "transition: width 0.1s ease; width: " <> show percentage <> "%;"

progressDetailsStyle :: String
progressDetailsStyle =
  "display: flex; justify-content: space-between; margin-top: 8px; " <>
  "font-size: 12px; color: var(--lattice-text-secondary);"

actionsSectionStyle :: String
actionsSectionStyle =
  "display: flex; gap: 8px; flex-wrap: wrap;"

primaryBtnStyle :: String
primaryBtnStyle =
  "flex: 1; min-width: 120px; padding: 10px 16px; border: none; " <>
  "border-radius: 6px; font-size: 14px; font-weight: 500; cursor: pointer; " <>
  "background: linear-gradient(135deg, #4f46e5, #7c3aed); color: white;"

cancelBtnStyle :: String
cancelBtnStyle =
  "flex: 1; min-width: 120px; padding: 10px 16px; " <>
  "border: 1px solid var(--lattice-border-default); border-radius: 6px; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "font-size: 14px; font-weight: 500; cursor: pointer;"

downloadBtnStyle :: String
downloadBtnStyle =
  "flex: 1; min-width: 120px; padding: 10px 16px; border: none; " <>
  "border-radius: 6px; font-size: 14px; font-weight: 500; cursor: pointer; " <>
  "background: #059669; color: white;"

warningStyle :: String
warningStyle =
  "display: flex; align-items: center; gap: 8px; padding: 12px; " <>
  "background: rgba(234, 179, 8, 0.1); border: 1px solid rgba(234, 179, 8, 0.3); " <>
  "border-radius: 6px; font-size: 13px; color: #fbbf24;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ { input = input }
  
  SetExportMode mode -> do
    H.modify_ _ { exportMode = mode }
  
  SetCodec codec -> do
    H.modify_ _ { selectedCodec = codec }
  
  SetQuality quality -> do
    H.modify_ _ { selectedQuality = quality }
  
  SetFormat format -> do
    H.modify_ _ { sequenceFormat = format }
  
  SetSequenceQuality val -> do
    let quality = parseIntSafe val 95
    H.modify_ _ { sequenceQuality = quality }
  
  StartExportAction -> do
    state <- H.get
    H.modify_ _ 
      { isExporting = true
      , exportComplete = false
      , result = Nothing
      , progress = { framesEncoded: 0, totalFrames: state.input.totalFrames, percentage: 0.0, bytesWritten: 0 }
      }
    H.raise $ StartExport
      { mode: state.exportMode
      , codec: state.selectedCodec
      , quality: state.selectedQuality
      , format: state.sequenceFormat
      , sequenceQuality: state.sequenceQuality
      }
  
  CancelExportAction -> do
    H.modify_ _ { isExporting = false }
    H.raise CancelExport
  
  DownloadAction -> do
    H.raise DownloadResult

parseIntSafe :: String -> Int -> Int
parseIntSafe str defaultVal = Utils.parseIntOr defaultVal str

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  SetProgress progress next -> do
    H.modify_ _ { progress = progress }
    pure (Just next)
  
  SetComplete result next -> do
    H.modify_ _ 
      { isExporting = false
      , exportComplete = true
      , result = Just result
      }
    pure (Just next)
  
  ResetExport next -> do
    H.modify_ _ 
      { isExporting = false
      , exportComplete = false
      , result = Nothing
      , progress = { framesEncoded: 0, totalFrames: 0, percentage: 0.0, bytesWritten: 0 }
      }
    pure (Just next)
