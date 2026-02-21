-- | Output Module Panel Component
-- |
-- | Configures output settings for rendered content.
-- | Settings include:
-- | - Format (PNG sequence, JPEG sequence, MP4, WebM, GIF)
-- | - Color profile (sRGB, Display P3, ProPhoto RGB)
-- | - Color depth (8-bit, 16-bit)
-- | - Alpha channel (straight, premultiplied, none)
-- | - Naming pattern (comp name, custom pattern)
-- | - Destination (download, ComfyUI output folder, custom)
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/OutputModulePanel.vue
module Lattice.UI.Components.OutputModulePanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , OutputModuleSettings
  , OutputFormat(..)
  , VideoBitrate(..)
  , ColorDepth(..)
  , ColorProfile(..)
  , AlphaMode(..)
  , NamingPattern(..)
  , Destination(..)
  , PostAction(..)
  ) where

import Prelude

import Data.Array (elem)
import Data.Array as Array
import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls)

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { settings :: OutputModuleSettings
  , compositionName :: String
  }

data Output
  = SettingsChanged OutputModuleSettings

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                         // settings // types
-- =============================================================================

type OutputModuleSettings =
  { format :: OutputFormat
  , quality :: Int                  -- 1-100 for lossy formats
  , videoBitrate :: VideoBitrate
  , colorDepth :: ColorDepth
  , colorProfile :: ColorProfile
  , alpha :: AlphaMode
  , namingPattern :: NamingPattern
  , customPattern :: String
  , framePadding :: Int             -- 0, 2, 4, 5
  , destination :: Destination
  , customPath :: String
  , createSubfolder :: Boolean
  , openOnComplete :: Boolean
  , notifyOnComplete :: Boolean
  , postAction :: PostAction
  }

data OutputFormat
  = PngSequence
  | JpegSequence
  | WebpSequence
  | Mp4Video
  | WebmVideo
  | AnimatedGif

derive instance eqOutputFormat :: Eq OutputFormat

data VideoBitrate
  = BitrateLow
  | BitrateMedium
  | BitrateHigh
  | BitrateUltra

derive instance eqVideoBitrate :: Eq VideoBitrate

data ColorDepth
  = Depth8Bit
  | Depth16Bit

derive instance eqColorDepth :: Eq ColorDepth

data ColorProfile
  = ProfileSrgb
  | ProfileDisplayP3
  | ProfileProPhotoRgb
  | ProfileNone

derive instance eqColorProfile :: Eq ColorProfile

data AlphaMode
  = AlphaNone
  | AlphaStraight
  | AlphaPremultiplied

derive instance eqAlphaMode :: Eq AlphaMode

data NamingPattern
  = PatternComp
  | PatternCompFrame
  | PatternFrameOnly
  | PatternCustom

derive instance eqNamingPattern :: Eq NamingPattern

data Destination
  = DestDownload
  | DestComfyui
  | DestCustom

derive instance eqDestination :: Eq Destination

data PostAction
  = ActionNone
  | ActionImport
  | ActionComfyuiQueue

derive instance eqPostAction :: Eq PostAction

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { settings :: OutputModuleSettings
  , compositionName :: String
  , baseId :: String
  }

data Action
  = Initialize
  | Receive Input
  | SetFormat OutputFormat
  | SetQuality Int
  | SetVideoBitrate VideoBitrate
  | SetColorDepth ColorDepth
  | SetColorProfile ColorProfile
  | SetAlphaMode AlphaMode
  | SetNamingPattern NamingPattern
  | SetCustomPattern String
  | SetFramePadding Int
  | SetDestination Destination
  | SetCustomPath String
  | ToggleCreateSubfolder
  | ToggleOpenOnComplete
  | ToggleNotifyOnComplete
  | SetPostAction PostAction

type Slots = ()

-- =============================================================================
--                                                               // component
-- =============================================================================

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { settings: input.settings
  , compositionName: input.compositionName
  , baseId: "lattice-output-module"
  }

defaultSettings :: OutputModuleSettings
defaultSettings =
  { format: PngSequence
  , quality: 90
  , videoBitrate: BitrateMedium
  , colorDepth: Depth8Bit
  , colorProfile: ProfileSrgb
  , alpha: AlphaNone
  , namingPattern: PatternCompFrame
  , customPattern: "frame_[####]"
  , framePadding: 4
  , destination: DestDownload
  , customPath: ""
  , createSubfolder: true
  , openOnComplete: false
  , notifyOnComplete: true
  , postAction: ActionNone
  }

-- =============================================================================
--                                                                    // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-output-module-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "Output Module Settings"
    ]
    [ renderFormatSection state
    , renderColorSection state
    , renderOutputSection state
    , renderPostRenderSection state
    , renderPreviewFooter state
    ]

-- =============================================================================
--                                                        // format // section
-- =============================================================================

renderFormatSection :: forall m. State -> H.ComponentHTML Action Slots m
renderFormatSection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h4 [ HP.attr (HH.AttrName "style") sectionTitleStyle ] 
        [ HH.text "Output Module" ]
    
    -- Format
    , renderFormRow "Format"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueInput \v -> SetFormat (parseFormat v)
            , HP.attr (HH.AttrName "aria-label") "Output format"
            ]
            [ HH.option [ HP.value "png-sequence", HP.selected (state.settings.format == PngSequence) ] 
                [ HH.text "PNG Sequence" ]
            , HH.option [ HP.value "jpeg-sequence", HP.selected (state.settings.format == JpegSequence) ] 
                [ HH.text "JPEG Sequence" ]
            , HH.option [ HP.value "webp-sequence", HP.selected (state.settings.format == WebpSequence) ] 
                [ HH.text "WebP Sequence" ]
            , HH.option [ HP.value "mp4", HP.selected (state.settings.format == Mp4Video) ] 
                [ HH.text "MP4 Video (H.264)" ]
            , HH.option [ HP.value "webm", HP.selected (state.settings.format == WebmVideo) ] 
                [ HH.text "WebM Video (VP9)" ]
            , HH.option [ HP.value "gif", HP.selected (state.settings.format == AnimatedGif) ] 
                [ HH.text "Animated GIF" ]
            ]
        ]
    
    -- Quality (for lossy formats)
    , if showQualitySlider state.settings.format
        then renderSubFormRow "Quality"
               [ HH.div
                   [ cls [ "slider-row" ]
                   , HP.attr (HH.AttrName "style") sliderRowStyle
                   ]
                   [ HH.input
                       [ HP.type_ HP.InputRange
                       , HP.attr (HH.AttrName "style") rangeInputStyle
                       , HP.min 1.0
                       , HP.max 100.0
                       , HP.value (show state.settings.quality)
                       , HE.onValueInput \v -> SetQuality (parseIntOr 90 v)
                       , HP.attr (HH.AttrName "aria-label") "Quality"
                       ]
                   , HH.span 
                       [ cls [ "slider-value" ]
                       , HP.attr (HH.AttrName "style") sliderValueStyle
                       ] 
                       [ HH.text (show state.settings.quality <> "%") ]
                   ]
               ]
        else HH.text ""
    
    -- Video Bitrate (for video formats)
    , if isVideoFormat state.settings.format
        then renderSubFormRow "Bitrate"
               [ HH.select
                   [ cls [ "lattice-select" ]
                   , HP.attr (HH.AttrName "style") selectStyle
                   , HE.onValueInput \v -> SetVideoBitrate (parseBitrate v)
                   , HP.attr (HH.AttrName "aria-label") "Video bitrate"
                   ]
                   [ HH.option [ HP.value "low", HP.selected (state.settings.videoBitrate == BitrateLow) ] 
                       [ HH.text "Low (2 Mbps)" ]
                   , HH.option [ HP.value "medium", HP.selected (state.settings.videoBitrate == BitrateMedium) ] 
                       [ HH.text "Medium (5 Mbps)" ]
                   , HH.option [ HP.value "high", HP.selected (state.settings.videoBitrate == BitrateHigh) ] 
                       [ HH.text "High (10 Mbps)" ]
                   , HH.option [ HP.value "ultra", HP.selected (state.settings.videoBitrate == BitrateUltra) ] 
                       [ HH.text "Ultra (20 Mbps)" ]
                   ]
               ]
        else HH.text ""
    ]

-- =============================================================================
--                                                         // color // section
-- =============================================================================

renderColorSection :: forall m. State -> H.ComponentHTML Action Slots m
renderColorSection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h4 [ HP.attr (HH.AttrName "style") sectionTitleStyle ] 
        [ HH.text "Color" ]
    
    -- Color Depth
    , renderFormRow "Depth"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueInput \v -> SetColorDepth (parseColorDepth v)
            , HP.attr (HH.AttrName "aria-label") "Color depth"
            ]
            [ HH.option [ HP.value "8", HP.selected (state.settings.colorDepth == Depth8Bit) ] 
                [ HH.text "8-bit (Standard)" ]
            , HH.option [ HP.value "16", HP.selected (state.settings.colorDepth == Depth16Bit) ] 
                [ HH.text "16-bit (HDR)" ]
            ]
        ]
    
    -- Color Profile
    , renderFormRow "Profile"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueInput \v -> SetColorProfile (parseColorProfile v)
            , HP.attr (HH.AttrName "aria-label") "Color profile"
            ]
            [ HH.option [ HP.value "srgb", HP.selected (state.settings.colorProfile == ProfileSrgb) ] 
                [ HH.text "sRGB (Web)" ]
            , HH.option [ HP.value "display-p3", HP.selected (state.settings.colorProfile == ProfileDisplayP3) ] 
                [ HH.text "Display P3 (Wide Gamut)" ]
            , HH.option [ HP.value "prophoto-rgb", HP.selected (state.settings.colorProfile == ProfileProPhotoRgb) ] 
                [ HH.text "ProPhoto RGB" ]
            , HH.option [ HP.value "none", HP.selected (state.settings.colorProfile == ProfileNone) ] 
                [ HH.text "Unmanaged" ]
            ]
        ]
    
    -- Alpha Channel
    , if supportsAlpha state.settings.format
        then renderFormRow "Alpha"
               [ HH.select
                   [ cls [ "lattice-select" ]
                   , HP.attr (HH.AttrName "style") selectStyle
                   , HE.onValueInput \v -> SetAlphaMode (parseAlphaMode v)
                   , HP.attr (HH.AttrName "aria-label") "Alpha channel mode"
                   ]
                   [ HH.option [ HP.value "none", HP.selected (state.settings.alpha == AlphaNone) ] 
                       [ HH.text "No Alpha" ]
                   , HH.option [ HP.value "straight", HP.selected (state.settings.alpha == AlphaStraight) ] 
                       [ HH.text "Straight (Unmatted)" ]
                   , HH.option [ HP.value "premultiplied", HP.selected (state.settings.alpha == AlphaPremultiplied) ] 
                       [ HH.text "Premultiplied" ]
                   ]
               ]
        else HH.text ""
    ]

-- =============================================================================
--                                                        // output // section
-- =============================================================================

renderOutputSection :: forall m. State -> H.ComponentHTML Action Slots m
renderOutputSection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h4 [ HP.attr (HH.AttrName "style") sectionTitleStyle ] 
        [ HH.text "Output" ]
    
    -- Naming Pattern
    , renderFormRow "Naming"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueInput \v -> SetNamingPattern (parseNamingPattern v)
            , HP.attr (HH.AttrName "aria-label") "File naming pattern"
            ]
            [ HH.option [ HP.value "comp", HP.selected (state.settings.namingPattern == PatternComp) ] 
                [ HH.text "Composition Name" ]
            , HH.option [ HP.value "comp-frame", HP.selected (state.settings.namingPattern == PatternCompFrame) ] 
                [ HH.text "Comp_[frame]" ]
            , HH.option [ HP.value "frame-only", HP.selected (state.settings.namingPattern == PatternFrameOnly) ] 
                [ HH.text "[frame]" ]
            , HH.option [ HP.value "custom", HP.selected (state.settings.namingPattern == PatternCustom) ] 
                [ HH.text "Custom Pattern" ]
            ]
        ]
    
    -- Custom Pattern
    , if state.settings.namingPattern == PatternCustom
        then renderSubFormRow "Pattern"
               [ HH.input
                   [ HP.type_ HP.InputText
                   , cls [ "lattice-input" ]
                   , HP.attr (HH.AttrName "style") textInputStyle
                   , HP.placeholder "frame_[####]"
                   , HP.value state.settings.customPattern
                   , HE.onValueInput SetCustomPattern
                   , HP.attr (HH.AttrName "aria-label") "Custom naming pattern"
                   ]
               ]
        else HH.text ""
    
    -- Frame Padding
    , if isSequenceFormat state.settings.format
        then renderFormRow "Padding"
               [ HH.select
                   [ cls [ "lattice-select" ]
                   , HP.attr (HH.AttrName "style") selectStyle
                   , HE.onValueInput \v -> SetFramePadding (parseIntOr 4 v)
                   , HP.attr (HH.AttrName "aria-label") "Frame number padding"
                   ]
                   [ HH.option [ HP.value "0", HP.selected (state.settings.framePadding == 0) ] 
                       [ HH.text "No padding (1, 2, 10)" ]
                   , HH.option [ HP.value "2", HP.selected (state.settings.framePadding == 2) ] 
                       [ HH.text "2 digits (01, 02, 10)" ]
                   , HH.option [ HP.value "4", HP.selected (state.settings.framePadding == 4) ] 
                       [ HH.text "4 digits (0001, 0002)" ]
                   , HH.option [ HP.value "5", HP.selected (state.settings.framePadding == 5) ] 
                       [ HH.text "5 digits (00001, 00002)" ]
                   ]
               ]
        else HH.text ""
    
    -- Destination
    , renderFormRow "Destination"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueInput \v -> SetDestination (parseDestination v)
            , HP.attr (HH.AttrName "aria-label") "Output destination"
            ]
            [ HH.option [ HP.value "download", HP.selected (state.settings.destination == DestDownload) ] 
                [ HH.text "Download (Browser)" ]
            , HH.option [ HP.value "comfyui", HP.selected (state.settings.destination == DestComfyui) ] 
                [ HH.text "ComfyUI Output" ]
            , HH.option [ HP.value "custom", HP.selected (state.settings.destination == DestCustom) ] 
                [ HH.text "Custom Path" ]
            ]
        ]
    
    -- Custom Path
    , if state.settings.destination == DestCustom
        then renderSubFormRow "Path"
               [ HH.div
                   [ cls [ "path-input" ]
                   , HP.attr (HH.AttrName "style") pathInputStyle
                   ]
                   [ HH.input
                       [ HP.type_ HP.InputText
                       , cls [ "lattice-input" ]
                       , HP.attr (HH.AttrName "style") (textInputStyle <> " flex: 1;")
                       , HP.placeholder "/path/to/output"
                       , HP.value state.settings.customPath
                       , HE.onValueInput SetCustomPath
                       , HP.attr (HH.AttrName "aria-label") "Custom output path"
                       ]
                   , HH.button
                       [ cls [ "browse-btn" ]
                       , HP.attr (HH.AttrName "style") browseButtonStyle
                       , HP.attr (HH.AttrName "title") "Browse"
                       , HP.attr (HH.AttrName "aria-label") "Browse for folder"
                       ]
                       [ HH.text "..." ]
                   ]
               ]
        else HH.text ""
    
    -- Create Subfolder
    , renderCheckboxRow "Create Subfolder per Render" state.settings.createSubfolder ToggleCreateSubfolder
    ]

-- =============================================================================
--                                                   // post-render // section
-- =============================================================================

renderPostRenderSection :: forall m. State -> H.ComponentHTML Action Slots m
renderPostRenderSection state =
  HH.div
    [ cls [ "panel-section" ]
    , HP.attr (HH.AttrName "style") sectionStyle
    ]
    [ HH.h4 [ HP.attr (HH.AttrName "style") sectionTitleStyle ] 
        [ HH.text "Post-Render" ]
    
    , renderCheckboxRow "Open Output on Complete" state.settings.openOnComplete ToggleOpenOnComplete
    , renderCheckboxRow "Notify When Done" state.settings.notifyOnComplete ToggleNotifyOnComplete
    
    -- Post Action
    , renderFormRow "Action"
        [ HH.select
            [ cls [ "lattice-select" ]
            , HP.attr (HH.AttrName "style") selectStyle
            , HE.onValueInput \v -> SetPostAction (parsePostAction v)
            , HP.attr (HH.AttrName "aria-label") "Post-render action"
            ]
            [ HH.option [ HP.value "none", HP.selected (state.settings.postAction == ActionNone) ] 
                [ HH.text "None" ]
            , HH.option [ HP.value "import", HP.selected (state.settings.postAction == ActionImport) ] 
                [ HH.text "Import to Project" ]
            , HH.option [ HP.value "comfyui-queue", HP.selected (state.settings.postAction == ActionComfyuiQueue) ] 
                [ HH.text "Send to ComfyUI Queue" ]
            ]
        ]
    ]

-- =============================================================================
--                                                       // preview // footer
-- =============================================================================

renderPreviewFooter :: forall m. State -> H.ComponentHTML Action Slots m
renderPreviewFooter state =
  let
    preview = outputPreview state.compositionName state.settings
  in
    HH.div
      [ cls [ "preview-footer" ]
      , HP.attr (HH.AttrName "style") previewFooterStyle
      ]
      [ HH.div
          [ cls [ "output-preview" ]
          , HP.attr (HH.AttrName "style") outputPreviewStyle
          ]
          [ HH.span [ cls [ "preview-label" ], HP.attr (HH.AttrName "style") previewLabelStyle ] 
              [ HH.text "Output:" ]
          , HH.span [ cls [ "preview-value" ], HP.attr (HH.AttrName "style") previewValueStyle ] 
              [ HH.text preview ]
          ]
      ]

-- =============================================================================
--                                                        // helper // renders
-- =============================================================================

renderFormRow :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
renderFormRow labelText children =
  HH.div
    [ cls [ "form-row" ]
    , HP.attr (HH.AttrName "style") formRowStyle
    ]
    ([ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text labelText ] ] <> children)

renderSubFormRow :: forall m. String -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
renderSubFormRow labelText children =
  HH.div
    [ cls [ "form-row", "sub-row" ]
    , HP.attr (HH.AttrName "style") (formRowStyle <> " margin-left: 20px;")
    ]
    ([ HH.label [ HP.attr (HH.AttrName "style") labelStyle ] [ HH.text labelText ] ] <> children)

renderCheckboxRow :: forall m. String -> Boolean -> Action -> H.ComponentHTML Action Slots m
renderCheckboxRow labelText checked action =
  HH.div
    [ cls [ "form-row" ]
    , HP.attr (HH.AttrName "style") formRowStyle
    ]
    [ HH.label
        [ cls [ "checkbox-label" ]
        , HP.attr (HH.AttrName "style") checkboxLabelStyle
        ]
        [ HH.input
            [ HP.type_ HP.InputCheckbox
            , HP.checked checked
            , HE.onChecked \_ -> action
            , HP.attr (HH.AttrName "aria-label") labelText
            ]
        , HH.text labelText
        ]
    ]

-- =============================================================================
--                                                       // helper // functions
-- =============================================================================

showQualitySlider :: OutputFormat -> Boolean
showQualitySlider format = elem format [JpegSequence, WebpSequence, Mp4Video, WebmVideo]

isVideoFormat :: OutputFormat -> Boolean
isVideoFormat format = elem format [Mp4Video, WebmVideo]

isSequenceFormat :: OutputFormat -> Boolean
isSequenceFormat format = elem format [PngSequence, JpegSequence, WebpSequence]

supportsAlpha :: OutputFormat -> Boolean
supportsAlpha format = elem format [PngSequence, WebpSequence, WebmVideo]

parseFormat :: String -> OutputFormat
parseFormat = case _ of
  "png-sequence" -> PngSequence
  "jpeg-sequence" -> JpegSequence
  "webp-sequence" -> WebpSequence
  "mp4" -> Mp4Video
  "webm" -> WebmVideo
  "gif" -> AnimatedGif
  _ -> PngSequence

parseBitrate :: String -> VideoBitrate
parseBitrate = case _ of
  "low" -> BitrateLow
  "medium" -> BitrateMedium
  "high" -> BitrateHigh
  "ultra" -> BitrateUltra
  _ -> BitrateMedium

parseColorDepth :: String -> ColorDepth
parseColorDepth = case _ of
  "8" -> Depth8Bit
  "16" -> Depth16Bit
  _ -> Depth8Bit

parseColorProfile :: String -> ColorProfile
parseColorProfile = case _ of
  "srgb" -> ProfileSrgb
  "display-p3" -> ProfileDisplayP3
  "prophoto-rgb" -> ProfileProPhotoRgb
  "none" -> ProfileNone
  _ -> ProfileSrgb

parseAlphaMode :: String -> AlphaMode
parseAlphaMode = case _ of
  "none" -> AlphaNone
  "straight" -> AlphaStraight
  "premultiplied" -> AlphaPremultiplied
  _ -> AlphaNone

parseNamingPattern :: String -> NamingPattern
parseNamingPattern = case _ of
  "comp" -> PatternComp
  "comp-frame" -> PatternCompFrame
  "frame-only" -> PatternFrameOnly
  "custom" -> PatternCustom
  _ -> PatternCompFrame

parseDestination :: String -> Destination
parseDestination = case _ of
  "download" -> DestDownload
  "comfyui" -> DestComfyui
  "custom" -> DestCustom
  _ -> DestDownload

parsePostAction :: String -> PostAction
parsePostAction = case _ of
  "none" -> ActionNone
  "import" -> ActionImport
  "comfyui-queue" -> ActionComfyuiQueue
  _ -> ActionNone

parseIntOr :: Int -> String -> Int
parseIntOr default s = case Int.fromString s of
  Just n -> n
  Nothing -> default

getExtension :: OutputFormat -> String
getExtension = case _ of
  PngSequence -> "png"
  JpegSequence -> "jpg"
  WebpSequence -> "webp"
  Mp4Video -> "mp4"
  WebmVideo -> "webm"
  AnimatedGif -> "gif"

outputPreview :: String -> OutputModuleSettings -> String
outputPreview compName settings =
  let
    ext = getExtension settings.format
    padding = repeatChar '0' settings.framePadding
    name = case settings.namingPattern of
      PatternComp -> compName
      PatternCompFrame -> compName <> "_" <> padding
      PatternFrameOnly -> padding
      PatternCustom -> String.replaceAll (String.Pattern "[####]") (String.Replacement padding) settings.customPattern
  in
    name <> "." <> ext

repeatChar :: Char -> Int -> String
repeatChar c n = 
  if n <= 0 
    then "" 
    else String.fromCodePointArray (map (\_ -> String.codePointFromChar c) (Array.range 1 n))

-- =============================================================================
--                                                                    // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; gap: 16px; padding: 12px; " <>
  "font-size: 12px; color: var(--lattice-text-primary);"

sectionStyle :: String
sectionStyle =
  "display: flex; flex-direction: column; gap: 8px; padding-bottom: 12px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

sectionTitleStyle :: String
sectionTitleStyle =
  "margin: 0; font-size: 11px; font-weight: 600; text-transform: uppercase; " <>
  "letter-spacing: 0.5px; color: var(--lattice-text-muted);"

formRowStyle :: String
formRowStyle =
  "display: flex; align-items: center; gap: 8px;"

labelStyle :: String
labelStyle =
  "flex: 0 0 80px; color: var(--lattice-text-muted);"

selectStyle :: String
selectStyle =
  "flex: 1; padding: 4px 8px; background: var(--lattice-surface-2); " <>
  "border: 1px solid var(--lattice-border); border-radius: 4px; " <>
  "color: var(--lattice-text-primary); font-size: 12px;"

textInputStyle :: String
textInputStyle =
  "padding: 4px 8px; background: var(--lattice-surface-2); " <>
  "border: 1px solid var(--lattice-border); border-radius: 4px; " <>
  "color: var(--lattice-text-primary); font-size: 12px;"

sliderRowStyle :: String
sliderRowStyle =
  "display: flex; align-items: center; gap: 8px; flex: 1;"

rangeInputStyle :: String
rangeInputStyle =
  "flex: 1; height: 4px; -webkit-appearance: none; " <>
  "background: var(--lattice-surface-3); border-radius: 2px;"

sliderValueStyle :: String
sliderValueStyle =
  "min-width: 45px; text-align: right; color: var(--lattice-text-muted); font-family: monospace;"

pathInputStyle :: String
pathInputStyle =
  "display: flex; flex: 1; gap: 4px;"

browseButtonStyle :: String
browseButtonStyle =
  "padding: 4px 8px; background: var(--lattice-surface-3); " <>
  "border: 1px solid var(--lattice-border); border-radius: 4px; " <>
  "color: var(--lattice-text-muted); cursor: pointer;"

checkboxLabelStyle :: String
checkboxLabelStyle =
  "display: flex; align-items: center; gap: 8px; cursor: pointer; color: var(--lattice-text-primary);"

previewFooterStyle :: String
previewFooterStyle =
  "padding-top: 12px; border-top: 1px solid var(--lattice-border-subtle);"

outputPreviewStyle :: String
outputPreviewStyle =
  "display: flex; align-items: center; gap: 8px; padding: 8px; " <>
  "background: var(--lattice-surface-2); border-radius: 4px;"

previewLabelStyle :: String
previewLabelStyle =
  "color: var(--lattice-text-muted);"

previewValueStyle :: String
previewValueStyle =
  "font-family: monospace; color: var(--lattice-accent);"

-- =============================================================================
--                                                                   // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { settings = input.settings, compositionName = input.compositionName }

  SetFormat format -> do
    state <- H.get
    let newSettings = state.settings { format = format }
    -- Clear alpha if format doesn't support it
    let finalSettings = if supportsAlpha format
                          then newSettings
                          else newSettings { alpha = AlphaNone }
    H.modify_ _ { settings = finalSettings }
    H.raise (SettingsChanged finalSettings)

  SetQuality quality -> do
    updateAndRaise \s -> s { quality = quality }

  SetVideoBitrate bitrate -> do
    updateAndRaise \s -> s { videoBitrate = bitrate }

  SetColorDepth depth -> do
    updateAndRaise \s -> s { colorDepth = depth }

  SetColorProfile profile -> do
    updateAndRaise \s -> s { colorProfile = profile }

  SetAlphaMode alpha -> do
    updateAndRaise \s -> s { alpha = alpha }

  SetNamingPattern pattern -> do
    updateAndRaise \s -> s { namingPattern = pattern }

  SetCustomPattern pattern -> do
    updateAndRaise \s -> s { customPattern = pattern }

  SetFramePadding padding -> do
    updateAndRaise \s -> s { framePadding = padding }

  SetDestination dest -> do
    updateAndRaise \s -> s { destination = dest }

  SetCustomPath path -> do
    updateAndRaise \s -> s { customPath = path }

  ToggleCreateSubfolder -> do
    state <- H.get
    updateAndRaise \s -> s { createSubfolder = not state.settings.createSubfolder }

  ToggleOpenOnComplete -> do
    state <- H.get
    updateAndRaise \s -> s { openOnComplete = not state.settings.openOnComplete }

  ToggleNotifyOnComplete -> do
    state <- H.get
    updateAndRaise \s -> s { notifyOnComplete = not state.settings.notifyOnComplete }

  SetPostAction action -> do
    updateAndRaise \s -> s { postAction = action }

  where
    updateAndRaise :: (OutputModuleSettings -> OutputModuleSettings) -> H.HalogenM State Action Slots Output m Unit
    updateAndRaise f = do
      state <- H.get
      let newSettings = f state.settings
      H.modify_ _ { settings = newSettings }
      H.raise (SettingsChanged newSettings)
