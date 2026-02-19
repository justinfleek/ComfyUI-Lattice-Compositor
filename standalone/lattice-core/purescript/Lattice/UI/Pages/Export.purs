-- | Export Page Component
-- |
-- | Export and render queue management for the Lattice Compositor.
-- | Shows:
-- | - Active render jobs
-- | - Completed exports
-- | - Export format settings
module Lattice.UI.Pages.Export
  ( component
  ) where

import Prelude

import Data.Array (length)
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ============================================================
-- TYPES
-- ============================================================

data JobStatus
  = Queued
  | Rendering
  | Completed
  | Failed

derive instance eqJobStatus :: Eq JobStatus

data ExportFormat
  = MP4
  | ProRes
  | PNG_Sequence
  | EXR_Sequence

derive instance eqExportFormat :: Eq ExportFormat

type RenderJob =
  { id :: String
  , compositionName :: String
  , format :: ExportFormat
  , status :: JobStatus
  , progress :: Number  -- 0.0 to 1.0
  , outputPath :: String
  , startTime :: String
  , endTime :: String
  }

type State =
  { jobs :: Array RenderJob
  , selectedFormat :: ExportFormat
  , outputPath :: String
  }

data Action
  = Initialize
  | SetFormat ExportFormat
  | SetOutputPath String
  | StartExport
  | CancelJob String
  | ClearCompleted

-- ============================================================
-- COMPONENT
-- ============================================================

component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: State
initialState =
  { jobs: []  -- Empty queue
  , selectedFormat: MP4
  , outputPath: "~/exports/"
  }

-- ============================================================
-- RENDER
-- ============================================================

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-page", "lattice-export-page" ]
    , HP.attr (HH.AttrName "style") pageStyle
    ]
    [ HH.div
        [ cls [ "lattice-export-container" ]
        , HP.attr (HH.AttrName "style") containerStyle
        ]
        [ -- Header
          renderHeader
        
          -- Main content
        , HH.div 
            [ cls [ "lattice-export-content" ]
            , HP.attr (HH.AttrName "style") contentStyle
            ]
            [ -- Export settings panel
              renderExportSettings state
            
              -- Render queue panel
            , renderRenderQueue state
            ]
        ]
    ]

renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.header
    [ cls [ "lattice-export-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h1 
        [ HP.attr (HH.AttrName "style") titleStyle ]
        [ HH.text "Export / Render Queue" ]
    ]

renderExportSettings :: forall m. State -> H.ComponentHTML Action () m
renderExportSettings state =
  HH.section
    [ cls [ "lattice-export-settings" ]
    , HP.attr (HH.AttrName "style") settingsStyle
    ]
    [ HH.h2 
        [ HP.attr (HH.AttrName "style") sectionTitleStyle ]
        [ HH.text "Export Settings" ]
    
      -- Format selection
    , HH.div [ cls [ "lattice-setting-group" ], HP.attr (HH.AttrName "style") settingGroupStyle ]
        [ HH.label 
            [ HP.attr (HH.AttrName "style") labelStyle ]
            [ HH.text "Format" ]
        , HH.div 
            [ cls [ "lattice-format-options" ]
            , HP.attr (HH.AttrName "style") formatOptionsStyle
            ]
            [ renderFormatOption state MP4 "MP4 (H.264)" "Best for web and sharing"
            , renderFormatOption state ProRes "ProRes" "Best for editing"
            , renderFormatOption state PNG_Sequence "PNG Sequence" "Lossless with alpha"
            , renderFormatOption state EXR_Sequence "EXR Sequence" "HDR / VFX workflows"
            ]
        ]
    
      -- Output path
    , HH.div [ cls [ "lattice-setting-group" ], HP.attr (HH.AttrName "style") settingGroupStyle ]
        [ HH.label 
            [ HP.attr (HH.AttrName "style") labelStyle ]
            [ HH.text "Output Location" ]
        , HH.div [ cls [ "lattice-path-input" ], HP.attr (HH.AttrName "style") pathInputStyle ]
            [ HH.input
                [ cls [ "lattice-input" ]
                , HP.value state.outputPath
                , HP.attr (HH.AttrName "style") "flex: 1;"
                , HE.onValueInput SetOutputPath
                ]
            , HH.button
                [ cls [ "lattice-btn", "lattice-btn-ghost" ]
                ]
                [ HH.text "Browse" ]
            ]
        ]
    
      -- Export button
    , HH.div [ HP.attr (HH.AttrName "style") exportButtonContainerStyle ]
        [ HH.button
            [ cls [ "lattice-btn", "lattice-btn-primary" ]
            , HP.attr (HH.AttrName "style") exportButtonStyle
            , HE.onClick \_ -> StartExport
            ]
            [ HH.text "Add to Render Queue" ]
        ]
    ]

renderFormatOption :: forall m. State -> ExportFormat -> String -> String -> H.ComponentHTML Action () m
renderFormatOption state format label description =
  let isSelected = state.selectedFormat == format
  in HH.button
    [ cls [ "lattice-format-option" ]
    , HP.attr (HH.AttrName "style") (formatOptionStyle isSelected)
    , HP.attr (HH.AttrName "data-selected") (if isSelected then "true" else "false")
    , HE.onClick \_ -> SetFormat format
    ]
    [ HH.div [ cls [ "lattice-format-radio" ], HP.attr (HH.AttrName "style") (radioStyle isSelected) ] []
    , HH.div [ cls [ "lattice-format-info" ] ]
        [ HH.span 
            [ HP.attr (HH.AttrName "style") formatLabelStyle ]
            [ HH.text label ]
        , HH.span 
            [ HP.attr (HH.AttrName "style") formatDescStyle ]
            [ HH.text description ]
        ]
    ]

renderRenderQueue :: forall m. State -> H.ComponentHTML Action () m
renderRenderQueue state =
  HH.section
    [ cls [ "lattice-render-queue" ]
    , HP.attr (HH.AttrName "style") queueStyle
    ]
    [ HH.div [ cls [ "lattice-queue-header" ], HP.attr (HH.AttrName "style") queueHeaderStyle ]
        [ HH.h2 
            [ HP.attr (HH.AttrName "style") sectionTitleStyle ]
            [ HH.text "Render Queue" ]
        , if length state.jobs > 0
            then HH.button
                [ cls [ "lattice-btn", "lattice-btn-ghost" ]
                , HP.attr (HH.AttrName "style") "font-size: var(--lattice-text-sm);"
                , HE.onClick \_ -> ClearCompleted
                ]
                [ HH.text "Clear Completed" ]
            else HH.text ""
        ]
    
    , if length state.jobs == 0
        then renderEmptyQueue
        else HH.div [ cls [ "lattice-job-list" ] ]
            (map (renderJobItem state) state.jobs)
    ]

renderEmptyQueue :: forall m. H.ComponentHTML Action () m
renderEmptyQueue =
  HH.div 
    [ cls [ "lattice-empty-queue" ]
    , HP.attr (HH.AttrName "style") emptyQueueStyle
    ]
    [ HH.div 
        [ cls [ "lattice-empty-icon" ]
        , HP.attr (HH.AttrName "style") emptyIconStyle
        ]
        [ HH.text "🎬" ]
    , HH.h3 
        [ HP.attr (HH.AttrName "style") emptyTitleStyle ]
        [ HH.text "No renders in queue" ]
    , HH.p 
        [ HP.attr (HH.AttrName "style") emptyTextStyle ]
        [ HH.text "Configure export settings and add compositions to the render queue" ]
    ]

renderJobItem :: forall m. State -> RenderJob -> H.ComponentHTML Action () m
renderJobItem _ job =
  HH.div 
    [ cls [ "lattice-job-item" ]
    , HP.attr (HH.AttrName "style") jobItemStyle
    , HP.attr (HH.AttrName "data-status") (statusToString job.status)
    ]
    [ HH.div [ cls [ "lattice-job-info" ] ]
        [ HH.div [ cls [ "lattice-job-name-row" ] ]
            [ HH.span 
                [ HP.attr (HH.AttrName "style") jobNameStyle ]
                [ HH.text job.compositionName ]
            , HH.span 
                [ cls [ "lattice-job-status" ]
                , HP.attr (HH.AttrName "style") (statusStyle job.status)
                ]
                [ HH.text (statusLabel job.status) ]
            ]
        , HH.span 
            [ HP.attr (HH.AttrName "style") jobFormatStyle ]
            [ HH.text $ formatLabel job.format <> " • " <> job.outputPath ]
        ]
    
    , case job.status of
        Rendering -> 
          HH.div [ cls [ "lattice-job-progress" ] ]
            [ HH.div 
                [ cls [ "lattice-progress-bar" ]
                , HP.attr (HH.AttrName "style") progressBarStyle
                ]
                [ HH.div 
                    [ cls [ "lattice-progress-fill" ]
                    , HP.attr (HH.AttrName "style") (progressFillStyle job.progress)
                    ]
                    []
                ]
            , HH.span 
                [ HP.attr (HH.AttrName "style") progressTextStyle ]
                [ HH.text $ show (floor (job.progress * 100.0)) <> "%" ]
            ]
        _ -> 
          HH.button
            [ cls [ "lattice-btn", "lattice-btn-ghost" ]
            , HP.attr (HH.AttrName "style") "font-size: var(--lattice-text-xs);"
            , HE.onClick \_ -> CancelJob job.id
            ]
            [ HH.text (if job.status == Queued then "Cancel" else "Remove") ]
    ]

-- ============================================================
-- HELPERS
-- ============================================================

floor :: Number -> Int
floor n = n # (\x -> x - (x `mod` 1.0)) # round
  where
  round :: Number -> Int
  round x = if x >= 0.0 then truncate x else truncate x - 1

truncate :: Number -> Int
truncate _ = 0  -- Simplified

statusToString :: JobStatus -> String
statusToString = case _ of
  Queued -> "queued"
  Rendering -> "rendering"
  Completed -> "completed"
  Failed -> "failed"

statusLabel :: JobStatus -> String
statusLabel = case _ of
  Queued -> "Queued"
  Rendering -> "Rendering"
  Completed -> "Completed"
  Failed -> "Failed"

formatLabel :: ExportFormat -> String
formatLabel = case _ of
  MP4 -> "MP4"
  ProRes -> "ProRes"
  PNG_Sequence -> "PNG Sequence"
  EXR_Sequence -> "EXR Sequence"

-- ============================================================
-- ACTIONS
-- ============================================================

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  SetFormat format ->
    H.modify_ _ { selectedFormat = format }
  
  SetOutputPath path ->
    H.modify_ _ { outputPath = path }
  
  StartExport -> 
    pure unit  -- Would add job to queue
  
  CancelJob _ ->
    pure unit  -- Would cancel/remove job
  
  ClearCompleted ->
    pure unit  -- Would remove completed jobs

-- ============================================================
-- STYLES
-- ============================================================

pageStyle :: String
pageStyle =
  "min-height: 100vh; background: var(--lattice-void); padding: var(--lattice-space-8);"

containerStyle :: String
containerStyle =
  "max-width: 1200px; margin: 0 auto;"

headerStyle :: String
headerStyle =
  "margin-bottom: var(--lattice-space-6);"

titleStyle :: String
titleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-3xl); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0;"

contentStyle :: String
contentStyle =
  "display: grid; grid-template-columns: 1fr 1fr; gap: var(--lattice-space-6);"

settingsStyle :: String
settingsStyle =
  "background: var(--lattice-surface-1); border-radius: var(--lattice-radius-xl); " <>
  "padding: var(--lattice-space-6); border: 1px solid var(--lattice-border-subtle);"

sectionTitleStyle :: String
sectionTitleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-lg); " <>
  "font-weight: var(--lattice-font-semibold); margin: 0 0 var(--lattice-space-4);"

settingGroupStyle :: String
settingGroupStyle =
  "margin-bottom: var(--lattice-space-5);"

labelStyle :: String
labelStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-sm); " <>
  "font-weight: var(--lattice-font-medium); display: block; margin-bottom: var(--lattice-space-2);"

formatOptionsStyle :: String
formatOptionsStyle =
  "display: flex; flex-direction: column; gap: var(--lattice-space-2);"

formatOptionStyle :: Boolean -> String
formatOptionStyle isSelected =
  "display: flex; align-items: center; gap: var(--lattice-space-3); " <>
  "padding: var(--lattice-space-3); border-radius: var(--lattice-radius-md); " <>
  "background: " <> (if isSelected then "var(--lattice-accent-muted)" else "var(--lattice-surface-0)") <> "; " <>
  "border: 1px solid " <> (if isSelected then "var(--lattice-accent)" else "var(--lattice-border-default)") <> "; " <>
  "cursor: pointer; text-align: left; transition: all var(--lattice-transition-fast);"

radioStyle :: Boolean -> String
radioStyle isSelected =
  "width: 16px; height: 16px; border-radius: 50%; " <>
  "border: 2px solid " <> (if isSelected then "var(--lattice-accent)" else "var(--lattice-border-default)") <> "; " <>
  "background: " <> (if isSelected then "var(--lattice-accent)" else "transparent") <> "; " <>
  "position: relative;" <>
  if isSelected then " box-shadow: inset 0 0 0 3px var(--lattice-surface-1);" else ""

formatLabelStyle :: String
formatLabelStyle =
  "color: var(--lattice-text-primary); font-weight: var(--lattice-font-medium); display: block;"

formatDescStyle :: String
formatDescStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-xs); display: block;"

pathInputStyle :: String
pathInputStyle =
  "display: flex; gap: var(--lattice-space-2);"

exportButtonContainerStyle :: String
exportButtonContainerStyle =
  "margin-top: var(--lattice-space-6); padding-top: var(--lattice-space-4); " <>
  "border-top: 1px solid var(--lattice-border-subtle);"

exportButtonStyle :: String
exportButtonStyle =
  "width: 100%;"

queueStyle :: String
queueStyle =
  "background: var(--lattice-surface-1); border-radius: var(--lattice-radius-xl); " <>
  "padding: var(--lattice-space-6); border: 1px solid var(--lattice-border-subtle);"

queueHeaderStyle :: String
queueHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; margin-bottom: var(--lattice-space-4);"

emptyQueueStyle :: String
emptyQueueStyle =
  "text-align: center; padding: var(--lattice-space-8);"

emptyIconStyle :: String
emptyIconStyle =
  "font-size: 48px; margin-bottom: var(--lattice-space-3); opacity: 0.5;"

emptyTitleStyle :: String
emptyTitleStyle =
  "color: var(--lattice-text-primary); font-size: var(--lattice-text-base); margin: 0 0 var(--lattice-space-1);"

emptyTextStyle :: String
emptyTextStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-sm); margin: 0;"

jobItemStyle :: String
jobItemStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: var(--lattice-space-3); border-radius: var(--lattice-radius-md); " <>
  "background: var(--lattice-surface-0); margin-bottom: var(--lattice-space-2);"

jobNameStyle :: String
jobNameStyle =
  "color: var(--lattice-text-primary); font-weight: var(--lattice-font-medium);"

statusStyle :: JobStatus -> String
statusStyle status =
  let color = case status of
        Queued -> "var(--lattice-text-muted)"
        Rendering -> "var(--lattice-accent)"
        Completed -> "var(--lattice-success)"
        Failed -> "var(--lattice-error)"
  in "color: " <> color <> "; font-size: var(--lattice-text-xs); " <>
     "text-transform: uppercase; letter-spacing: 0.5px; margin-left: var(--lattice-space-2);"

jobFormatStyle :: String
jobFormatStyle =
  "color: var(--lattice-text-muted); font-size: var(--lattice-text-xs); display: block;"

progressBarStyle :: String
progressBarStyle =
  "height: 4px; background: var(--lattice-surface-3); border-radius: var(--lattice-radius-full); " <>
  "overflow: hidden; flex: 1; margin-right: var(--lattice-space-2);"

progressFillStyle :: Number -> String
progressFillStyle progress =
  "height: 100%; background: var(--lattice-accent); border-radius: var(--lattice-radius-full); " <>
  "width: " <> show (progress * 100.0) <> "%;"

progressTextStyle :: String
progressTextStyle =
  "color: var(--lattice-text-secondary); font-size: var(--lattice-text-xs); " <>
  "font-family: var(--lattice-font-mono); min-width: 40px; text-align: right;"
