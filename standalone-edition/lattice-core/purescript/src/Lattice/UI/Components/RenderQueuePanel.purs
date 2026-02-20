-- | Render Queue Panel Component
-- |
-- | Render queue management for batch rendering compositions.
-- | Supports:
-- | - Job queue with priority ordering
-- | - Start/pause/stop queue controls
-- | - Per-job progress tracking
-- | - Download completed renders
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/RenderQueuePanel.vue
module Lattice.UI.Components.RenderQueuePanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , RenderJob
  , JobStatus(..)
  , RenderFormat(..)
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

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { jobs :: Array RenderJob
  , isRunning :: Boolean
  , isPaused :: Boolean
  , activeCompositionId :: Maybe String
  , activeCompositionName :: String
  , defaultWidth :: Int
  , defaultHeight :: Int
  , defaultFps :: Int
  , defaultFrameCount :: Int
  }

data Output
  = StartQueue
  | PauseQueue
  | StopQueue
  | AddJob NewJobConfig
  | PauseJob String
  | ResumeJob String
  | RemoveJob String
  | DownloadJob String

data Query a
  = RefreshJobs a
  | UpdateJobProgress String JobProgress a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                             // render // types
-- =============================================================================

data JobStatus
  = StatusPending
  | StatusRendering
  | StatusPaused
  | StatusCompleted
  | StatusFailed
  | StatusCancelled

derive instance eqJobStatus :: Eq JobStatus

instance showJobStatus :: Show JobStatus where
  show = case _ of
    StatusPending -> "pending"
    StatusRendering -> "rendering"
    StatusPaused -> "paused"
    StatusCompleted -> "completed"
    StatusFailed -> "failed"
    StatusCancelled -> "cancelled"

statusLabel :: JobStatus -> String
statusLabel = case _ of
  StatusPending -> "pending"
  StatusRendering -> "rendering"
  StatusPaused -> "paused"
  StatusCompleted -> "completed"
  StatusFailed -> "failed"
  StatusCancelled -> "cancelled"

data RenderFormat
  = FormatPNGSequence
  | FormatWebM
  | FormatMP4

derive instance eqRenderFormat :: Eq RenderFormat

instance showRenderFormat :: Show RenderFormat where
  show = case _ of
    FormatPNGSequence -> "png-sequence"
    FormatWebM -> "webm"
    FormatMP4 -> "mp4"

formatLabel :: RenderFormat -> String
formatLabel = case _ of
  FormatPNGSequence -> "PNG Sequence"
  FormatWebM -> "WebM Video"
  FormatMP4 -> "MP4 Video"

type RenderJob =
  { id :: String
  , name :: String
  , compositionId :: String
  , width :: Int
  , height :: Int
  , fps :: Int
  , startFrame :: Int
  , endFrame :: Int
  , format :: RenderFormat
  , quality :: Int
  , progress :: JobProgress
  }

type JobProgress =
  { status :: JobStatus
  , percentage :: Number
  , totalFrames :: Int
  , renderedFrames :: Int
  , estimatedTimeRemaining :: Number
  }

type NewJobConfig =
  { name :: String
  , compositionId :: String
  , startFrame :: Int
  , endFrame :: Int
  , width :: Int
  , height :: Int
  , fps :: Int
  , format :: RenderFormat
  , quality :: Int
  }

type QueueStats =
  { totalJobs :: Int
  , activeJobs :: Int
  , pendingJobs :: Int
  , completedJobs :: Int
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { input :: Input
  , baseId :: String
  , showAddJobDialog :: Boolean
  , newJobName :: String
  , newJobStartFrame :: Int
  , newJobEndFrame :: Int
  , newJobWidth :: Int
  , newJobHeight :: Int
  , newJobFormat :: RenderFormat
  , newJobQuality :: Int
  }

data Action
  = Initialize
  | Receive Input
  | StartQueueAction
  | PauseQueueAction
  | StopQueueAction
  | ShowAddJobDialog
  | HideAddJobDialog
  | SetNewJobName String
  | SetNewJobStartFrame String
  | SetNewJobEndFrame String
  | SetNewJobWidth String
  | SetNewJobHeight String
  | SetNewJobFormat String
  | SetNewJobQuality String
  | SubmitAddJob
  | PauseJobAction String
  | ResumeJobAction String
  | RemoveJobAction String
  | DownloadJobAction String

type Slots = ()

-- =============================================================================
--                                                                  // component
-- =============================================================================

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
  , baseId: "render-queue-panel"
  , showAddJobDialog: false
  , newJobName: "Render Job"
  , newJobStartFrame: 0
  , newJobEndFrame: input.defaultFrameCount - 1
  , newJobWidth: input.defaultWidth
  , newJobHeight: input.defaultHeight
  , newJobFormat: FormatPNGSequence
  , newJobQuality: 95
  }

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "render-queue-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Render Queue"
    ]
    [ renderHeader state
    , renderStatsBar state
    , renderAddJobButton
    , renderJobList state
    , if state.showAddJobDialog
        then renderAddJobDialog state
        else HH.text ""
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.h3 [ HP.attr (HH.AttrName "style") titleStyle ] [ HH.text "Render Queue" ]
    , HH.div
        [ cls [ "header-actions" ]
        , HP.attr (HH.AttrName "style") headerActionsStyle
        ]
        [ HH.button
            [ cls [ "icon-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Start Queue"
            , HP.attr (HH.AttrName "style") (iconBtnStyle (state.input.isRunning && not state.input.isPaused))
            , HP.attr (HH.AttrName "data-state") (if state.input.isRunning && not state.input.isPaused then "active" else "inactive")
            , HE.onClick \_ -> StartQueueAction
            ]
            [ HH.text "\x{25B6}" ]
        , HH.button
            [ cls [ "icon-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Pause Queue"
            , HP.attr (HH.AttrName "style") (iconBtnStyle state.input.isPaused)
            , HP.attr (HH.AttrName "data-state") (if state.input.isPaused then "active" else "inactive")
            , HE.onClick \_ -> PauseQueueAction
            ]
            [ HH.text "\x{23F8}" ]
        , HH.button
            [ cls [ "icon-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Stop Queue"
            , HP.attr (HH.AttrName "style") (iconBtnStyle false)
            , HE.onClick \_ -> StopQueueAction
            ]
            [ HH.text "\x{23F9}" ]
        ]
    ]

renderStatsBar :: forall m. State -> H.ComponentHTML Action Slots m
renderStatsBar state =
  let
    stats = computeStats state.input.jobs
  in
  HH.div
    [ cls [ "stats-bar" ]
    , HP.attr (HH.AttrName "style") statsBarStyle
    ]
    [ renderStat "pending" stats.pendingJobs
    , renderStat "rendering" stats.activeJobs
    , renderStat "done" stats.completedJobs
    ]

renderStat :: forall m. String -> Int -> H.ComponentHTML Action Slots m
renderStat label value =
  HH.span
    [ cls [ "stat" ]
    , HP.attr (HH.AttrName "style") statStyle
    ]
    [ HH.span [ cls [ "stat-value" ], HP.attr (HH.AttrName "style") statValueStyle ] [ HH.text (show value) ]
    , HH.text (" " <> label)
    ]

computeStats :: Array RenderJob -> QueueStats
computeStats jobs =
  { totalJobs: Array.length jobs
  , activeJobs: Array.length (Array.filter (\j -> j.progress.status == StatusRendering) jobs)
  , pendingJobs: Array.length (Array.filter (\j -> j.progress.status == StatusPending) jobs)
  , completedJobs: Array.length (Array.filter (\j -> j.progress.status == StatusCompleted) jobs)
  }

renderAddJobButton :: forall m. H.ComponentHTML Action Slots m
renderAddJobButton =
  HH.div
    [ cls [ "add-job-section" ]
    , HP.attr (HH.AttrName "style") addJobSectionStyle
    ]
    [ HH.button
        [ cls [ "add-job-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") addJobBtnStyle
        , HE.onClick \_ -> ShowAddJobDialog
        ]
        [ HH.text "+ Add Current Composition" ]
    ]

renderJobList :: forall m. State -> H.ComponentHTML Action Slots m
renderJobList state =
  HH.div
    [ cls [ "job-list" ]
    , HP.attr (HH.AttrName "style") jobListStyle
    ]
    (if Array.null state.input.jobs
      then [ renderEmptyState ]
      else map renderJobItem state.input.jobs)

renderJobItem :: forall m. RenderJob -> H.ComponentHTML Action Slots m
renderJobItem job =
  let
    isActive = job.progress.status == StatusRendering
  in
  HH.div
    [ cls [ "job-item" ]
    , HP.attr (HH.AttrName "style") (jobItemStyle isActive)
    , HP.attr (HH.AttrName "data-state") (if isActive then "active" else "inactive")
    ]
    [ HH.div
        [ cls [ "job-header" ]
        , HP.attr (HH.AttrName "style") jobHeaderStyle
        ]
        [ HH.span [ cls [ "job-name" ], HP.attr (HH.AttrName "style") jobNameStyle ] [ HH.text job.name ]
        , HH.span 
            [ cls [ "job-status" ]
            , HP.attr (HH.AttrName "style") (jobStatusStyle job.progress.status)
            ] 
            [ HH.text (statusLabel job.progress.status) ]
        ]
    , HH.div
        [ cls [ "job-details" ]
        , HP.attr (HH.AttrName "style") jobDetailsStyle
        ]
        [ HH.span_ [ HH.text (show job.width <> "x" <> show job.height <> " @ " <> show job.fps <> "fps") ]
        , HH.span_ [ HH.text (show job.progress.totalFrames <> " frames") ]
        ]
    , renderJobProgress job
    , renderJobActions job
    ]

renderJobProgress :: forall m. RenderJob -> H.ComponentHTML Action Slots m
renderJobProgress job =
  HH.div
    [ cls [ "progress-container" ]
    , HP.attr (HH.AttrName "style") progressContainerStyle
    , HP.attr (HH.AttrName "role") "progressbar"
    , ARIA.valueNow (formatNumber job.progress.percentage)
    , ARIA.valueMin "0"
    , ARIA.valueMax "100"
    ]
    [ HH.div
        [ cls [ "progress-bar" ]
        , HP.attr (HH.AttrName "style") (progressBarFillStyle job.progress.percentage job.progress.status)
        ]
        []
    , HH.span
        [ cls [ "progress-text" ]
        , HP.attr (HH.AttrName "style") progressTextStyle
        ]
        [ HH.text (formatNumber job.progress.percentage <> "%")
        , if job.progress.status == StatusRendering
            then HH.text (" (" <> formatTime job.progress.estimatedTimeRemaining <> " remaining)")
            else HH.text ""
        ]
    ]

renderJobActions :: forall m. RenderJob -> H.ComponentHTML Action Slots m
renderJobActions job =
  HH.div
    [ cls [ "job-actions" ]
    , HP.attr (HH.AttrName "style") jobActionsStyle
    ]
    [ case job.progress.status of
        StatusRendering ->
          HH.button
            [ cls [ "job-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Pause"
            , HP.attr (HH.AttrName "style") jobBtnStyle
            , HE.onClick \_ -> PauseJobAction job.id
            ]
            [ HH.text "\x{23F8}" ]
        StatusPaused ->
          HH.button
            [ cls [ "job-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.title "Resume"
            , HP.attr (HH.AttrName "style") jobBtnStyle
            , HE.onClick \_ -> ResumeJobAction job.id
            ]
            [ HH.text "\x{25B6}" ]
        _ -> HH.text ""
    , if job.progress.status == StatusCompleted
        then HH.button
              [ cls [ "job-btn", "primary" ]
              , HP.type_ HP.ButtonButton
              , HP.title "Download"
              , HP.attr (HH.AttrName "style") jobBtnPrimaryStyle
              , HE.onClick \_ -> DownloadJobAction job.id
              ]
              [ HH.text "\x{2B07}" ]
        else HH.text ""
    , HH.button
        [ cls [ "job-btn", "danger" ]
        , HP.type_ HP.ButtonButton
        , HP.title "Remove"
        , HP.attr (HH.AttrName "style") jobBtnDangerStyle
        , HE.onClick \_ -> RemoveJobAction job.id
        ]
        [ HH.text "\x{1F5D1}" ]
    ]

renderEmptyState :: forall m. H.ComponentHTML Action Slots m
renderEmptyState =
  HH.div
    [ cls [ "empty-state" ]
    , HP.attr (HH.AttrName "style") emptyStateStyle
    ]
    [ HH.span [ HP.attr (HH.AttrName "style") emptyIconStyle ] [ HH.text "\x{1F3AC}" ]
    , HH.p_ [ HH.text "No render jobs in queue" ]
    , HH.p [ cls [ "hint" ], HP.attr (HH.AttrName "style") hintStyle ] 
        [ HH.text "Click \"Add Current Composition\" to start rendering" ]
    ]

-- =============================================================================
--                                                          // add job dialog
-- =============================================================================

renderAddJobDialog :: forall m. State -> H.ComponentHTML Action Slots m
renderAddJobDialog state =
  HH.div
    [ cls [ "dialog-overlay" ]
    , HP.attr (HH.AttrName "style") dialogOverlayStyle
    , HP.attr (HH.AttrName "role") "dialog"
    , ARIA.modal "true"
    , ARIA.labelledBy (state.baseId <> "-dialog-title")
    , HE.onClick \_ -> HideAddJobDialog
    ]
    [ HH.div
        [ cls [ "dialog" ]
        , HP.attr (HH.AttrName "style") dialogStyle
        , HE.onClick \e -> Initialize -- Prevent propagation by doing nothing meaningful
        ]
        [ HH.div
            [ cls [ "dialog-header" ]
            , HP.attr (HH.AttrName "style") dialogHeaderStyle
            ]
            [ HH.h4 
                [ HP.id (state.baseId <> "-dialog-title")
                , HP.attr (HH.AttrName "style") dialogTitleStyle
                ] 
                [ HH.text "Add Render Job" ]
            , HH.button
                [ cls [ "close-btn" ]
                , HP.type_ HP.ButtonButton
                , HP.attr (HH.AttrName "style") closeBtnStyle
                , HE.onClick \_ -> HideAddJobDialog
                ]
                [ HH.text "\x{2715}" ]
            ]
        , HH.div
            [ cls [ "dialog-content" ]
            , HP.attr (HH.AttrName "style") dialogContentStyle
            ]
            [ renderFormRow "Name" (renderTextInput state.newJobName SetNewJobName)
            , renderFormRow "Frame Range" (renderRangeInputs state)
            , renderFormRow "Output Size" (renderSizeInputs state)
            , renderFormRow "Format" (renderFormatSelect state)
            , renderFormRow "Quality" (renderQualitySlider state)
            ]
        , HH.div
            [ cls [ "dialog-footer" ]
            , HP.attr (HH.AttrName "style") dialogFooterStyle
            ]
            [ HH.button
                [ cls [ "btn", "secondary" ]
                , HP.type_ HP.ButtonButton
                , HP.attr (HH.AttrName "style") btnSecondaryStyle
                , HE.onClick \_ -> HideAddJobDialog
                ]
                [ HH.text "Cancel" ]
            , HH.button
                [ cls [ "btn", "primary" ]
                , HP.type_ HP.ButtonButton
                , HP.attr (HH.AttrName "style") btnPrimaryStyle
                , HE.onClick \_ -> SubmitAddJob
                ]
                [ HH.text "Add to Queue" ]
            ]
        ]
    ]

renderFormRow :: forall m. String -> H.ComponentHTML Action Slots m -> H.ComponentHTML Action Slots m
renderFormRow label control =
  HH.div
    [ cls [ "form-row" ]
    , HP.attr (HH.AttrName "style") formRowStyle
    ]
    [ HH.label [ HP.attr (HH.AttrName "style") formLabelStyle ] [ HH.text label ]
    , control
    ]

renderTextInput :: forall m. String -> (String -> Action) -> H.ComponentHTML Action Slots m
renderTextInput value action =
  HH.input
    [ HP.type_ HP.InputText
    , HP.value value
    , HP.placeholder "Render Job"
    , HP.attr (HH.AttrName "style") formInputStyle
    , HE.onValueInput action
    ]

renderRangeInputs :: forall m. State -> H.ComponentHTML Action Slots m
renderRangeInputs state =
  HH.div
    [ cls [ "range-inputs" ]
    , HP.attr (HH.AttrName "style") rangeInputsStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (show state.newJobStartFrame)
        , HP.attr (HH.AttrName "min") "0"
        , HP.attr (HH.AttrName "style") smallInputStyle
        , HE.onValueInput SetNewJobStartFrame
        ]
    , HH.span_ [ HH.text "to" ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (show state.newJobEndFrame)
        , HP.attr (HH.AttrName "min") "0"
        , HP.attr (HH.AttrName "style") smallInputStyle
        , HE.onValueInput SetNewJobEndFrame
        ]
    ]

renderSizeInputs :: forall m. State -> H.ComponentHTML Action Slots m
renderSizeInputs state =
  HH.div
    [ cls [ "size-inputs" ]
    , HP.attr (HH.AttrName "style") rangeInputsStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (show state.newJobWidth)
        , HP.attr (HH.AttrName "min") "8"
        , HP.attr (HH.AttrName "step") "8"
        , HP.attr (HH.AttrName "style") smallInputStyle
        , HE.onValueInput SetNewJobWidth
        ]
    , HH.span_ [ HH.text "x" ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (show state.newJobHeight)
        , HP.attr (HH.AttrName "min") "8"
        , HP.attr (HH.AttrName "step") "8"
        , HP.attr (HH.AttrName "style") smallInputStyle
        , HE.onValueInput SetNewJobHeight
        ]
    ]

renderFormatSelect :: forall m. State -> H.ComponentHTML Action Slots m
renderFormatSelect state =
  HH.select
    [ HP.attr (HH.AttrName "style") formSelectStyle
    , HE.onValueChange SetNewJobFormat
    ]
    [ HH.option [ HP.value "png-sequence", HP.selected (state.newJobFormat == FormatPNGSequence) ] 
        [ HH.text "PNG Sequence" ]
    , HH.option [ HP.value "webm", HP.selected (state.newJobFormat == FormatWebM) ] 
        [ HH.text "WebM Video" ]
    , HH.option [ HP.value "mp4", HP.selected (state.newJobFormat == FormatMP4) ] 
        [ HH.text "MP4 Video" ]
    ]

renderQualitySlider :: forall m. State -> H.ComponentHTML Action Slots m
renderQualitySlider state =
  HH.div
    [ cls [ "quality-row" ]
    , HP.attr (HH.AttrName "style") qualityRowStyle
    ]
    [ HH.input
        [ HP.type_ HP.InputRange
        , HP.value (show state.newJobQuality)
        , HP.attr (HH.AttrName "min") "50"
        , HP.attr (HH.AttrName "max") "100"
        , HP.attr (HH.AttrName "style") qualitySliderStyle
        , HE.onValueInput SetNewJobQuality
        ]
    , HH.span [ cls [ "value-display" ], HP.attr (HH.AttrName "style") valueDisplayStyle ] 
        [ HH.text (show state.newJobQuality <> "%") ]
    ]

-- =============================================================================
--                                                                    // helpers
-- =============================================================================

formatNumber :: Number -> String
formatNumber = Utils.formatFixed 1

formatTime :: Number -> String
formatTime seconds =
  if seconds <= 0.0 then "--:--"
  else
    let
      mins = floor (seconds / 60.0)
      secs = floor (seconds - (toNumber mins * 60.0))
    in
      show mins <> ":" <> padZeros (show secs) 2

floor :: Number -> Int
floor = Utils.floor

toNumber :: Int -> Number
toNumber = Utils.toNumber

padZeros :: String -> Int -> String
padZeros s len = Utils.padStart len '0' s

parseIntSafe :: String -> Int -> Int
parseIntSafe str defaultVal = Utils.parseIntOr defaultVal str

-- =============================================================================
--                                                                     // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1, #121212);"

headerStyle :: String
headerStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 12px; border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 14px; font-weight: 600; " <>
  "color: var(--lattice-text-primary, #e0e0e0);"

headerActionsStyle :: String
headerActionsStyle =
  "display: flex; gap: 4px;"

iconBtnStyle :: Boolean -> String
iconBtnStyle isActive =
  let
    baseStyle = "width: 28px; height: 28px; display: flex; align-items: center; " <>
                "justify-content: center; background: var(--lattice-surface-2, #1a1a1a); " <>
                "border: 1px solid var(--lattice-border-default, #333); " <>
                "border-radius: 4px; color: var(--lattice-text-secondary, #a0a0a0); " <>
                "cursor: pointer; transition: all 0.15s;"
    activeStyle = if isActive
      then "background: var(--lattice-accent, #8B5CF6); " <>
           "border-color: var(--lattice-accent, #8B5CF6); color: white;"
      else ""
  in
    baseStyle <> activeStyle

statsBarStyle :: String
statsBarStyle =
  "display: flex; gap: 16px; padding: 8px 12px; " <>
  "background: var(--lattice-surface-0, #0a0a0a); font-size: 11px;"

statStyle :: String
statStyle =
  "color: var(--lattice-text-muted, #666);"

statValueStyle :: String
statValueStyle =
  "color: var(--lattice-text-primary, #e0e0e0); font-weight: 600;"

addJobSectionStyle :: String
addJobSectionStyle =
  "padding: 12px;"

addJobBtnStyle :: String
addJobBtnStyle =
  "width: 100%; padding: 10px; display: flex; align-items: center; " <>
  "justify-content: center; gap: 8px; " <>
  "background: var(--lattice-accent, #8B5CF6); border: none; " <>
  "border-radius: 6px; color: white; font-size: 13px; " <>
  "font-weight: 500; cursor: pointer;"

jobListStyle :: String
jobListStyle =
  "flex: 1; overflow-y: auto; padding: 0 12px 12px;"

jobItemStyle :: Boolean -> String
jobItemStyle isActive =
  let
    baseStyle = "background: var(--lattice-surface-2, #1a1a1a); " <>
                "border: 1px solid var(--lattice-border-subtle, #222); " <>
                "border-radius: 8px; padding: 12px; margin-bottom: 8px;"
    activeStyle = if isActive
      then "border-color: var(--lattice-accent, #8B5CF6);"
      else ""
  in
    baseStyle <> activeStyle

jobHeaderStyle :: String
jobHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; margin-bottom: 8px;"

jobNameStyle :: String
jobNameStyle =
  "font-weight: 500; color: var(--lattice-text-primary, #e0e0e0);"

jobStatusStyle :: JobStatus -> String
jobStatusStyle status =
  let
    baseStyle = "font-size: 11px; padding: 2px 8px; border-radius: 10px; text-transform: uppercase;"
    colorStyle = case status of
      StatusPending -> "background: var(--lattice-surface-3, #222); color: var(--lattice-text-muted, #666);"
      StatusRendering -> "background: var(--lattice-accent, #8B5CF6); color: white;"
      StatusPaused -> "background: #F59E0B; color: white;"
      StatusCompleted -> "background: #10B981; color: white;"
      StatusFailed -> "background: #EF4444; color: white;"
      StatusCancelled -> "background: var(--lattice-surface-3, #222); color: var(--lattice-text-muted, #666);"
  in
    baseStyle <> colorStyle

jobDetailsStyle :: String
jobDetailsStyle =
  "display: flex; gap: 16px; font-size: 11px; " <>
  "color: var(--lattice-text-muted, #666); margin-bottom: 8px;"

progressContainerStyle :: String
progressContainerStyle =
  "position: relative; height: 20px; " <>
  "background: var(--lattice-surface-0, #0a0a0a); " <>
  "border-radius: 4px; overflow: hidden; margin-bottom: 8px;"

progressBarFillStyle :: Number -> JobStatus -> String
progressBarFillStyle percentage status =
  let
    colorStyle = case status of
      StatusCompleted -> "background: #10B981;"
      StatusFailed -> "background: #EF4444;"
      StatusPaused -> "background: #F59E0B;"
      _ -> "background: var(--lattice-accent, #8B5CF6);"
  in
    "height: 100%; transition: width 0.3s; width: " <> formatNumber percentage <> "%; " <> colorStyle

progressTextStyle :: String
progressTextStyle =
  "position: absolute; top: 50%; left: 50%; transform: translate(-50%, -50%); " <>
  "font-size: 11px; color: white; text-shadow: 0 1px 2px rgba(0, 0, 0, 0.5);"

jobActionsStyle :: String
jobActionsStyle =
  "display: flex; gap: 8px;"

jobBtnStyle :: String
jobBtnStyle =
  "padding: 6px 12px; background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 4px; color: var(--lattice-text-secondary, #a0a0a0); " <>
  "font-size: 12px; cursor: pointer;"

jobBtnPrimaryStyle :: String
jobBtnPrimaryStyle =
  "padding: 6px 12px; background: var(--lattice-accent, #8B5CF6); " <>
  "border: 1px solid var(--lattice-accent, #8B5CF6); " <>
  "border-radius: 4px; color: white; font-size: 12px; cursor: pointer;"

jobBtnDangerStyle :: String
jobBtnDangerStyle =
  "padding: 6px 12px; background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 4px; color: var(--lattice-text-secondary, #a0a0a0); " <>
  "font-size: 12px; cursor: pointer;"

emptyStateStyle :: String
emptyStateStyle =
  "text-align: center; padding: 40px 20px; color: var(--lattice-text-muted, #666);"

emptyIconStyle :: String
emptyIconStyle =
  "font-size: 48px; margin-bottom: 16px; opacity: 0.3; display: block;"

hintStyle :: String
hintStyle =
  "font-size: 12px; opacity: 0.7; margin: 0;"

dialogOverlayStyle :: String
dialogOverlayStyle =
  "position: fixed; top: 0; left: 0; right: 0; bottom: 0; " <>
  "background: rgba(0, 0, 0, 0.7); display: flex; " <>
  "align-items: center; justify-content: center; z-index: 1000;"

dialogStyle :: String
dialogStyle =
  "width: 400px; background: var(--lattice-surface-1, #121212); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 12px; overflow: hidden;"

dialogHeaderStyle :: String
dialogHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 16px; border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a);"

dialogTitleStyle :: String
dialogTitleStyle =
  "margin: 0; font-size: 16px; color: var(--lattice-text-primary, #e0e0e0);"

closeBtnStyle :: String
closeBtnStyle =
  "background: none; border: none; color: var(--lattice-text-muted, #666); " <>
  "cursor: pointer; padding: 4px; font-size: 16px;"

dialogContentStyle :: String
dialogContentStyle =
  "padding: 16px;"

formRowStyle :: String
formRowStyle =
  "margin-bottom: 16px;"

formLabelStyle :: String
formLabelStyle =
  "display: block; margin-bottom: 8px; font-size: 12px; " <>
  "color: var(--lattice-text-secondary, #a0a0a0);"

formInputStyle :: String
formInputStyle =
  "width: 100%; padding: 8px 12px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 6px; color: var(--lattice-text-primary, #e0e0e0); font-size: 13px;"

formSelectStyle :: String
formSelectStyle =
  "width: 100%; padding: 8px 12px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 6px; color: var(--lattice-text-primary, #e0e0e0); font-size: 13px;"

rangeInputsStyle :: String
rangeInputsStyle =
  "display: flex; align-items: center; gap: 8px;"

smallInputStyle :: String
smallInputStyle =
  "width: 80px; padding: 8px 12px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "border-radius: 6px; color: var(--lattice-text-primary, #e0e0e0); font-size: 13px;"

qualityRowStyle :: String
qualityRowStyle =
  "display: flex; align-items: center; gap: 8px;"

qualitySliderStyle :: String
qualitySliderStyle =
  "flex: 1;"

valueDisplayStyle :: String
valueDisplayStyle =
  "min-width: 40px; text-align: right; font-size: 12px; " <>
  "color: var(--lattice-text-secondary, #a0a0a0);"

dialogFooterStyle :: String
dialogFooterStyle =
  "display: flex; justify-content: flex-end; gap: 12px; padding: 16px; " <>
  "border-top: 1px solid var(--lattice-border-subtle, #1a1a1a);"

btnSecondaryStyle :: String
btnSecondaryStyle =
  "padding: 8px 20px; border-radius: 6px; font-size: 13px; font-weight: 500; " <>
  "cursor: pointer; background: var(--lattice-surface-3, #222); " <>
  "border: 1px solid var(--lattice-border-default, #333); " <>
  "color: var(--lattice-text-primary, #e0e0e0);"

btnPrimaryStyle :: String
btnPrimaryStyle =
  "padding: 8px 20px; border-radius: 6px; font-size: 13px; font-weight: 500; " <>
  "cursor: pointer; background: var(--lattice-accent, #8B5CF6); " <>
  "border: 1px solid var(--lattice-accent, #8B5CF6); color: white;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { input = input }

  StartQueueAction -> H.raise StartQueue
  PauseQueueAction -> H.raise PauseQueue
  StopQueueAction -> H.raise StopQueue

  ShowAddJobDialog -> do
    state <- H.get
    H.modify_ _ 
      { showAddJobDialog = true
      , newJobName = state.input.activeCompositionName
      , newJobStartFrame = 0
      , newJobEndFrame = state.input.defaultFrameCount - 1
      , newJobWidth = state.input.defaultWidth
      , newJobHeight = state.input.defaultHeight
      }

  HideAddJobDialog -> do
    H.modify_ _ { showAddJobDialog = false }

  SetNewJobName val -> H.modify_ _ { newJobName = val }
  SetNewJobStartFrame val -> H.modify_ _ { newJobStartFrame = parseIntSafe val 0 }
  SetNewJobEndFrame val -> do
    state <- H.get
    H.modify_ _ { newJobEndFrame = parseIntSafe val (state.input.defaultFrameCount - 1) }
  SetNewJobWidth val -> H.modify_ _ { newJobWidth = parseIntSafe val 512 }
  SetNewJobHeight val -> H.modify_ _ { newJobHeight = parseIntSafe val 512 }
  SetNewJobFormat val -> H.modify_ _ { newJobFormat = parseFormat val }
  SetNewJobQuality val -> H.modify_ _ { newJobQuality = parseIntSafe val 95 }

  SubmitAddJob -> do
    state <- H.get
    case state.input.activeCompositionId of
      Nothing -> pure unit
      Just compId -> do
        H.raise $ AddJob
          { name: state.newJobName
          , compositionId: compId
          , startFrame: state.newJobStartFrame
          , endFrame: state.newJobEndFrame
          , width: state.newJobWidth
          , height: state.newJobHeight
          , fps: state.input.defaultFps
          , format: state.newJobFormat
          , quality: state.newJobQuality
          }
        H.modify_ _ { showAddJobDialog = false }

  PauseJobAction jobId -> H.raise (PauseJob jobId)
  ResumeJobAction jobId -> H.raise (ResumeJob jobId)
  RemoveJobAction jobId -> H.raise (RemoveJob jobId)
  DownloadJobAction jobId -> H.raise (DownloadJob jobId)

parseFormat :: String -> RenderFormat
parseFormat = case _ of
  "webm" -> FormatWebM
  "mp4" -> FormatMP4
  _ -> FormatPNGSequence

-- =============================================================================
--                                                                    // queries
-- =============================================================================

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  RefreshJobs next -> do
    pure (Just next)

  UpdateJobProgress jobId progress next -> do
    H.modify_ \s -> s
      { input = s.input
          { jobs = map (\j -> if j.id == jobId then j { progress = progress } else j) s.input.jobs
          }
      }
    pure (Just next)
