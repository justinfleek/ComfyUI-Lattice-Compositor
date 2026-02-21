-- | EnhancedLayerTrack Component
-- |
-- | Full-featured timeline layer track with:
-- | - Sidebar mode: AV features, layer info, switches, parent linking
-- | - Track mode: duration bar with trim handles, waveform for audio layers
-- | - Expandable property groups (Transform, Material Options, etc.)
-- | - Context menu for layer operations
-- | - Color picker for layer labels
-- | - Drag-drop reordering
module Lattice.UI.Components.EnhancedLayerTrack
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , EnhancedLayerInfo
  , LayoutMode(..)
  , PropertyGroup
  , AnimatablePropertyInfo
  ) where

import Prelude

import Data.Array (filter, length, mapWithIndex)
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

-- | Animatable property info for property groups
type AnimatablePropertyInfo =
  { path :: String
  , name :: String
  , animated :: Boolean
  , hasKeyframes :: Boolean
  }

-- | Property group (Transform, Material Options, etc.)
type PropertyGroup =
  { name :: String
  , properties :: Array AnimatablePropertyInfo
  }

-- | Parent layer reference for linking
type ParentLayerRef =
  { id :: String
  , index :: Int
  , name :: String
  }

-- | Enhanced layer info with all AE-style features
type EnhancedLayerInfo =
  { id :: String
  , name :: String
  , layerType :: String
  , index :: Int
  -- AV Features
  , visible :: Boolean
  , audioEnabled :: Boolean
  , isolate :: Boolean
  , locked :: Boolean
  -- Switches
  , minimized :: Boolean
  , flattenTransform :: Boolean
  , quality :: String  -- "best" | "draft"
  , effectsEnabled :: Boolean
  , frameBlending :: Boolean
  , motionBlur :: Boolean
  , effectLayer :: Boolean
  , threeD :: Boolean
  -- Timing
  , inPoint :: Int
  , outPoint :: Int
  -- Appearance
  , labelColor :: String
  -- Parenting
  , parentId :: Maybe String
  -- Property groups (computed)
  , propertyGroups :: Array PropertyGroup
  }

data LayoutMode = SidebarLayout | TrackLayout

derive instance eqLayoutMode :: Eq LayoutMode

type Input =
  { layer :: EnhancedLayerInfo
  , layoutMode :: LayoutMode
  , isExpanded :: Boolean
  , isSelected :: Boolean
  , frameCount :: Int
  , pixelsPerFrame :: Number
  , availableParents :: Array ParentLayerRef
  , hasAudioCapability :: Boolean
  }

data Output
  = SelectLayer String
  | ToggleExpand String Boolean
  | UpdateLayerVisibility String Boolean
  | UpdateLayerAudio String Boolean
  | UpdateLayerIsolate String Boolean
  | UpdateLayerLocked String Boolean
  | UpdateLayerMinimized String Boolean
  | UpdateLayerFlattenTransform String Boolean
  | UpdateLayerQuality String String
  | UpdateLayerEffectsEnabled String Boolean
  | UpdateLayerFrameBlending String Boolean
  | UpdateLayerMotionBlur String Boolean
  | UpdateLayerEffectLayer String Boolean
  | UpdateLayer3D String Boolean
  | UpdateLayerParent String (Maybe String)
  | UpdateLayerLabelColor String String
  | UpdateLayerTiming String Int Int
  | RenameLayer String String
  | DuplicateLayer String
  | DeleteLayer String
  | NestLayer String
  | ConvertToSplines String
  | ResetTransform String
  | EnterNestedComp String
  | ReorderLayer String Int

data Query a

type Slot id = H.Slot Query Output id

type State =
  { layer :: EnhancedLayerInfo
  , layoutMode :: LayoutMode
  , isExpanded :: Boolean
  , isSelected :: Boolean
  , frameCount :: Int
  , pixelsPerFrame :: Number
  , availableParents :: Array ParentLayerRef
  , hasAudioCapability :: Boolean
  -- UI state
  , expandedGroups :: Set String
  , isRenaming :: Boolean
  , renameValue :: String
  , isDragTarget :: Boolean
  , showColorPicker :: Boolean
  , colorPickerPos :: { x :: Number, y :: Number }
  , contextMenu :: Maybe { x :: Number, y :: Number }
  }

-- Label colors (After Effects style)
labelColors :: Array String
labelColors =
  [ "#999999"  -- None (gray)
  , "#e24b4b"  -- Red
  , "#f5c343"  -- Yellow
  , "#c8e04d"  -- Lime
  , "#4be08e"  -- Sea Green
  , "#4bcde0"  -- Aqua
  , "#5b8ef0"  -- Blue
  , "#9d70e8"  -- Purple
  , "#e070d0"  -- Pink
  , "#e0a070"  -- Peach
  , "#e07070"  -- Light Red
  , "#70e0a0"  -- Mint
  , "#7090e0"  -- Sky Blue
  , "#a070e0"  -- Violet
  , "#e07090"  -- Rose
  , "#90c8e0"  -- Pale Blue
  ]

data Action
  = Receive Input
  | HandleSelectLayer
  | HandleToggleExpand
  | HandleToggleGroup String
  -- AV Features
  | HandleToggleVisibility
  | HandleToggleAudio
  | HandleToggleIsolate
  | HandleToggleLock
  -- Switches
  | HandleToggleMinimized
  | HandleToggleFlattenTransform
  | HandleToggleQuality
  | HandleToggleEffects
  | HandleToggleFrameBlend
  | HandleToggleMotionBlur
  | HandleToggleEffectLayer
  | HandleToggle3D
  -- Parenting
  | HandleSetParent (Maybe String)
  -- Color picker
  | HandleShowColorPicker Number Number
  | HandleHideColorPicker
  | HandleSetLabelColor String
  -- Renaming
  | HandleStartRename
  | HandleRenameInput String
  | HandleFinishRename
  | HandleCancelRename
  -- Context menu
  | HandleShowContextMenu Number Number
  | HandleHideContextMenu
  | HandleDuplicate
  | HandleDelete
  | HandleNest
  | HandleConvertToSplines
  | HandleResetTransform
  -- Drag/drop
  | HandleDragStart
  | HandleDragOver
  | HandleDragLeave
  | HandleDrop String
  -- Double-click actions
  | HandleDoubleClick

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { layer: input.layer
  , layoutMode: input.layoutMode
  , isExpanded: input.isExpanded
  , isSelected: input.isSelected
  , frameCount: input.frameCount
  , pixelsPerFrame: input.pixelsPerFrame
  , availableParents: input.availableParents
  , hasAudioCapability: input.hasAudioCapability
  -- UI state
  , expandedGroups: Set.fromFoldable ["Transform", "Text", "More Options"]
  , isRenaming: false
  , renameValue: ""
  , isDragTarget: false
  , showColorPicker: false
  , colorPickerPos: { x: 0.0, y: 0.0 }
  , contextMenu: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-track-wrapper" ]
    , HP.attr (HH.AttrName "style") trackWrapperStyle
    ]
    [ case state.layoutMode of
        SidebarLayout -> renderSidebarMode state
        TrackLayout -> renderTrackMode state
    
      -- Color picker portal
    , if state.showColorPicker
        then renderColorPicker state
        else HH.text ""
    
      -- Context menu portal
    , case state.contextMenu of
        Just pos -> renderContextMenu state pos
        Nothing -> HH.text ""
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // sidebar // mode
-- ════════════════════════════════════════════════════════════════════════════

renderSidebarMode :: forall m. State -> H.ComponentHTML Action () m
renderSidebarMode state =
  HH.div_
    [ -- Main sidebar row
      HH.div
        [ cls $ [ "lattice-sidebar-row" ]
              <> (if state.isSelected then [ "selected" ] else [])
              <> (if state.isDragTarget then [ "drag-over" ] else [])
        , HP.attr (HH.AttrName "style") sidebarRowStyle
        , HE.onClick \_ -> HandleSelectLayer
        , HE.onDoubleClick \_ -> HandleDoubleClick
        ]
        [ -- AV Features section
          renderAVFeatures state
        
          -- Layer info section
        , renderLayerInfo state
        
          -- Switches section
        , renderSwitches state
        
          -- Parent & Link section
        , renderParentLink state
        ]
    
      -- Expanded children (property groups)
    , if state.isExpanded
        then renderExpandedGroups state
        else HH.text ""
    ]

renderAVFeatures :: forall m. State -> H.ComponentHTML Action () m
renderAVFeatures state =
  HH.div
    [ cls [ "lattice-av-features" ]
    , HP.attr (HH.AttrName "style") avFeaturesStyle
    ]
    [ -- Visibility toggle
      iconCol (if state.layer.visible then "👁" else "○")
        (if state.layer.visible then "Hide" else "Show")
        HandleToggleVisibility
        (not state.layer.visible)
    
      -- Audio toggle (if applicable)
    , if state.hasAudioCapability
        then iconCol (if state.layer.audioEnabled then "🔊" else "🔇")
          (if state.layer.audioEnabled then "Mute Audio" else "Enable Audio")
          HandleToggleAudio
          (not state.layer.audioEnabled)
        else HH.div [ cls [ "lattice-icon-col", "placeholder" ] ] []
    
      -- Isolate toggle
    , iconCol "●"
        (if state.layer.isolate then "Unisolate" else "Isolate")
        HandleToggleIsolate
        state.layer.isolate
    
      -- Lock toggle
    , iconCol (if state.layer.locked then "🔒" else "🔓")
        (if state.layer.locked then "Unlock" else "Lock")
        HandleToggleLock
        state.layer.locked
    ]

renderLayerInfo :: forall m. State -> H.ComponentHTML Action () m
renderLayerInfo state =
  HH.div
    [ cls [ "lattice-layer-info" ]
    , HP.attr (HH.AttrName "style") layerInfoStyle
    ]
    [ -- Label color box
      HH.div
        [ cls [ "lattice-label-box" ]
        , HP.attr (HH.AttrName "style") (labelBoxStyle state.layer.labelColor)
        , HE.onClick \_ -> HandleShowColorPicker 0.0 0.0
        ]
        []
    
      -- Layer index
    , HH.div
        [ cls [ "lattice-layer-id" ]
        , HP.attr (HH.AttrName "style") layerIdStyle
        ]
        [ HH.text (show state.layer.index) ]
    
      -- Expand arrow
    , HH.div
        [ cls [ "lattice-arrow-col" ]
        , HP.attr (HH.AttrName "style") arrowColStyle
        , HE.onClick \_ -> HandleToggleExpand
        ]
        [ HH.span [ cls [ "lattice-arrow" ] ]
            [ HH.text (if state.isExpanded then "▼" else "▶") ]
        ]
    
      -- Layer name (editable or static)
    , HH.div
        [ cls [ "lattice-layer-name-col" ]
        , HP.attr (HH.AttrName "style") layerNameColStyle
        ]
        [ -- Type icon
          HH.span [ cls [ "lattice-type-icon" ] ]
            [ HH.text (getLayerIcon state.layer.layerType) ]
        
          -- Name text or input
        , if state.isRenaming
            then HH.input
              [ cls [ "lattice-rename-input" ]
              , HP.attr (HH.AttrName "style") renameInputStyle
              , HP.value state.renameValue
              , HE.onValueInput HandleRenameInput
              , HE.onBlur \_ -> HandleFinishRename
              ]
            else HH.span
              [ cls [ "lattice-name-text" ]
              , HP.attr (HH.AttrName "style") nameTextStyle
              ]
              [ HH.text state.layer.name ]
        ]
    ]

renderSwitches :: forall m. State -> H.ComponentHTML Action () m
renderSwitches state =
  HH.div
    [ cls [ "lattice-layer-switches" ]
    , HP.attr (HH.AttrName "style") layerSwitchesStyle
    ]
    [ -- Minimized (hide when filter enabled)
      switchIcon "👁" "Minimize" HandleToggleMinimized state.layer.minimized
    
      -- Flatten transform / Continuously Rasterize
    , switchIcon "☀" "Flatten Transform" HandleToggleFlattenTransform state.layer.flattenTransform
    
      -- Quality (draft/best)
    , switchIcon "◐" (if state.layer.quality == "best" then "Draft Quality" else "Best Quality")
        HandleToggleQuality (state.layer.quality == "best")
    
      -- Effects enabled
    , switchText "fx" (if state.layer.effectsEnabled then "Disable Effects" else "Enable Effects")
        HandleToggleEffects state.layer.effectsEnabled
    
      -- Frame blending
    , switchIcon "⊞" "Frame Blending" HandleToggleFrameBlend state.layer.frameBlending
    
      -- Motion blur
    , switchIcon "◔" "Motion Blur" HandleToggleMotionBlur state.layer.motionBlur
    
      -- Effect/Adjustment layer
    , switchIcon "◐" "Effect Layer" HandleToggleEffectLayer state.layer.effectLayer
    
      -- 3D layer
    , switchIcon "⬡" "3D Layer" HandleToggle3D state.layer.threeD
    ]

renderParentLink :: forall m. State -> H.ComponentHTML Action () m
renderParentLink state =
  HH.div
    [ cls [ "lattice-col-parent" ]
    , HP.attr (HH.AttrName "style") colParentStyle
    ]
    [ HH.select
        [ cls [ "lattice-mini-select" ]
        , HP.attr (HH.AttrName "style") miniSelectStyle
        , HE.onValueChange \val -> HandleSetParent (if val == "" then Nothing else Just val)
        ]
        ( [ HH.option [ HP.value "" ] [ HH.text "None" ] ]
          <> map renderParentOption state.availableParents
        )
    ]
  where
    renderParentOption :: ParentLayerRef -> H.ComponentHTML Action () m
    renderParentOption p =
      HH.option
        [ HP.value p.id
        , HP.selected (state.layer.parentId == Just p.id)
        ]
        [ HH.text (show p.index <> ". " <> p.name) ]

renderExpandedGroups :: forall m. State -> H.ComponentHTML Action () m
renderExpandedGroups state =
  HH.div
    [ cls [ "lattice-children-container" ]
    , HP.attr (HH.AttrName "style") childrenContainerStyle
    ]
    (map (renderPropertyGroup state) state.layer.propertyGroups)

renderPropertyGroup :: forall m. State -> PropertyGroup -> H.ComponentHTML Action () m
renderPropertyGroup state group =
  let
    isGroupExpanded = Set.member group.name state.expandedGroups
  in
  HH.div [ cls [ "lattice-property-group" ] ]
    [ -- Group header
      HH.div
        [ cls [ "lattice-group-header", "sidebar-row" ]
        , HP.attr (HH.AttrName "style") groupHeaderStyle
        , HE.onClick \_ -> HandleToggleGroup group.name
        ]
        [ HH.div [ cls [ "lattice-arrow-col" ] ]
            [ HH.span [ cls [ "lattice-arrow" ] ]
                [ HH.text (if isGroupExpanded then "▼" else "▶") ]
            ]
        , HH.div
            [ cls [ "lattice-group-label" ]
            , HP.attr (HH.AttrName "style") groupLabelStyle
            ]
            [ HH.text group.name
            , if group.name == "Transform"
                then HH.span
                  [ cls [ "lattice-reset-link" ]
                  , HP.attr (HH.AttrName "style") resetLinkStyle
                  , HE.onClick \_ -> HandleResetTransform
                  ]
                  [ HH.text "Reset" ]
                else HH.text ""
            ]
        ]
    
      -- Group properties (when expanded)
    , if isGroupExpanded
        then HH.div [ cls [ "lattice-group-properties" ] ]
            (map renderPropertyRow group.properties)
        else HH.text ""
    ]
  where
    renderPropertyRow :: AnimatablePropertyInfo -> H.ComponentHTML Action () m
    renderPropertyRow prop =
      HH.div
        [ cls [ "lattice-property-row" ]
        , HP.attr (HH.AttrName "style") propertyRowStyle
        ]
        [ HH.span [ cls [ "lattice-prop-name" ] ]
            [ HH.text prop.name ]
        , if prop.animated
            then HH.span [ cls [ "lattice-animated-badge" ] ] [ HH.text "◆" ]
            else HH.text ""
        ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                              // track // mode
-- ════════════════════════════════════════════════════════════════════════════

renderTrackMode :: forall m. State -> H.ComponentHTML Action () m
renderTrackMode state =
  HH.div_
    [ -- Layer bar row
      HH.div
        [ cls [ "lattice-layer-row", "track-bg" ]
        , HP.attr (HH.AttrName "style") trackBgStyle
        , HE.onClick \_ -> HandleSelectLayer
        ]
        [ -- Duration bar
          renderDurationBar state
        ]
    
      -- Expanded property tracks
    , if state.isExpanded
        then HH.div [ cls [ "lattice-children-container" ] ]
            (map renderPropertyTrackRow state.layer.propertyGroups)
        else HH.text ""
    ]

renderDurationBar :: forall m. State -> H.ComponentHTML Action () m
renderDurationBar state =
  let
    leftPct = Int.toNumber state.layer.inPoint / Int.toNumber state.frameCount * 100.0
    widthPct = Int.toNumber (state.layer.outPoint - state.layer.inPoint + 1) / Int.toNumber state.frameCount * 100.0
  in
  HH.div
    [ cls [ "lattice-duration-bar" ]
    , HP.attr (HH.AttrName "style") (durationBarStyle leftPct widthPct)
    ]
    [ -- Left trim handle
      HH.div
        [ cls [ "lattice-bar-handle", "bar-handle-left" ]
        , HP.attr (HH.AttrName "style") barHandleLeftStyle
        ]
        []
    
      -- Bar fill with label color
    , HH.div
        [ cls [ "lattice-bar-fill" ]
        , HP.attr (HH.AttrName "style") (barFillStyle state.layer.labelColor)
        ]
        []
    
      -- Right trim handle
    , HH.div
        [ cls [ "lattice-bar-handle", "bar-handle-right" ]
        , HP.attr (HH.AttrName "style") barHandleRightStyle
        ]
        []
    ]

renderPropertyTrackRow :: forall m. PropertyGroup -> H.ComponentHTML Action () m
renderPropertyTrackRow group =
  HH.div [ cls [ "lattice-property-track-row" ] ]
    [ HH.div
        [ cls [ "lattice-group-header", "track-bg" ]
        , HP.attr (HH.AttrName "style") trackBgStyle
        ]
        []
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // color picker
-- ════════════════════════════════════════════════════════════════════════════

renderColorPicker :: forall m. State -> H.ComponentHTML Action () m
renderColorPicker state =
  HH.div
    [ cls [ "lattice-layer-color-picker" ]
    , HP.attr (HH.AttrName "style") (colorPickerStyle state.colorPickerPos.x state.colorPickerPos.y)
    ]
    [ HH.div
        [ cls [ "lattice-color-grid" ]
        , HP.attr (HH.AttrName "style") colorGridStyle
        ]
        (map renderColorSwatch labelColors)
    ]
  where
    renderColorSwatch :: String -> H.ComponentHTML Action () m
    renderColorSwatch color =
      HH.button
        [ cls $ [ "lattice-color-swatch" ]
              <> (if state.layer.labelColor == color then [ "active" ] else [])
        , HP.attr (HH.AttrName "style") (colorSwatchStyle color)
        , HE.onClick \_ -> HandleSetLabelColor color
        ]
        []

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // context menu
-- ════════════════════════════════════════════════════════════════════════════

renderContextMenu :: forall m. State -> { x :: Number, y :: Number } -> H.ComponentHTML Action () m
renderContextMenu state pos =
  HH.div
    [ cls [ "lattice-layer-context-menu" ]
    , HP.attr (HH.AttrName "style") (contextMenuStyle pos.x pos.y)
    ]
    [ menuButton "Duplicate Layer" HandleDuplicate
    , menuButton "Rename" HandleStartRename
    , HH.hr [ HP.attr (HH.AttrName "style") menuHrStyle ]
    , menuButton (if state.layer.visible then "Hide Layer" else "Show Layer") HandleToggleVisibility
    , menuButton (if state.layer.locked then "Unlock Layer" else "Lock Layer") HandleToggleLock
    , menuButton (if state.layer.threeD then "Make 2D" else "Make 3D") HandleToggle3D
    , HH.hr [ HP.attr (HH.AttrName "style") menuHrStyle ]
    , if state.layer.layerType == "text"
        then menuButton "Convert to Splines" HandleConvertToSplines
        else HH.text ""
    , menuButton "Nest Layers..." HandleNest
    , HH.hr [ HP.attr (HH.AttrName "style") menuHrStyle ]
    , HH.button
        [ cls [ "lattice-context-menu-btn", "danger" ]
        , HP.attr (HH.AttrName "style") (menuBtnStyle <> " color: #e57373;")
        , HE.onClick \_ -> HandleDelete
        ]
        [ HH.text "Delete Layer" ]
    ]
  where
    menuButton :: String -> Action -> H.ComponentHTML Action () m
    menuButton label action =
      HH.button
        [ cls [ "lattice-context-menu-btn" ]
        , HP.attr (HH.AttrName "style") menuBtnStyle
        , HE.onClick \_ -> action
        ]
        [ HH.text label ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                  // helpers
-- ════════════════════════════════════════════════════════════════════════════

iconCol :: forall m. String -> String -> Action -> Boolean -> H.ComponentHTML Action () m
iconCol icon title action active =
  HH.div
    [ cls [ "lattice-icon-col" ]
    , HP.attr (HH.AttrName "style") iconColStyle
    , HP.title title
    , HE.onClick \_ -> action
    ]
    [ HH.span
        [ cls $ [ "lattice-icon" ] <> (if active then [ "active" ] else []) ]
        [ HH.text icon ]
    ]

switchIcon :: forall m. String -> String -> Action -> Boolean -> H.ComponentHTML Action () m
switchIcon icon title action active =
  HH.div
    [ cls [ "lattice-icon-col" ]
    , HP.attr (HH.AttrName "style") iconColStyle
    , HP.title title
    , HE.onClick \_ -> action
    ]
    [ HH.span
        [ cls $ [ "lattice-switch-icon" ] <> (if active then [ "active" ] else []) ]
        [ HH.text icon ]
    ]

switchText :: forall m. String -> String -> Action -> Boolean -> H.ComponentHTML Action () m
switchText txt title action active =
  HH.div
    [ cls [ "lattice-icon-col" ]
    , HP.attr (HH.AttrName "style") iconColStyle
    , HP.title title
    , HE.onClick \_ -> action
    ]
    [ HH.span
        [ cls $ [ "lattice-switch-text" ] <> (if active then [ "active" ] else [ "inactive" ]) ]
        [ HH.text txt ]
    ]

getLayerIcon :: String -> String
getLayerIcon layerType = case layerType of
  "text" -> "T"
  "solid" -> "■"
  "camera" -> "◎"
  "nestedComp" -> "▣"
  "image" -> "▧"
  "video" -> "▶"
  "audio" -> "🔊"
  "shape" -> "◇"
  "spline" -> "〰"
  "particles" -> "✨"
  "light" -> "💡"
  "model" -> "🎲"
  "pointcloud" -> "☁"
  _ -> "•"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

trackWrapperStyle :: String
trackWrapperStyle =
  "display: flex; " <>
  "flex-direction: column; " <>
  "width: 100%;"

sidebarRowStyle :: String
sidebarRowStyle =
  "display: flex; " <>
  "align-items: stretch; " <>
  "height: 32px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "background: var(--lattice-surface-1, #0f0f0f); " <>
  "color: var(--lattice-text-primary, #E5E5E5); " <>
  "font-size: 13px; " <>
  "user-select: none; " <>
  "cursor: pointer;"

avFeaturesStyle :: String
avFeaturesStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "border-right: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "flex-shrink: 0;"

layerInfoStyle :: String
layerInfoStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "flex: 1; " <>
  "min-width: 0; " <>
  "gap: 4px; " <>
  "padding: 0 4px;"

layerSwitchesStyle :: String
layerSwitchesStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "border-left: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "flex-shrink: 0;"

colParentStyle :: String
colParentStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "padding: 0 4px; " <>
  "border-left: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "min-width: 80px;"

iconColStyle :: String
iconColStyle =
  "display: flex; " <>
  "justify-content: center; " <>
  "align-items: center; " <>
  "width: 26px; " <>
  "height: 100%; " <>
  "cursor: pointer; " <>
  "font-size: 14px;"

labelBoxStyle :: String -> String
labelBoxStyle color =
  "width: 12px; " <>
  "height: 12px; " <>
  "background: " <> color <> "; " <>
  "border: 1px solid rgba(0,0,0,0.4); " <>
  "border-radius: 2px; " <>
  "cursor: pointer; " <>
  "flex-shrink: 0;"

layerIdStyle :: String
layerIdStyle =
  "font-size: 12px; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "min-width: 16px; " <>
  "text-align: center; " <>
  "flex-shrink: 0;"

arrowColStyle :: String
arrowColStyle =
  "display: flex; " <>
  "justify-content: center; " <>
  "align-items: center; " <>
  "width: 16px; " <>
  "cursor: pointer;"

layerNameColStyle :: String
layerNameColStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "flex: 1; " <>
  "min-width: 0; " <>
  "overflow: hidden;"

nameTextStyle :: String
nameTextStyle =
  "white-space: nowrap; " <>
  "overflow: hidden; " <>
  "text-overflow: ellipsis; " <>
  "font-size: 12px;"

renameInputStyle :: String
renameInputStyle =
  "background: var(--lattice-surface-0, #080808); " <>
  "border: 1px solid var(--lattice-accent, #8B5CF6); " <>
  "color: var(--lattice-text-primary, #fff); " <>
  "padding: 2px 4px; " <>
  "font-size: 12px; " <>
  "width: 100%;"

miniSelectStyle :: String
miniSelectStyle =
  "width: 100%; " <>
  "background: transparent; " <>
  "border: none; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "font-size: 12px; " <>
  "cursor: pointer;"

childrenContainerStyle :: String
childrenContainerStyle =
  "background: var(--lattice-surface-0, #080808);"

groupHeaderStyle :: String
groupHeaderStyle =
  "background: var(--lattice-surface-2, #161616); " <>
  "font-weight: 600; " <>
  "color: var(--lattice-text-muted, #6B7280); " <>
  "cursor: pointer; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "height: 28px; " <>
  "padding: 0 8px;"

groupLabelStyle :: String
groupLabelStyle =
  "padding-left: 4px; " <>
  "font-size: 12px; " <>
  "display: flex; " <>
  "align-items: center; " <>
  "gap: 12px;"

resetLinkStyle :: String
resetLinkStyle =
  "font-size: 12px; " <>
  "color: var(--lattice-accent, #8B5CF6); " <>
  "cursor: pointer; " <>
  "font-weight: normal;"

propertyRowStyle :: String
propertyRowStyle =
  "display: flex; " <>
  "align-items: center; " <>
  "height: 24px; " <>
  "padding: 0 8px 0 32px; " <>
  "font-size: 12px; " <>
  "color: var(--lattice-text-secondary, #9CA3AF);"

trackBgStyle :: String
trackBgStyle =
  "height: 28px; " <>
  "background: var(--lattice-surface-0, #080808); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #1a1a1a); " <>
  "position: relative; " <>
  "width: 100%;"

durationBarStyle :: Number -> Number -> String
durationBarStyle leftPct widthPct =
  "position: absolute; " <>
  "height: 22px; " <>
  "top: 3px; " <>
  "left: " <> show leftPct <> "%; " <>
  "width: " <> show widthPct <> "%; " <>
  "border: 1px solid rgba(0,0,0,0.6); " <>
  "border-radius: 6px; " <>
  "cursor: move; " <>
  "display: flex; " <>
  "align-items: center;"

barHandleLeftStyle :: String
barHandleLeftStyle =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "left: 0; " <>
  "width: 8px; " <>
  "background: rgba(255,255,255,0.15); " <>
  "cursor: ew-resize; " <>
  "z-index: 2; " <>
  "border-radius: 6px 0 0 6px;"

barHandleRightStyle :: String
barHandleRightStyle =
  "position: absolute; " <>
  "top: 0; " <>
  "bottom: 0; " <>
  "right: 0; " <>
  "width: 8px; " <>
  "background: rgba(255,255,255,0.15); " <>
  "cursor: ew-resize; " <>
  "z-index: 2; " <>
  "border-radius: 0 6px 6px 0;"

barFillStyle :: String -> String
barFillStyle labelColor =
  "flex: 1; " <>
  "height: 100%; " <>
  "background: " <> labelColor <> "; " <>
  "border-radius: 4px;"

colorPickerStyle :: Number -> Number -> String
colorPickerStyle x y =
  "position: fixed; " <>
  "left: " <> show x <> "px; " <>
  "top: " <> show y <> "px; " <>
  "background: var(--lattice-surface-2, #161616); " <>
  "border: 1px solid var(--lattice-border-default, #2a2a2a); " <>
  "border-radius: 6px; " <>
  "padding: 8px; " <>
  "z-index: 1000;"

colorGridStyle :: String
colorGridStyle =
  "display: grid; " <>
  "grid-template-columns: repeat(4, 1fr); " <>
  "gap: 4px;"

colorSwatchStyle :: String -> String
colorSwatchStyle color =
  "width: 20px; " <>
  "height: 20px; " <>
  "background: " <> color <> "; " <>
  "border: 2px solid transparent; " <>
  "border-radius: 4px; " <>
  "cursor: pointer;"

contextMenuStyle :: Number -> Number -> String
contextMenuStyle x y =
  "position: fixed; " <>
  "left: " <> show x <> "px; " <>
  "top: " <> show y <> "px; " <>
  "background: var(--lattice-surface-2, #2a2a2a); " <>
  "border: 1px solid var(--lattice-border-subtle, #444); " <>
  "border-radius: 4px; " <>
  "box-shadow: 0 4px 12px rgba(0, 0, 0, 0.4); " <>
  "z-index: 1000; " <>
  "min-width: 160px; " <>
  "padding: 4px 0;"

menuBtnStyle :: String
menuBtnStyle =
  "display: block; " <>
  "width: 100%; " <>
  "padding: 6px 12px; " <>
  "border: none; " <>
  "background: transparent; " <>
  "color: var(--lattice-text-primary, #e0e0e0); " <>
  "font-size: 13px; " <>
  "text-align: left; " <>
  "cursor: pointer;"

menuHrStyle :: String
menuHrStyle =
  "border: none; " <>
  "border-top: 1px solid var(--lattice-border-subtle, #444); " <>
  "margin: 4px 0;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { layer = input.layer
      , layoutMode = input.layoutMode
      , isExpanded = input.isExpanded
      , isSelected = input.isSelected
      , frameCount = input.frameCount
      , pixelsPerFrame = input.pixelsPerFrame
      , availableParents = input.availableParents
      , hasAudioCapability = input.hasAudioCapability
      }
  
  HandleSelectLayer -> do
    state <- H.get
    H.raise (SelectLayer state.layer.id)
  
  HandleToggleExpand -> do
    state <- H.get
    H.raise (ToggleExpand state.layer.id (not state.isExpanded))
  
  HandleToggleGroup groupName -> do
    state <- H.get
    let newGroups = 
          if Set.member groupName state.expandedGroups
            then Set.delete groupName state.expandedGroups
            else Set.insert groupName state.expandedGroups
    H.modify_ _ { expandedGroups = newGroups }
  
  -- AV Features
  HandleToggleVisibility -> do
    state <- H.get
    H.raise (UpdateLayerVisibility state.layer.id (not state.layer.visible))
  
  HandleToggleAudio -> do
    state <- H.get
    H.raise (UpdateLayerAudio state.layer.id (not state.layer.audioEnabled))
  
  HandleToggleIsolate -> do
    state <- H.get
    H.raise (UpdateLayerIsolate state.layer.id (not state.layer.isolate))
  
  HandleToggleLock -> do
    state <- H.get
    H.raise (UpdateLayerLocked state.layer.id (not state.layer.locked))
  
  -- Switches
  HandleToggleMinimized -> do
    state <- H.get
    H.raise (UpdateLayerMinimized state.layer.id (not state.layer.minimized))
  
  HandleToggleFlattenTransform -> do
    state <- H.get
    H.raise (UpdateLayerFlattenTransform state.layer.id (not state.layer.flattenTransform))
  
  HandleToggleQuality -> do
    state <- H.get
    let newQuality = if state.layer.quality == "best" then "draft" else "best"
    H.raise (UpdateLayerQuality state.layer.id newQuality)
  
  HandleToggleEffects -> do
    state <- H.get
    H.raise (UpdateLayerEffectsEnabled state.layer.id (not state.layer.effectsEnabled))
  
  HandleToggleFrameBlend -> do
    state <- H.get
    H.raise (UpdateLayerFrameBlending state.layer.id (not state.layer.frameBlending))
  
  HandleToggleMotionBlur -> do
    state <- H.get
    H.raise (UpdateLayerMotionBlur state.layer.id (not state.layer.motionBlur))
  
  HandleToggleEffectLayer -> do
    state <- H.get
    H.raise (UpdateLayerEffectLayer state.layer.id (not state.layer.effectLayer))
  
  HandleToggle3D -> do
    state <- H.get
    H.raise (UpdateLayer3D state.layer.id (not state.layer.threeD))
  
  -- Parenting
  HandleSetParent parentId -> do
    state <- H.get
    H.raise (UpdateLayerParent state.layer.id parentId)
  
  -- Color picker
  HandleShowColorPicker x y -> do
    H.modify_ _ { showColorPicker = true, colorPickerPos = { x, y } }
  
  HandleHideColorPicker -> do
    H.modify_ _ { showColorPicker = false }
  
  HandleSetLabelColor color -> do
    state <- H.get
    H.raise (UpdateLayerLabelColor state.layer.id color)
    H.modify_ _ { showColorPicker = false }
  
  -- Renaming
  HandleStartRename -> do
    state <- H.get
    H.modify_ _ { isRenaming = true, renameValue = state.layer.name }
    handleAction HandleHideContextMenu
  
  HandleRenameInput val -> do
    H.modify_ _ { renameValue = val }
  
  HandleFinishRename -> do
    state <- H.get
    when (state.renameValue /= "") do
      H.raise (RenameLayer state.layer.id state.renameValue)
    H.modify_ _ { isRenaming = false, renameValue = "" }
  
  HandleCancelRename -> do
    H.modify_ _ { isRenaming = false, renameValue = "" }
  
  -- Context menu
  HandleShowContextMenu x y -> do
    H.modify_ _ { contextMenu = Just { x, y } }
  
  HandleHideContextMenu -> do
    H.modify_ _ { contextMenu = Nothing }
  
  HandleDuplicate -> do
    state <- H.get
    H.raise (DuplicateLayer state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleDelete -> do
    state <- H.get
    H.raise (DeleteLayer state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleNest -> do
    state <- H.get
    H.raise (NestLayer state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleConvertToSplines -> do
    state <- H.get
    H.raise (ConvertToSplines state.layer.id)
    handleAction HandleHideContextMenu
  
  HandleResetTransform -> do
    state <- H.get
    H.raise (ResetTransform state.layer.id)
  
  -- Drag/drop
  HandleDragStart -> do
    pure unit  -- Parent handles actual drag data
  
  HandleDragOver -> do
    H.modify_ _ { isDragTarget = true }
  
  HandleDragLeave -> do
    H.modify_ _ { isDragTarget = false }
  
  HandleDrop draggedLayerId -> do
    state <- H.get
    H.modify_ _ { isDragTarget = false }
    when (draggedLayerId /= state.layer.id) do
      H.raise (ReorderLayer draggedLayerId state.layer.index)
  
  -- Double-click (enter nested comp or start rename)
  HandleDoubleClick -> do
    state <- H.get
    if state.layer.layerType == "nestedComp"
      then H.raise (EnterNestedComp state.layer.id)
      else handleAction HandleStartRename
