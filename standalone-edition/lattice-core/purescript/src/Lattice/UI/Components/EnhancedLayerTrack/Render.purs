-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // enhanced-layer-track // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Render functions for EnhancedLayerTrack component.
-- |
-- | Two layout modes:
-- | - SidebarLayout: AV features, layer info, switches, parent linking
-- | - TrackLayout: duration bar with trim handles, property tracks
-- |
module Lattice.UI.Components.EnhancedLayerTrack.Render
  ( render
  , labelColors
  ) where

import Prelude

import Data.Int as Int
import Data.Maybe (Maybe(..))
import Data.Set as Set
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.EnhancedLayerTrack.Types
  ( Action(..)
  , AnimatablePropertyInfo
  , DragMode(..)
  , LayoutMode(..)
  , ParentLayerRef
  , PropertyGroup
  , State
  )
import Lattice.UI.Components.EnhancedLayerTrack.Styles as S

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // constants
-- ════════════════════════════════════════════════════════════════════════════

-- | Label colors (After Effects style)
labelColors :: Array String
labelColors =
  [ "#999999"  -- none (gray)
  , "#e24b4b"  -- red
  , "#f5c343"  -- yellow
  , "#c8e04d"  -- lime
  , "#4be08e"  -- sea green
  , "#4bcde0"  -- aqua
  , "#5b8ef0"  -- blue
  , "#9d70e8"  -- purple
  , "#e070d0"  -- pink
  , "#e0a070"  -- peach
  , "#e07070"  -- light red
  , "#70e0a0"  -- mint
  , "#7090e0"  -- sky blue
  , "#a070e0"  -- violet
  , "#e07090"  -- rose
  , "#90c8e0"  -- pale blue
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // main // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> HH.ComponentHTML Action () m
render state =
  HH.div
    [ cls [ "lattice-track-wrapper" ]
    , HP.attr (HH.AttrName "style") S.trackWrapperStyle
    ]
    [ case state.layoutMode of
        SidebarLayout -> renderSidebarMode state
        TrackLayout -> renderTrackMode state
    
      -- color picker portal
    , if state.showColorPicker
        then renderColorPicker state
        else HH.text ""
    
      -- context menu portal
    , case state.contextMenu of
        Just pos -> renderContextMenu state pos
        Nothing -> HH.text ""
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // sidebar // mode
-- ════════════════════════════════════════════════════════════════════════════

renderSidebarMode :: forall m. State -> HH.ComponentHTML Action () m
renderSidebarMode state =
  HH.div_
    [ -- main sidebar row
      HH.div
        [ cls $ [ "lattice-sidebar-row" ]
              <> (if state.isSelected then [ "selected" ] else [])
              <> (if state.isDragTarget then [ "drag-over" ] else [])
        , HP.attr (HH.AttrName "style") S.sidebarRowStyle
        , HE.onClick \_ -> HandleSelectLayer
        , HE.onDoubleClick \_ -> HandleDoubleClick
        ]
        [ renderAVFeatures state
        , renderLayerInfo state
        , renderSwitches state
        , renderParentLink state
        ]
    
      -- expanded children (property groups)
    , if state.isExpanded
        then renderExpandedGroups state
        else HH.text ""
    ]

-- ────────────────────────────────────────────────────────────────────────────
--                                                    // av features
-- ────────────────────────────────────────────────────────────────────────────

renderAVFeatures :: forall m. State -> HH.ComponentHTML Action () m
renderAVFeatures state =
  HH.div
    [ cls [ "lattice-av-features" ]
    , HP.attr (HH.AttrName "style") S.avFeaturesStyle
    ]
    [ iconCol (if state.layer.visible then "V" else "o")
        (if state.layer.visible then "Hide" else "Show")
        HandleToggleVisibility
        (not state.layer.visible)
    
    , if state.hasAudioCapability
        then iconCol (if state.layer.audioEnabled then "A" else "x")
          (if state.layer.audioEnabled then "Mute Audio" else "Enable Audio")
          HandleToggleAudio
          (not state.layer.audioEnabled)
        else HH.div [ cls [ "lattice-icon-col", "placeholder" ] ] []
    
    , iconCol "*"
        (if state.layer.isolate then "Unisolate" else "Isolate")
        HandleToggleIsolate
        state.layer.isolate
    
    , iconCol (if state.layer.locked then "L" else "U")
        (if state.layer.locked then "Unlock" else "Lock")
        HandleToggleLock
        state.layer.locked
    ]

-- ────────────────────────────────────────────────────────────────────────────
--                                                    // layer info
-- ────────────────────────────────────────────────────────────────────────────

renderLayerInfo :: forall m. State -> HH.ComponentHTML Action () m
renderLayerInfo state =
  HH.div
    [ cls [ "lattice-layer-info" ]
    , HP.attr (HH.AttrName "style") S.layerInfoStyle
    ]
    [ HH.div
        [ cls [ "lattice-label-box" ]
        , HP.attr (HH.AttrName "style") (S.labelBoxStyle state.layer.labelColor)
        , HE.onClick \_ -> HandleShowColorPicker 0.0 0.0
        ]
        []
    
    , HH.div
        [ cls [ "lattice-layer-id" ]
        , HP.attr (HH.AttrName "style") S.layerIdStyle
        ]
        [ HH.text (show state.layer.index) ]
    
    , HH.div
        [ cls [ "lattice-arrow-col" ]
        , HP.attr (HH.AttrName "style") S.arrowColStyle
        , HE.onClick \_ -> HandleToggleExpand
        ]
        [ HH.span [ cls [ "lattice-arrow" ] ]
            [ HH.text (if state.isExpanded then "v" else ">") ]
        ]
    
    , HH.div
        [ cls [ "lattice-layer-name-col" ]
        , HP.attr (HH.AttrName "style") S.layerNameColStyle
        ]
        [ HH.span [ cls [ "lattice-type-icon" ] ]
            [ HH.text (getLayerIcon state.layer.layerType) ]
        
        , if state.isRenaming
            then HH.input
              [ cls [ "lattice-rename-input" ]
              , HP.attr (HH.AttrName "style") S.renameInputStyle
              , HP.value state.renameValue
              , HE.onValueInput HandleRenameInput
              , HE.onBlur \_ -> HandleFinishRename
              ]
            else HH.span
              [ cls [ "lattice-name-text" ]
              , HP.attr (HH.AttrName "style") S.nameTextStyle
              ]
              [ HH.text state.layer.name ]
        ]
    ]

-- ────────────────────────────────────────────────────────────────────────────
--                                                    // switches
-- ────────────────────────────────────────────────────────────────────────────

renderSwitches :: forall m. State -> HH.ComponentHTML Action () m
renderSwitches state =
  HH.div
    [ cls [ "lattice-layer-switches" ]
    , HP.attr (HH.AttrName "style") S.layerSwitchesStyle
    ]
    [ switchIcon "M" "Minimize" HandleToggleMinimized state.layer.minimized
    , switchIcon "F" "Flatten Transform" HandleToggleFlattenTransform state.layer.flattenTransform
    , switchIcon "Q" (if state.layer.quality == "best" then "Draft Quality" else "Best Quality")
        HandleToggleQuality (state.layer.quality == "best")
    , switchText "fx" (if state.layer.effectsEnabled then "Disable Effects" else "Enable Effects")
        HandleToggleEffects state.layer.effectsEnabled
    , switchIcon "B" "Frame Blending" HandleToggleFrameBlend state.layer.frameBlending
    , switchIcon "m" "Motion Blur" HandleToggleMotionBlur state.layer.motionBlur
    , switchIcon "E" "Effect Layer" HandleToggleEffectLayer state.layer.effectLayer
    , switchIcon "3" "3D Layer" HandleToggle3D state.layer.threeD
    ]

-- ────────────────────────────────────────────────────────────────────────────
--                                                    // parent link
-- ────────────────────────────────────────────────────────────────────────────

renderParentLink :: forall m. State -> HH.ComponentHTML Action () m
renderParentLink state =
  HH.div
    [ cls [ "lattice-col-parent" ]
    , HP.attr (HH.AttrName "style") S.colParentStyle
    ]
    [ HH.select
        [ cls [ "lattice-mini-select" ]
        , HP.attr (HH.AttrName "style") S.miniSelectStyle
        , HE.onValueChange \val -> HandleSetParent (if val == "" then Nothing else Just val)
        ]
        ( [ HH.option [ HP.value "" ] [ HH.text "None" ] ]
          <> map renderParentOption state.availableParents
        )
    ]
  where
    renderParentOption :: ParentLayerRef -> HH.ComponentHTML Action () m
    renderParentOption p =
      HH.option
        [ HP.value p.id
        , HP.selected (state.layer.parentId == Just p.id)
        ]
        [ HH.text (show p.index <> ". " <> p.name) ]

-- ────────────────────────────────────────────────────────────────────────────
--                                                    // property groups
-- ────────────────────────────────────────────────────────────────────────────

renderExpandedGroups :: forall m. State -> HH.ComponentHTML Action () m
renderExpandedGroups state =
  HH.div
    [ cls [ "lattice-children-container" ]
    , HP.attr (HH.AttrName "style") S.childrenContainerStyle
    ]
    (map (renderPropertyGroup state) state.layer.propertyGroups)

renderPropertyGroup :: forall m. State -> PropertyGroup -> HH.ComponentHTML Action () m
renderPropertyGroup state group =
  let
    isGroupExpanded = Set.member group.name state.expandedGroups
  in
  HH.div [ cls [ "lattice-property-group" ] ]
    [ HH.div
        [ cls [ "lattice-group-header", "sidebar-row" ]
        , HP.attr (HH.AttrName "style") S.groupHeaderStyle
        , HE.onClick \_ -> HandleToggleGroup group.name
        ]
        [ HH.div [ cls [ "lattice-arrow-col" ] ]
            [ HH.span [ cls [ "lattice-arrow" ] ]
                [ HH.text (if isGroupExpanded then "v" else ">") ]
            ]
        , HH.div
            [ cls [ "lattice-group-label" ]
            , HP.attr (HH.AttrName "style") S.groupLabelStyle
            ]
            [ HH.text group.name
            , if group.name == "Transform"
                then HH.span
                  [ cls [ "lattice-reset-link" ]
                  , HP.attr (HH.AttrName "style") S.resetLinkStyle
                  , HE.onClick \_ -> HandleResetTransform
                  ]
                  [ HH.text "Reset" ]
                else HH.text ""
            ]
        ]
    
    , if isGroupExpanded
        then HH.div [ cls [ "lattice-group-properties" ] ]
            (map renderPropertyRow group.properties)
        else HH.text ""
    ]
  where
    renderPropertyRow :: AnimatablePropertyInfo -> HH.ComponentHTML Action () m
    renderPropertyRow prop =
      HH.div
        [ cls [ "lattice-property-row" ]
        , HP.attr (HH.AttrName "style") S.propertyRowStyle
        ]
        [ HH.span [ cls [ "lattice-prop-name" ] ]
            [ HH.text prop.name ]
        , if prop.animated
            then HH.span [ cls [ "lattice-animated-badge" ] ] [ HH.text "*" ]
            else HH.text ""
        ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // track // mode
-- ════════════════════════════════════════════════════════════════════════════

renderTrackMode :: forall m. State -> HH.ComponentHTML Action () m
renderTrackMode state =
  HH.div_
    [ HH.div
        [ cls [ "lattice-layer-row", "track-bg" ]
        , HP.attr (HH.AttrName "style") S.trackBgStyle
        , HE.onClick \_ -> HandleSelectLayer
        ]
        [ renderDurationBar state ]
    
    , if state.isExpanded
        then HH.div [ cls [ "lattice-children-container" ] ]
            (map renderPropertyTrackRow state.layer.propertyGroups)
        else HH.text ""
    ]

renderDurationBar :: forall m. State -> HH.ComponentHTML Action () m
renderDurationBar state =
  let
    leftPct = Int.toNumber state.layer.inPoint / Int.toNumber state.frameCount * 100.0
    widthPct = Int.toNumber (state.layer.outPoint - state.layer.inPoint + 1) / Int.toNumber state.frameCount * 100.0
    isDragging = state.dragMode /= NotDragging
  in
  HH.div
    [ cls $ [ "lattice-duration-bar" ] <> (if isDragging then [ "dragging" ] else [])
    , HP.attr (HH.AttrName "style") (S.durationBarStyle leftPct widthPct)
    , HE.onMouseDown StartBarDrag
    ]
    [ HH.div
        [ cls [ "lattice-bar-handle", "bar-handle-left" ]
        , HP.attr (HH.AttrName "style") S.barHandleLeftStyle
        , HE.onMouseDown StartResizeLeft
        ]
        []
    
    , HH.div
        [ cls [ "lattice-bar-fill" ]
        , HP.attr (HH.AttrName "style") (S.barFillStyle state.layer.labelColor)
        ]
        []
    
    , HH.div
        [ cls [ "lattice-bar-handle", "bar-handle-right" ]
        , HP.attr (HH.AttrName "style") S.barHandleRightStyle
        , HE.onMouseDown StartResizeRight
        ]
        []
    ]

renderPropertyTrackRow :: forall m. PropertyGroup -> HH.ComponentHTML Action () m
renderPropertyTrackRow _group =
  HH.div [ cls [ "lattice-property-track-row" ] ]
    [ HH.div
        [ cls [ "lattice-group-header", "track-bg" ]
        , HP.attr (HH.AttrName "style") S.trackBgStyle
        ]
        []
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // overlays
-- ════════════════════════════════════════════════════════════════════════════

renderColorPicker :: forall m. State -> HH.ComponentHTML Action () m
renderColorPicker state =
  HH.div
    [ cls [ "lattice-layer-color-picker" ]
    , HP.attr (HH.AttrName "style") (S.colorPickerStyle state.colorPickerPos.x state.colorPickerPos.y)
    ]
    [ HH.div
        [ cls [ "lattice-color-grid" ]
        , HP.attr (HH.AttrName "style") S.colorGridStyle
        ]
        (map renderColorSwatch labelColors)
    ]
  where
    renderColorSwatch :: String -> HH.ComponentHTML Action () m
    renderColorSwatch color =
      HH.button
        [ cls $ [ "lattice-color-swatch" ]
              <> (if state.layer.labelColor == color then [ "active" ] else [])
        , HP.attr (HH.AttrName "style") (S.colorSwatchStyle color)
        , HE.onClick \_ -> HandleSetLabelColor color
        ]
        []

renderContextMenu :: forall m. State -> { x :: Number, y :: Number } -> HH.ComponentHTML Action () m
renderContextMenu state pos =
  HH.div
    [ cls [ "lattice-layer-context-menu" ]
    , HP.attr (HH.AttrName "style") (S.contextMenuStyle pos.x pos.y)
    ]
    [ menuButton "Duplicate Layer" HandleDuplicate
    , menuButton "Rename" HandleStartRename
    , HH.hr [ HP.attr (HH.AttrName "style") S.menuHrStyle ]
    , menuButton (if state.layer.visible then "Hide Layer" else "Show Layer") HandleToggleVisibility
    , menuButton (if state.layer.locked then "Unlock Layer" else "Lock Layer") HandleToggleLock
    , menuButton (if state.layer.threeD then "Make 2D" else "Make 3D") HandleToggle3D
    , HH.hr [ HP.attr (HH.AttrName "style") S.menuHrStyle ]
    , if state.layer.layerType == "text"
        then menuButton "Convert to Splines" HandleConvertToSplines
        else HH.text ""
    , menuButton "Nest Layers..." HandleNest
    , HH.hr [ HP.attr (HH.AttrName "style") S.menuHrStyle ]
    , HH.button
        [ cls [ "lattice-context-menu-btn", "danger" ]
        , HP.attr (HH.AttrName "style") (S.menuBtnStyle <> " color: #e57373;")
        , HE.onClick \_ -> HandleDelete
        ]
        [ HH.text "Delete Layer" ]
    ]
  where
    menuButton :: String -> Action -> HH.ComponentHTML Action () m
    menuButton label action =
      HH.button
        [ cls [ "lattice-context-menu-btn" ]
        , HP.attr (HH.AttrName "style") S.menuBtnStyle
        , HE.onClick \_ -> action
        ]
        [ HH.text label ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                    // helpers
-- ════════════════════════════════════════════════════════════════════════════

iconCol :: forall m. String -> String -> Action -> Boolean -> HH.ComponentHTML Action () m
iconCol icon title action active =
  HH.div
    [ cls [ "lattice-icon-col" ]
    , HP.attr (HH.AttrName "style") S.iconColStyle
    , HP.title title
    , HE.onClick \_ -> action
    ]
    [ HH.span
        [ cls $ [ "lattice-icon" ] <> (if active then [ "active" ] else []) ]
        [ HH.text icon ]
    ]

switchIcon :: forall m. String -> String -> Action -> Boolean -> HH.ComponentHTML Action () m
switchIcon icon title action active =
  HH.div
    [ cls [ "lattice-icon-col" ]
    , HP.attr (HH.AttrName "style") S.iconColStyle
    , HP.title title
    , HE.onClick \_ -> action
    ]
    [ HH.span
        [ cls $ [ "lattice-switch-icon" ] <> (if active then [ "active" ] else []) ]
        [ HH.text icon ]
    ]

switchText :: forall m. String -> String -> Action -> Boolean -> HH.ComponentHTML Action () m
switchText txt title action active =
  HH.div
    [ cls [ "lattice-icon-col" ]
    , HP.attr (HH.AttrName "style") S.iconColStyle
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
  "solid" -> "#"
  "camera" -> "C"
  "nestedComp" -> "N"
  "image" -> "I"
  "video" -> ">"
  "audio" -> "A"
  "shape" -> "S"
  "spline" -> "~"
  "particles" -> "P"
  "light" -> "L"
  "model" -> "M"
  "pointcloud" -> "."
  _ -> "*"
