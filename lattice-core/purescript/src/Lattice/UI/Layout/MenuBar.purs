-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // lattice // ui // menubar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Menu Bar Component
-- |
-- | Top-level menu bar with File, Edit, Create, Effects, Layer, View, Window, Help.
-- | Dropdown menus appear on click/hover with keyboard shortcuts displayed.
-- |
-- | Architecture:
-- | - Pure PureScript component, no JavaScript FFI
-- | - Actions emitted as Output to parent for handling via Bridge
-- | - Menu state managed locally (which menu is open)
-- |
module Lattice.UI.Layout.MenuBar
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , MenuAction(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { projectName :: String
  , hasUnsavedChanges :: Boolean
  , canUndo :: Boolean
  , canRedo :: Boolean
  , hasSelection :: Boolean
  }

-- | Actions emitted when menu items are clicked
data MenuAction
  -- File
  = NewProject
  | OpenProject
  | SaveProject
  | SaveProjectAs
  | Import
  | Export
  | ProjectSettings
  | Preferences
  -- Edit
  | Undo
  | Redo
  | Cut
  | Copy
  | Paste
  | Duplicate
  | Delete
  | SelectAll
  | DeselectAll
  -- Create
  | CreateSolid
  | CreateText
  | CreateShape
  | CreatePath
  | CreateCamera
  | CreateLight
  | CreateControl
  | CreateParticle
  | CreateDepth
  | CreateNormal
  | CreateGenerated
  | CreateGroup
  | CreateEffectLayer
  | CreateMatte
  -- Layer
  | Precompose
  | SplitLayer
  | TimeStretch
  | TimeReverse
  | FreezeFrame
  | LockLayer
  | ToggleVisibility
  | IsolateLayer
  | BringToFront
  | SendToBack
  | BringForward
  | SendBackward
  -- View
  | ZoomIn
  | ZoomOut
  | ZoomFit
  | Zoom100
  | ToggleGrid
  | ToggleRulers
  | ToggleGuides
  | ToggleSafeZones
  | ToggleCurveEditor
  -- Window
  | ShowProperties
  | ShowEffects
  | ShowCamera
  | ShowAudio
  | ShowAlign
  | ShowAIChat
  | ShowAIGenerate
  | ShowExport
  | ShowPreview
  -- Help
  | ShowKeyboardShortcuts
  | ShowDocumentation
  | ShowAbout
  -- Effects (subset - full list would be very long)
  | ApplyEffect String

derive instance eqMenuAction :: Eq MenuAction

data Output = MenuActionSelected MenuAction

data Query a

type Slot id = H.Slot Query Output id

data ActiveMenu
  = MenuNone
  | MenuFile
  | MenuEdit
  | MenuCreate
  | MenuEffects
  | MenuLayer
  | MenuView
  | MenuWindow
  | MenuHelp

derive instance eqActiveMenu :: Eq ActiveMenu

type State =
  { activeMenu :: ActiveMenu
  , projectName :: String
  , hasUnsavedChanges :: Boolean
  , canUndo :: Boolean
  , canRedo :: Boolean
  , hasSelection :: Boolean
  }

data Action
  = Initialize
  | Receive Input
  | ToggleMenu ActiveMenu
  | OpenMenu ActiveMenu
  | CloseMenu
  | SelectAction MenuAction

type Slots :: Row Type
type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                                 // component
-- ════════════════════════════════════════════════════════════════════════════

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
  { activeMenu: MenuNone
  , projectName: input.projectName
  , hasUnsavedChanges: input.hasUnsavedChanges
  , canUndo: input.canUndo
  , canRedo: input.canRedo
  , hasSelection: input.hasSelection
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-menubar" ]
    , HP.attr (HH.AttrName "style") menuBarStyle
    , HP.attr (HH.AttrName "role") "menubar"
    ]
    [ -- Menu items
      HH.div [ cls [ "lattice-menubar-left" ] ]
        [ renderMenu state MenuFile "File"
        , renderMenu state MenuEdit "Edit"
        , renderMenu state MenuCreate "Create"
        , renderMenu state MenuEffects "Effects"
        , renderMenu state MenuLayer "Layer"
        , renderMenu state MenuView "View"
        , renderMenu state MenuWindow "Window"
        , renderMenu state MenuHelp "Help"
        ]
    
      -- Spacer
    , HH.div [ cls [ "lattice-menubar-spacer" ] ] []
    
      -- Project name
    , HH.div 
        [ cls [ "lattice-project-name" ]
        , HP.title (if state.hasUnsavedChanges then "Unsaved changes" else "Saved")
        ]
        [ if state.hasUnsavedChanges
            then HH.span [ cls [ "lattice-unsaved" ] ] [ HH.text "*" ]
            else HH.text ""
        , HH.text (if state.projectName == "" then "Untitled Project" else state.projectName)
        ]
    ]

renderMenu :: forall m. State -> ActiveMenu -> String -> H.ComponentHTML Action Slots m
renderMenu state menu label =
  HH.div
    [ cls [ "lattice-menu-item" ]
    , HE.onMouseEnter \_ -> OpenMenu menu
    , HE.onMouseLeave \_ -> CloseMenu
    ]
    [ HH.button
        [ cls [ "lattice-menu-trigger" ]
        , HP.attr (HH.AttrName "data-state") (if state.activeMenu == menu then "active" else "inactive")
        , HE.onClick \_ -> ToggleMenu menu
        ]
        [ HH.text label ]
    , if state.activeMenu == menu
        then renderDropdown state menu
        else HH.text ""
    ]

renderDropdown :: forall m. State -> ActiveMenu -> H.ComponentHTML Action Slots m
renderDropdown state menu =
  HH.div
    [ cls [ "lattice-menu-dropdown" ]
    , HP.attr (HH.AttrName "style") dropdownStyle
    , HE.onMouseEnter \_ -> OpenMenu menu
    , HE.onMouseLeave \_ -> CloseMenu
    ]
    (case menu of
      MenuFile -> renderFileMenu
      MenuEdit -> renderEditMenu state
      MenuCreate -> renderCreateMenu
      MenuEffects -> renderEffectsMenu
      MenuLayer -> renderLayerMenu state
      MenuView -> renderViewMenu
      MenuWindow -> renderWindowMenu
      MenuHelp -> renderHelpMenu
      MenuNone -> [])

-- ════════════════════════════════════════════════════════════════════════════
--                                                                     // menus
-- ════════════════════════════════════════════════════════════════════════════

renderFileMenu :: forall m. Array (H.ComponentHTML Action Slots m)
renderFileMenu =
  [ menuItem "New Project" (Just "Ctrl+N") true NewProject
  , menuItem "Open Project..." (Just "Ctrl+O") true OpenProject
  , separator
  , menuItem "Save Project" (Just "Ctrl+S") true SaveProject
  , menuItem "Save Project As..." (Just "Ctrl+Shift+S") true SaveProjectAs
  , separator
  , menuItem "Import..." (Just "Ctrl+I") true Import
  , menuItem "Export..." (Just "Ctrl+M") true Export
  , separator
  , menuItem "Project Settings..." (Just "Ctrl+Alt+P") true ProjectSettings
  , menuItem "Preferences..." (Just "Ctrl+,") true Preferences
  ]

renderEditMenu :: forall m. State -> Array (H.ComponentHTML Action Slots m)
renderEditMenu state =
  [ menuItem "Undo" (Just "Ctrl+Z") state.canUndo Undo
  , menuItem "Redo" (Just "Ctrl+Shift+Z") state.canRedo Redo
  , separator
  , menuItem "Cut" (Just "Ctrl+X") true Cut
  , menuItem "Copy" (Just "Ctrl+C") true Copy
  , menuItem "Paste" (Just "Ctrl+V") true Paste
  , menuItem "Duplicate" (Just "Ctrl+D") true Duplicate
  , menuItem "Delete" (Just "Delete") true Delete
  , separator
  , menuItem "Select All" (Just "Ctrl+A") true SelectAll
  , menuItem "Deselect All" (Just "F2") true DeselectAll
  ]

renderCreateMenu :: forall m. Array (H.ComponentHTML Action Slots m)
renderCreateMenu =
  [ menuItem "Solid" Nothing true CreateSolid
  , menuItem "Text" (Just "T") true CreateText
  , menuItem "Shape" (Just "P") true CreateShape
  , menuItem "Path" Nothing true CreatePath
  , separator
  , menuItem "Camera" Nothing true CreateCamera
  , menuItem "Light" Nothing true CreateLight
  , menuItem "Control (Null)" Nothing true CreateControl
  , separator
  , menuItem "Particle System" Nothing true CreateParticle
  , menuItem "Depth Map" Nothing true CreateDepth
  , menuItem "Normal Map" Nothing true CreateNormal
  , menuItem "AI Generated" Nothing true CreateGenerated
  , separator
  , menuItem "Group" Nothing true CreateGroup
  , menuItem "Effect Layer" Nothing true CreateEffectLayer
  , menuItem "Procedural Matte" Nothing true CreateMatte
  ]

renderEffectsMenu :: forall m. Array (H.ComponentHTML Action Slots m)
renderEffectsMenu =
  [ sectionLabel "Blur & Sharpen"
  , menuItem "Gaussian Blur" Nothing true (ApplyEffect "gaussian-blur")
  , menuItem "Directional Blur" Nothing true (ApplyEffect "directional-blur")
  , menuItem "Radial Blur" Nothing true (ApplyEffect "radial-blur")
  , menuItem "Sharpen" Nothing true (ApplyEffect "sharpen")
  , separator
  , sectionLabel "Color Correction"
  , menuItem "Brightness/Contrast" Nothing true (ApplyEffect "brightness-contrast")
  , menuItem "Hue/Saturation" Nothing true (ApplyEffect "hue-saturation")
  , menuItem "Levels" Nothing true (ApplyEffect "levels")
  , menuItem "Curves" Nothing true (ApplyEffect "curves")
  , separator
  , sectionLabel "Light & Glow"
  , menuItem "Glow" Nothing true (ApplyEffect "glow")
  , menuItem "Drop Shadow" Nothing true (ApplyEffect "drop-shadow")
  , menuItem "Vignette" Nothing true (ApplyEffect "vignette")
  , separator
  , sectionLabel "Distort"
  , menuItem "Transform" Nothing true (ApplyEffect "transform")
  , menuItem "Warp" Nothing true (ApplyEffect "warp")
  , menuItem "Displacement Map" Nothing true (ApplyEffect "displacement-map")
  , separator
  , sectionLabel "Stylize"
  , menuItem "Glitch" Nothing true (ApplyEffect "glitch")
  , menuItem "RGB Split" Nothing true (ApplyEffect "rgb-split")
  , menuItem "Halftone" Nothing true (ApplyEffect "halftone")
  , separator
  , sectionLabel "Generate"
  , menuItem "Fill" Nothing true (ApplyEffect "fill")
  , menuItem "Gradient Ramp" Nothing true (ApplyEffect "gradient-ramp")
  , menuItem "Fractal Noise" Nothing true (ApplyEffect "fractal-noise")
  ]

renderLayerMenu :: forall m. State -> Array (H.ComponentHTML Action Slots m)
renderLayerMenu state =
  [ menuItem "Pre-compose..." (Just "Ctrl+Shift+C") state.hasSelection Precompose
  , separator
  , menuItem "Split Layer" (Just "Ctrl+Shift+D") state.hasSelection SplitLayer
  , menuItem "Time Stretch..." (Just "Ctrl+Alt+T") state.hasSelection TimeStretch
  , menuItem "Time Reverse" (Just "Ctrl+Alt+R") state.hasSelection TimeReverse
  , menuItem "Freeze Frame" (Just "Ctrl+Shift+F") state.hasSelection FreezeFrame
  , separator
  , menuItem "Lock Layer" (Just "Ctrl+L") state.hasSelection LockLayer
  , menuItem "Show/Hide Layer" Nothing state.hasSelection ToggleVisibility
  , menuItem "Isolate (Solo)" Nothing state.hasSelection IsolateLayer
  , separator
  , menuItem "Bring to Front" (Just "Ctrl+Shift+]") state.hasSelection BringToFront
  , menuItem "Send to Back" (Just "Ctrl+Shift+[") state.hasSelection SendToBack
  , menuItem "Bring Forward" (Just "Ctrl+]") state.hasSelection BringForward
  , menuItem "Send Backward" (Just "Ctrl+[") state.hasSelection SendBackward
  ]

renderViewMenu :: forall m. Array (H.ComponentHTML Action Slots m)
renderViewMenu =
  [ menuItem "Zoom In" (Just "Ctrl+=") true ZoomIn
  , menuItem "Zoom Out" (Just "Ctrl+-") true ZoomOut
  , menuItem "Fit in Window" (Just "Ctrl+0") true ZoomFit
  , menuItem "100%" (Just "Ctrl+Shift+0") true Zoom100
  , separator
  , menuItem "Show Grid" (Just "Ctrl+'") true ToggleGrid
  , menuItem "Show Rulers" (Just "Ctrl+R") true ToggleRulers
  , menuItem "Show Guides" (Just "Ctrl+;") true ToggleGuides
  , menuItem "Safe Zones" Nothing true ToggleSafeZones
  , separator
  , menuItem "Curve Editor" (Just "Shift+G") true ToggleCurveEditor
  ]

renderWindowMenu :: forall m. Array (H.ComponentHTML Action Slots m)
renderWindowMenu =
  [ menuItem "Properties" Nothing true ShowProperties
  , menuItem "Effects" Nothing true ShowEffects
  , menuItem "Camera" Nothing true ShowCamera
  , menuItem "Audio" Nothing true ShowAudio
  , menuItem "Align" Nothing true ShowAlign
  , separator
  , menuItem "AI Chat" Nothing true ShowAIChat
  , menuItem "AI Generate" Nothing true ShowAIGenerate
  , separator
  , menuItem "Export" Nothing true ShowExport
  , menuItem "Preview" Nothing true ShowPreview
  ]

renderHelpMenu :: forall m. Array (H.ComponentHTML Action Slots m)
renderHelpMenu =
  [ menuItem "Keyboard Shortcuts" (Just "Ctrl+/") true ShowKeyboardShortcuts
  , menuItem "Documentation" Nothing true ShowDocumentation
  , separator
  , menuItem "About Lattice Compositor" Nothing true ShowAbout
  ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // helpers
-- ════════════════════════════════════════════════════════════════════════════

menuItem :: forall m. String -> Maybe String -> Boolean -> MenuAction -> H.ComponentHTML Action Slots m
menuItem label shortcut enabled action =
  HH.button
    [ cls [ "lattice-menu-item-btn" ]
    , HP.disabled (not enabled)
    , HE.onClick \_ -> SelectAction action
    ]
    [ HH.span [ cls [ "lattice-menu-label" ] ] [ HH.text label ]
    , case shortcut of
        Just s -> HH.span [ cls [ "lattice-menu-shortcut" ] ] [ HH.text s ]
        Nothing -> HH.text ""
    ]

separator :: forall m. H.ComponentHTML Action Slots m
separator = HH.div [ cls [ "lattice-menu-separator" ] ] []

sectionLabel :: forall m. String -> H.ComponentHTML Action Slots m
sectionLabel label =
  HH.div [ cls [ "lattice-menu-section-label" ] ] [ HH.text label ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

menuBarStyle :: String
menuBarStyle =
  "display: flex; align-items: center; height: 28px; " <>
  "background: var(--lattice-surface-0); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle); " <>
  "padding: 0 8px; font-size: 12px; font-weight: 500; user-select: none;"

dropdownStyle :: String
dropdownStyle =
  "position: absolute; top: 100%; left: 0; min-width: 220px; " <>
  "background: var(--lattice-surface-1); " <>
  "border: 1px solid var(--lattice-border-subtle); " <>
  "border-radius: 6px; padding: 4px 0; " <>
  "box-shadow: 0 8px 24px rgba(0, 0, 0, 0.4); z-index: 1000;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> 
    H.modify_ _ 
      { projectName = input.projectName
      , hasUnsavedChanges = input.hasUnsavedChanges
      , canUndo = input.canUndo
      , canRedo = input.canRedo
      , hasSelection = input.hasSelection
      }
  
  ToggleMenu menu -> 
    H.modify_ \s -> s { activeMenu = if s.activeMenu == menu then MenuNone else menu }
  
  OpenMenu menu -> do
    state <- H.get
    -- Only open on hover if a menu is already open
    when (state.activeMenu /= MenuNone) $
      H.modify_ _ { activeMenu = menu }
  
  CloseMenu -> 
    H.modify_ _ { activeMenu = MenuNone }
  
  SelectAction action -> do
    H.modify_ _ { activeMenu = MenuNone }
    H.raise (MenuActionSelected action)
