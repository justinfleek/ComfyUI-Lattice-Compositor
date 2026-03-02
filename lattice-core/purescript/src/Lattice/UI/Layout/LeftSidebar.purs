-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // lattice // ui // left-sidebar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- |
-- | Left Sidebar Component
-- |
-- | Tabbed sidebar with Project, Effects, and Assets panels.
-- | Emits Output for parent to handle via Bridge to Haskell backend.
-- |
-- | Tabs:
-- | - Project: Composition tree, layer hierarchy
-- | - Effects: Effect library browser
-- | - Assets: Asset manager (images, video, audio, meshes)
-- |
module Lattice.UI.Layout.LeftSidebar
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , LeftTab(..)
  , SidebarAction(..)
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

data LeftTab
  = TabProject
  | TabEffects
  | TabAssets

derive instance eqLeftTab :: Eq LeftTab

type Input =
  { activeTab :: LeftTab
  , projectName :: String
  , compositionCount :: Int
  , assetCount :: Int
  }

-- | Actions emitted from sidebar
data SidebarAction
  = TabChanged LeftTab
  | OpenCompositionSettings
  | CreateLayersFromSvg String
  | UseMeshAsEmitter String
  | EnvironmentUpdate String
  | EnvironmentLoad String
  | EnvironmentClear
  | SelectComposition String
  | SelectAsset String
  | ApplyEffectFromLibrary String

data Output = SidebarActionSelected SidebarAction

data Query a

type Slot id = H.Slot Query Output id

type State =
  { activeTab :: LeftTab
  , projectName :: String
  , compositionCount :: Int
  , assetCount :: Int
  }

data Action
  = Initialize
  | Receive Input
  | SwitchTab LeftTab
  | EmitAction SidebarAction

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
  { activeTab: input.activeTab
  , projectName: input.projectName
  , compositionCount: input.compositionCount
  , assetCount: input.assetCount
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-left-sidebar" ]
    , HP.attr (HH.AttrName "style") sidebarStyle
    ]
    [ -- Tab bar
      HH.div
        [ cls [ "lattice-sidebar-tabs" ]
        , HP.attr (HH.AttrName "style") tabBarStyle
        , HP.attr (HH.AttrName "role") "tablist"
        , HP.attr (HH.AttrName "aria-label") "Left panel tabs"
        ]
        [ tabButton state TabProject "Project"
        , tabButton state TabEffects "Effects"
        , tabButton state TabAssets "Assets"
        ]
    
    , -- Tab content
      HH.div
        [ cls [ "lattice-sidebar-content" ]
        , HP.attr (HH.AttrName "style") contentStyle
        , HP.attr (HH.AttrName "role") "tabpanel"
        , HP.id ("left-panel-" <> tabId state.activeTab)
        ]
        [ case state.activeTab of
            TabProject -> renderProjectPanel state
            TabEffects -> renderEffectsPanel
            TabAssets -> renderAssetsPanel
        ]
    ]

tabButton :: forall m. State -> LeftTab -> String -> H.ComponentHTML Action Slots m
tabButton state tab label =
  HH.button
    [ cls [ "lattice-tab-btn" ]
    , HP.attr (HH.AttrName "role") "tab"
    , HP.attr (HH.AttrName "aria-selected") (if state.activeTab == tab then "true" else "false")
    , HP.attr (HH.AttrName "aria-controls") ("left-panel-" <> tabId tab)
    , HP.attr (HH.AttrName "style") (tabButtonStyle (state.activeTab == tab))
    , HE.onClick \_ -> SwitchTab tab
    ]
    [ HH.text label ]

tabId :: LeftTab -> String
tabId = case _ of
  TabProject -> "project"
  TabEffects -> "effects"
  TabAssets -> "assets"

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // project panel
-- ════════════════════════════════════════════════════════════════════════════

renderProjectPanel :: forall m. State -> H.ComponentHTML Action Slots m
renderProjectPanel state =
  HH.div [ cls [ "lattice-project-panel" ] ]
    [ -- Panel header with settings button
      HH.div
        [ cls [ "lattice-panel-header" ]
        , HP.attr (HH.AttrName "style") panelHeaderStyle
        ]
        [ HH.span [] [ HH.text state.projectName ]
        , HH.button
            [ cls [ "lattice-icon-btn" ]
            , HP.title "Composition Settings"
            , HP.attr (HH.AttrName "style") iconBtnStyle
            , HE.onClick \_ -> EmitAction OpenCompositionSettings
            ]
            [ HH.text "⚙" ]
        ]
    
    , -- Composition tree section
      HH.div
        [ cls [ "lattice-tree-section" ]
        , HP.attr (HH.AttrName "style") treeSectionStyle
        ]
        [ HH.div
            [ cls [ "lattice-section-header" ]
            , HP.attr (HH.AttrName "style") sectionHeaderStyle
            ]
            [ HH.text "Compositions" ]
        , HH.div [ cls [ "lattice-tree-content" ] ]
            [ -- Placeholder for composition tree - will be populated by parent
              HH.div
                [ cls [ "lattice-tree-item" ]
                , HP.attr (HH.AttrName "style") treeItemStyle
                ]
                [ HH.span [ cls [ "lattice-tree-icon" ] ] [ HH.text "📁" ]
                , HH.span [] [ HH.text "Main Composition" ]
                ]
            , HH.div
                [ cls [ "lattice-tree-item", "lattice-tree-nested" ]
                , HP.attr (HH.AttrName "style") (treeItemStyle <> " padding-left: 24px;")
                ]
                [ HH.span [ cls [ "lattice-tree-icon" ] ] [ HH.text "🎬" ]
                , HH.span [] [ HH.text "Scene 1" ]
                ]
            ]
        ]
    
    , -- Layer hierarchy section
      HH.div
        [ cls [ "lattice-tree-section" ]
        , HP.attr (HH.AttrName "style") treeSectionStyle
        ]
        [ HH.div
            [ cls [ "lattice-section-header" ]
            , HP.attr (HH.AttrName "style") sectionHeaderStyle
            ]
            [ HH.text "Layer Hierarchy" ]
        , HH.div [ cls [ "lattice-tree-content" ] ]
            [ -- Example layers - actual layers come from state
              renderLayerItem "🎨" "Background" false
            , renderLayerItem "📷" "Camera 1" false
            , renderLayerItem "💡" "Light 1" false
            , renderLayerItem "⬜" "Shape Layer" true
            ]
        ]
    ]

renderLayerItem :: forall m. String -> String -> Boolean -> H.ComponentHTML Action Slots m
renderLayerItem iconText name selected =
  HH.div
    [ cls [ "lattice-tree-item" ]
    , HP.attr (HH.AttrName "style") (treeItemStyle <> if selected then " background: var(--lattice-accent-dim);" else "")
    ]
    [ HH.span [ cls [ "lattice-tree-icon" ] ] [ HH.text iconText ]
    , HH.span [] [ HH.text name ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // effects panel
-- ════════════════════════════════════════════════════════════════════════════

renderEffectsPanel :: forall m. H.ComponentHTML Action Slots m
renderEffectsPanel =
  HH.div [ cls [ "lattice-effects-panel" ] ]
    [ -- Search bar
      HH.div
        [ cls [ "lattice-search-bar" ]
        , HP.attr (HH.AttrName "style") searchBarStyle
        ]
        [ HH.input
            [ HP.type_ HP.InputText
            , HP.placeholder "Search effects..."
            , HP.attr (HH.AttrName "style") searchInputStyle
            ]
        ]
    
    , -- Effect categories
      HH.div [ cls [ "lattice-effect-categories" ] ]
        [ renderEffectCategory "Blur & Sharpen" 
            [ "Gaussian Blur", "Directional Blur", "Radial Blur", "Sharpen" ]
        , renderEffectCategory "Color Correction"
            [ "Brightness/Contrast", "Hue/Saturation", "Levels", "Curves" ]
        , renderEffectCategory "Light & Glow"
            [ "Glow", "Drop Shadow", "Vignette", "Light Rays" ]
        , renderEffectCategory "Distort"
            [ "Transform", "Warp", "Displacement Map", "Spherize" ]
        , renderEffectCategory "Stylize"
            [ "Glitch", "RGB Split", "Halftone", "Posterize" ]
        , renderEffectCategory "Generate"
            [ "Fill", "Gradient Ramp", "Fractal Noise", "Grid" ]
        , renderEffectCategory "AI Effects"
            [ "Depth Map", "Normal Map", "Segmentation", "Inpainting" ]
        ]
    ]

renderEffectCategory :: forall m. String -> Array String -> H.ComponentHTML Action Slots m
renderEffectCategory name effects =
  HH.div
    [ cls [ "lattice-effect-category" ]
    , HP.attr (HH.AttrName "style") categoryStyle
    ]
    [ HH.div
        [ cls [ "lattice-category-header" ]
        , HP.attr (HH.AttrName "style") categoryHeaderStyle
        ]
        [ HH.span [ cls [ "lattice-expand-icon" ] ] [ HH.text "▼" ]
        , HH.text name
        ]
    , HH.div [ cls [ "lattice-category-items" ] ]
        (map renderEffectItem effects)
    ]

renderEffectItem :: forall m. String -> H.ComponentHTML Action Slots m
renderEffectItem name =
  HH.div
    [ cls [ "lattice-effect-item" ]
    , HP.attr (HH.AttrName "style") effectItemStyle
    , HE.onClick \_ -> EmitAction (ApplyEffectFromLibrary name)
    ]
    [ HH.text name ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                             // assets panel
-- ════════════════════════════════════════════════════════════════════════════

renderAssetsPanel :: forall m. H.ComponentHTML Action Slots m
renderAssetsPanel =
  HH.div [ cls [ "lattice-assets-panel" ] ]
    [ -- Toolbar
      HH.div
        [ cls [ "lattice-assets-toolbar" ]
        , HP.attr (HH.AttrName "style") assetsToolbarStyle
        ]
        [ HH.button
            [ cls [ "lattice-icon-btn" ]
            , HP.title "Import Asset"
            , HP.attr (HH.AttrName "style") iconBtnStyle
            ]
            [ HH.text "+" ]
        , HH.input
            [ HP.type_ HP.InputText
            , HP.placeholder "Search assets..."
            , HP.attr (HH.AttrName "style") searchInputStyle
            ]
        ]
    
    , -- Asset type filters
      HH.div
        [ cls [ "lattice-asset-filters" ]
        , HP.attr (HH.AttrName "style") assetFiltersStyle
        ]
        [ filterButton "All" true
        , filterButton "Images" false
        , filterButton "Video" false
        , filterButton "Audio" false
        , filterButton "3D" false
        ]
    
    , -- Asset grid
      HH.div
        [ cls [ "lattice-asset-grid" ]
        , HP.attr (HH.AttrName "style") assetGridStyle
        ]
        [ renderAssetThumbnail "image" "background.jpg"
        , renderAssetThumbnail "video" "footage.mp4"
        , renderAssetThumbnail "audio" "music.mp3"
        , renderAssetThumbnail "mesh" "model.glb"
        , renderAssetThumbnail "image" "texture.png"
        , renderAssetThumbnail "svg" "icon.svg"
        ]
    
    , -- Environment section
      HH.div
        [ cls [ "lattice-environment-section" ]
        , HP.attr (HH.AttrName "style") environmentSectionStyle
        ]
        [ HH.div
            [ cls [ "lattice-section-header" ]
            , HP.attr (HH.AttrName "style") sectionHeaderStyle
            ]
            [ HH.text "Environment" ]
        , HH.div [ cls [ "lattice-environment-controls" ] ]
            [ HH.button
                [ cls [ "lattice-btn", "lattice-btn-secondary" ]
                , HP.attr (HH.AttrName "style") envBtnStyle
                , HE.onClick \_ -> EmitAction (EnvironmentLoad "default")
                ]
                [ HH.text "Load HDRI" ]
            , HH.button
                [ cls [ "lattice-btn" ]
                , HP.attr (HH.AttrName "style") envBtnStyle
                , HE.onClick \_ -> EmitAction EnvironmentClear
                ]
                [ HH.text "Clear" ]
            ]
        ]
    ]

filterButton :: forall m. String -> Boolean -> H.ComponentHTML Action Slots m
filterButton label active =
  HH.button
    [ cls [ "lattice-filter-btn" ]
    , HP.attr (HH.AttrName "style") (filterBtnStyle active)
    ]
    [ HH.text label ]

renderAssetThumbnail :: forall m. String -> String -> H.ComponentHTML Action Slots m
renderAssetThumbnail assetType name =
  HH.div
    [ cls [ "lattice-asset-thumb" ]
    , HP.attr (HH.AttrName "style") assetThumbStyle
    , HP.title name
    , HE.onClick \_ -> EmitAction (SelectAsset name)
    ]
    [ HH.div
        [ cls [ "lattice-asset-icon" ]
        , HP.attr (HH.AttrName "style") assetIconStyle
        ]
        [ HH.text (assetIcon assetType) ]
    , HH.div
        [ cls [ "lattice-asset-name" ]
        , HP.attr (HH.AttrName "style") assetNameStyle
        ]
        [ HH.text name ]
    ]

assetIcon :: String -> String
assetIcon = case _ of
  "image" -> "🖼"
  "video" -> "🎬"
  "audio" -> "🎵"
  "mesh" -> "🧊"
  "svg" -> "✏"
  _ -> "📄"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // styles
-- ════════════════════════════════════════════════════════════════════════════

sidebarStyle :: String
sidebarStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1, #121212);"

tabBarStyle :: String
tabBarStyle =
  "display: flex; gap: 0; padding: 0; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333);"

tabButtonStyle :: Boolean -> String
tabButtonStyle active =
  "flex: 1; padding: 6px 8px; background: transparent; border: none; " <>
  "cursor: pointer; font-size: 11px; font-weight: 500; " <>
  "text-transform: uppercase; letter-spacing: 0.5px; " <>
  "transition: all 0.15s ease; " <>
  if active
    then "color: var(--lattice-accent, #8b5cf6); " <>
         "background: var(--lattice-surface-1, #121212); " <>
         "border-bottom: 2px solid var(--lattice-accent, #8b5cf6);"
    else "color: var(--lattice-text-secondary, #888);"

contentStyle :: String
contentStyle =
  "flex: 1; overflow: auto;"

panelHeaderStyle :: String
panelHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 8px 12px; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-bottom: 1px solid var(--lattice-border, #333); " <>
  "font-size: 12px; font-weight: 500;"

iconBtnStyle :: String
iconBtnStyle =
  "padding: 4px 8px; background: transparent; border: none; " <>
  "cursor: pointer; color: var(--lattice-text-secondary, #888); " <>
  "border-radius: 4px; transition: all 0.15s ease;"

treeSectionStyle :: String
treeSectionStyle =
  "padding: 8px 0;"

sectionHeaderStyle :: String
sectionHeaderStyle =
  "padding: 4px 12px; font-size: 10px; font-weight: 600; " <>
  "text-transform: uppercase; letter-spacing: 0.5px; " <>
  "color: var(--lattice-text-tertiary, #666);"

treeItemStyle :: String
treeItemStyle =
  "display: flex; align-items: center; gap: 8px; " <>
  "padding: 4px 12px; cursor: pointer; font-size: 12px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "transition: background 0.15s ease;"

searchBarStyle :: String
searchBarStyle =
  "padding: 8px 12px;"

searchInputStyle :: String
searchInputStyle =
  "width: 100%; padding: 6px 10px; " <>
  "background: var(--lattice-surface-2, #1a1a1a); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "border-radius: 4px; font-size: 12px; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

categoryStyle :: String
categoryStyle =
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);"

categoryHeaderStyle :: String
categoryHeaderStyle =
  "display: flex; align-items: center; gap: 6px; " <>
  "padding: 6px 12px; cursor: pointer; font-size: 11px; " <>
  "font-weight: 500; color: var(--lattice-text-secondary, #888);"

effectItemStyle :: String
effectItemStyle =
  "padding: 4px 12px 4px 28px; cursor: pointer; font-size: 12px; " <>
  "color: var(--lattice-text-primary, #e5e5e5); " <>
  "transition: background 0.15s ease;"

assetsToolbarStyle :: String
assetsToolbarStyle =
  "display: flex; align-items: center; gap: 8px; " <>
  "padding: 8px 12px; border-bottom: 1px solid var(--lattice-border, #333);"

assetFiltersStyle :: String
assetFiltersStyle =
  "display: flex; gap: 4px; padding: 8px 12px; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle, #2a2a2a);"

filterBtnStyle :: Boolean -> String
filterBtnStyle active =
  "padding: 4px 8px; border: none; border-radius: 4px; " <>
  "cursor: pointer; font-size: 10px; transition: all 0.15s ease; " <>
  if active
    then "background: var(--lattice-accent, #8b5cf6); " <>
         "color: var(--lattice-text-primary, #e5e5e5);"
    else "background: var(--lattice-surface-3, #252525); " <>
         "color: var(--lattice-text-secondary, #888);"

assetGridStyle :: String
assetGridStyle =
  "display: grid; grid-template-columns: repeat(3, 1fr); gap: 8px; " <>
  "padding: 12px;"

assetThumbStyle :: String
assetThumbStyle =
  "display: flex; flex-direction: column; align-items: center; " <>
  "padding: 8px; background: var(--lattice-surface-2, #1a1a1a); " <>
  "border-radius: 6px; cursor: pointer; transition: all 0.15s ease;"

assetIconStyle :: String
assetIconStyle =
  "font-size: 24px; margin-bottom: 4px;"

assetNameStyle :: String
assetNameStyle =
  "font-size: 9px; color: var(--lattice-text-secondary, #888); " <>
  "text-overflow: ellipsis; overflow: hidden; white-space: nowrap; " <>
  "max-width: 100%;"

environmentSectionStyle :: String
environmentSectionStyle =
  "padding: 8px 0; border-top: 1px solid var(--lattice-border, #333);"

envBtnStyle :: String
envBtnStyle =
  "padding: 4px 12px; margin: 4px 12px; " <>
  "background: var(--lattice-surface-3, #252525); " <>
  "border: 1px solid var(--lattice-border, #333); " <>
  "border-radius: 4px; cursor: pointer; font-size: 11px; " <>
  "color: var(--lattice-text-primary, #e5e5e5);"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> 
    H.modify_ _ 
      { activeTab = input.activeTab
      , projectName = input.projectName
      , compositionCount = input.compositionCount
      , assetCount = input.assetCount
      }
  
  SwitchTab tab -> do
    H.modify_ _ { activeTab = tab }
    H.raise (SidebarActionSelected (TabChanged tab))
  
  EmitAction action -> 
    H.raise (SidebarActionSelected action)
