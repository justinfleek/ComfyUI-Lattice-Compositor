-- | Assets Panel Component
-- |
-- | Asset management panel with tabbed interface for:
-- | - Materials (PBR material library with presets)
-- | - SVG (imported vector graphics and logos)
-- | - Meshes (3D mesh particles for particle systems)
-- | - Sprites (sprite sheets for animated textures)
-- | - Environment (HDR environment maps)
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/AssetsPanel.vue
module Lattice.UI.Components.AssetsPanel
  ( component
  , Input
  , Output(..)
  , Query(..)
  , Slot
  , AssetTab(..)
  ) where

import Prelude

import Data.Array (filter, length, snoc)
import Data.Array as Array
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA
import Web.Event.Event as Event
import Web.HTML as HTML
import Web.HTML.HTMLElement as HTMLElement
import Web.HTML.Window as Window
import Web.UIEvent.KeyboardEvent as KE

import Lattice.UI.Core (cls, textMuted)
import Lattice.UI.Utils (getElementById)

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                                     // types
-- ════════════════════════════════════════════════════════════════════════════

type Input =
  { materials :: Array Material
  , svgDocuments :: Array SvgDocument
  , meshParticles :: Array MeshParticle
  , spriteSheets :: Array SpriteSheet
  }

data Output
  = MaterialSelected String
  | MaterialCreated String
  | MaterialDeleted String
  | SvgSelected String
  | SvgDeleted String
  | CreateLayersFromSvg String
  | RegisterSvgAsMesh String
  | MeshSelected String
  | MeshDeleted String
  | UseMeshAsEmitter String
  | SpriteSelected String
  | SpriteDeleted String
  | ImportSpriteSheet
  | TabChanged AssetTab

data Query a
  = SetTab AssetTab a
  | RefreshAssets a
  | GetSelectedMaterial (Maybe String -> a)

type Slot id = H.Slot Query Output id

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // asset // types
-- ════════════════════════════════════════════════════════════════════════════

data AssetTab
  = TabMaterials
  | TabSvg
  | TabMeshes
  | TabSprites
  | TabEnvironment

derive instance eqAssetTab :: Eq AssetTab

instance showAssetTab :: Show AssetTab where
  show = case _ of
    TabMaterials -> "materials"
    TabSvg -> "svg"
    TabMeshes -> "meshes"
    TabSprites -> "sprites"
    TabEnvironment -> "environment"

allTabs :: Array AssetTab
allTabs = [ TabMaterials, TabSvg, TabMeshes, TabSprites, TabEnvironment ]

tabLabel :: AssetTab -> String
tabLabel = case _ of
  TabMaterials -> "Materials"
  TabSvg -> "SVG"
  TabMeshes -> "Meshes"
  TabSprites -> "Sprites"
  TabEnvironment -> "Env"

tabIcon :: AssetTab -> String
tabIcon = case _ of
  TabMaterials -> "◉"
  TabSvg -> "✎"
  TabMeshes -> "◇"
  TabSprites -> "▦"
  TabEnvironment -> "☀"

tabTooltip :: AssetTab -> String
tabTooltip = case _ of
  TabMaterials -> "PBR Materials"
  TabSvg -> "SVG Logos & Shapes"
  TabMeshes -> "Mesh Particles"
  TabSprites -> "Sprite Sheets"
  TabEnvironment -> "Environment Map"

type Material =
  { id :: String
  , name :: String
  , color :: String
  , previewUrl :: Maybe String
  }

type SvgDocument =
  { id :: String
  , name :: String
  , pathCount :: Int
  }

data MeshSource
  = MeshPrimitive
  | MeshSvg
  | MeshCustom

derive instance eqMeshSource :: Eq MeshSource

type MeshParticle =
  { id :: String
  , name :: String
  , source :: MeshSource
  , vertexCount :: Int
  , boundingRadius :: Number
  }

type SpriteSheet =
  { id :: String
  , name :: String
  , textureUrl :: String
  , totalFrames :: Int
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // state
-- ════════════════════════════════════════════════════════════════════════════

type State =
  { activeTab :: AssetTab
  , materials :: Array Material
  , svgDocuments :: Array SvgDocument
  , meshParticles :: Array MeshParticle
  , spriteSheets :: Array SpriteSheet
  , selectedMaterialId :: Maybe String
  , selectedSvgId :: Maybe String
  , selectedMeshId :: Maybe String
  , selectedSpriteId :: Maybe String
  , selectedPreset :: String
  , isLoading :: Boolean
  , lastError :: Maybe String
  , baseId :: String
  }

data Action
  = Initialize
  | Receive Input
  | SetActiveTab AssetTab
  | HandleTabKeyDown Int KE.KeyboardEvent
  | SelectMaterial String
  | CreateMaterial
  | DeleteMaterial String
  | SetMaterialPreset String
  | SelectSvg String
  | DeleteSvg String
  | CreateLayersFromSvgAction String
  | RegisterSvgAsMeshAction String
  | SelectMesh String
  | DeleteMesh String
  | UseMeshAsEmitterAction String
  | SelectSprite String
  | DeleteSprite String
  | OpenSpriteImport
  | ClearError

type Slots = ()

-- ════════════════════════════════════════════════════════════════════════════
--                                                          // material presets
-- ════════════════════════════════════════════════════════════════════════════

materialPresets :: Array String
materialPresets =
  [ "chrome"
  , "gold"
  , "silver"
  , "copper"
  , "brass"
  , "glass"
  , "plastic"
  , "rubber"
  , "wood"
  , "concrete"
  , "emissive"
  , "holographic"
  ]

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
  { activeTab: TabMaterials
  , materials: input.materials
  , svgDocuments: input.svgDocuments
  , meshParticles: input.meshParticles
  , spriteSheets: input.spriteSheets
  , selectedMaterialId: Nothing
  , selectedSvgId: Nothing
  , selectedMeshId: Nothing
  , selectedSpriteId: Nothing
  , selectedPreset: ""
  , isLoading: false
  , lastError: Nothing
  , baseId: "lattice-assets"
  }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                    // render
-- ════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-assets-panel" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , ARIA.label "Asset Manager"
    ]
    [ renderTabs state
    , renderContent state
    , renderLoadingOverlay state
    , renderErrorToast state
    ]

renderTabs :: forall m. State -> H.ComponentHTML Action Slots m
renderTabs state =
  HH.div
    [ cls [ "asset-tabs" ]
    , HP.attr (HH.AttrName "style") tabsStyle
    , HP.attr (HH.AttrName "role") "tablist"
    , ARIA.label "Asset type tabs"
    , HP.attr (HH.AttrName "aria-orientation") "horizontal"
    ]
    (Array.mapWithIndex (renderTabButton state) allTabs)

renderTabButton :: forall m. State -> Int -> AssetTab -> H.ComponentHTML Action Slots m
renderTabButton state idx tab =
  let
    isSelected = tab == state.activeTab
    tabId = state.baseId <> "-tab-" <> show tab
    panelId = state.baseId <> "-panel-" <> show tab
  in
  HH.button
    [ cls [ "asset-tab" ]
    , HP.type_ HP.ButtonButton
    , HP.id tabId
    , HP.tabIndex (if isSelected then 0 else (-1))
    , HP.attr (HH.AttrName "style") (tabButtonStyle isSelected)
    , HP.attr (HH.AttrName "title") (tabTooltip tab)
    , HP.attr (HH.AttrName "role") "tab"
    , ARIA.selected (show isSelected)
    , ARIA.controls panelId
    , HP.attr (HH.AttrName "data-state") (if isSelected then "active" else "inactive")
    , HE.onClick \_ -> SetActiveTab tab
    , HE.onKeyDown (HandleTabKeyDown idx)
    ]
    [ HH.span 
        [ cls [ "tab-icon" ]
        , HP.attr (HH.AttrName "style") tabIconStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ] 
        [ HH.text (tabIcon tab) ]
    , HH.span 
        [ cls [ "tab-label" ]
        , HP.attr (HH.AttrName "style") tabLabelStyle
        ] 
        [ HH.text (tabLabel tab) ]
    ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  let
    tabId = state.baseId <> "-tab-" <> show state.activeTab
    panelId = state.baseId <> "-panel-" <> show state.activeTab
  in
  HH.div
    [ cls [ "asset-content" ]
    , HP.id panelId
    , HP.attr (HH.AttrName "style") contentStyle
    , HP.attr (HH.AttrName "role") "tabpanel"
    , HP.tabIndex 0
    , ARIA.labelledBy tabId
    , HP.attr (HH.AttrName "data-state") "active"
    ]
    [ case state.activeTab of
        TabMaterials -> renderMaterialsTab state
        TabSvg -> renderSvgTab state
        TabMeshes -> renderMeshesTab state
        TabSprites -> renderSpritesTab state
        TabEnvironment -> renderEnvironmentTab state
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                       // materials // tab
-- ════════════════════════════════════════════════════════════════════════════

renderMaterialsTab :: forall m. State -> H.ComponentHTML Action Slots m
renderMaterialsTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") tabPanelStyle
    ]
    [ renderMaterialsToolbar state
    , renderMaterialsList state
    ]

renderMaterialsToolbar :: forall m. State -> H.ComponentHTML Action Slots m
renderMaterialsToolbar state =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    ]
    [ HH.button
        [ cls [ "toolbar-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") toolbarBtnStyle
        , HP.attr (HH.AttrName "title") "New Material"
        , HE.onClick \_ -> CreateMaterial
        ]
        [ HH.span [ cls [ "icon" ] ] [ HH.text "+" ]
        , HH.text " New"
        ]
    , HH.select
        [ cls [ "preset-select" ]
        , HP.attr (HH.AttrName "style") selectStyle
        , HP.value state.selectedPreset
        , HE.onValueChange SetMaterialPreset
        ]
        ([ HH.option [ HP.value "" ] [ HH.text "From Preset..." ] ] <>
         map (\p -> HH.option [ HP.value p ] [ HH.text p ]) materialPresets)
    ]

renderMaterialsList :: forall m. State -> H.ComponentHTML Action Slots m
renderMaterialsList state =
  HH.div
    [ cls [ "material-list" ]
    , HP.attr (HH.AttrName "style") listStyle
    , HP.attr (HH.AttrName "role") "listbox"
    , ARIA.label "Materials"
    ]
    (map (renderMaterialItem state) state.materials)

renderMaterialItem :: forall m. State -> Material -> H.ComponentHTML Action Slots m
renderMaterialItem state mat =
  let isSelected = state.selectedMaterialId == Just mat.id
  in
  HH.div
    [ cls [ "material-item" ]
    , HP.attr (HH.AttrName "style") (listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectMaterial mat.id
    ]
    [ HH.div 
        [ cls [ "material-preview" ]
        , HP.attr (HH.AttrName "style") (materialPreviewStyle mat.color mat.previewUrl)
        ] 
        []
    , HH.span 
        [ cls [ "material-name" ]
        , HP.attr (HH.AttrName "style") itemNameStyle
        ] 
        [ HH.text mat.name ]
    , HH.button
        [ cls [ "delete-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") deleteBtnStyle
        , HP.attr (HH.AttrName "title") "Delete"
        , ARIA.label ("Delete " <> mat.name)
        , HE.onClick \_ -> DeleteMaterial mat.id
        ]
        [ HH.text "×" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                           // svg // tab
-- ════════════════════════════════════════════════════════════════════════════

renderSvgTab :: forall m. State -> H.ComponentHTML Action Slots m
renderSvgTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") tabPanelStyle
    ]
    [ renderSvgToolbar
    , renderSvgList state
    ]

renderSvgToolbar :: forall m. H.ComponentHTML Action Slots m
renderSvgToolbar =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    ]
    [ HH.button
        [ cls [ "toolbar-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") toolbarBtnStyle
        , HP.attr (HH.AttrName "title") "Import SVG"
        ]
        [ HH.span [ cls [ "icon" ] ] [ HH.text "+" ]
        , HH.text " Import SVG"
        ]
    ]

renderSvgList :: forall m. State -> H.ComponentHTML Action Slots m
renderSvgList state =
  HH.div
    [ cls [ "svg-list" ]
    , HP.attr (HH.AttrName "style") listStyle
    , HP.attr (HH.AttrName "role") "listbox"
    , ARIA.label "SVG Documents"
    ]
    (map (renderSvgItem state) state.svgDocuments)

renderSvgItem :: forall m. State -> SvgDocument -> H.ComponentHTML Action Slots m
renderSvgItem state svg =
  let isSelected = state.selectedSvgId == Just svg.id
  in
  HH.div
    [ cls [ "svg-item" ]
    , HP.attr (HH.AttrName "style") (listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectSvg svg.id
    ]
    [ HH.div 
        [ cls [ "svg-preview" ]
        , HP.attr (HH.AttrName "style") svgPreviewStyle
        ]
        [ HH.span 
            [ cls [ "path-count" ]
            , HP.attr (HH.AttrName "style") pathCountStyle
            ] 
            [ HH.text (show svg.pathCount <> " paths") ]
        ]
    , HH.span 
        [ cls [ "svg-name" ]
        , HP.attr (HH.AttrName "style") itemNameStyle
        ] 
        [ HH.text svg.name ]
    , HH.div 
        [ cls [ "svg-actions" ]
        , HP.attr (HH.AttrName "style") actionsStyle
        ]
        [ HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") smallActionBtnStyle
            , HP.attr (HH.AttrName "title") "Create Layers"
            , ARIA.label "Create layers from SVG"
            , HE.onClick \_ -> CreateLayersFromSvgAction svg.id
            ]
            [ HH.text "↗" ]
        , HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") smallActionBtnStyle
            , HP.attr (HH.AttrName "title") "Use as Particle"
            , ARIA.label "Register as mesh particle"
            , HE.onClick \_ -> RegisterSvgAsMeshAction svg.id
            ]
            [ HH.text "✦" ]
        , HH.button
            [ cls [ "delete-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") deleteBtnStyle
            , HP.attr (HH.AttrName "title") "Delete"
            , ARIA.label ("Delete " <> svg.name)
            , HE.onClick \_ -> DeleteSvg svg.id
            ]
            [ HH.text "×" ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // meshes // tab
-- ════════════════════════════════════════════════════════════════════════════

renderMeshesTab :: forall m. State -> H.ComponentHTML Action Slots m
renderMeshesTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") tabPanelStyle
    ]
    [ renderMeshesToolbar
    , renderMeshesList state
    , renderMeshDetails state
    ]

renderMeshesToolbar :: forall m. H.ComponentHTML Action Slots m
renderMeshesToolbar =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    ]
    [ HH.select
        [ cls [ "primitive-select" ]
        , HP.attr (HH.AttrName "style") selectStyle
        ]
        [ HH.option [ HP.value "" ] [ HH.text "Add Primitive..." ]
        , HH.option [ HP.value "cube" ] [ HH.text "Cube" ]
        , HH.option [ HP.value "sphere" ] [ HH.text "Sphere" ]
        , HH.option [ HP.value "cone" ] [ HH.text "Cone" ]
        , HH.option [ HP.value "cylinder" ] [ HH.text "Cylinder" ]
        , HH.option [ HP.value "torus" ] [ HH.text "Torus" ]
        , HH.option [ HP.value "tetrahedron" ] [ HH.text "Tetrahedron" ]
        , HH.option [ HP.value "octahedron" ] [ HH.text "Octahedron" ]
        , HH.option [ HP.value "icosahedron" ] [ HH.text "Icosahedron" ]
        ]
    ]

renderMeshesList :: forall m. State -> H.ComponentHTML Action Slots m
renderMeshesList state =
  HH.div
    [ cls [ "mesh-list" ]
    , HP.attr (HH.AttrName "style") listStyle
    , HP.attr (HH.AttrName "role") "listbox"
    , ARIA.label "Mesh Particles"
    ]
    (map (renderMeshItem state) state.meshParticles)

renderMeshItem :: forall m. State -> MeshParticle -> H.ComponentHTML Action Slots m
renderMeshItem state mesh =
  let isSelected = state.selectedMeshId == Just mesh.id
  in
  HH.div
    [ cls [ "mesh-item" ]
    , HP.attr (HH.AttrName "style") (listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectMesh mesh.id
    ]
    [ HH.div 
        [ cls [ "mesh-icon" ]
        , HP.attr (HH.AttrName "style") meshIconStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ]
        [ HH.text (meshSourceIcon mesh.source) ]
    , HH.div 
        [ cls [ "mesh-info" ]
        , HP.attr (HH.AttrName "style") meshInfoStyle
        ]
        [ HH.span [ cls [ "mesh-name" ] ] [ HH.text mesh.name ]
        , HH.span 
            [ cls [ "mesh-verts" ]
            , HP.attr (HH.AttrName "style") meshVertsStyle
            ] 
            [ HH.text (show mesh.vertexCount <> " verts") ]
        ]
    , HH.button
        [ cls [ "delete-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") deleteBtnStyle
        , HP.attr (HH.AttrName "title") "Delete"
        , ARIA.label ("Delete " <> mesh.name)
        , HE.onClick \_ -> DeleteMesh mesh.id
        ]
        [ HH.text "×" ]
    ]

meshSourceIcon :: MeshSource -> String
meshSourceIcon = case _ of
  MeshPrimitive -> "◇"
  MeshSvg -> "◈"
  MeshCustom -> "◆"

renderMeshDetails :: forall m. State -> H.ComponentHTML Action Slots m
renderMeshDetails state =
  case findSelected state.selectedMeshId state.meshParticles of
    Nothing -> HH.text ""
    Just mesh ->
      HH.div
        [ cls [ "mesh-details" ]
        , HP.attr (HH.AttrName "style") detailsStyle
        ]
        [ HH.h4 [ HP.attr (HH.AttrName "style") detailsTitleStyle ] [ HH.text mesh.name ]
        , renderDetailRow "Source" (meshSourceLabel mesh.source)
        , renderDetailRow "Vertices" (show mesh.vertexCount)
        , renderDetailRow "Bounding Radius" (formatNumber mesh.boundingRadius)
        , HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") fullWidthBtnStyle
            , HE.onClick \_ -> UseMeshAsEmitterAction mesh.id
            ]
            [ HH.text "Use as Emitter Shape" ]
        ]

meshSourceLabel :: MeshSource -> String
meshSourceLabel = case _ of
  MeshPrimitive -> "primitive"
  MeshSvg -> "svg"
  MeshCustom -> "custom"

findSelected :: forall a. Maybe String -> Array { id :: String | a } -> Maybe { id :: String | a }
findSelected mId items =
  case mId of
    Nothing -> Nothing
    Just id -> Array.find (\item -> item.id == id) items

renderDetailRow :: forall m. String -> String -> H.ComponentHTML Action Slots m
renderDetailRow label value =
  HH.div
    [ cls [ "detail-row" ]
    , HP.attr (HH.AttrName "style") detailRowStyle
    ]
    [ HH.span [ cls [ "label" ], HP.attr (HH.AttrName "style") detailLabelStyle ] [ HH.text label ]
    , HH.span [ cls [ "value" ] ] [ HH.text value ]
    ]

formatNumber :: Number -> String
formatNumber n = show n

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // sprites // tab
-- ════════════════════════════════════════════════════════════════════════════

renderSpritesTab :: forall m. State -> H.ComponentHTML Action Slots m
renderSpritesTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") tabPanelStyle
    ]
    [ renderSpritesToolbar
    , renderSpritesList state
    ]

renderSpritesToolbar :: forall m. H.ComponentHTML Action Slots m
renderSpritesToolbar =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") toolbarStyle
    ]
    [ HH.button
        [ cls [ "toolbar-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") toolbarBtnStyle
        , HP.attr (HH.AttrName "title") "Import Sprite Sheet"
        , HE.onClick \_ -> OpenSpriteImport
        ]
        [ HH.span [ cls [ "icon" ] ] [ HH.text "+" ]
        , HH.text " Import"
        ]
    ]

renderSpritesList :: forall m. State -> H.ComponentHTML Action Slots m
renderSpritesList state =
  HH.div
    [ cls [ "sprite-list" ]
    , HP.attr (HH.AttrName "style") listStyle
    , HP.attr (HH.AttrName "role") "listbox"
    , ARIA.label "Sprite Sheets"
    ]
    (map (renderSpriteItem state) state.spriteSheets)

renderSpriteItem :: forall m. State -> SpriteSheet -> H.ComponentHTML Action Slots m
renderSpriteItem state sprite =
  let isSelected = state.selectedSpriteId == Just sprite.id
  in
  HH.div
    [ cls [ "sprite-item" ]
    , HP.attr (HH.AttrName "style") (listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectSprite sprite.id
    ]
    [ HH.img
        [ HP.src sprite.textureUrl
        , HP.alt sprite.name
        , cls [ "sprite-preview" ]
        , HP.attr (HH.AttrName "style") spritePreviewStyle
        ]
    , HH.div 
        [ cls [ "sprite-info" ]
        , HP.attr (HH.AttrName "style") spriteInfoStyle
        ]
        [ HH.span [ cls [ "sprite-name" ] ] [ HH.text sprite.name ]
        , HH.span 
            [ cls [ "sprite-frames" ]
            , HP.attr (HH.AttrName "style") spriteFramesStyle
            ] 
            [ HH.text (show sprite.totalFrames <> " frames") ]
        ]
    , HH.button
        [ cls [ "delete-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") deleteBtnStyle
        , HP.attr (HH.AttrName "title") "Delete"
        , ARIA.label ("Delete " <> sprite.name)
        , HE.onClick \_ -> DeleteSprite sprite.id
        ]
        [ HH.text "×" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                      // environment // tab
-- ════════════════════════════════════════════════════════════════════════════

renderEnvironmentTab :: forall m. State -> H.ComponentHTML Action Slots m
renderEnvironmentTab _state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") tabPanelStyle
    ]
    [ HH.div 
        [ cls [ "environment-placeholder" ]
        , HP.attr (HH.AttrName "style") placeholderStyle
        ]
        [ textMuted "Environment settings will appear here"
        , HH.p [ cls [ "hint" ] ] 
            [ textMuted "Load an HDR environment map for PBR lighting" ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // overlays
-- ════════════════════════════════════════════════════════════════════════════

renderLoadingOverlay :: forall m. State -> H.ComponentHTML Action Slots m
renderLoadingOverlay state =
  if state.isLoading
    then
      HH.div
        [ cls [ "loading-overlay" ]
        , HP.attr (HH.AttrName "style") loadingOverlayStyle
        , HP.attr (HH.AttrName "role") "alert"
        , ARIA.busy "true"
        ]
        [ HH.div [ cls [ "spinner" ], HP.attr (HH.AttrName "style") spinnerStyle ] []
        , HH.span_ [ HH.text "Loading..." ]
        ]
    else HH.text ""

renderErrorToast :: forall m. State -> H.ComponentHTML Action Slots m
renderErrorToast state =
  case state.lastError of
    Nothing -> HH.text ""
    Just err ->
      HH.div
        [ cls [ "error-toast" ]
        , HP.attr (HH.AttrName "style") errorToastStyle
        , HP.attr (HH.AttrName "role") "alert"
        , HE.onClick \_ -> ClearError
        ]
        [ HH.text err ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // styles
-- ════════════════════════════════════════════════════════════════════════════

panelStyle :: String
panelStyle =
  "display: flex; flex-direction: column; height: 100%; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); " <>
  "font-size: 13px; position: relative;"

tabsStyle :: String
tabsStyle =
  "display: flex; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle); overflow-x: auto;"

tabButtonStyle :: Boolean -> String
tabButtonStyle active =
  "flex: 1; min-width: 50px; padding: 6px 4px; border: none; " <>
  "background: transparent; cursor: pointer; " <>
  "border-bottom: 2px solid " <> (if active then "var(--lattice-accent)" else "transparent") <> "; " <>
  "display: flex; flex-direction: column; align-items: center; gap: 2px; " <>
  "color: " <> (if active then "var(--lattice-accent)" else "var(--lattice-text-muted)") <> "; " <>
  "font-size: 12px;"

tabIconStyle :: String
tabIconStyle = "font-size: 14px;"

tabLabelStyle :: String
tabLabelStyle = "font-size: 11px;"

contentStyle :: String
contentStyle = "flex: 1; overflow: hidden;"

tabPanelStyle :: String
tabPanelStyle =
  "height: 100%; display: flex; flex-direction: column; overflow: hidden;"

toolbarStyle :: String
toolbarStyle =
  "display: flex; gap: 4px; padding: 6px; " <>
  "background: var(--lattice-surface-2); border-bottom: 1px solid var(--lattice-border-subtle);"

toolbarBtnStyle :: String
toolbarBtnStyle =
  "padding: 4px 8px; background: var(--lattice-surface-3); border: none; " <>
  "color: var(--lattice-text-primary); border-radius: 3px; cursor: pointer; font-size: 12px;"

selectStyle :: String
selectStyle =
  "flex: 1; padding: 4px; background: var(--lattice-surface-0); " <>
  "border: 1px solid var(--lattice-border-default); color: var(--lattice-text-primary); " <>
  "border-radius: 3px; font-size: 12px;"

listStyle :: String
listStyle = "flex: 1; overflow-y: auto; padding: 4px;"

listItemStyle :: Boolean -> String
listItemStyle selected =
  "display: flex; align-items: center; gap: 8px; padding: 6px; " <>
  "background: " <> (if selected then "var(--lattice-accent-muted)" else "var(--lattice-surface-2)") <> "; " <>
  "border-radius: 4px; margin-bottom: 4px; cursor: pointer; " <>
  (if selected then "border: 1px solid var(--lattice-accent);" else "")

materialPreviewStyle :: String -> Maybe String -> String
materialPreviewStyle color mUrl =
  "width: 32px; height: 32px; border-radius: 4px; " <>
  "border: 1px solid var(--lattice-border-default); " <>
  "background-color: " <> color <> "; " <>
  case mUrl of
    Just url -> "background-image: url(" <> url <> "); background-size: cover;"
    Nothing -> ""

itemNameStyle :: String
itemNameStyle =
  "flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap;"

deleteBtnStyle :: String
deleteBtnStyle =
  "padding: 2px 6px; background: transparent; border: none; " <>
  "color: var(--lattice-text-muted); cursor: pointer; border-radius: 3px;"

svgPreviewStyle :: String
svgPreviewStyle =
  "width: 40px; height: 40px; background: var(--lattice-surface-0); " <>
  "border-radius: 4px; display: flex; align-items: center; justify-content: center;"

pathCountStyle :: String
pathCountStyle = "font-size: 11px; color: var(--lattice-text-muted);"

actionsStyle :: String
actionsStyle = "display: flex; gap: 2px;"

smallActionBtnStyle :: String
smallActionBtnStyle =
  "padding: 2px 6px; background: var(--lattice-surface-3); border: none; " <>
  "color: var(--lattice-text-secondary); cursor: pointer; border-radius: 3px; font-size: 12px;"

meshIconStyle :: String
meshIconStyle =
  "width: 32px; height: 32px; background: var(--lattice-surface-0); " <>
  "border-radius: 4px; display: flex; align-items: center; justify-content: center; " <>
  "font-size: 18px; color: var(--lattice-accent);"

meshInfoStyle :: String
meshInfoStyle = "flex: 1; display: flex; flex-direction: column;"

meshVertsStyle :: String
meshVertsStyle = "font-size: 11px; color: var(--lattice-text-muted);"

detailsStyle :: String
detailsStyle =
  "padding: 8px; background: var(--lattice-surface-2); " <>
  "border-top: 1px solid var(--lattice-border-subtle);"

detailsTitleStyle :: String
detailsTitleStyle =
  "margin: 0 0 8px; font-size: 13px; color: var(--lattice-text-secondary);"

detailRowStyle :: String
detailRowStyle =
  "display: flex; justify-content: space-between; padding: 4px 0; " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

detailLabelStyle :: String
detailLabelStyle = "color: var(--lattice-text-muted);"

fullWidthBtnStyle :: String
fullWidthBtnStyle =
  "width: 100%; margin-top: 8px; padding: 8px; " <>
  "background: var(--lattice-accent); border: none; color: white; " <>
  "border-radius: 4px; cursor: pointer;"

spritePreviewStyle :: String
spritePreviewStyle =
  "width: 48px; height: 48px; object-fit: contain; " <>
  "background: var(--lattice-surface-0); border-radius: 4px;"

spriteInfoStyle :: String
spriteInfoStyle = "flex: 1; display: flex; flex-direction: column;"

spriteFramesStyle :: String
spriteFramesStyle = "font-size: 11px; color: var(--lattice-text-muted);"

placeholderStyle :: String
placeholderStyle =
  "display: flex; flex-direction: column; align-items: center; justify-content: center; " <>
  "height: 100%; gap: 8px; color: var(--lattice-text-muted);"

loadingOverlayStyle :: String
loadingOverlayStyle =
  "position: absolute; inset: 0; background: rgba(0, 0, 0, 0.7); " <>
  "display: flex; flex-direction: column; align-items: center; justify-content: center; " <>
  "gap: 12px; z-index: 100;"

spinnerStyle :: String
spinnerStyle =
  "width: 32px; height: 32px; border: 3px solid var(--lattice-border-default); " <>
  "border-top-color: var(--lattice-accent); border-radius: 50%; " <>
  "animation: spin 1s linear infinite;"

errorToastStyle :: String
errorToastStyle =
  "position: absolute; bottom: 12px; left: 12px; right: 12px; " <>
  "padding: 12px; background: #c62828; color: white; border-radius: 4px; " <>
  "cursor: pointer; z-index: 101;"

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // actions
-- ════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    H.modify_ _ 
      { materials = input.materials
      , svgDocuments = input.svgDocuments
      , meshParticles = input.meshParticles
      , spriteSheets = input.spriteSheets
      }
  
  SetActiveTab tab -> do
    H.modify_ _ { activeTab = tab }
    H.raise (TabChanged tab)
  
  HandleTabKeyDown currentIdx ke -> do
    state <- H.get
    let
      key = KE.key ke
      tabCount = Array.length allTabs
      
      nextIdx = case key of
        "ArrowRight" -> Just ((currentIdx + 1) `mod` tabCount)
        "ArrowLeft" -> Just ((currentIdx - 1 + tabCount) `mod` tabCount)
        "Home" -> Just 0
        "End" -> Just (tabCount - 1)
        _ -> Nothing

    for_ nextIdx \idx -> do
      liftEffect $ Event.preventDefault (KE.toEvent ke)
      case Array.index allTabs idx of
        Just tab -> do
          doc <- liftEffect $ HTML.window >>= Window.document
          let tabId = state.baseId <> "-tab-" <> show tab
          mEl <- liftEffect $ getElementById tabId doc
          for_ mEl \el -> liftEffect $ HTMLElement.focus el
          handleAction (SetActiveTab tab)
        Nothing -> pure unit
  
  SelectMaterial id -> do
    H.modify_ _ { selectedMaterialId = Just id }
    H.raise (MaterialSelected id)
  
  CreateMaterial -> do
    H.raise (MaterialCreated "new-material")
  
  DeleteMaterial id -> do
    state <- H.get
    when (state.selectedMaterialId == Just id) do
      H.modify_ _ { selectedMaterialId = Nothing }
    H.raise (MaterialDeleted id)
  
  SetMaterialPreset preset -> do
    H.modify_ _ { selectedPreset = preset }
    when (preset /= "") do
      H.raise (MaterialCreated preset)
      H.modify_ _ { selectedPreset = "" }
  
  SelectSvg id -> do
    H.modify_ _ { selectedSvgId = Just id }
    H.raise (SvgSelected id)
  
  DeleteSvg id -> do
    state <- H.get
    when (state.selectedSvgId == Just id) do
      H.modify_ _ { selectedSvgId = Nothing }
    H.raise (SvgDeleted id)
  
  CreateLayersFromSvgAction id -> do
    H.raise (CreateLayersFromSvg id)
  
  RegisterSvgAsMeshAction id -> do
    H.raise (RegisterSvgAsMesh id)
    H.modify_ _ { activeTab = TabMeshes }
  
  SelectMesh id -> do
    H.modify_ _ { selectedMeshId = Just id }
    H.raise (MeshSelected id)
  
  DeleteMesh id -> do
    state <- H.get
    when (state.selectedMeshId == Just id) do
      H.modify_ _ { selectedMeshId = Nothing }
    H.raise (MeshDeleted id)
  
  UseMeshAsEmitterAction id -> do
    H.raise (UseMeshAsEmitter id)
  
  SelectSprite id -> do
    H.modify_ _ { selectedSpriteId = Just id }
    H.raise (SpriteSelected id)
  
  DeleteSprite id -> do
    state <- H.get
    when (state.selectedSpriteId == Just id) do
      H.modify_ _ { selectedSpriteId = Nothing }
    H.raise (SpriteDeleted id)
  
  OpenSpriteImport -> do
    H.raise ImportSpriteSheet
  
  ClearError -> do
    H.modify_ _ { lastError = Nothing }

-- ════════════════════════════════════════════════════════════════════════════
--                                                                   // queries
-- ════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  SetTab tab next -> do
    handleAction (SetActiveTab tab)
    pure (Just next)
  
  RefreshAssets next -> do
    -- Parent would typically refresh via input props
    pure (Just next)
  
  GetSelectedMaterial reply -> do
    state <- H.get
    pure (Just (reply state.selectedMaterialId))


