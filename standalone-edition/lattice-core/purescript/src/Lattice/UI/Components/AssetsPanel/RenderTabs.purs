-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Assets Panel Tab Render Functions
-- |
-- | Render functions for individual asset tabs (Materials, SVG, Meshes, etc.)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.AssetsPanel.RenderTabs
  ( renderMaterialsTab
  , renderSvgTab
  , renderMeshesTab
  , renderSpritesTab
  , renderEnvironmentTab
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Properties.ARIA as ARIA

import Lattice.UI.Core (cls, textMuted)

import Lattice.UI.Components.AssetsPanel.Types
  ( State
  , Action(..)
  , Slots
  , Material
  , SvgDocument
  , MeshParticle
  , SpriteSheet
  , materialPresets
  , meshSourceIcon
  , meshSourceLabel
  , findSelected
  , formatNumber
  )
import Lattice.UI.Components.AssetsPanel.Styles as S

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                          // materials tab
-- ════════════════════════════════════════════════════════════════════════════

renderMaterialsTab :: forall m. State -> H.ComponentHTML Action Slots m
renderMaterialsTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") S.tabPanelStyle
    ]
    [ renderMaterialsToolbar state
    , renderMaterialsList state
    ]

renderMaterialsToolbar :: forall m. State -> H.ComponentHTML Action Slots m
renderMaterialsToolbar state =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") S.toolbarStyle
    ]
    [ HH.button
        [ cls [ "toolbar-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") S.toolbarBtnStyle
        , HP.attr (HH.AttrName "title") "New Material"
        , HE.onClick \_ -> CreateMaterial
        ]
        [ HH.span [ cls [ "icon" ] ] [ HH.text "+" ]
        , HH.text " New"
        ]
    , HH.select
        [ cls [ "preset-select" ]
        , HP.attr (HH.AttrName "style") S.selectStyle
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
    , HP.attr (HH.AttrName "style") S.listStyle
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
    , HP.attr (HH.AttrName "style") (S.listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectMaterial mat.id
    ]
    [ HH.div 
        [ cls [ "material-preview" ]
        , HP.attr (HH.AttrName "style") (S.materialPreviewStyle mat.color mat.previewUrl)
        ] 
        []
    , HH.span 
        [ cls [ "material-name" ]
        , HP.attr (HH.AttrName "style") S.itemNameStyle
        ] 
        [ HH.text mat.name ]
    , HH.button
        [ cls [ "delete-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") S.deleteBtnStyle
        , HP.attr (HH.AttrName "title") "Delete"
        , ARIA.label ("Delete " <> mat.name)
        , HE.onClick \_ -> DeleteMaterial mat.id
        ]
        [ HH.text "x" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                               // svg tab
-- ════════════════════════════════════════════════════════════════════════════

renderSvgTab :: forall m. State -> H.ComponentHTML Action Slots m
renderSvgTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") S.tabPanelStyle
    ]
    [ renderSvgToolbar
    , renderSvgList state
    ]

renderSvgToolbar :: forall m. H.ComponentHTML Action Slots m
renderSvgToolbar =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") S.toolbarStyle
    ]
    [ HH.button
        [ cls [ "toolbar-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") S.toolbarBtnStyle
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
    , HP.attr (HH.AttrName "style") S.listStyle
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
    , HP.attr (HH.AttrName "style") (S.listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectSvg svg.id
    ]
    [ HH.div 
        [ cls [ "svg-preview" ]
        , HP.attr (HH.AttrName "style") S.svgPreviewStyle
        ]
        [ HH.span 
            [ cls [ "path-count" ]
            , HP.attr (HH.AttrName "style") S.pathCountStyle
            ] 
            [ HH.text (show svg.pathCount <> " paths") ]
        ]
    , HH.span 
        [ cls [ "svg-name" ]
        , HP.attr (HH.AttrName "style") S.itemNameStyle
        ] 
        [ HH.text svg.name ]
    , HH.div 
        [ cls [ "svg-actions" ]
        , HP.attr (HH.AttrName "style") S.actionsStyle
        ]
        [ HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") S.smallActionBtnStyle
            , HP.attr (HH.AttrName "title") "Create Layers"
            , ARIA.label "Create layers from SVG"
            , HE.onClick \_ -> CreateLayersFromSvgAction svg.id
            ]
            [ HH.text "L" ]
        , HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") S.smallActionBtnStyle
            , HP.attr (HH.AttrName "title") "Use as Particle"
            , ARIA.label "Register as mesh particle"
            , HE.onClick \_ -> RegisterSvgAsMeshAction svg.id
            ]
            [ HH.text "P" ]
        , HH.button
            [ cls [ "delete-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") S.deleteBtnStyle
            , HP.attr (HH.AttrName "title") "Delete"
            , ARIA.label ("Delete " <> svg.name)
            , HE.onClick \_ -> DeleteSvg svg.id
            ]
            [ HH.text "x" ]
        ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // meshes tab
-- ════════════════════════════════════════════════════════════════════════════

renderMeshesTab :: forall m. State -> H.ComponentHTML Action Slots m
renderMeshesTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") S.tabPanelStyle
    ]
    [ renderMeshesToolbar
    , renderMeshesList state
    , renderMeshDetails state
    ]

renderMeshesToolbar :: forall m. H.ComponentHTML Action Slots m
renderMeshesToolbar =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") S.toolbarStyle
    ]
    [ HH.select
        [ cls [ "primitive-select" ]
        , HP.attr (HH.AttrName "style") S.selectStyle
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
    , HP.attr (HH.AttrName "style") S.listStyle
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
    , HP.attr (HH.AttrName "style") (S.listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectMesh mesh.id
    ]
    [ HH.div 
        [ cls [ "mesh-icon" ]
        , HP.attr (HH.AttrName "style") S.meshIconStyle
        , HP.attr (HH.AttrName "aria-hidden") "true"
        ]
        [ HH.text (meshSourceIcon mesh.source) ]
    , HH.div 
        [ cls [ "mesh-info" ]
        , HP.attr (HH.AttrName "style") S.meshInfoStyle
        ]
        [ HH.span [ cls [ "mesh-name" ] ] [ HH.text mesh.name ]
        , HH.span 
            [ cls [ "mesh-verts" ]
            , HP.attr (HH.AttrName "style") S.meshVertsStyle
            ] 
            [ HH.text (show mesh.vertexCount <> " verts") ]
        ]
    , HH.button
        [ cls [ "delete-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") S.deleteBtnStyle
        , HP.attr (HH.AttrName "title") "Delete"
        , ARIA.label ("Delete " <> mesh.name)
        , HE.onClick \_ -> DeleteMesh mesh.id
        ]
        [ HH.text "x" ]
    ]

renderMeshDetails :: forall m. State -> H.ComponentHTML Action Slots m
renderMeshDetails state =
  case findSelected state.selectedMeshId state.meshParticles of
    Nothing -> HH.text ""
    Just mesh ->
      HH.div
        [ cls [ "mesh-details" ]
        , HP.attr (HH.AttrName "style") S.detailsStyle
        ]
        [ HH.h4 [ HP.attr (HH.AttrName "style") S.detailsTitleStyle ] [ HH.text mesh.name ]
        , renderDetailRow "Source" (meshSourceLabel mesh.source)
        , renderDetailRow "Vertices" (show mesh.vertexCount)
        , renderDetailRow "Bounding Radius" (formatNumber mesh.boundingRadius)
        , HH.button
            [ cls [ "action-btn" ]
            , HP.type_ HP.ButtonButton
            , HP.attr (HH.AttrName "style") S.fullWidthBtnStyle
            , HE.onClick \_ -> UseMeshAsEmitterAction mesh.id
            ]
            [ HH.text "Use as Emitter Shape" ]
        ]

renderDetailRow :: forall m. String -> String -> H.ComponentHTML Action Slots m
renderDetailRow label value =
  HH.div
    [ cls [ "detail-row" ]
    , HP.attr (HH.AttrName "style") S.detailRowStyle
    ]
    [ HH.span [ cls [ "label" ], HP.attr (HH.AttrName "style") S.detailLabelStyle ] [ HH.text label ]
    , HH.span [ cls [ "value" ] ] [ HH.text value ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                            // sprites tab
-- ════════════════════════════════════════════════════════════════════════════

renderSpritesTab :: forall m. State -> H.ComponentHTML Action Slots m
renderSpritesTab state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") S.tabPanelStyle
    ]
    [ renderSpritesToolbar
    , renderSpritesList state
    ]

renderSpritesToolbar :: forall m. H.ComponentHTML Action Slots m
renderSpritesToolbar =
  HH.div
    [ cls [ "panel-toolbar" ]
    , HP.attr (HH.AttrName "style") S.toolbarStyle
    ]
    [ HH.button
        [ cls [ "toolbar-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") S.toolbarBtnStyle
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
    , HP.attr (HH.AttrName "style") S.listStyle
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
    , HP.attr (HH.AttrName "style") (S.listItemStyle isSelected)
    , HP.attr (HH.AttrName "role") "option"
    , ARIA.selected (show isSelected)
    , HE.onClick \_ -> SelectSprite sprite.id
    ]
    [ HH.img
        [ HP.src sprite.textureUrl
        , HP.alt sprite.name
        , cls [ "sprite-preview" ]
        , HP.attr (HH.AttrName "style") S.spritePreviewStyle
        ]
    , HH.div 
        [ cls [ "sprite-info" ]
        , HP.attr (HH.AttrName "style") S.spriteInfoStyle
        ]
        [ HH.span [ cls [ "sprite-name" ] ] [ HH.text sprite.name ]
        , HH.span 
            [ cls [ "sprite-frames" ]
            , HP.attr (HH.AttrName "style") S.spriteFramesStyle
            ] 
            [ HH.text (show sprite.totalFrames <> " frames") ]
        ]
    , HH.button
        [ cls [ "delete-btn" ]
        , HP.type_ HP.ButtonButton
        , HP.attr (HH.AttrName "style") S.deleteBtnStyle
        , HP.attr (HH.AttrName "title") "Delete"
        , ARIA.label ("Delete " <> sprite.name)
        , HE.onClick \_ -> DeleteSprite sprite.id
        ]
        [ HH.text "x" ]
    ]

-- ════════════════════════════════════════════════════════════════════════════
--                                                         // environment tab
-- ════════════════════════════════════════════════════════════════════════════

renderEnvironmentTab :: forall m. State -> H.ComponentHTML Action Slots m
renderEnvironmentTab _state =
  HH.div
    [ cls [ "tab-panel" ]
    , HP.attr (HH.AttrName "style") S.tabPanelStyle
    ]
    [ HH.div 
        [ cls [ "environment-placeholder" ]
        , HP.attr (HH.AttrName "style") S.placeholderStyle
        ]
        [ textMuted "Environment settings will appear here"
        , HH.p [ cls [ "hint" ] ] 
            [ textMuted "Load an HDR environment map for PBR lighting" ]
        ]
    ]
