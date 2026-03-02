-- | AddLayerDialog Component
-- | Dialog for adding new layers to the composition
module Lattice.UI.Components.AddLayerDialog where

import Prelude
import Data.Maybe (Maybe(..))
import Type.Proxy (Proxy(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Lattice.UI.Core (cls)
import Lattice.UI.Radix.Dialog as Dialog
import Lattice.Project (LayerType(..))

type Input = { isOpen :: Boolean }

data Output
  = DialogClosed
  | LayerTypeSelected LayerType String

data Query a
type Slot id = H.Slot Query Output id

type State =
  { isOpen :: Boolean
  , selectedCategory :: LayerCategory
  , layerName :: String
  }

data LayerCategory
  = CatVisual
  | CatShape
  | CatAudio
  | Cat3D
  | CatControl
  | CatGenerated

derive instance eqLayerCategory :: Eq LayerCategory

data Action
  = Initialize
  | Receive Input
  | SetCategory LayerCategory
  | SetLayerName String
  | SelectLayerType LayerType
  | Close
  | HandleDialogOutput Dialog.Output

type Slots = ( dialog :: Dialog.Slot Unit )

_dialog :: Proxy "dialog"
_dialog = Proxy

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
  { isOpen: input.isOpen
  , selectedCategory: CatVisual
  , layerName: "New Layer"
  }

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.slot _dialog unit Dialog.component
    { isOpen: state.isOpen
    , title: "Add Layer"
    , description: "Choose a layer type to add"
    }
    HandleDialogOutput
  `withContent`
    [ renderCategoryTabs state
    , renderLayerGrid state
    , renderNameInput state
    ]

withContent :: forall m. H.ComponentHTML Action Slots m -> Array (H.ComponentHTML Action Slots m) -> H.ComponentHTML Action Slots m
withContent dialog content =
  HH.div [ cls [ "lattice-add-layer-dialog" ] ]
    ([ dialog ] <> content)

renderCategoryTabs :: forall m. State -> H.ComponentHTML Action Slots m
renderCategoryTabs state =
  HH.div
    [ cls [ "lattice-layer-categories" ]
    , HP.attr (HH.AttrName "style") categoriesStyle
    ]
    [ categoryTab "Visual" CatVisual state.selectedCategory
    , categoryTab "Shape" CatShape state.selectedCategory
    , categoryTab "Audio" CatAudio state.selectedCategory
    , categoryTab "3D" Cat3D state.selectedCategory
    , categoryTab "Control" CatControl state.selectedCategory
    , categoryTab "Generated" CatGenerated state.selectedCategory
    ]

categoryTab :: forall m. String -> LayerCategory -> LayerCategory -> H.ComponentHTML Action Slots m
categoryTab label cat selectedCat =
  HH.button
    [ cls [ "lattice-category-tab" ]
    , HP.attr (HH.AttrName "style") (tabStyle (cat == selectedCat))
    , HE.onClick \_ -> SetCategory cat
    ]
    [ HH.text label ]

renderLayerGrid :: forall m. State -> H.ComponentHTML Action Slots m
renderLayerGrid state =
  HH.div
    [ cls [ "lattice-layer-grid" ]
    , HP.attr (HH.AttrName "style") gridStyle
    ]
    (map renderLayerOption (layersForCategory state.selectedCategory))

renderLayerOption :: forall m. { layerType :: LayerType, name :: String, icon :: String, desc :: String } -> H.ComponentHTML Action Slots m
renderLayerOption opt =
  HH.button
    [ cls [ "lattice-layer-option" ]
    , HP.attr (HH.AttrName "style") optionStyle
    , HE.onClick \_ -> SelectLayerType opt.layerType
    ]
    [ HH.span [ cls [ "lattice-layer-icon" ] ] [ HH.text opt.icon ]
    , HH.span [ cls [ "lattice-layer-name" ] ] [ HH.text opt.name ]
    , HH.span [ cls [ "lattice-layer-desc" ] ] [ HH.text opt.desc ]
    ]

renderNameInput :: forall m. State -> H.ComponentHTML Action Slots m
renderNameInput state =
  HH.div
    [ cls [ "lattice-layer-name-input" ]
    , HP.attr (HH.AttrName "style") nameInputStyle
    ]
    [ HH.label_ [ HH.text "Layer Name" ]
    , HH.input
        [ cls [ "lattice-input" ]
        , HP.value state.layerName
        , HE.onValueInput SetLayerName
        ]
    ]

layersForCategory :: LayerCategory -> Array { layerType :: LayerType, name :: String, icon :: String, desc :: String }
layersForCategory = case _ of
  CatVisual ->
    [ { layerType: LTImage, name: "Image", icon: "🖼", desc: "Import image file" }
    , { layerType: LTVideo, name: "Video", icon: "🎬", desc: "Import video file" }
    , { layerType: LTSolid, name: "Solid", icon: "■", desc: "Solid color layer" }
    , { layerType: LTText, name: "Text", icon: "T", desc: "Text layer" }
    ]
  CatShape ->
    [ { layerType: LTShape, name: "Shape", icon: "◇", desc: "Vector shape" }
    , { layerType: LTSpline, name: "Spline", icon: "〰", desc: "Bezier spline" }
    , { layerType: LTPath, name: "Path", icon: "✏", desc: "Motion path" }
    ]
  CatAudio ->
    [ { layerType: LTAudio, name: "Audio", icon: "🔊", desc: "Audio track" }
    ]
  Cat3D ->
    [ { layerType: LTCamera, name: "Camera", icon: "📷", desc: "3D camera" }
    , { layerType: LTLight, name: "Light", icon: "💡", desc: "3D light source" }
    , { layerType: LTModel, name: "3D Model", icon: "🎲", desc: "Import 3D model" }
    , { layerType: LTPointCloud, name: "Point Cloud", icon: "⁘", desc: "Point cloud data" }
    ]
  CatControl ->
    [ { layerType: LTNull, name: "Null", icon: "◎", desc: "Null object" }
    , { layerType: LTControl, name: "Control", icon: "⊕", desc: "Control point" }
    , { layerType: LTGroup, name: "Group", icon: "📂", desc: "Layer group" }
    , { layerType: LTAdjustment, name: "Adjustment", icon: "◐", desc: "Adjustment layer" }
    ]
  CatGenerated ->
    [ { layerType: LTDepth, name: "Depth", icon: "▦", desc: "Depth map" }
    , { layerType: LTNormal, name: "Normal", icon: "↗", desc: "Normal map" }
    , { layerType: LTGenerated, name: "Generated", icon: "⚡", desc: "AI generated" }
    , { layerType: LTMatte, name: "Matte", icon: "◧", desc: "Matte layer" }
    , { layerType: LTPose, name: "Pose", icon: "🦴", desc: "Pose skeleton" }
    , { layerType: LTParticle, name: "Particle", icon: "✨", desc: "Particle system" }
    ]

categoriesStyle :: String
categoriesStyle =
  "display: flex; gap: var(--lattice-space-1); padding: var(--lattice-space-3); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

tabStyle :: Boolean -> String
tabStyle active =
  "padding: var(--lattice-space-2) var(--lattice-space-3); " <>
  "border-radius: var(--lattice-radius-sm); border: none; cursor: pointer; " <>
  "background: " <> (if active then "var(--lattice-accent)" else "transparent") <> "; " <>
  "color: " <> (if active then "white" else "var(--lattice-text-secondary)") <> ";"

gridStyle :: String
gridStyle =
  "display: grid; grid-template-columns: repeat(auto-fill, minmax(140px, 1fr)); " <>
  "gap: var(--lattice-space-2); padding: var(--lattice-space-3); " <>
  "max-height: 300px; overflow-y: auto;"

optionStyle :: String
optionStyle =
  "display: flex; flex-direction: column; align-items: center; gap: var(--lattice-space-1); " <>
  "padding: var(--lattice-space-3); border-radius: var(--lattice-radius-md); " <>
  "background: var(--lattice-surface-2); border: 1px solid var(--lattice-border-subtle); " <>
  "cursor: pointer; transition: all 0.15s ease;"

nameInputStyle :: String
nameInputStyle =
  "display: flex; flex-direction: column; gap: var(--lattice-space-1); " <>
  "padding: var(--lattice-space-3); border-top: 1px solid var(--lattice-border-subtle);"

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> H.modify_ _ { isOpen = input.isOpen }

  SetCategory cat -> H.modify_ _ { selectedCategory = cat }

  SetLayerName name -> H.modify_ _ { layerName = name }

  SelectLayerType layerType -> do
    state <- H.get
    H.raise (LayerTypeSelected layerType state.layerName)
    H.modify_ _ { isOpen = false }

  Close -> do
    H.modify_ _ { isOpen = false }
    H.raise DialogClosed

  HandleDialogOutput output -> case output of
    Dialog.Closed -> do
      H.modify_ _ { isOpen = false }
      H.raise DialogClosed
    _ -> pure unit
