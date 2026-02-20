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
  let
    dialogContent :: { trigger :: H.ComponentHTML Dialog.Action Dialog.Slots m
                     , title :: H.ComponentHTML Dialog.Action Dialog.Slots m
                     , description :: H.ComponentHTML Dialog.Action Dialog.Slots m
                     , body :: H.ComponentHTML Dialog.Action Dialog.Slots m
                     , close :: H.ComponentHTML Dialog.Action Dialog.Slots m
                     }
    dialogContent =
      { trigger: HH.text ""  -- No trigger, dialog is controlled externally
      , title: HH.text "Add Layer"
      , description: HH.text "Choose a layer type to add"
      , body: renderDialogBody state
      , close: HH.text "×"
      }
    
    dialogInput :: Dialog.Input
    dialogInput = Dialog.defaultInput { open = Just state.isOpen }
  in
  HH.slot _dialog unit (Dialog.component dialogContent) dialogInput HandleDialogOutput

-- | Render the dialog body content (needs to be typed for Dialog's internal slots)
renderDialogBody :: forall m. State -> H.ComponentHTML Dialog.Action Dialog.Slots m
renderDialogBody state =
  HH.div [ cls [ "lattice-add-layer-dialog-body" ] ]
    [ renderCategoryTabsInternal state
    , renderLayerGridInternal state
    , renderNameInputInternal state
    ]

-- | Internal versions that use Dialog's Action type
renderCategoryTabsInternal :: forall m. State -> H.ComponentHTML Dialog.Action Dialog.Slots m
renderCategoryTabsInternal state =
  HH.div
    [ cls [ "lattice-layer-categories" ]
    , HP.attr (HH.AttrName "style") categoriesStyle
    ]
    [ categoryTabInternal "Visual" CatVisual state.selectedCategory
    , categoryTabInternal "Shape" CatShape state.selectedCategory
    , categoryTabInternal "Audio" CatAudio state.selectedCategory
    , categoryTabInternal "3D" Cat3D state.selectedCategory
    , categoryTabInternal "Control" CatControl state.selectedCategory
    , categoryTabInternal "Generated" CatGenerated state.selectedCategory
    ]

categoryTabInternal :: forall m. String -> LayerCategory -> LayerCategory -> H.ComponentHTML Dialog.Action Dialog.Slots m
categoryTabInternal label cat selectedCat =
  HH.button
    [ cls (if cat == selectedCat then [ "lattice-category-tab", "active" ] else [ "lattice-category-tab" ])
    , HP.attr (HH.AttrName "style") (categoryTabStyle (cat == selectedCat))
    ]
    [ HH.text label ]

renderLayerGridInternal :: forall m. State -> H.ComponentHTML Dialog.Action Dialog.Slots m
renderLayerGridInternal state =
  HH.div
    [ cls [ "lattice-layer-grid" ]
    , HP.attr (HH.AttrName "style") gridStyle
    ]
    (map layerTypeButtonInternal (getLayerTypesForCategory state.selectedCategory))

layerTypeButtonInternal :: forall m. { layerType :: LayerType, label :: String, icon :: String } -> H.ComponentHTML Dialog.Action Dialog.Slots m
layerTypeButtonInternal { label, icon } =
  HH.button
    [ cls [ "lattice-layer-type-button" ]
    , HP.attr (HH.AttrName "style") layerButtonStyle
    ]
    [ HH.span [ cls [ "lattice-layer-icon" ] ] [ HH.text icon ]
    , HH.span [ cls [ "lattice-layer-label" ] ] [ HH.text label ]
    ]

renderNameInputInternal :: forall m. State -> H.ComponentHTML Dialog.Action Dialog.Slots m
renderNameInputInternal state =
  HH.div
    [ cls [ "lattice-layer-name-input" ]
    , HP.attr (HH.AttrName "style") nameInputContainerStyle
    ]
    [ HH.label [ cls [ "lattice-input-label" ] ] [ HH.text "Layer Name" ]
    , HH.input
        [ cls [ "lattice-text-input" ]
        , HP.type_ HP.InputText
        , HP.value state.layerName
        , HP.attr (HH.AttrName "style") nameInputStyle
        ]
    ]

-- | External render functions that use our Action type
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
    [ cls (if cat == selectedCat then [ "lattice-category-tab", "active" ] else [ "lattice-category-tab" ])
    , HP.attr (HH.AttrName "style") (categoryTabStyle (cat == selectedCat))
    , HE.onClick \_ -> SetCategory cat
    ]
    [ HH.text label ]

renderLayerGrid :: forall m. State -> H.ComponentHTML Action Slots m
renderLayerGrid state =
  HH.div
    [ cls [ "lattice-layer-grid" ]
    , HP.attr (HH.AttrName "style") gridStyle
    ]
    (map layerTypeButton (getLayerTypesForCategory state.selectedCategory))

layerTypeButton :: forall m. { layerType :: LayerType, label :: String, icon :: String } -> H.ComponentHTML Action Slots m
layerTypeButton { layerType, label, icon } =
  HH.button
    [ cls [ "lattice-layer-type-button" ]
    , HP.attr (HH.AttrName "style") layerButtonStyle
    , HE.onClick \_ -> SelectLayerType layerType
    ]
    [ HH.span [ cls [ "lattice-layer-icon" ] ] [ HH.text icon ]
    , HH.span [ cls [ "lattice-layer-label" ] ] [ HH.text label ]
    ]

renderNameInput :: forall m. State -> H.ComponentHTML Action Slots m
renderNameInput state =
  HH.div
    [ cls [ "lattice-layer-name-input" ]
    , HP.attr (HH.AttrName "style") nameInputContainerStyle
    ]
    [ HH.label [ cls [ "lattice-input-label" ] ] [ HH.text "Layer Name" ]
    , HH.input
        [ cls [ "lattice-text-input" ]
        , HP.type_ HP.InputText
        , HP.value state.layerName
        , HP.attr (HH.AttrName "style") nameInputStyle
        , HE.onValueInput SetLayerName
        ]
    ]

getLayerTypesForCategory :: LayerCategory -> Array { layerType :: LayerType, label :: String, icon :: String }
getLayerTypesForCategory = case _ of
  CatVisual ->
    [ { layerType: LTImage, label: "Image", icon: "🖼" }
    , { layerType: LTVideo, label: "Video", icon: "🎬" }
    , { layerType: LTText, label: "Text", icon: "T" }
    , { layerType: LTSolid, label: "Solid", icon: "■" }
    ]
  CatShape ->
    [ { layerType: LTShape, label: "Shape", icon: "◆" }
    ]
  CatAudio ->
    [ { layerType: LTAudio, label: "Audio", icon: "🔊" }
    ]
  Cat3D ->
    [ { layerType: LTCamera, label: "Camera", icon: "📷" }
    , { layerType: LTLight, label: "Light", icon: "💡" }
    ]
  CatControl ->
    [ { layerType: LTNull, label: "Null", icon: "◯" }
    , { layerType: LTAdjustment, label: "Adjustment", icon: "⚙" }
    ]
  CatGenerated ->
    [ { layerType: LTTextToImage, label: "T2I", icon: "🖼" }
    , { layerType: LTImageToVideo, label: "I2V", icon: "🎬" }
    , { layerType: LTTextToVideo, label: "T2V", icon: "🎥" }
    , { layerType: LTImageToImage, label: "I2I", icon: "🔄" }
    , { layerType: LTInpaint, label: "Inpaint", icon: "✏️" }
    , { layerType: LTOutpaint, label: "Outpaint", icon: "↔️" }
    , { layerType: LTUpscale, label: "Upscale", icon: "⬆️" }
    , { layerType: LTRemoveBackground, label: "RMBG", icon: "🎭" }
    , { layerType: LTPreComp, label: "Precomp", icon: "📦" }
    ]

-- Styles
categoriesStyle :: String
categoriesStyle =
  "display: flex; gap: 4px; padding: 8px; border-bottom: 1px solid var(--lattice-border-subtle);"

categoryTabStyle :: Boolean -> String
categoryTabStyle isActive =
  "padding: 6px 12px; border: none; border-radius: 4px; cursor: pointer; " <>
  if isActive
    then "background: var(--lattice-accent); color: white;"
    else "background: transparent; color: var(--lattice-text-secondary);"

gridStyle :: String
gridStyle =
  "display: grid; grid-template-columns: repeat(auto-fill, minmax(80px, 1fr)); gap: 8px; padding: 16px;"

layerButtonStyle :: String
layerButtonStyle =
  "display: flex; flex-direction: column; align-items: center; gap: 4px; " <>
  "padding: 12px; border: 1px solid var(--lattice-border-subtle); border-radius: 8px; " <>
  "background: var(--lattice-surface-2); cursor: pointer; transition: all 0.15s ease;"

nameInputContainerStyle :: String
nameInputContainerStyle =
  "padding: 16px; border-top: 1px solid var(--lattice-border-subtle);"

nameInputStyle :: String
nameInputStyle =
  "width: 100%; padding: 8px 12px; border: 1px solid var(--lattice-border); " <>
  "border-radius: 4px; background: var(--lattice-surface-1); color: var(--lattice-text);"

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { isOpen = input.isOpen }

  SetCategory cat -> do
    H.modify_ _ { selectedCategory = cat }

  SetLayerName name -> do
    H.modify_ _ { layerName = name }

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
