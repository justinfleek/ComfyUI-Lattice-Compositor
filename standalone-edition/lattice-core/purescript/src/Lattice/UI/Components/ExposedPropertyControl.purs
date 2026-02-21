-- | Exposed Property Control Component
-- |
-- | A dynamic property editor for template-exposed properties.
-- | Supports multiple property types:
-- | - sourceText: Text input
-- | - number: Slider with numeric input
-- | - checkbox: Toggle switch
-- | - dropdown: Select menu
-- | - color: Color picker
-- | - point: X/Y coordinate inputs
-- | - media: File picker with preview
-- | - layer: Layer reference picker
-- | - font: Font family selector
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/ExposedPropertyControl.vue
module Lattice.UI.Components.ExposedPropertyControl
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , ExposedProperty
  , PropertyType(..)
  , PropertyConfig(..)
  , PropertyValue(..)
  , LayerInfo
  ) where

import Prelude

import Data.Array (filter, find)
import Data.Int (round)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split)
import Data.String as String
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
  { property :: ExposedProperty
  , currentValue :: Maybe PropertyValue
  , availableLayers :: Array LayerInfo
  }

data Output
  = PropertyNameChanged String String  -- propertyId, newName
  | PropertyValueChanged String PropertyValue  -- propertyId, newValue
  | PropertyRemoved String  -- propertyId
  | MediaSelectRequested String  -- propertyId

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                             // property types
-- =============================================================================

type ExposedProperty =
  { id :: String
  , name :: String
  , propertyType :: PropertyType
  , sourcePropertyPath :: String
  , config :: PropertyConfig
  }

data PropertyType
  = SourceText
  | NumberType
  | Checkbox
  | Dropdown
  | ColorType
  | PointType
  | MediaType
  | LayerType
  | FontType

derive instance eqPropertyType :: Eq PropertyType

instance showPropertyType :: Show PropertyType where
  show = case _ of
    SourceText -> "sourceText"
    NumberType -> "number"
    Checkbox -> "checkbox"
    Dropdown -> "dropdown"
    ColorType -> "color"
    PointType -> "point"
    MediaType -> "media"
    LayerType -> "layer"
    FontType -> "font"

parsePropertyType :: String -> PropertyType
parsePropertyType = case _ of
  "number" -> NumberType
  "checkbox" -> Checkbox
  "dropdown" -> Dropdown
  "color" -> ColorType
  "point" -> PointType
  "media" -> MediaType
  "layer" -> LayerType
  "font" -> FontType
  _ -> SourceText

data PropertyConfig
  = NumberConfig { min :: Number, max :: Number, step :: Number }
  | DropdownConfig { options :: Array DropdownOption }
  | EmptyConfig

type DropdownOption = { value :: String, label :: String }

data PropertyValue
  = StringValue String
  | NumberValue Number
  | BooleanValue Boolean
  | ColorValue { r :: Number, g :: Number, b :: Number, a :: Number }
  | PointValue { x :: Number, y :: Number }
  | NullValue

derive instance eqPropertyValue :: Eq PropertyValue

type LayerInfo =
  { id :: String
  , name :: String
  , layerType :: String
  }

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { property :: ExposedProperty
  , currentValue :: Maybe PropertyValue
  , availableLayers :: Array LayerInfo
  , localName :: String
  }

data Action
  = Initialize
  | Receive Input
  -- Name editing
  | UpdateLocalName String
  | CommitName
  -- Value changes
  | SetTextValue String
  | SetNumberValue String
  | SetCheckboxValue Boolean
  | SetDropdownValue String
  | SetColorValue String
  | SetPointX String
  | SetPointY String
  | SelectMedia
  | SetLayerValue String
  | SetFontValue String
  -- Remove
  | Remove

type Slots = ()

-- =============================================================================
--                                                                  // component
-- =============================================================================

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
  { property: input.property
  , currentValue: input.currentValue
  , availableLayers: input.availableLayers
  , localName: input.property.name
  }

-- =============================================================================
--                                                                     // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "exposed-property-control" ]
    , HP.attr (HH.AttrName "style") controlStyle
    ]
    [ renderHeader state
    , renderPropertyValue state
    , renderPropertyPath state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "property-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.input
        [ cls [ "property-name-input" ]
        , HP.type_ HP.InputText
        , HP.value state.localName
        , HP.attr (HH.AttrName "style") nameInputStyle
        , HE.onValueInput UpdateLocalName
        , HE.onBlur \_ -> CommitName
        , ARIA.label "Property name"
        ]
    , HH.div
        [ cls [ "property-actions" ]
        , HP.attr (HH.AttrName "style") actionsStyle
        ]
        [ HH.button
            [ cls [ "btn-icon-tiny" ]
            , HP.attr (HH.AttrName "style") removeButtonStyle
            , HP.title "Remove"
            , ARIA.label "Remove property"
            , HE.onClick \_ -> Remove
            ]
            [ HH.text "\x{00D7}" ]
        ]
    ]

renderPropertyValue :: forall m. State -> H.ComponentHTML Action Slots m
renderPropertyValue state =
  HH.div
    [ cls [ "property-value" ]
    , HP.attr (HH.AttrName "style") valueContainerStyle
    ]
    [ case state.property.propertyType of
        SourceText -> renderTextInput state
        NumberType -> renderNumberInput state
        Checkbox -> renderCheckbox state
        Dropdown -> renderDropdown state
        ColorType -> renderColorPicker state
        PointType -> renderPointInput state
        MediaType -> renderMediaPicker state
        LayerType -> renderLayerPicker state
        FontType -> renderFontPicker state
    ]

renderPropertyPath :: forall m. State -> H.ComponentHTML Action Slots m
renderPropertyPath state =
  HH.div
    [ cls [ "property-path" ]
    , HP.attr (HH.AttrName "style") pathStyle
    ]
    [ HH.text state.property.sourcePropertyPath ]

-- =============================================================================
--                                                             // input renderers
-- =============================================================================

renderTextInput :: forall m. State -> H.ComponentHTML Action Slots m
renderTextInput state =
  HH.input
    [ cls [ "text-input" ]
    , HP.type_ HP.InputText
    , HP.value (getStringValue state.currentValue)
    , HP.placeholder "Enter text..."
    , HP.attr (HH.AttrName "style") textInputStyle
    , HE.onValueInput SetTextValue
    ]

renderNumberInput :: forall m. State -> H.ComponentHTML Action Slots m
renderNumberInput state =
  let
    val = getNumberValue state.currentValue
    { min, max, step } = getNumberConfig state.property.config
  in HH.div [ cls [ "slider-control" ], HP.attr (HH.AttrName "style") sliderControlStyle ]
    [ HH.input
        [ HP.type_ HP.InputRange
        , HP.value (show val)
        , HP.attr (HH.AttrName "min") (show min)
        , HP.attr (HH.AttrName "max") (show max)
        , HP.attr (HH.AttrName "step") (show step)
        , HP.attr (HH.AttrName "style") sliderStyle
        , HE.onValueInput SetNumberValue
        ]
    , HH.input
        [ HP.type_ HP.InputNumber
        , HP.value (Utils.formatNumber 2 val)
        , HP.attr (HH.AttrName "style") numberInputStyle
        , HE.onValueInput SetNumberValue
        ]
    ]

renderCheckbox :: forall m. State -> H.ComponentHTML Action Slots m
renderCheckbox state =
  let checked = getBoolValue state.currentValue
  in HH.label [ cls [ "checkbox-control" ], HP.attr (HH.AttrName "style") checkboxControlStyle ]
    [ HH.input
        [ HP.type_ HP.InputCheckbox
        , HP.checked checked
        , HE.onChecked SetCheckboxValue
        ]
    , HH.span [ cls [ "checkbox-label" ], HP.attr (HH.AttrName "style") checkboxLabelStyle ]
        [ HH.text (if checked then "On" else "Off") ]
    ]

renderDropdown :: forall m. State -> H.ComponentHTML Action Slots m
renderDropdown state =
  let
    currentVal = getStringValue state.currentValue
    options = getDropdownOptions state.property.config
  in HH.select
    [ cls [ "dropdown-input" ]
    , HP.attr (HH.AttrName "style") dropdownStyle
    , HE.onValueChange SetDropdownValue
    ]
    (map (dropdownOption currentVal) options)

dropdownOption :: forall m. String -> DropdownOption -> H.ComponentHTML Action Slots m
dropdownOption current opt =
  HH.option
    [ HP.value opt.value, HP.selected (current == opt.value) ]
    [ HH.text opt.label ]

renderColorPicker :: forall m. State -> H.ComponentHTML Action Slots m
renderColorPicker state =
  let hexColor = colorToHex state.currentValue
  in HH.div [ cls [ "color-control" ], HP.attr (HH.AttrName "style") colorControlStyle ]
    [ HH.input
        [ HP.type_ HP.InputColor
        , HP.value hexColor
        , HP.attr (HH.AttrName "style") colorInputStyle
        , HE.onValueInput SetColorValue
        ]
    , HH.span [ cls [ "color-hex" ], HP.attr (HH.AttrName "style") colorHexStyle ]
        [ HH.text hexColor ]
    ]

renderPointInput :: forall m. State -> H.ComponentHTML Action Slots m
renderPointInput state =
  let { x, y } = getPointValue state.currentValue
  in HH.div [ cls [ "point-control" ], HP.attr (HH.AttrName "style") pointControlStyle ]
    [ HH.label_
        [ HH.text "X:"
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.value (Utils.formatNumber 1 x)
            , HP.attr (HH.AttrName "style") pointInputStyle
            , HE.onValueInput SetPointX
            ]
        ]
    , HH.label_
        [ HH.text "Y:"
        , HH.input
            [ HP.type_ HP.InputNumber
            , HP.value (Utils.formatNumber 1 y)
            , HP.attr (HH.AttrName "style") pointInputStyle
            , HE.onValueInput SetPointY
            ]
        ]
    ]

renderMediaPicker :: forall m. State -> H.ComponentHTML Action Slots m
renderMediaPicker state =
  let mediaUrl = getStringValue state.currentValue
  in HH.div [ cls [ "media-control" ], HP.attr (HH.AttrName "style") mediaControlStyle ]
    [ HH.div
        [ cls [ "media-preview" ]
        , HP.attr (HH.AttrName "style") mediaPreviewStyle
        , HP.title "Click to replace media"
        , HE.onClick \_ -> SelectMedia
        , ARIA.role "button"
        ]
        [ if mediaUrl /= ""
            then HH.img [ HP.src mediaUrl, HP.alt "", HP.attr (HH.AttrName "style") mediaImgStyle ]
            else HH.span [ cls [ "media-placeholder" ] ] [ HH.text "\x{1F4C1}" ]
        ]
    , HH.div [ cls [ "media-info" ], HP.attr (HH.AttrName "style") mediaInfoStyle ]
        [ HH.span
            [ cls [ "media-filename" ]
            , HP.attr (HH.AttrName "style") (if mediaUrl == "" then mediaFilenameStyleMuted else mediaFilenameStyle)
            ]
            [ HH.text (if mediaUrl == "" then "No media selected" else getMediaFilename mediaUrl) ]
        , HH.button
            [ cls [ "btn-small" ]
            , HP.attr (HH.AttrName "style") smallButtonStyle
            , HE.onClick \_ -> SelectMedia
            ]
            [ HH.text "Replace..." ]
        ]
    ]

renderLayerPicker :: forall m. State -> H.ComponentHTML Action Slots m
renderLayerPicker state =
  let
    currentLayerId = getStringValue state.currentValue
    selectedLayer = find (\l -> l.id == currentLayerId) state.availableLayers
  in HH.div [ cls [ "layer-control" ], HP.attr (HH.AttrName "style") layerControlStyle ]
    [ HH.select
        [ cls [ "dropdown-input", "layer-picker" ]
        , HP.attr (HH.AttrName "style") dropdownStyle
        , HE.onValueChange SetLayerValue
        ]
        ([ HH.option [ HP.value "", HP.selected (currentLayerId == "") ] [ HH.text "None" ] ]
          <> map (layerOption currentLayerId) state.availableLayers)
    , case selectedLayer of
        Just layer ->
          HH.div [ cls [ "layer-info" ], HP.attr (HH.AttrName "style") layerInfoStyle ]
            [ HH.span [ cls [ "layer-type" ], HP.attr (HH.AttrName "style") layerTypeStyle ]
                [ HH.text layer.layerType ]
            ]
        Nothing -> HH.text ""
    ]

layerOption :: forall m. String -> LayerInfo -> H.ComponentHTML Action Slots m
layerOption current layer =
  HH.option
    [ HP.value layer.id, HP.selected (current == layer.id) ]
    [ HH.text layer.name ]

renderFontPicker :: forall m. State -> H.ComponentHTML Action Slots m
renderFontPicker state =
  let currentFont = getStringValue state.currentValue
  in HH.select
    [ cls [ "dropdown-input" ]
    , HP.attr (HH.AttrName "style") dropdownStyle
    , HE.onValueChange SetFontValue
    ]
    (map (fontOption currentFont) availableFonts)

fontOption :: forall m. String -> String -> H.ComponentHTML Action Slots m
fontOption current font =
  HH.option
    [ HP.value font, HP.selected (current == font) ]
    [ HH.text font ]

availableFonts :: Array String
availableFonts =
  [ "Arial", "Helvetica", "Times New Roman", "Georgia", "Verdana", "Courier New"
  , "Inter", "Roboto", "Open Sans", "Lato", "Montserrat", "Poppins"
  , "Source Sans Pro", "Nunito", "Raleway"
  ]

-- =============================================================================
--                                                              // value helpers
-- =============================================================================

getStringValue :: Maybe PropertyValue -> String
getStringValue = case _ of
  Just (StringValue s) -> s
  _ -> ""

getNumberValue :: Maybe PropertyValue -> Number
getNumberValue = case _ of
  Just (NumberValue n) -> n
  _ -> 0.0

getBoolValue :: Maybe PropertyValue -> Boolean
getBoolValue = case _ of
  Just (BooleanValue b) -> b
  _ -> false

getPointValue :: Maybe PropertyValue -> { x :: Number, y :: Number }
getPointValue = case _ of
  Just (PointValue p) -> p
  _ -> { x: 0.0, y: 0.0 }

getNumberConfig :: PropertyConfig -> { min :: Number, max :: Number, step :: Number }
getNumberConfig = case _ of
  NumberConfig cfg -> cfg
  _ -> { min: 0.0, max: 100.0, step: 1.0 }

getDropdownOptions :: PropertyConfig -> Array DropdownOption
getDropdownOptions = case _ of
  DropdownConfig cfg -> cfg.options
  _ -> []

colorToHex :: Maybe PropertyValue -> String
colorToHex = case _ of
  Just (ColorValue { r, g, b }) ->
    let
      ri = round (r * (if r > 1.0 then 1.0 else 255.0))
      gi = round (g * (if g > 1.0 then 1.0 else 255.0))
      bi = round (b * (if b > 1.0 then 1.0 else 255.0))
    in "#" <> Utils.padStart 2 "0" (Utils.intToHex ri) 
           <> Utils.padStart 2 "0" (Utils.intToHex gi)
           <> Utils.padStart 2 "0" (Utils.intToHex bi)
  Just (StringValue s) -> s
  _ -> "#ffffff"

hexToColor :: String -> PropertyValue
hexToColor hex =
  let 
    cleanHex = String.drop 1 hex  -- Remove #
    r = Utils.hexToInt (String.take 2 cleanHex) / 255.0
    g = Utils.hexToInt (String.take 2 (String.drop 2 cleanHex)) / 255.0
    b = Utils.hexToInt (String.take 2 (String.drop 4 cleanHex)) / 255.0
  in ColorValue { r, g, b, a: 1.0 }

getMediaFilename :: String -> String
getMediaFilename url =
  if String.take 5 url == "data:"
    then "[embedded]"
    else case lastSegment url of
      "" -> "media"
      name -> name

lastSegment :: String -> String
lastSegment url =
  let segments = split (Pattern "/") url
  in fromMaybe "" (lastOf segments)

lastOf :: forall a. Array a -> Maybe a
lastOf arr =
  let len = Utils.arrayLength arr
  in if len == 0 then Nothing else Utils.arrayIndex (len - 1) arr

-- =============================================================================
--                                                                     // styles
-- =============================================================================

controlStyle :: String
controlStyle =
  "padding: 8px;"

headerStyle :: String
headerStyle =
  "display: flex; align-items: center; justify-content: space-between; margin-bottom: 6px;"

nameInputStyle :: String
nameInputStyle =
  "flex: 1; background: transparent; border: none; " <>
  "color: var(--lattice-text-primary, #E5E5E5); " <>
  "font-size: 12px; font-weight: 500; padding: 2px 0;"

actionsStyle :: String
actionsStyle =
  "display: flex; gap: 4px; opacity: 0; transition: opacity 0.15s ease;"

removeButtonStyle :: String
removeButtonStyle =
  "width: 18px; height: 18px; padding: 0; background: none; border: none; " <>
  "color: var(--lattice-text-muted, #6B7280); cursor: pointer; font-size: 14px;"

valueContainerStyle :: String
valueContainerStyle =
  "margin-bottom: 4px;"

pathStyle :: String
pathStyle =
  "font-size: 9px; color: var(--lattice-text-muted, #6B7280); font-family: monospace;"

textInputStyle :: String
textInputStyle =
  "width: 100%; padding: 6px 8px; " <>
  "background: var(--lattice-surface-0, #0A0A0A); " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; color: var(--lattice-text-primary, #E5E5E5); font-size: 12px;"

sliderControlStyle :: String
sliderControlStyle =
  "display: flex; align-items: center; gap: 8px;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px; appearance: none; " <>
  "background: var(--lattice-surface-0, #0A0A0A); border-radius: 2px;"

numberInputStyle :: String
numberInputStyle =
  "width: 60px; padding: 4px 6px; " <>
  "background: var(--lattice-surface-0, #0A0A0A); " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; color: var(--lattice-text-primary, #E5E5E5); " <>
  "font-size: 11px; text-align: right;"

checkboxControlStyle :: String
checkboxControlStyle =
  "display: flex; align-items: center; gap: 8px; cursor: pointer;"

checkboxLabelStyle :: String
checkboxLabelStyle =
  "font-size: 12px; color: var(--lattice-text-secondary, #9CA3AF);"

dropdownStyle :: String
dropdownStyle =
  "width: 100%; padding: 6px 8px; " <>
  "background: var(--lattice-surface-0, #0A0A0A); " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; color: var(--lattice-text-primary, #E5E5E5); font-size: 12px;"

colorControlStyle :: String
colorControlStyle =
  "display: flex; align-items: center; gap: 8px;"

colorInputStyle :: String
colorInputStyle =
  "width: 32px; height: 24px; padding: 0; " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; cursor: pointer;"

colorHexStyle :: String
colorHexStyle =
  "font-size: 11px; font-family: monospace; color: var(--lattice-text-secondary, #9CA3AF);"

pointControlStyle :: String
pointControlStyle =
  "display: flex; gap: 12px;"

pointInputStyle :: String
pointInputStyle =
  "width: 60px; padding: 4px 6px; " <>
  "background: var(--lattice-surface-0, #0A0A0A); " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; color: var(--lattice-text-primary, #E5E5E5); font-size: 11px;"

mediaControlStyle :: String
mediaControlStyle =
  "display: flex; align-items: flex-start; gap: 10px;"

mediaPreviewStyle :: String
mediaPreviewStyle =
  "width: 56px; height: 42px; " <>
  "background: var(--lattice-surface-0, #0A0A0A); " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; display: flex; align-items: center; justify-content: center; " <>
  "overflow: hidden; cursor: pointer; flex-shrink: 0;"

mediaImgStyle :: String
mediaImgStyle =
  "width: 100%; height: 100%; object-fit: cover;"

mediaInfoStyle :: String
mediaInfoStyle =
  "display: flex; flex-direction: column; gap: 4px; flex: 1; min-width: 0;"

mediaFilenameStyle :: String
mediaFilenameStyle =
  "font-size: 11px; color: var(--lattice-text-secondary, #9CA3AF); " <>
  "white-space: nowrap; overflow: hidden; text-overflow: ellipsis;"

mediaFilenameStyleMuted :: String
mediaFilenameStyleMuted =
  "font-size: 11px; color: var(--lattice-text-muted, #6B7280); font-style: italic; " <>
  "white-space: nowrap; overflow: hidden; text-overflow: ellipsis;"

smallButtonStyle :: String
smallButtonStyle =
  "padding: 4px 8px; background: var(--lattice-surface-3, #222222); " <>
  "border: 1px solid var(--lattice-border-subtle, #2A2A2A); " <>
  "border-radius: 3px; color: var(--lattice-text-secondary, #9CA3AF); " <>
  "font-size: 10px; cursor: pointer;"

layerControlStyle :: String
layerControlStyle =
  "display: flex; flex-direction: column; gap: 4px;"

layerInfoStyle :: String
layerInfoStyle =
  "display: flex; align-items: center; gap: 6px; padding: 2px 0;"

layerTypeStyle :: String
layerTypeStyle =
  "font-size: 10px; color: var(--lattice-text-muted, #6B7280); " <>
  "background: var(--lattice-surface-0, #0A0A0A); padding: 2px 6px; " <>
  "border-radius: 3px; text-transform: uppercase; letter-spacing: 0.5px;"

-- =============================================================================
--                                                                    // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit
  
  Receive input -> do
    state <- H.get
    -- Update from new input but preserve local name if editing
    when (input.property.name /= state.property.name) do
      H.modify_ _ { localName = input.property.name }
    H.modify_ _ 
      { property = input.property
      , currentValue = input.currentValue
      , availableLayers = input.availableLayers
      }
  
  UpdateLocalName name -> H.modify_ _ { localName = name }
  
  CommitName -> do
    state <- H.get
    when (state.localName /= state.property.name) do
      H.raise (PropertyNameChanged state.property.id state.localName)
  
  SetTextValue val -> emitValue (StringValue val)
  
  SetNumberValue val -> do
    state <- H.get
    let num = Utils.parseFloatOr (getNumberValue state.currentValue) val
    emitValue (NumberValue num)
  
  SetCheckboxValue checked -> emitValue (BooleanValue checked)
  
  SetDropdownValue val -> emitValue (StringValue val)
  
  SetColorValue hex -> emitValue (hexToColor hex)
  
  SetPointX val -> do
    state <- H.get
    let pt = getPointValue state.currentValue
    let x = Utils.parseFloatOr pt.x val
    emitValue (PointValue (pt { x = x }))
  
  SetPointY val -> do
    state <- H.get
    let pt = getPointValue state.currentValue
    let y = Utils.parseFloatOr pt.y val
    emitValue (PointValue (pt { y = y }))
  
  SelectMedia -> do
    state <- H.get
    H.raise (MediaSelectRequested state.property.id)
  
  SetLayerValue val -> emitValue (StringValue val)
  
  SetFontValue val -> emitValue (StringValue val)
  
  Remove -> do
    state <- H.get
    H.raise (PropertyRemoved state.property.id)

emitValue :: forall m. MonadAff m => PropertyValue -> H.HalogenM State Action Slots Output m Unit
emitValue val = do
  state <- H.get
  H.modify_ _ { currentValue = Just val }
  H.raise (PropertyValueChanged state.property.id val)
