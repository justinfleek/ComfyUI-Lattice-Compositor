-- | Effect Controls Panel Component
-- |
-- | Displays and edits effect parameters for a selected layer.
-- | Features:
-- | - Collapsible effect sections with enable/disable toggles
-- | - Parameter editing (sliders, color pickers, angles, positions, enums)
-- | - Keyframe animation toggles per parameter
-- | - Drag-and-drop effect reordering
-- | - Add effect dropdown menu by category
-- |
-- | Based on ComfyUI-Lattice-Compositor/ui/src/components/panels/EffectControlsPanel.vue
module Lattice.UI.Components.EffectControlsPanel
  ( component
  , Input
  , Output(..)
  , Query
  , Slot
  , EffectInstance
  , EffectParameter
  , ParameterValue(..)
  , ParameterType(..)
  ) where

import Prelude

import Data.Array (concat, deleteAt, filter, findIndex, insertAt, length, mapWithIndex, snoc)
import Data.Array as Array
import Control.Monad (when)
import Data.Foldable (for_)
import Data.Int as Int
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Number as Number
import Data.String (Pattern(..), contains, toLower)
import Data.String as String
import Data.Tuple (Tuple(..))
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

import Lattice.UI.Core (cls, emptyState)
import Lattice.UI.Utils (getElementById)

-- =============================================================================
--                                                                      // types
-- =============================================================================

type Input =
  { layer :: Maybe LayerInfo
  , availableLayers :: Array LayerInfo
  }

-- | Minimal layer info needed for effect controls
type LayerInfo =
  { id :: String
  , name :: String
  , layerType :: LayerType
  , effects :: Array EffectInstance
  }

data LayerType
  = Solid
  | Text
  | Spline
  | NullLayer
  | Camera
  | Light
  | Particles
  | Image

derive instance eqLayerType :: Eq LayerType

layerIcon :: LayerType -> String
layerIcon = case _ of
  Solid -> "■"
  Text -> "T"
  Spline -> "~"
  NullLayer -> "□"
  Camera -> "▣"
  Light -> "◎"
  Particles -> "✦"
  Image -> "▤"

-- | An effect applied to a layer
type EffectInstance =
  { id :: String
  , effectKey :: String
  , name :: String
  , enabled :: Boolean
  , expanded :: Boolean
  , parameters :: Array (Tuple String EffectParameter)
  }

-- | A single parameter on an effect
type EffectParameter =
  { name :: String
  , paramType :: ParameterType
  , value :: ParameterValue
  , animated :: Boolean
  , min :: Maybe Number
  , max :: Maybe Number
  , step :: Maybe Number
  , options :: Array { value :: String, label :: String }
  }

data ParameterType
  = NumberParam
  | AngleParam
  | PositionParam
  | ColorParam
  | EnumParam
  | CheckboxParam
  | LayerParam

derive instance eqParameterType :: Eq ParameterType

data ParameterValue
  = NumValue Number
  | PointValue { x :: Number, y :: Number }
  | ColorValue { r :: Int, g :: Int, b :: Int, a :: Number }
  | StringValue String
  | BoolValue Boolean
  | LayerRefValue (Maybe String)

data Output
  = EffectAdded String String                          -- layerId, effectKey
  | EffectRemoved String String                        -- layerId, effectId
  | EffectToggled String String Boolean                -- layerId, effectId, enabled
  | EffectReordered String Int Int                     -- layerId, fromIndex, toIndex
  | ParameterChanged String String String ParameterValue  -- layerId, effectId, paramKey, value
  | ParameterAnimationToggled String String String Boolean -- layerId, effectId, paramKey, animated

data Query a

type Slot id = H.Slot Query Output id

-- =============================================================================
--                                                                     // state
-- =============================================================================

type State =
  { layer :: Maybe LayerInfo
  , availableLayers :: Array LayerInfo
  , showAddMenu :: Boolean
  , expandedCategories :: Array String
  , dragState :: Maybe DragState
  , baseId :: String
  }

type DragState =
  { fromIndex :: Int
  , overIndex :: Maybe Int
  }

data Action
  = Initialize
  | Receive Input
  | ToggleAddMenu
  | CloseAddMenu
  | ToggleEffectCategory String
  | AddEffect String
  | RemoveEffect String
  | ToggleEffect String
  | ToggleEffectExpanded String
  | UpdateParameter String String ParameterValue
  | ToggleParameterAnimation String String
  | StartDrag Int
  | DragOver Int
  | DragEnd
  | Drop Int
  | HandleKeyDown KE.KeyboardEvent

type Slots = ()

-- =============================================================================
--                                                               // component
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
  { layer: input.layer
  , availableLayers: input.availableLayers
  , showAddMenu: false
  , expandedCategories: []
  , dragState: Nothing
  , baseId: "lattice-effect-controls"
  }

-- =============================================================================
--                                                                    // render
-- =============================================================================

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ cls [ "lattice-effect-controls" ]
    , HP.attr (HH.AttrName "style") panelStyle
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-label") "Effect Controls"
    ]
    [ renderHeader state
    , renderContent state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.div
    [ cls [ "lattice-panel-header" ]
    , HP.attr (HH.AttrName "style") headerStyle
    ]
    [ HH.div
        [ cls [ "header-row" ]
        , HP.attr (HH.AttrName "style") headerRowStyle
        ]
        [ HH.h3 
            [ HP.attr (HH.AttrName "style") titleStyle ] 
            [ HH.text "Effect Controls" ]
        , case state.layer of
            Just layer ->
              HH.div
                [ cls [ "layer-badge" ]
                , HP.attr (HH.AttrName "style") layerBadgeStyle
                ]
                [ HH.span [ cls [ "layer-type-icon" ] ] 
                    [ HH.text (layerIcon layer.layerType) ]
                , HH.text layer.name
                ]
            Nothing -> HH.text ""
        ]
    , renderAddEffectButton state
    ]

renderAddEffectButton :: forall m. State -> H.ComponentHTML Action Slots m
renderAddEffectButton state =
  HH.div
    [ cls [ "add-effect-wrapper" ]
    , HP.attr (HH.AttrName "style") "position: relative;"
    ]
    [ HH.button
        [ cls [ "lattice-btn", "add-btn" ]
        , HP.attr (HH.AttrName "style") addButtonStyle
        , HP.disabled (not (isJust state.layer))
        , HE.onClick \_ -> ToggleAddMenu
        , HP.attr (HH.AttrName "aria-haspopup") "menu"
        , HP.attr (HH.AttrName "aria-expanded") (if state.showAddMenu then "true" else "false")
        ]
        [ HH.span [ cls [ "icon" ] ] [ HH.text "+" ]
        , HH.text " Add Effect"
        ]
    , if state.showAddMenu
        then renderEffectMenu state
        else HH.text ""
    ]

renderEffectMenu :: forall m. State -> H.ComponentHTML Action Slots m
renderEffectMenu state =
  HH.div
    [ cls [ "effect-menu" ]
    , HP.attr (HH.AttrName "style") effectMenuStyle
    , HP.attr (HH.AttrName "role") "menu"
    , HP.attr (HH.AttrName "aria-label") "Add effect"
    ]
    (map (renderEffectCategoryMenu state) effectCategories)

renderEffectCategoryMenu :: forall m. State -> EffectCategoryDef -> H.ComponentHTML Action Slots m
renderEffectCategoryMenu state cat =
  let
    isExpanded = Array.elem cat.key state.expandedCategories
    effects = effectsForCategoryKey cat.key
  in
    HH.div
      [ cls [ "effect-category" ]
      ]
      [ HH.div
          [ cls [ "category-label" ]
          , HP.attr (HH.AttrName "style") categoryLabelStyle
          , HE.onClick \_ -> ToggleEffectCategory cat.key
          , HP.attr (HH.AttrName "role") "menuitem"
          , HP.attr (HH.AttrName "aria-expanded") (if isExpanded then "true" else "false")
          ]
          [ HH.span [ cls [ "cat-icon" ] ] [ HH.text cat.icon ]
          , HH.text (" " <> cat.label)
          , HH.span [ cls [ "expand-arrow" ], HP.attr (HH.AttrName "style") "margin-left: auto;" ]
              [ HH.text (if isExpanded then "▼" else "►") ]
          ]
      , if isExpanded
          then HH.div
                 [ cls [ "category-items" ]
                 , HP.attr (HH.AttrName "style") categoryItemsStyle
                 , HP.attr (HH.AttrName "role") "group"
                 ]
                 (map renderEffectMenuItem effects)
          else HH.text ""
      ]

renderEffectMenuItem :: forall m. EffectDef -> H.ComponentHTML Action Slots m
renderEffectMenuItem effect =
  HH.button
    [ cls [ "effect-menu-item" ]
    , HP.attr (HH.AttrName "style") effectMenuItemStyle
    , HP.attr (HH.AttrName "role") "menuitem"
    , HE.onClick \_ -> AddEffect effect.key
    ]
    [ HH.text effect.name ]

renderContent :: forall m. State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    [ cls [ "lattice-panel-content" ]
    , HP.attr (HH.AttrName "style") contentStyle
    ]
    [ case state.layer of
        Nothing ->
          emptyState
            { icon: "fx"
            , title: "No Layer Selected"
            , description: "Select a layer to edit its effects"
            }
        Just layer ->
          if length layer.effects == 0
            then emptyState
                   { icon: "+"
                   , title: "No Effects Applied"
                   , description: "Click 'Add Effect' to add effects to this layer"
                   }
            else HH.div
                   [ cls [ "effects-list" ]
                   , HP.attr (HH.AttrName "role") "list"
                   ]
                   (mapWithIndex (renderEffectItem state layer.id) layer.effects)
    ]

renderEffectItem :: forall m. State -> String -> Int -> EffectInstance -> H.ComponentHTML Action Slots m
renderEffectItem state layerId index effect =
  let
    isDragOver = case state.dragState of
      Just ds -> ds.overIndex == Just index
      Nothing -> false
  in
    HH.div
      [ cls [ "effect-item" ]
      , HP.attr (HH.AttrName "style") (effectItemStyle effect.expanded isDragOver)
      , HP.attr (HH.AttrName "role") "listitem"
      , HP.attr (HH.AttrName "draggable") "true"
      , HE.onDragStart \_ -> StartDrag index
      , HE.onDragOver \e -> DragOver index
      , HE.onDragEnd \_ -> DragEnd
      , HE.onDrop \_ -> Drop index
      ]
      [ renderEffectHeader state effect
      , if effect.expanded
          then renderEffectParams state layerId effect
          else HH.text ""
      ]

renderEffectHeader :: forall m. State -> EffectInstance -> H.ComponentHTML Action Slots m
renderEffectHeader _state effect =
  HH.div
    [ cls [ "effect-header" ]
    , HP.attr (HH.AttrName "style") effectHeaderStyle
    , HE.onClick \_ -> ToggleEffectExpanded effect.id
    ]
    [ HH.div 
        [ cls [ "header-left" ]
        , HP.attr (HH.AttrName "style") "display: flex; align-items: center; gap: 4px;"
        ]
        [ HH.span [ cls [ "arrow" ], HP.attr (HH.AttrName "style") arrowStyle ]
            [ HH.text (if effect.expanded then "▼" else "▶") ]
        , HH.button
            [ cls [ "icon-btn" ]
            , HP.attr (HH.AttrName "style") iconBtnStyle
            , HE.onClick \e -> ToggleEffect effect.id
            , HP.attr (HH.AttrName "aria-label") (if effect.enabled then "Disable effect" else "Enable effect")
            , HP.attr (HH.AttrName "aria-pressed") (if effect.enabled then "true" else "false")
            ]
            [ HH.span 
                [ cls [ "fx-icon" ]
                , HP.attr (HH.AttrName "style") (fxIconStyle effect.enabled)
                ] 
                [ HH.text "fx" ]
            ]
        , HH.span [ cls [ "effect-name" ], HP.attr (HH.AttrName "style") effectNameStyle ]
            [ HH.text effect.name ]
        ]
    , HH.div [ cls [ "header-right" ] ]
        [ HH.button
            [ cls [ "icon-btn", "delete" ]
            , HP.attr (HH.AttrName "style") (iconBtnStyle <> " color: var(--lattice-danger);")
            , HP.attr (HH.AttrName "title") "Remove Effect"
            , HP.attr (HH.AttrName "aria-label") "Remove effect"
            , HE.onClick \_ -> RemoveEffect effect.id
            ]
            [ HH.text "×" ]
        ]
    ]

renderEffectParams :: forall m. State -> String -> EffectInstance -> H.ComponentHTML Action Slots m
renderEffectParams state layerId effect =
  HH.div
    [ cls [ "effect-params" ]
    , HP.attr (HH.AttrName "style") effectParamsStyle
    ]
    (map (renderParameter state effect.id) effect.parameters)

renderParameter :: forall m. State -> String -> Tuple String EffectParameter -> H.ComponentHTML Action Slots m
renderParameter state effectId (Tuple paramKey param) =
  HH.div
    [ cls [ "param-row" ]
    , HP.attr (HH.AttrName "style") paramRowStyle
    ]
    [ HH.div
        [ cls [ "param-header" ]
        , HP.attr (HH.AttrName "style") paramHeaderStyle
        ]
        [ HH.span 
            [ cls [ "param-name" ]
            , HP.attr (HH.AttrName "style") paramNameStyle
            , HP.attr (HH.AttrName "title") paramKey
            ] 
            [ HH.text param.name ]
        , HH.button
            [ cls [ "keyframe-toggle" ]
            , HP.attr (HH.AttrName "style") (keyframeToggleStyle param.animated)
            , HP.attr (HH.AttrName "aria-label") "Toggle animation"
            , HP.attr (HH.AttrName "aria-pressed") (if param.animated then "true" else "false")
            , HP.attr (HH.AttrName "title") "Toggle Animation"
            , HE.onClick \_ -> ToggleParameterAnimation effectId paramKey
            ]
            [ HH.text "◆" ]
        ]
    , HH.div [ cls [ "param-control" ] ]
        [ renderParameterControl state effectId paramKey param ]
    ]

renderParameterControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderParameterControl state effectId paramKey param =
  case param.paramType of
    NumberParam ->
      renderNumberControl state effectId paramKey param
    
    AngleParam ->
      renderAngleControl state effectId paramKey param
    
    PositionParam ->
      renderPositionControl state effectId paramKey param
    
    ColorParam ->
      renderColorControl state effectId paramKey param
    
    EnumParam ->
      renderEnumControl state effectId paramKey param
    
    CheckboxParam ->
      renderCheckboxControl state effectId paramKey param
    
    LayerParam ->
      renderLayerControl state effectId paramKey param

renderNumberControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderNumberControl _state effectId paramKey param =
  let
    currentValue = case param.value of
      NumValue n -> n
      _ -> 0.0
    minVal = fromMaybe 0.0 param.min
    maxVal = fromMaybe 100.0 param.max
    stepVal = fromMaybe 1.0 param.step
  in
    HH.div
      [ cls [ "control-group" ]
      , HP.attr (HH.AttrName "style") controlGroupStyle
      ]
      [ -- Slider (if has range)
        if isJust param.min || isJust param.max
          then HH.input
                 [ HP.type_ HP.InputRange
                 , HP.attr (HH.AttrName "style") sliderStyle
                 , HP.min minVal
                 , HP.max maxVal
                 , HP.step (HP.Step stepVal)
                 , HP.value (show currentValue)
                 , HE.onValueInput \v -> UpdateParameter effectId paramKey (NumValue (parseNumber v))
                 , HP.attr (HH.AttrName "aria-label") param.name
                 ]
          else HH.text ""
      , -- Number input
        HH.input
          [ HP.type_ HP.InputNumber
          , cls [ "lattice-input", "number-input" ]
          , HP.attr (HH.AttrName "style") numberInputStyle
          , HP.value (show currentValue)
          , HP.step (HP.Step stepVal)
          , HE.onValueInput \v -> UpdateParameter effectId paramKey (NumValue (parseNumber v))
          , HP.attr (HH.AttrName "aria-label") param.name
          ]
      ]

renderAngleControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderAngleControl _state effectId paramKey param =
  let
    currentValue = case param.value of
      NumValue n -> n
      _ -> 0.0
  in
    HH.div
      [ cls [ "control-group" ]
      , HP.attr (HH.AttrName "style") controlGroupStyle
      ]
      [ -- Simple angle dial representation (circular indicator)
        HH.div
          [ cls [ "angle-dial-mini" ]
          , HP.attr (HH.AttrName "style") (anglDialMiniStyle currentValue)
          , HP.attr (HH.AttrName "title") (show currentValue <> "°")
          ]
          []
      , HH.input
          [ HP.type_ HP.InputNumber
          , cls [ "lattice-input", "number-input" ]
          , HP.attr (HH.AttrName "style") numberInputStyle
          , HP.value (show currentValue)
          , HP.step (HP.Step 1.0)
          , HE.onValueInput \v -> UpdateParameter effectId paramKey (NumValue (parseNumber v))
          , HP.attr (HH.AttrName "aria-label") (param.name <> " angle")
          ]
      , HH.span [ cls [ "unit" ], HP.attr (HH.AttrName "style") unitStyle ] [ HH.text "°" ]
      ]

renderPositionControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderPositionControl _state effectId paramKey param =
  let
    currentPoint = case param.value of
      PointValue p -> p
      _ -> { x: 0.0, y: 0.0 }
  in
    HH.div
      [ cls [ "control-group", "point-group" ]
      , HP.attr (HH.AttrName "style") pointGroupStyle
      ]
      [ HH.div [ cls [ "point-input" ] ]
          [ HH.label [ HP.attr (HH.AttrName "style") pointLabelStyle ] [ HH.text "X" ]
          , HH.input
              [ HP.type_ HP.InputNumber
              , cls [ "lattice-input" ]
              , HP.attr (HH.AttrName "style") pointInputStyle
              , HP.value (show currentPoint.x)
              , HP.step (HP.Step 1.0)
              , HE.onValueInput \v -> UpdateParameter effectId paramKey 
                  (PointValue { x: parseNumber v, y: currentPoint.y })
              , HP.attr (HH.AttrName "aria-label") (param.name <> " X")
              ]
          ]
      , HH.div [ cls [ "point-input" ] ]
          [ HH.label [ HP.attr (HH.AttrName "style") pointLabelStyle ] [ HH.text "Y" ]
          , HH.input
              [ HP.type_ HP.InputNumber
              , cls [ "lattice-input" ]
              , HP.attr (HH.AttrName "style") pointInputStyle
              , HP.value (show currentPoint.y)
              , HP.step (HP.Step 1.0)
              , HE.onValueInput \v -> UpdateParameter effectId paramKey 
                  (PointValue { x: currentPoint.x, y: parseNumber v })
              , HP.attr (HH.AttrName "aria-label") (param.name <> " Y")
              ]
          ]
      ]

renderColorControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderColorControl _state effectId paramKey param =
  let
    currentColor = case param.value of
      ColorValue c -> c
      _ -> { r: 255, g: 255, b: 255, a: 1.0 }
    hexColor = rgbToHex currentColor.r currentColor.g currentColor.b
  in
    HH.div
      [ cls [ "control-group", "color-group" ]
      , HP.attr (HH.AttrName "style") controlGroupStyle
      ]
      [ HH.input
          [ HP.type_ HP.InputColor
          , cls [ "color-input" ]
          , HP.attr (HH.AttrName "style") colorInputStyle
          , HP.value hexColor
          , HE.onValueInput \v -> 
              let rgb = hexToRgb v
              in UpdateParameter effectId paramKey (ColorValue { r: rgb.r, g: rgb.g, b: rgb.b, a: currentColor.a })
          , HP.attr (HH.AttrName "aria-label") param.name
          ]
      , HH.input
          [ HP.type_ HP.InputText
          , cls [ "lattice-input", "hex-input" ]
          , HP.attr (HH.AttrName "style") hexInputStyle
          , HP.value hexColor
          , HE.onValueInput \v -> 
              let rgb = hexToRgb v
              in UpdateParameter effectId paramKey (ColorValue { r: rgb.r, g: rgb.g, b: rgb.b, a: currentColor.a })
          , HP.attr (HH.AttrName "aria-label") (param.name <> " hex value")
          ]
      ]

renderEnumControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderEnumControl _state effectId paramKey param =
  let
    currentValue = case param.value of
      StringValue s -> s
      _ -> ""
  in
    HH.select
      [ cls [ "lattice-select", "param-select" ]
      , HP.attr (HH.AttrName "style") selectStyle
      , HP.value currentValue
      , HE.onValueInput \v -> UpdateParameter effectId paramKey (StringValue v)
      , HP.attr (HH.AttrName "aria-label") param.name
      ]
      (map (\opt -> 
        HH.option 
          [ HP.value opt.value
          , HP.selected (opt.value == currentValue)
          ] 
          [ HH.text opt.label ]
      ) param.options)

renderCheckboxControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderCheckboxControl _state effectId paramKey param =
  let
    currentValue = case param.value of
      BoolValue b -> b
      _ -> false
  in
    HH.input
      [ HP.type_ HP.InputCheckbox
      , cls [ "lattice-checkbox" ]
      , HP.checked currentValue
      , HE.onChecked \b -> UpdateParameter effectId paramKey (BoolValue b)
      , HP.attr (HH.AttrName "aria-label") param.name
      ]

renderLayerControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderLayerControl state effectId paramKey param =
  let
    currentValue = case param.value of
      LayerRefValue (Just id) -> id
      _ -> ""
    -- Filter out current layer from available layers
    availLayers = case state.layer of
      Just l -> filter (\al -> al.id /= l.id) state.availableLayers
      Nothing -> state.availableLayers
  in
    HH.select
      [ cls [ "lattice-select", "param-select", "layer-select" ]
      , HP.attr (HH.AttrName "style") layerSelectStyle
      , HP.value currentValue
      , HE.onValueInput \v -> 
          UpdateParameter effectId paramKey (LayerRefValue (if v == "" then Nothing else Just v))
      , HP.attr (HH.AttrName "aria-label") param.name
      ]
      ([ HH.option [ HP.value "" ] [ HH.text "None" ] ] <>
       map (\l -> 
         HH.option 
           [ HP.value l.id
           , HP.selected (l.id == currentValue)
           ] 
           [ HH.text l.name ]
       ) availLayers)

-- =============================================================================
--                                                           // helper functions
-- =============================================================================

parseNumber :: String -> Number
parseNumber s = fromMaybe 0.0 (Number.fromString s)

rgbToHex :: Int -> Int -> Int -> String
rgbToHex r g b =
  "#" <> toHexPair r <> toHexPair g <> toHexPair b
  where
    toHexPair :: Int -> String
    toHexPair n = 
      let hex = Int.toStringAs Int.hexadecimal (max 0 (min 255 n))
      in if String.length hex == 1 then "0" <> hex else hex

hexToRgb :: String -> { r :: Int, g :: Int, b :: Int }
hexToRgb hex =
  let
    clean = if String.take 1 hex == "#" then String.drop 1 hex else hex
    r = fromMaybe 255 (Int.fromStringAs Int.hexadecimal (String.take 2 clean))
    g = fromMaybe 255 (Int.fromStringAs Int.hexadecimal (String.take 2 (String.drop 2 clean)))
    b = fromMaybe 255 (Int.fromStringAs Int.hexadecimal (String.take 2 (String.drop 4 clean)))
  in { r, g, b }

-- =============================================================================
--                                                         // effect definitions
-- =============================================================================

type EffectCategoryDef =
  { key :: String
  , label :: String
  , icon :: String
  }

type EffectDef =
  { key :: String
  , name :: String
  , category :: String
  }

effectCategories :: Array EffectCategoryDef
effectCategories =
  [ { key: "blur", label: "Blur & Sharpen", icon: "◐" }
  , { key: "color", label: "Color Correction", icon: "◑" }
  , { key: "distort", label: "Distort", icon: "◪" }
  , { key: "generate", label: "Generate", icon: "✦" }
  , { key: "stylize", label: "Stylize", icon: "◈" }
  , { key: "utility", label: "Utility", icon: "⚙" }
  ]

effectsForCategoryKey :: String -> Array EffectDef
effectsForCategoryKey = case _ of
  "blur" ->
    [ { key: "gaussian-blur", name: "Gaussian Blur", category: "blur" }
    , { key: "box-blur", name: "Box Blur", category: "blur" }
    , { key: "directional-blur", name: "Directional Blur", category: "blur" }
    , { key: "radial-blur", name: "Radial Blur", category: "blur" }
    , { key: "sharpen", name: "Sharpen", category: "blur" }
    ]
  "color" ->
    [ { key: "curves", name: "Curves", category: "color" }
    , { key: "levels", name: "Levels", category: "color" }
    , { key: "hue-saturation", name: "Hue/Saturation", category: "color" }
    , { key: "color-balance", name: "Color Balance", category: "color" }
    , { key: "exposure", name: "Exposure", category: "color" }
    ]
  "distort" ->
    [ { key: "transform", name: "Transform", category: "distort" }
    , { key: "corner-pin", name: "Corner Pin", category: "distort" }
    , { key: "mesh-warp", name: "Mesh Warp", category: "distort" }
    , { key: "spherize", name: "Spherize", category: "distort" }
    , { key: "displacement-map", name: "Displacement Map", category: "distort" }
    ]
  "generate" ->
    [ { key: "solid", name: "Solid", category: "generate" }
    , { key: "gradient-ramp", name: "Gradient Ramp", category: "generate" }
    , { key: "fractal-noise", name: "Fractal Noise", category: "generate" }
    , { key: "checkerboard", name: "Checkerboard", category: "generate" }
    ]
  "stylize" ->
    [ { key: "glow", name: "Glow", category: "stylize" }
    , { key: "find-edges", name: "Find Edges", category: "stylize" }
    , { key: "posterize", name: "Posterize", category: "stylize" }
    , { key: "mosaic", name: "Mosaic", category: "stylize" }
    ]
  "utility" ->
    [ { key: "set-matte", name: "Set Matte", category: "utility" }
    , { key: "set-channels", name: "Set Channels", category: "utility" }
    , { key: "invert", name: "Invert", category: "utility" }
    ]
  _ -> []

-- =============================================================================
--                                                                    // styles
-- =============================================================================

panelStyle :: String
panelStyle =
  "height: 100%; display: flex; flex-direction: column; " <>
  "background: var(--lattice-surface-1); color: var(--lattice-text-primary); font-size: 13px;"

headerStyle :: String
headerStyle =
  "padding: 8px; background: var(--lattice-surface-2); border-bottom: 1px solid var(--lattice-border);"

headerRowStyle :: String
headerRowStyle =
  "display: flex; justify-content: space-between; align-items: center; margin-bottom: 8px;"

titleStyle :: String
titleStyle =
  "margin: 0; font-size: 13px; font-weight: 600; color: var(--lattice-text-muted); text-transform: uppercase;"

layerBadgeStyle :: String
layerBadgeStyle =
  "background: var(--lattice-surface-3); padding: 2px 6px; border-radius: 3px; " <>
  "color: var(--lattice-text-primary); font-size: 12px; display: flex; align-items: center; gap: 4px;"

addButtonStyle :: String
addButtonStyle =
  "width: 100%; background: var(--lattice-surface-3); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 4px; cursor: pointer; border-radius: 3px; " <>
  "display: flex; align-items: center; justify-content: center; gap: 4px;"

effectMenuStyle :: String
effectMenuStyle =
  "position: absolute; top: 100%; left: 0; right: 0; " <>
  "background: var(--lattice-surface-2); border: 1px solid var(--lattice-border); " <>
  "box-shadow: 0 4px 12px rgba(0,0,0,0.5); z-index: 1000; max-height: 400px; overflow-y: auto; margin-top: 2px;"

categoryLabelStyle :: String
categoryLabelStyle =
  "padding: 4px 8px; background: var(--lattice-surface-3); color: var(--lattice-text-muted); " <>
  "font-weight: 600; border-bottom: 1px solid var(--lattice-border); display: flex; align-items: center; " <>
  "cursor: pointer; position: sticky; top: 0;"

categoryItemsStyle :: String
categoryItemsStyle =
  "display: flex; flex-direction: column;"

effectMenuItemStyle :: String
effectMenuItemStyle =
  "display: block; width: 100%; text-align: left; padding: 6px 12px; " <>
  "background: transparent; border: none; color: var(--lattice-text-primary); " <>
  "cursor: pointer; border-bottom: 1px solid var(--lattice-border-subtle);"

contentStyle :: String
contentStyle =
  "flex: 1; overflow-y: auto; overflow-x: hidden;"

effectItemStyle :: Boolean -> Boolean -> String
effectItemStyle expanded isDragOver =
  "border-bottom: 1px solid var(--lattice-border); " <>
  "background: " <> (if isDragOver then "var(--lattice-accent-muted)" else "var(--lattice-surface-2)") <> "; " <>
  "cursor: grab;" <>
  (if isDragOver then " border-top: 2px solid var(--lattice-accent); margin-top: -2px;" else "")

effectHeaderStyle :: String
effectHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center; " <>
  "padding: 4px 2px; cursor: pointer; background: var(--lattice-surface-2); " <>
  "border-bottom: 1px solid var(--lattice-border-subtle);"

arrowStyle :: String
arrowStyle =
  "font-size: 11px; width: 12px; text-align: center; color: var(--lattice-text-muted);"

iconBtnStyle :: String
iconBtnStyle =
  "background: transparent; border: none; color: var(--lattice-text-muted); " <>
  "cursor: pointer; padding: 2px; display: flex; align-items: center; justify-content: center;"

fxIconStyle :: Boolean -> String
fxIconStyle enabled =
  "font-family: serif; font-weight: bold; font-size: 12px; " <>
  "color: " <> (if enabled then "var(--lattice-accent)" else "var(--lattice-text-muted)") <> ";"

effectNameStyle :: String
effectNameStyle =
  "font-weight: 600; color: var(--lattice-text-primary);"

effectParamsStyle :: String
effectParamsStyle =
  "padding: 4px 0; background: var(--lattice-surface-1);"

paramRowStyle :: String
paramRowStyle =
  "padding: 4px 8px; display: flex; flex-direction: column; gap: 2px; " <>
  "border-bottom: 1px solid var(--lattice-surface-2);"

paramHeaderStyle :: String
paramHeaderStyle =
  "display: flex; justify-content: space-between; align-items: center;"

paramNameStyle :: String
paramNameStyle =
  "color: var(--lattice-text-muted);"

keyframeToggleStyle :: Boolean -> String
keyframeToggleStyle active =
  "background: transparent; border: none; cursor: pointer; font-size: 12px; padding: 0; " <>
  "color: " <> (if active then "var(--lattice-accent)" else "var(--lattice-text-muted)") <> ";"

controlGroupStyle :: String
controlGroupStyle =
  "display: flex; align-items: center; gap: 8px; margin-top: 2px;"

sliderStyle :: String
sliderStyle =
  "flex: 1; height: 4px; -webkit-appearance: none; background: var(--lattice-surface-3); border-radius: 2px;"

numberInputStyle :: String
numberInputStyle =
  "width: 60px; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px;"

anglDialMiniStyle :: Number -> String
anglDialMiniStyle angle =
  "width: 24px; height: 24px; border-radius: 50%; border: 2px solid var(--lattice-border); " <>
  "background: var(--lattice-surface-3); position: relative; " <>
  "background-image: linear-gradient(from " <> show angle <> "deg, var(--lattice-accent) 2px, transparent 2px);"

unitStyle :: String
unitStyle =
  "color: var(--lattice-text-muted); font-size: 12px;"

pointGroupStyle :: String
pointGroupStyle =
  "display: grid; grid-template-columns: 1fr 1fr; gap: 8px;"

pointLabelStyle :: String
pointLabelStyle =
  "font-size: 11px; color: var(--lattice-text-muted); margin-right: 4px;"

pointInputStyle :: String
pointInputStyle =
  "width: 100%; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px;"

colorInputStyle :: String
colorInputStyle =
  "width: 32px; height: 24px; padding: 0; border: none; cursor: pointer;"

hexInputStyle :: String
hexInputStyle =
  "flex: 1; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px; font-family: monospace;"

selectStyle :: String
selectStyle =
  "width: 100%; background: var(--lattice-surface-1); border: 1px solid var(--lattice-border); " <>
  "color: var(--lattice-text-primary); padding: 2px 4px; border-radius: 2px; font-size: 12px;"

layerSelectStyle :: String
layerSelectStyle =
  selectStyle <> " background: var(--lattice-surface-2); border-color: var(--lattice-accent-muted);"

-- =============================================================================
--                                                                   // actions
-- =============================================================================

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  Receive input -> do
    H.modify_ _ { layer = input.layer, availableLayers = input.availableLayers }

  ToggleAddMenu -> do
    H.modify_ \s -> s { showAddMenu = not s.showAddMenu }

  CloseAddMenu -> do
    H.modify_ _ { showAddMenu = false }

  ToggleEffectCategory cat -> do
    state <- H.get
    let cats = state.expandedCategories
    let newCats = if Array.elem cat cats
                    then filter (_ /= cat) cats
                    else snoc cats cat
    H.modify_ _ { expandedCategories = newCats }

  AddEffect effectKey -> do
    state <- H.get
    case state.layer of
      Just layer -> do
        H.raise (EffectAdded layer.id effectKey)
        H.modify_ _ { showAddMenu = false }
      Nothing -> pure unit

  RemoveEffect effectId -> do
    state <- H.get
    case state.layer of
      Just layer -> H.raise (EffectRemoved layer.id effectId)
      Nothing -> pure unit

  ToggleEffect effectId -> do
    state <- H.get
    case state.layer of
      Just layer ->
        case Array.find (\e -> e.id == effectId) layer.effects of
          Just effect -> H.raise (EffectToggled layer.id effectId (not effect.enabled))
          Nothing -> pure unit
      Nothing -> pure unit

  ToggleEffectExpanded effectId -> do
    -- This would normally update local UI state
    -- For now, we just toggle locally in layer data (would need proper state management)
    state <- H.get
    case state.layer of
      Just layer ->
        let
          updatedEffects = map (\e -> 
            if e.id == effectId 
              then e { expanded = not e.expanded }
              else e
          ) layer.effects
          updatedLayer = layer { effects = updatedEffects }
        in
          H.modify_ _ { layer = Just updatedLayer }
      Nothing -> pure unit

  UpdateParameter effectId paramKey value -> do
    state <- H.get
    case state.layer of
      Just layer -> H.raise (ParameterChanged layer.id effectId paramKey value)
      Nothing -> pure unit

  ToggleParameterAnimation effectId paramKey -> do
    state <- H.get
    case state.layer of
      Just layer ->
        case Array.find (\e -> e.id == effectId) layer.effects of
          Just effect ->
            case Array.find (\(Tuple k _) -> k == paramKey) effect.parameters of
              Just (Tuple _ param) ->
                H.raise (ParameterAnimationToggled layer.id effectId paramKey (not param.animated))
              Nothing -> pure unit
          Nothing -> pure unit
      Nothing -> pure unit

  StartDrag index -> do
    H.modify_ _ { dragState = Just { fromIndex: index, overIndex: Nothing } }

  DragOver index -> do
    H.modify_ \s -> case s.dragState of
      Just ds -> s { dragState = Just (ds { overIndex = Just index }) }
      Nothing -> s

  DragEnd -> do
    H.modify_ _ { dragState = Nothing }

  Drop targetIndex -> do
    state <- H.get
    case state.dragState, state.layer of
      Just ds, Just layer -> do
        when (ds.fromIndex /= targetIndex) do
          H.raise (EffectReordered layer.id ds.fromIndex targetIndex)
        H.modify_ _ { dragState = Nothing }
      _, _ -> H.modify_ _ { dragState = Nothing }

  HandleKeyDown ke -> do
    let key = KE.key ke
    case key of
      "Escape" -> handleAction CloseAddMenu
      _ -> pure unit
