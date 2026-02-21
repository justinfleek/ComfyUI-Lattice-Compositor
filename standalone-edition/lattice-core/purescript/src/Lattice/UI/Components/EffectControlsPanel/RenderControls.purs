-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- | Effect Controls Panel Parameter Controls
-- |
-- | Render functions for individual parameter type controls.
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
module Lattice.UI.Components.EffectControlsPanel.RenderControls
  ( renderParameterControl
  ) where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

import Lattice.UI.Core (cls)
import Lattice.UI.Components.EffectControlsPanel.Types
  ( State
  , Action(..)
  , Slots
  , EffectParameter
  , ParameterType(..)
  , ParameterValue(..)
  , parseNumber
  , rgbToHex
  , hexToRgb
  )
import Lattice.UI.Components.EffectControlsPanel.Styles as S

-- ════════════════════════════════════════════════════════════════════════════
--                                                     // parameter controls
-- ════════════════════════════════════════════════════════════════════════════

renderParameterControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderParameterControl state effectId paramKey param =
  case param.paramType of
    NumberParam ->
      renderNumberControl effectId paramKey param
    
    AngleParam ->
      renderAngleControl effectId paramKey param
    
    PositionParam ->
      renderPositionControl effectId paramKey param
    
    ColorParam ->
      renderColorControl effectId paramKey param
    
    EnumParam ->
      renderEnumControl effectId paramKey param
    
    CheckboxParam ->
      renderCheckboxControl effectId paramKey param
    
    LayerParam ->
      renderLayerControl state effectId paramKey param

-- ── number control ──

renderNumberControl :: forall m. String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderNumberControl effectId paramKey param =
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
      , HP.attr (HH.AttrName "style") S.controlGroupStyle
      ]
      [ -- slider (if has range)
        if isJust param.min || isJust param.max
          then HH.input
                 [ HP.type_ HP.InputRange
                 , HP.attr (HH.AttrName "style") S.sliderStyle
                 , HP.min minVal
                 , HP.max maxVal
                 , HP.step (HP.Step stepVal)
                 , HP.value (show currentValue)
                 , HE.onValueInput \v -> UpdateParameter effectId paramKey (NumValue (parseNumber v))
                 , HP.attr (HH.AttrName "aria-label") param.name
                 ]
          else HH.text ""
      , -- number input
        HH.input
          [ HP.type_ HP.InputNumber
          , cls [ "lattice-input", "number-input" ]
          , HP.attr (HH.AttrName "style") S.numberInputStyle
          , HP.value (show currentValue)
          , HP.step (HP.Step stepVal)
          , HE.onValueInput \v -> UpdateParameter effectId paramKey (NumValue (parseNumber v))
          , HP.attr (HH.AttrName "aria-label") param.name
          ]
      ]

-- ── angle control ──

renderAngleControl :: forall m. String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderAngleControl effectId paramKey param =
  let
    currentValue = case param.value of
      NumValue n -> n
      _ -> 0.0
  in
    HH.div
      [ cls [ "control-group" ]
      , HP.attr (HH.AttrName "style") S.controlGroupStyle
      ]
      [ -- simple angle dial representation (circular indicator)
        HH.div
          [ cls [ "angle-dial-mini" ]
          , HP.attr (HH.AttrName "style") (S.angleDialMiniStyle currentValue)
          , HP.attr (HH.AttrName "title") (show currentValue <> " deg")
          ]
          []
      , HH.input
          [ HP.type_ HP.InputNumber
          , cls [ "lattice-input", "number-input" ]
          , HP.attr (HH.AttrName "style") S.numberInputStyle
          , HP.value (show currentValue)
          , HP.step (HP.Step 1.0)
          , HE.onValueInput \v -> UpdateParameter effectId paramKey (NumValue (parseNumber v))
          , HP.attr (HH.AttrName "aria-label") (param.name <> " angle")
          ]
      , HH.span [ cls [ "unit" ], HP.attr (HH.AttrName "style") S.unitStyle ] [ HH.text " deg" ]
      ]

-- ── position control ──

renderPositionControl :: forall m. String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderPositionControl effectId paramKey param =
  let
    currentPoint = case param.value of
      PointValue p -> p
      _ -> { x: 0.0, y: 0.0 }
  in
    HH.div
      [ cls [ "control-group", "point-group" ]
      , HP.attr (HH.AttrName "style") S.pointGroupStyle
      ]
      [ HH.div [ cls [ "point-input" ] ]
          [ HH.label [ HP.attr (HH.AttrName "style") S.pointLabelStyle ] [ HH.text "X" ]
          , HH.input
              [ HP.type_ HP.InputNumber
              , cls [ "lattice-input" ]
              , HP.attr (HH.AttrName "style") S.pointInputStyle
              , HP.value (show currentPoint.x)
              , HP.step (HP.Step 1.0)
              , HE.onValueInput \v -> UpdateParameter effectId paramKey 
                  (PointValue { x: parseNumber v, y: currentPoint.y })
              , HP.attr (HH.AttrName "aria-label") (param.name <> " X")
              ]
          ]
      , HH.div [ cls [ "point-input" ] ]
          [ HH.label [ HP.attr (HH.AttrName "style") S.pointLabelStyle ] [ HH.text "Y" ]
          , HH.input
              [ HP.type_ HP.InputNumber
              , cls [ "lattice-input" ]
              , HP.attr (HH.AttrName "style") S.pointInputStyle
              , HP.value (show currentPoint.y)
              , HP.step (HP.Step 1.0)
              , HE.onValueInput \v -> UpdateParameter effectId paramKey 
                  (PointValue { x: currentPoint.x, y: parseNumber v })
              , HP.attr (HH.AttrName "aria-label") (param.name <> " Y")
              ]
          ]
      ]

-- ── color control ──

renderColorControl :: forall m. String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderColorControl effectId paramKey param =
  let
    currentColor = case param.value of
      ColorValue c -> c
      _ -> { r: 255, g: 255, b: 255, a: 1.0 }
    hexColor = rgbToHex currentColor.r currentColor.g currentColor.b
  in
    HH.div
      [ cls [ "control-group", "color-group" ]
      , HP.attr (HH.AttrName "style") S.controlGroupStyle
      ]
      [ HH.input
          [ HP.type_ HP.InputColor
          , cls [ "color-input" ]
          , HP.attr (HH.AttrName "style") S.colorInputStyle
          , HP.value hexColor
          , HE.onValueInput \v -> 
              let rgb = hexToRgb v
              in UpdateParameter effectId paramKey (ColorValue { r: rgb.r, g: rgb.g, b: rgb.b, a: currentColor.a })
          , HP.attr (HH.AttrName "aria-label") param.name
          ]
      , HH.input
          [ HP.type_ HP.InputText
          , cls [ "lattice-input", "hex-input" ]
          , HP.attr (HH.AttrName "style") S.hexInputStyle
          , HP.value hexColor
          , HE.onValueInput \v -> 
              let rgb = hexToRgb v
              in UpdateParameter effectId paramKey (ColorValue { r: rgb.r, g: rgb.g, b: rgb.b, a: currentColor.a })
          , HP.attr (HH.AttrName "aria-label") (param.name <> " hex value")
          ]
      ]

-- ── enum control ──

renderEnumControl :: forall m. String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderEnumControl effectId paramKey param =
  let
    currentValue = case param.value of
      StringValue s -> s
      _ -> ""
  in
    HH.select
      [ cls [ "lattice-select", "param-select" ]
      , HP.attr (HH.AttrName "style") S.selectStyle
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

-- ── checkbox control ──

renderCheckboxControl :: forall m. String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderCheckboxControl effectId paramKey param =
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

-- ── layer reference control ──

renderLayerControl :: forall m. State -> String -> String -> EffectParameter -> H.ComponentHTML Action Slots m
renderLayerControl state effectId paramKey param =
  let
    currentValue = case param.value of
      LayerRefValue (Just id) -> id
      _ -> ""
    -- filter out current layer from available layers
    availLayers = case state.layer of
      Just l -> filter (\al -> al.id /= l.id) state.availableLayers
      Nothing -> state.availableLayers
  in
    HH.select
      [ cls [ "lattice-select", "param-select", "layer-select" ]
      , HP.attr (HH.AttrName "style") S.layerSelectStyle
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
