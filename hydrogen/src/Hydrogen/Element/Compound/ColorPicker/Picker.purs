-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                               // hydrogen // element // colorpicker // picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker — The ULTIMATE color picker orchestrator.
-- |
-- | ## Design Philosophy
-- |
-- | This is the main color picker component that composes all sub-components
-- | into a unified, professional-grade color selection interface.
-- |
-- | ## Features
-- |
-- | - **Wheel mode**: Hue wheel with saturation/brightness panel
-- | - **Slider mode**: Individual H/S/L or R/G/B sliders
-- | - **Magnifier**: Pixel-level precision with zoom loupe
-- | - **All formats**: HEX, RGB, HSL, HSV displayed simultaneously
-- | - **Swatches**: Preset palettes and recent colors
-- | - **Harmony**: Complementary, analogous, triadic palettes
-- | - **Contrast**: WCAG accessibility checker
-- | - **Alpha**: Full opacity control
-- | - **Eyedropper**: Screen color picking (requires FFI)
-- |
-- | ## State Management
-- |
-- | The picker maintains internal state for:
-- | - Current color (RGBA)
-- | - Original color (for comparison)
-- | - Active tab/mode
-- | - Cursor position (for magnifier)
-- | - Recent colors history

module Hydrogen.Element.Compound.ColorPicker.Picker
  ( -- * Component
    colorPicker
  
  -- * State Machine
  , update
  
  -- * Props
  , PickerProps
  , PickerProp
  , defaultPickerProps
  
  -- * State
  , PickerState
  , initialPickerState
  
  -- * State Helpers
  , extractHueFromRGBA
  , rgbaToHsl
  
  -- * Messages
  , PickerMsg(SetColor, SetHue, SetSaturation, SetLightness, SetOpacity, SetTab, SetCursor, ToggleMagnifier, SelectSwatch, SelectHarmony, CopyValue, ActivateEyedropper)
  
  -- * Prop Builders
  , initialColor
  , showWheel
  , showSliders
  , showMagnifier
  , showPreview
  , showSwatches
  , showHarmony
  , showContrast
  , showAlpha
  , showEyedropper
  , showInputs
  , pickerWidth
  , onChange
  , onMsg
  
  -- * Tabs
  , PickerTab(TabWheel, TabSliders, TabSwatches, TabHarmony)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , not
  , ($)
  , (<>)
  , (-)
  , (*)
  , (/)
  , (<=)
  , (==)
  , (&&)
  )

import Data.Array (foldl, length, drop)
import Data.Int (fromString) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Color.Conversion as Convert
import Hydrogen.Schema.Dimension.Device as Device

import Data.Array (snoc) as Array

-- Sub-components
import Hydrogen.Element.Compound.ColorPicker.Wheel as Wheel
import Hydrogen.Element.Compound.ColorPicker.Panel as Panel
import Hydrogen.Element.Compound.ColorPicker.Input as Input
import Hydrogen.Element.Compound.ColorPicker.Preview as Preview
import Hydrogen.Element.Compound.ColorPicker.Swatches as Swatches
import Hydrogen.Element.Compound.ColorPicker.Harmony as Harmony
import Hydrogen.Element.Compound.ColorPicker.Contrast as Contrast
import Hydrogen.Element.Compound.ColorPicker.Alpha as Alpha
import Hydrogen.Element.Compound.ColorPicker.Magnifier as Magnifier
import Hydrogen.Element.Compound.ColorPicker.Eyedropper as Eyedropper

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // tabs
-- ═════════════════════════════════════════════════════════════════════════════

-- | Picker interface tabs
data PickerTab
  = TabWheel      -- ^ Wheel + panel
  | TabSliders    -- ^ HSL/RGB sliders
  | TabSwatches   -- ^ Preset palettes
  | TabHarmony    -- ^ Color harmonies

derive instance eqPickerTab :: Eq PickerTab

instance showPickerTab :: Show PickerTab where
  show TabWheel = "Wheel"
  show TabSliders = "Sliders"
  show TabSwatches = "Swatches"
  show TabHarmony = "Harmony"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Picker internal state
type PickerState =
  { currentColor :: RGB.RGBA
  , originalColor :: RGB.RGBA
  , activeTab :: PickerTab
  , cursorX :: Number
  , cursorY :: Number
  , recentColors :: Array RGB.RGBA
  , magnifierActive :: Boolean
  }

-- | Initial picker state
initialPickerState :: RGB.RGBA -> PickerState
initialPickerState color =
  { currentColor: color
  , originalColor: color
  , activeTab: TabWheel
  , cursorX: 0.0
  , cursorY: 0.0
  , recentColors: []
  , magnifierActive: false
  }

-- | Extract hue from RGBA color by converting through HSL
extractHueFromRGBA :: RGB.RGBA -> Hue.Hue
extractHueFromRGBA rgba =
  let
    rgb = RGB.fromRGBA rgba
    hsl = Convert.rgbToHsl rgb
  in
    HSL.hue hsl

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages the picker can produce
data PickerMsg
  = SetColor RGB.RGBA
  | SetHue Hue.Hue
  | SetSaturation Sat.Saturation
  | SetLightness Light.Lightness
  | SetOpacity Opacity.Opacity
  | SetTab PickerTab
  | SetCursor Number Number
  | ToggleMagnifier
  | SelectSwatch RGB.RGBA
  | SelectHarmony HSL.HSL
  | CopyValue String
  | ActivateEyedropper

derive instance eqPickerMsg :: Eq PickerMsg

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                     // update
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pure state update function
-- |
-- | Takes a message and current state, returns the new state.
-- | This implements the complete state machine for the color picker.
update :: PickerMsg -> PickerState -> PickerState
update msg state = case msg of
  SetColor rgba ->
    state 
      { currentColor = rgba
      , recentColors = addToRecent rgba state.recentColors
      }
  
  SetHue newHue ->
    let
      -- Get current HSL, replace hue, convert back to RGBA
      currentHsl = rgbaToHsl state.currentColor
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newHsl = HSL.hsl 
        (Hue.unwrap newHue) 
        (Sat.unwrap (HSL.saturation currentHsl)) 
        (Light.unwrap (HSL.lightness currentHsl))
      newRgb = Convert.hslToRgb newHsl
      rec = RGB.rgbToRecord newRgb
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state { currentColor = newRgba }
  
  SetSaturation newSat ->
    let
      currentHsl = rgbaToHsl state.currentColor
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newHsl = HSL.hsl 
        (Hue.unwrap (HSL.hue currentHsl)) 
        (Sat.unwrap newSat) 
        (Light.unwrap (HSL.lightness currentHsl))
      newRgb = Convert.hslToRgb newHsl
      rec = RGB.rgbToRecord newRgb
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state { currentColor = newRgba }
  
  SetLightness newLight ->
    let
      currentHsl = rgbaToHsl state.currentColor
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newHsl = HSL.hsl 
        (Hue.unwrap (HSL.hue currentHsl)) 
        (Sat.unwrap (HSL.saturation currentHsl)) 
        (Light.unwrap newLight)
      newRgb = Convert.hslToRgb newHsl
      rec = RGB.rgbToRecord newRgb
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state { currentColor = newRgba }
  
  SetOpacity newOpacity ->
    let
      rgb = RGB.fromRGBA state.currentColor
      rec = RGB.rgbToRecord rgb
      newRgba = RGB.rgba rec.r rec.g rec.b (Opacity.unwrap newOpacity)
    in
      state { currentColor = newRgba }
  
  SetTab tab ->
    state { activeTab = tab }
  
  SetCursor x y ->
    state { cursorX = x, cursorY = y, magnifierActive = true }
  
  ToggleMagnifier ->
    state { magnifierActive = not state.magnifierActive }
  
  SelectSwatch rgba ->
    state 
      { currentColor = rgba
      , recentColors = addToRecent rgba state.recentColors
      }
  
  SelectHarmony hsl ->
    let
      newRgb = Convert.hslToRgb hsl
      rec = RGB.rgbToRecord newRgb
      currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
      newRgba = RGB.rgba rec.r rec.g rec.b currentAlpha
    in
      state 
        { currentColor = newRgba
        , recentColors = addToRecent newRgba state.recentColors
        }
  
  CopyValue _value ->
    -- Copy is a side effect handled by the parent; state unchanged
    state
  
  ActivateEyedropper ->
    -- Eyedropper activation is handled by parent; state unchanged
    state

-- | Convert RGBA to HSL for manipulation
rgbaToHsl :: RGB.RGBA -> HSL.HSL
rgbaToHsl rgba = Convert.rgbToHsl (RGB.fromRGBA rgba)

-- | Add color to recent list, keeping max 16 entries
addToRecent :: RGB.RGBA -> Array RGB.RGBA -> Array RGB.RGBA
addToRecent color recents =
  let
    -- Remove if already present to avoid duplicates
    filtered = filterNot (\c -> c == color) recents
    -- Add to end, take last 16
    added = Array.snoc filtered color
  in
    takeLast 16 added

-- | Filter out elements matching predicate
filterNot :: forall a. (a -> Boolean) -> Array a -> Array a
filterNot pred = foldl (\acc x -> if pred x then acc else Array.snoc acc x) []

-- | Take last n elements from array
takeLast :: forall a. Int -> Array a -> Array a
takeLast n arr = 
  let len = length arr
  in if len <= n then arr else drop (len - n) arr

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Picker properties
type PickerProps msg =
  { -- Initial value
    initialColor :: RGB.RGBA
  
  -- Feature toggles
  , showWheel :: Boolean
  , showSliders :: Boolean
  , showMagnifier :: Boolean
  , showPreview :: Boolean
  , showSwatches :: Boolean
  , showHarmony :: Boolean
  , showContrast :: Boolean
  , showAlpha :: Boolean
  , showEyedropper :: Boolean
  , showInputs :: Boolean
  
  -- Dimensions
  , pickerWidth :: Device.Pixel
  
  -- Callbacks
  , onChange :: Maybe (RGB.RGBA -> msg)  -- ^ Called when color changes
  , onMsg :: Maybe (PickerMsg -> msg)    -- ^ Maps internal messages to parent type
  }

-- | Property modifier
type PickerProp msg = PickerProps msg -> PickerProps msg

-- | Default properties (full-featured picker)
defaultPickerProps :: forall msg. PickerProps msg
defaultPickerProps =
  { initialColor: RGB.rgba 255 0 0 100
  , showWheel: true
  , showSliders: true
  , showMagnifier: true
  , showPreview: true
  , showSwatches: true
  , showHarmony: true
  , showContrast: true
  , showAlpha: true
  , showEyedropper: true
  , showInputs: true
  , pickerWidth: Device.px 320.0
  , onChange: Nothing
  , onMsg: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

initialColor :: forall msg. RGB.RGBA -> PickerProp msg
initialColor c props = props { initialColor = c }

showWheel :: forall msg. Boolean -> PickerProp msg
showWheel b props = props { showWheel = b }

showSliders :: forall msg. Boolean -> PickerProp msg
showSliders b props = props { showSliders = b }

showMagnifier :: forall msg. Boolean -> PickerProp msg
showMagnifier b props = props { showMagnifier = b }

showPreview :: forall msg. Boolean -> PickerProp msg
showPreview b props = props { showPreview = b }

showSwatches :: forall msg. Boolean -> PickerProp msg
showSwatches b props = props { showSwatches = b }

showHarmony :: forall msg. Boolean -> PickerProp msg
showHarmony b props = props { showHarmony = b }

showContrast :: forall msg. Boolean -> PickerProp msg
showContrast b props = props { showContrast = b }

showAlpha :: forall msg. Boolean -> PickerProp msg
showAlpha b props = props { showAlpha = b }

showEyedropper :: forall msg. Boolean -> PickerProp msg
showEyedropper b props = props { showEyedropper = b }

showInputs :: forall msg. Boolean -> PickerProp msg
showInputs b props = props { showInputs = b }

pickerWidth :: forall msg. Device.Pixel -> PickerProp msg
pickerWidth w props = props { pickerWidth = w }

onChange :: forall msg. (RGB.RGBA -> msg) -> PickerProp msg
onChange handler props = props { onChange = Just handler }

-- | Set internal message handler
-- |
-- | This maps PickerMsg to the parent's message type, enabling full interactivity.
-- | Without this, the picker renders but produces no messages.
onMsg :: forall msg. (PickerMsg -> msg) -> PickerProp msg
onMsg handler props = props { onMsg = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the ULTIMATE color picker
-- |
-- | This composes all sub-components into a unified interface.
-- | State management is external - this is a pure view function.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | colorPicker state
-- |   [ onMsg MyPickerMsg        -- Required for interactivity
-- |   , onChange MyColorChanged  -- Optional final color callback
-- |   , showAlpha true
-- |   ]
-- | ```
colorPicker :: forall msg. PickerState -> Array (PickerProp msg) -> E.Element msg
colorPicker state propModifiers =
  let
    props = foldl (\p f -> f p) defaultPickerProps propModifiers
    
    widthPx = show (Device.unwrapPixel props.pickerWidth) <> "px"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "16px"
      , E.style "width" widthPx
      , E.style "padding" "16px"
      , E.style "background" "#fff"
      , E.style "border-radius" "12px"
      , E.style "box-shadow" "0 4px 24px rgba(0,0,0,0.15)"
      , E.style "font-family" "-apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif"
      ]
      [ -- Header with eyedropper
        renderHeader props state
        
        -- Tab bar
      , renderTabBar props state.activeTab
        
        -- Main picking area (based on active tab)
      , renderMainArea props state
        
        -- Alpha slider (if enabled)
      , if props.showAlpha
          then renderAlphaSection props state
          else E.span_ [] []
        
        -- Input fields (if enabled)
      , if props.showInputs
          then renderInputSection props state
          else E.span_ [] []
        
        -- Preview section
      , if props.showPreview
          then 
            let
              previewHandlers = case props.onMsg of
                Just toMsg ->
                  [ Preview.onCopyHex $ \hex -> toMsg (CopyValue hex)
                  , Preview.onCopyRgb $ \rgbStr -> toMsg (CopyValue rgbStr)
                  , Preview.onCopyHsl $ \hslStr -> toMsg (CopyValue hslStr)
                  ]
                Nothing -> []
            in
              Preview.colorPreview
                (previewHandlers <>
                [ Preview.currentColor state.currentColor
                , Preview.originalColor state.originalColor
                ])
          else E.span_ [] []
        
        -- Contrast checker (if enabled)
      , if props.showContrast
          then renderContrastSection state
          else E.span_ [] []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // section renders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render header with eyedropper button
renderHeader :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderHeader props _state =
  E.div_
    [ E.style "display" "flex"
    , E.style "justify-content" "space-between"
    , E.style "align-items" "center"
    ]
    [ E.span_
        [ E.style "font-size" "14px"
        , E.style "font-weight" "600"
        , E.style "color" "#374151"
        ]
        [ E.text "Color Picker" ]
    
    , if props.showEyedropper
        then 
          let
            eyedropperHandlers = case props.onMsg of
              Just toMsg -> [ Eyedropper.onActivate (toMsg ActivateEyedropper) ]
              Nothing -> []
          in
            Eyedropper.eyedropperButton eyedropperHandlers
        else E.span_ [] []
    ]

-- | Render tab bar
renderTabBar :: forall msg. PickerProps msg -> PickerTab -> E.Element msg
renderTabBar props activeTab =
  E.div_
    [ E.style "display" "flex"
    , E.style "gap" "4px"
    , E.style "padding" "4px"
    , E.style "background" "#f3f4f6"
    , E.style "border-radius" "8px"
    ]
    [ renderTab props TabWheel activeTab
    , renderTab props TabSliders activeTab
    , renderTab props TabSwatches activeTab
    , renderTab props TabHarmony activeTab
    ]

-- | Render a single tab
renderTab :: forall msg. PickerProps msg -> PickerTab -> PickerTab -> E.Element msg
renderTab props tab activeTab =
  let
    isActive = tab == activeTab
    bgColor = if isActive then "#fff" else "transparent"
    textColor = if isActive then "#374151" else "#6b7280"
    shadow = if isActive then "0 1px 3px rgba(0,0,0,0.1)" else "none"
    
    -- Wire click handler if onMsg is provided
    clickAttr = case props.onMsg of
      Just toMsg -> [ E.onClick (toMsg (SetTab tab)) ]
      Nothing -> []
  in
    E.button_
      (clickAttr <>
      [ E.style "flex" "1"
      , E.style "padding" "8px 12px"
      , E.style "font-size" "12px"
      , E.style "font-weight" "500"
      , E.style "background" bgColor
      , E.style "color" textColor
      , E.style "border" "none"
      , E.style "border-radius" "6px"
      , E.style "cursor" "pointer"
      , E.style "box-shadow" shadow
      , E.style "transition" "all 0.15s"
      ])
      [ E.text (show tab) ]

-- | Render main picking area based on active tab
renderMainArea :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderMainArea props state =
  case state.activeTab of
    TabWheel -> renderWheelMode props state
    TabSliders -> renderSliderMode props state
    TabSwatches -> renderSwatchMode props
    TabHarmony -> renderHarmonyMode props state

-- | Render wheel mode (wheel + panel + magnifier)
renderWheelMode :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderWheelMode props state =
  let
    -- Extract HSL from current color
    currentHsl = rgbaToHsl state.currentColor
    currentHue = HSL.hue currentHsl
    currentSat = HSL.saturation currentHsl
    currentLight = HSL.lightness currentHsl
    
    -- Wire handlers if onMsg is provided
    wheelHandlers = case props.onMsg of
      Just toMsg -> 
        [ Wheel.onHueChange $ \h -> toMsg (SetHue h) ]
      Nothing -> []
    
    panelHandlers = case props.onMsg of
      Just toMsg ->
        [ Panel.onChange $ \change -> toMsg (SetSaturation change.saturation) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "gap" "12px"
      ]
      [ -- Hue wheel for selecting hue angle
        Wheel.colorWheel
          (wheelHandlers <>
          [ Wheel.hue currentHue
          , Wheel.size (Device.px 180.0)
          ])
        
        -- Panel (saturation/brightness)
      , Panel.saturationPanel
          (panelHandlers <>
          [ Panel.hue currentHue
          , Panel.saturation currentSat
          , Panel.brightness currentLight
          ])
        
        -- Magnifier (if enabled and active)
      , if props.showMagnifier && state.magnifierActive
          then Magnifier.magnifier
              [ Magnifier.cursorX state.cursorX
              , Magnifier.cursorY state.cursorY
              ]
          else E.span_ [] []
      ]

-- | Render slider mode with HSL sliders
renderSliderMode :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderSliderMode props state =
  let
    -- Extract HSL from current color
    currentHsl = rgbaToHsl state.currentColor
    currentHue = HSL.hue currentHsl
    currentSat = HSL.saturation currentHsl
    currentLight = HSL.lightness currentHsl
    
    -- Common slider style
    sliderRowStyle = 
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "12px"
      ]
    
    sliderLabelStyle =
      [ E.style "width" "80px"
      , E.style "font-size" "12px"
      , E.style "color" "#374151"
      ]
    
    sliderValueStyle =
      [ E.style "width" "40px"
      , E.style "font-size" "12px"
      , E.style "color" "#6b7280"
      , E.style "text-align" "right"
      ]
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "12px"
      ]
      [ -- Section header
        E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "HSL Sliders" ]
      
        -- Hue slider (0-359)
      , E.div_ sliderRowStyle
          [ E.span_ sliderLabelStyle [ E.text "Hue" ]
          , renderHueSlider props currentHue
          , E.span_ sliderValueStyle [ E.text (show (Hue.unwrap currentHue) <> "°") ]
          ]
      
        -- Saturation slider (0-100)  
      , E.div_ sliderRowStyle
          [ E.span_ sliderLabelStyle [ E.text "Saturation" ]
          , renderSaturationSlider props currentHue currentSat
          , E.span_ sliderValueStyle [ E.text (show (Sat.unwrap currentSat) <> "%") ]
          ]
      
        -- Lightness slider (0-100)
      , E.div_ sliderRowStyle
          [ E.span_ sliderLabelStyle [ E.text "Lightness" ]
          , renderLightnessSlider props currentHue currentLight
          , E.span_ sliderValueStyle [ E.text (show (Light.unwrap currentLight) <> "%") ]
          ]
      ]

-- | Render hue slider (0-359 degrees)
renderHueSlider :: forall msg. PickerProps msg -> Hue.Hue -> E.Element msg
renderHueSlider props currentHue =
  let
    -- Hue gradient background
    hueGradient = "linear-gradient(to right, hsl(0,100%,50%), hsl(60,100%,50%), hsl(120,100%,50%), hsl(180,100%,50%), hsl(240,100%,50%), hsl(300,100%,50%), hsl(360,100%,50%))"
    
    -- Calculate thumb position (0-100%)
    thumbPos = show ((Hue.unwrap currentHue * 100) / 359) <> "%"
    
    -- Wire handler
    inputHandler = case props.onMsg of
      Just toMsg ->
        [ E.onInput $ \val -> toMsg (SetHue (Hue.hue (stringToInt val))) ]
      Nothing -> []
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "flex" "1"
      , E.style "height" "20px"
      , E.style "border-radius" "10px"
      , E.style "background" hueGradient
      ]
      [ E.input_
          (inputHandler <>
          [ E.attr "type" "range"
          , E.attr "min" "0"
          , E.attr "max" "359"
          , E.attr "value" (show (Hue.unwrap currentHue))
          , E.style "position" "absolute"
          , E.style "width" "100%"
          , E.style "height" "100%"
          , E.style "opacity" "0"
          , E.style "cursor" "pointer"
          ])
      , E.div_
          [ E.style "position" "absolute"
          , E.style "left" thumbPos
          , E.style "top" "50%"
          , E.style "transform" "translate(-50%, -50%)"
          , E.style "width" "16px"
          , E.style "height" "16px"
          , E.style "border-radius" "50%"
          , E.style "background" "#fff"
          , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
          , E.style "pointer-events" "none"
          ]
          []
      ]

-- | Render saturation slider (0-100%)
renderSaturationSlider :: forall msg. PickerProps msg -> Hue.Hue -> Sat.Saturation -> E.Element msg
renderSaturationSlider props currentHue currentSat =
  let
    -- Saturation gradient (gray to full saturation at current hue)
    h = Hue.unwrap currentHue
    satGradient = "linear-gradient(to right, hsl(" <> show h <> ",0%,50%), hsl(" <> show h <> ",100%,50%))"
    
    -- Calculate thumb position
    thumbPos = show (Sat.unwrap currentSat) <> "%"
    
    -- Wire handler
    inputHandler = case props.onMsg of
      Just toMsg ->
        [ E.onInput $ \val -> toMsg (SetSaturation (Sat.saturation (stringToInt val))) ]
      Nothing -> []
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "flex" "1"
      , E.style "height" "20px"
      , E.style "border-radius" "10px"
      , E.style "background" satGradient
      ]
      [ E.input_
          (inputHandler <>
          [ E.attr "type" "range"
          , E.attr "min" "0"
          , E.attr "max" "100"
          , E.attr "value" (show (Sat.unwrap currentSat))
          , E.style "position" "absolute"
          , E.style "width" "100%"
          , E.style "height" "100%"
          , E.style "opacity" "0"
          , E.style "cursor" "pointer"
          ])
      , E.div_
          [ E.style "position" "absolute"
          , E.style "left" thumbPos
          , E.style "top" "50%"
          , E.style "transform" "translate(-50%, -50%)"
          , E.style "width" "16px"
          , E.style "height" "16px"
          , E.style "border-radius" "50%"
          , E.style "background" "#fff"
          , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
          , E.style "pointer-events" "none"
          ]
          []
      ]

-- | Render lightness slider (0-100%)
renderLightnessSlider :: forall msg. PickerProps msg -> Hue.Hue -> Light.Lightness -> E.Element msg
renderLightnessSlider props currentHue currentLight =
  let
    -- Lightness gradient (black to white through the hue)
    h = Hue.unwrap currentHue
    lightGradient = "linear-gradient(to right, hsl(" <> show h <> ",100%,0%), hsl(" <> show h <> ",100%,50%), hsl(" <> show h <> ",100%,100%))"
    
    -- Calculate thumb position
    thumbPos = show (Light.unwrap currentLight) <> "%"
    
    -- Wire handler
    inputHandler = case props.onMsg of
      Just toMsg ->
        [ E.onInput $ \val -> toMsg (SetLightness (Light.lightness (stringToInt val))) ]
      Nothing -> []
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "flex" "1"
      , E.style "height" "20px"
      , E.style "border-radius" "10px"
      , E.style "background" lightGradient
      ]
      [ E.input_
          (inputHandler <>
          [ E.attr "type" "range"
          , E.attr "min" "0"
          , E.attr "max" "100"
          , E.attr "value" (show (Light.unwrap currentLight))
          , E.style "position" "absolute"
          , E.style "width" "100%"
          , E.style "height" "100%"
          , E.style "opacity" "0"
          , E.style "cursor" "pointer"
          ])
      , E.div_
          [ E.style "position" "absolute"
          , E.style "left" thumbPos
          , E.style "top" "50%"
          , E.style "transform" "translate(-50%, -50%)"
          , E.style "width" "16px"
          , E.style "height" "16px"
          , E.style "border-radius" "50%"
          , E.style "background" "#fff"
          , E.style "box-shadow" "0 1px 3px rgba(0,0,0,0.3)"
          , E.style "pointer-events" "none"
          ]
          []
      ]

-- | Parse string to int (for slider values)
stringToInt :: String -> Int
stringToInt s = case Int.fromString s of
  Just n -> n
  Nothing -> 0

-- | Render swatch palette mode
renderSwatchMode :: forall msg. PickerProps msg -> E.Element msg
renderSwatchMode props =
  let
    -- Wire handler if onMsg is provided
    swatchHandlers = case props.onMsg of
      Just toMsg ->
        [ Swatches.onSelect $ \rgba -> toMsg (SelectSwatch rgba) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "12px"
      ]
      [ E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "Material Colors" ]
      , Swatches.swatchGrid
          (swatchHandlers <>
          [ Swatches.swatches Swatches.materialPrimary
          , Swatches.columns 8
          ])
      ]

-- | Render harmony mode
renderHarmonyMode :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderHarmonyMode props state =
  let
    -- Base color for harmony calculations
    baseHsl = rgbaToHsl state.currentColor
    
    -- Wire handler if onMsg is provided
    harmonyHandlers = case props.onMsg of
      Just toMsg ->
        [ Harmony.onSelect $ \hsl -> toMsg (SelectHarmony hsl) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "16px"
      ]
      [ Harmony.harmonyPalette 
          (harmonyHandlers <>
          [ Harmony.harmonyType Harmony.Complementary
          , Harmony.baseColor baseHsl
          ])
      , Harmony.harmonyPalette 
          (harmonyHandlers <>
          [ Harmony.harmonyType Harmony.Analogous
          , Harmony.baseColor baseHsl
          ])
      , Harmony.harmonyPalette 
          (harmonyHandlers <>
          [ Harmony.harmonyType Harmony.Triadic
          , Harmony.baseColor baseHsl
          ])
      ]

-- | Render alpha slider section
renderAlphaSection :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderAlphaSection props state =
  let
    rgb = RGB.fromRGBA state.currentColor
    opacity = RGB.alpha state.currentColor
    
    -- Wire change handler if onMsg is provided
    changeHandler = case props.onMsg of
      Just toMsg -> [ Alpha.onChange (\change -> toMsg (SetOpacity change.opacity)) ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "4px"
      ]
      [ E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "Opacity" ]
      , Alpha.alphaSlider
          (changeHandler <>
          [ Alpha.color rgb
          , Alpha.opacity opacity
          ])
      ]

-- | Render input fields section
renderInputSection :: forall msg. PickerProps msg -> PickerState -> E.Element msg
renderInputSection props state =
  let
    -- Current values
    rgb = RGB.fromRGBA state.currentColor
    currentAlpha = Opacity.unwrap (RGB.alpha state.currentColor)
    
    -- Wire hex input handler
    hexHandlers = case props.onMsg of
      Just toMsg ->
        [ Input.onHexChange $ \change ->
            if change.valid
              then 
                let 
                  newRgb = Convert.hexToRgb change.hex
                  r = RGB.rgbToRecord newRgb
                in toMsg (SetColor (RGB.rgba r.r r.g r.b currentAlpha))
              else toMsg (SetColor state.currentColor)
        ]
      Nothing -> []
    
    -- Wire RGB input handler
    rgbHandlers = case props.onMsg of
      Just toMsg ->
        [ Input.onRgbChange $ \change ->
            toMsg (SetColor (RGB.rgba 
              (Channel.unwrap change.red) 
              (Channel.unwrap change.green) 
              (Channel.unwrap change.blue) 
              currentAlpha))
        ]
      Nothing -> []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ -- Hex input
        E.div_
          [ E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "gap" "8px"
          ]
          [ E.span_
              [ E.style "width" "32px"
              , E.style "font-size" "11px"
              , E.style "color" "#6b7280"
              ]
              [ E.text "HEX" ]
          , Input.hexInput
              (hexHandlers <>
              [ Input.hexValue (RGB.rgbToHex rgb) ])
          ]
        
        -- RGB inputs
      , E.div_
          [ E.style "display" "flex"
          , E.style "align-items" "center"
          , E.style "gap" "8px"
          ]
          [ E.span_
              [ E.style "width" "32px"
              , E.style "font-size" "11px"
              , E.style "color" "#6b7280"
              ]
              [ E.text "RGB" ]
          , Input.rgbInput
              (rgbHandlers <>
              [ Input.rgbValue rgb ])
          ]
      ]

-- | Render contrast checker section
renderContrastSection :: forall msg. PickerState -> E.Element msg
renderContrastSection state =
  let
    rgb = RGB.fromRGBA state.currentColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ E.div_
          [ E.style "font-size" "11px"
          , E.style "color" "#6b7280"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text "Contrast Check" ]
      , Contrast.contrastChecker
          [ Contrast.foreground rgb
          , Contrast.background (RGB.rgb 255 255 255)
          ]
      ]
