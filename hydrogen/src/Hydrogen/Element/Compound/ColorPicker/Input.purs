-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // colorpicker // input
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorInput — Text input fields for color values.
-- |
-- | ## Design Philosophy
-- |
-- | Provides precise color entry via text input. Supports multiple formats:
-- | - **Hex**: #ff5500, #f50, ff5500
-- | - **RGB**: rgb(255, 85, 0) or individual R/G/B fields
-- | - **HSL**: hsl(20, 100%, 50%) or individual H/S/L fields
-- |
-- | Each format has its own component. The hex input auto-validates and
-- | normalizes input. RGB/HSL inputs show labeled fields with value bounds.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | color         | Color     | RGB/HSL           | Current color value    |
-- | | width         | Dimension | Pixel             | Input width            |
-- | | fontSize      | Typography| FontSize          | Text size              |
-- | | borderColor   | Color     | RGB               | Input border           |
-- | | borderRadius  | Geometry  | Radius            | Corner rounding        |

module Hydrogen.Element.Compound.ColorPicker.Input
  ( -- * Hex Input
    hexInput
  , HexInputProps
  , HexInputProp
  , defaultHexProps
  
  -- * RGB Input
  , rgbInput
  , RgbInputProps
  , RgbInputProp
  , defaultRgbProps
  
  -- * HSL Input
  , hslInput
  , HslInputProps
  , HslInputProp
  , defaultHslProps
  
  -- * Change Types
  , HexChange
  , RgbChange
  , HslChange
  
  -- * Hex Props
  , hexValue
  , onHexChange
  
  -- * RGB Props
  , rgbValue
  , onRgbChange
  
  -- * HSL Props
  , hslValue
  , onHslChange
  
  -- * Common Props
  , inputWidth
  , inputFontSize
  , inputBorderColor
  , inputBorderRadius
  , showLabels
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , ($)
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.Hue as Hue
import Hydrogen.Schema.Color.Saturation as Sat
import Hydrogen.Schema.Color.Lightness as Light
import Hydrogen.Schema.Color.Channel as Channel
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // change types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Change event for hex input
type HexChange =
  { hex :: String
  , valid :: Boolean
  }

-- | Change event for RGB input
type RgbChange =
  { red :: Channel.Channel
  , green :: Channel.Channel
  , blue :: Channel.Channel
  }

-- | Change event for HSL input
type HslChange =
  { hue :: Hue.Hue
  , saturation :: Sat.Saturation
  , lightness :: Light.Lightness
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hex input props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Hex input properties
type HexInputProps msg =
  { -- Value
    value :: String                    -- ^ Current hex value (without #)
  
  -- Dimensions
  , width :: Device.Pixel
  , fontSize :: FontSize.FontSize
  
  -- Appearance
  , borderColor :: Maybe RGB.RGB
  , borderRadius :: Maybe Radius.Radius
  , showLabel :: Boolean
  
  -- Behavior
  , onChange :: Maybe (HexChange -> msg)
  }

-- | Property modifier
type HexInputProp msg = HexInputProps msg -> HexInputProps msg

-- | Default hex input properties
defaultHexProps :: forall msg. HexInputProps msg
defaultHexProps =
  { value: "000000"
  , width: Device.px 100.0
  , fontSize: FontSize.fontSize 14.0
  , borderColor: Nothing
  , borderRadius: Nothing
  , showLabel: true
  , onChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // rgb input props
-- ═════════════════════════════════════════════════════════════════════════════

-- | RGB input properties
type RgbInputProps msg =
  { -- Value
    red :: Channel.Channel
  , green :: Channel.Channel
  , blue :: Channel.Channel
  
  -- Dimensions
  , width :: Device.Pixel
  , fontSize :: FontSize.FontSize
  
  -- Appearance
  , borderColor :: Maybe RGB.RGB
  , borderRadius :: Maybe Radius.Radius
  , showLabels :: Boolean
  
  -- Behavior
  , onChange :: Maybe (RgbChange -> msg)
  }

-- | Property modifier
type RgbInputProp msg = RgbInputProps msg -> RgbInputProps msg

-- | Default RGB input properties
defaultRgbProps :: forall msg. RgbInputProps msg
defaultRgbProps =
  { red: Channel.channel 0
  , green: Channel.channel 0
  , blue: Channel.channel 0
  , width: Device.px 60.0
  , fontSize: FontSize.fontSize 14.0
  , borderColor: Nothing
  , borderRadius: Nothing
  , showLabels: true
  , onChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // hsl input props
-- ═════════════════════════════════════════════════════════════════════════════

-- | HSL input properties
type HslInputProps msg =
  { -- Value
    hue :: Hue.Hue
  , saturation :: Sat.Saturation
  , lightness :: Light.Lightness
  
  -- Dimensions
  , width :: Device.Pixel
  , fontSize :: FontSize.FontSize
  
  -- Appearance
  , borderColor :: Maybe RGB.RGB
  , borderRadius :: Maybe Radius.Radius
  , showLabels :: Boolean
  
  -- Behavior
  , onChange :: Maybe (HslChange -> msg)
  }

-- | Property modifier
type HslInputProp msg = HslInputProps msg -> HslInputProps msg

-- | Default HSL input properties
defaultHslProps :: forall msg. HslInputProps msg
defaultHslProps =
  { hue: Hue.hue 0
  , saturation: Sat.saturation 100
  , lightness: Light.lightness 50
  , width: Device.px 60.0
  , fontSize: FontSize.fontSize 14.0
  , borderColor: Nothing
  , borderRadius: Nothing
  , showLabels: true
  , onChange: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set hex value
hexValue :: forall msg. String -> HexInputProp msg
hexValue v props = props { value = v }

-- | Set hex change handler
onHexChange :: forall msg. (HexChange -> msg) -> HexInputProp msg
onHexChange handler props = props { onChange = Just handler }

-- | Set RGB value
rgbValue :: forall msg. RGB.RGB -> RgbInputProp msg
rgbValue rgb props = props 
  { red = RGB.red rgb
  , green = RGB.green rgb
  , blue = RGB.blue rgb 
  }

-- | Set RGB change handler
onRgbChange :: forall msg. (RgbChange -> msg) -> RgbInputProp msg
onRgbChange handler props = props { onChange = Just handler }

-- | Set HSL value
hslValue :: forall msg. HSL.HSL -> HslInputProp msg
hslValue hsl props = props
  { hue = HSL.hue hsl
  , saturation = HSL.saturation hsl
  , lightness = HSL.lightness hsl
  }

-- | Set HSL change handler
onHslChange :: forall msg. (HslChange -> msg) -> HslInputProp msg
onHslChange handler props = props { onChange = Just handler }

-- | Set input width (works for all input types)
inputWidth :: forall r. Device.Pixel -> { width :: Device.Pixel | r } -> { width :: Device.Pixel | r }
inputWidth w props = props { width = w }

-- | Set font size (works for all input types)
inputFontSize :: forall r. FontSize.FontSize -> { fontSize :: FontSize.FontSize | r } -> { fontSize :: FontSize.FontSize | r }
inputFontSize s props = props { fontSize = s }

-- | Set border color (works for all input types)
inputBorderColor :: forall r. RGB.RGB -> { borderColor :: Maybe RGB.RGB | r } -> { borderColor :: Maybe RGB.RGB | r }
inputBorderColor c props = props { borderColor = Just c }

-- | Set border radius (works for all input types)
inputBorderRadius :: forall r. Radius.Radius -> { borderRadius :: Maybe Radius.Radius | r } -> { borderRadius :: Maybe Radius.Radius | r }
inputBorderRadius r props = props { borderRadius = Just r }

-- | Set whether to show labels
showLabels :: forall r. Boolean -> { showLabels :: Boolean | r } -> { showLabels :: Boolean | r }
showLabels b props = props { showLabels = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // hex input render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a hex color input
-- |
-- | Displays a single text field for hex color entry (e.g., "ff5500").
-- | Auto-validates input and normalizes to 6-character lowercase.
hexInput :: forall msg. Array (HexInputProp msg) -> E.Element msg
hexInput propModifiers =
  let
    props = foldl (\p f -> f p) defaultHexProps propModifiers
    
    -- Styling
    widthPx = show (Device.unwrapPixel props.width) <> "px"
    fontSizePx = show (FontSize.unwrap props.fontSize) <> "px"
    
    borderStyle = case props.borderColor of
      Just c -> "1px solid " <> RGB.toLegacyCss c
      Nothing -> "1px solid #ccc"
    
    radiusStyle = case props.borderRadius of
      Just r -> Radius.toLegacyCss r
      Nothing -> "4px"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      ]
      [ -- Hash symbol prefix
        E.span_
          [ E.style "color" "#666"
          , E.style "font-size" fontSizePx
          , E.style "font-family" "monospace"
          ]
          [ E.text "#" ]
        
        -- Hex input field
      , E.input_
          [ E.attr "type" "text"
          , E.attr "value" props.value
          , E.attr "maxlength" "6"
          , E.attr "placeholder" "000000"
          , E.attr "aria-label" $ "Hex color value: #" <> props.value
          , E.style "width" widthPx
          , E.style "padding" "4px 8px"
          , E.style "font-size" fontSizePx
          , E.style "font-family" "monospace"
          , E.style "text-transform" "lowercase"
          , E.style "border" borderStyle
          , E.style "border-radius" radiusStyle
          , E.style "outline" "none"
          ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // rgb input render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render RGB channel inputs
-- |
-- | Displays three labeled number inputs for Red, Green, Blue channels.
-- | Each input is bounded 0-255.
rgbInput :: forall msg. Array (RgbInputProp msg) -> E.Element msg
rgbInput propModifiers =
  let
    props = foldl (\p f -> f p) defaultRgbProps propModifiers
    
    -- Values
    r = Channel.unwrap props.red
    g = Channel.unwrap props.green
    b = Channel.unwrap props.blue
    
    -- Styling
    widthPx = show (Device.unwrapPixel props.width) <> "px"
    fontSizePx = show (FontSize.unwrap props.fontSize) <> "px"
    
    borderStyle = case props.borderColor of
      Just c -> "1px solid " <> RGB.toLegacyCss c
      Nothing -> "1px solid #ccc"
    
    radiusStyle = case props.borderRadius of
      Just rad -> Radius.toLegacyCss rad
      Nothing -> "4px"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "gap" "8px"
      ]
      [ renderChannelInput "R" r widthPx fontSizePx borderStyle radiusStyle props.showLabels
      , renderChannelInput "G" g widthPx fontSizePx borderStyle radiusStyle props.showLabels
      , renderChannelInput "B" b widthPx fontSizePx borderStyle radiusStyle props.showLabels
      ]

-- | Render a single channel input field
renderChannelInput :: forall msg. String -> Int -> String -> String -> String -> String -> Boolean -> E.Element msg
renderChannelInput label value widthPx fontSizePx borderStyle radiusStyle showLabel =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "2px"
    ]
    [ -- Label (if shown)
      if showLabel
        then E.span_
          [ E.style "font-size" "11px"
          , E.style "color" "#666"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text label ]
        else E.span_ [] []
      
      -- Input
    , E.input_
        [ E.attr "type" "number"
        , E.attr "value" (show value)
        , E.attr "min" "0"
        , E.attr "max" "255"
        , E.style "width" widthPx
        , E.style "padding" "4px 8px"
        , E.style "font-size" fontSizePx
        , E.style "font-family" "monospace"
        , E.style "border" borderStyle
        , E.style "border-radius" radiusStyle
        , E.style "outline" "none"
        , E.style "text-align" "center"
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // hsl input render
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render HSL inputs
-- |
-- | Displays three labeled inputs for Hue (0-359), Saturation (0-100%), 
-- | and Lightness (0-100%).
hslInput :: forall msg. Array (HslInputProp msg) -> E.Element msg
hslInput propModifiers =
  let
    props = foldl (\p f -> f p) defaultHslProps propModifiers
    
    -- Values
    h = Hue.unwrap props.hue
    s = Sat.unwrap props.saturation
    l = Light.unwrap props.lightness
    
    -- Styling
    widthPx = show (Device.unwrapPixel props.width) <> "px"
    fontSizePx = show (FontSize.unwrap props.fontSize) <> "px"
    
    borderStyle = case props.borderColor of
      Just c -> "1px solid " <> RGB.toLegacyCss c
      Nothing -> "1px solid #ccc"
    
    radiusStyle = case props.borderRadius of
      Just rad -> Radius.toLegacyCss rad
      Nothing -> "4px"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "gap" "8px"
      ]
      [ renderHslInput "H" h "°" 0 359 widthPx fontSizePx borderStyle radiusStyle props.showLabels
      , renderHslInput "S" s "%" 0 100 widthPx fontSizePx borderStyle radiusStyle props.showLabels
      , renderHslInput "L" l "%" 0 100 widthPx fontSizePx borderStyle radiusStyle props.showLabels
      ]

-- | Render a single HSL component input
renderHslInput :: forall msg. String -> Int -> String -> Int -> Int -> String -> String -> String -> String -> Boolean -> E.Element msg
renderHslInput label value suffix minVal maxVal widthPx fontSizePx borderStyle radiusStyle showLabel =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "2px"
    ]
    [ -- Label with suffix hint
      if showLabel
        then E.span_
          [ E.style "font-size" "11px"
          , E.style "color" "#666"
          , E.style "text-transform" "uppercase"
          , E.style "font-weight" "500"
          ]
          [ E.text (label <> suffix) ]
        else E.span_ [] []
      
      -- Input
    , E.input_
        [ E.attr "type" "number"
        , E.attr "value" (show value)
        , E.attr "min" (show minVal)
        , E.attr "max" (show maxVal)
        , E.style "width" widthPx
        , E.style "padding" "4px 8px"
        , E.style "font-size" fontSizePx
        , E.style "font-family" "monospace"
        , E.style "border" borderStyle
        , E.style "border-radius" radiusStyle
        , E.style "outline" "none"
        , E.style "text-align" "center"
        ]
    ]
