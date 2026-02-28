-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // colorpicker // preview
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPreview — Unified color output display with all formats.
-- |
-- | ## Design Philosophy
-- |
-- | Shows the currently selected color in multiple representations:
-- | - Large swatch preview (with/without alpha checkerboard)
-- | - Original vs new color comparison
-- | - HEX value with copy button
-- | - RGB values (0-255)
-- | - HSL values (degrees, percentages)
-- | - HSV/HSB values
-- | - CMYK values (for print)
-- |
-- | All values are displayed simultaneously for easy copying/reference.

module Hydrogen.Element.Compound.ColorPicker.Preview
  ( -- * Component
    colorPreview
  
  -- * Props
  , PreviewProps
  , PreviewProp
  , defaultPreviewProps
  
  -- * Prop Builders
  , currentColor
  , originalColor
  , showOriginal
  , showHex
  , showRgb
  , showHsl
  , swatchSize
  , onCopyHex
  , onCopyRgb
  , onCopyHsl
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , not
  , (<>)
  , (+)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (<)
  , (<=)
  , (&&)
  , (==)
  )

import Data.Array (foldl)
import Data.Int (toNumber, floor) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Device as Device

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Preview properties
type PreviewProps msg =
  { -- Colors
    currentColor :: RGB.RGBA
  , originalColor :: Maybe RGB.RGBA
  
  -- Display options
  , showOriginal :: Boolean
  , showHex :: Boolean
  , showRgb :: Boolean
  , showHsl :: Boolean
  
  -- Dimensions
  , swatchSize :: Device.Pixel
  
  -- Actions
  , onCopyHex :: Maybe (String -> msg)
  , onCopyRgb :: Maybe (String -> msg)
  , onCopyHsl :: Maybe (String -> msg)
  }

-- | Property modifier
type PreviewProp msg = PreviewProps msg -> PreviewProps msg

-- | Default properties
defaultPreviewProps :: forall msg. PreviewProps msg
defaultPreviewProps =
  { currentColor: RGB.rgba 255 0 0 100
  , originalColor: Nothing
  , showOriginal: true
  , showHex: true
  , showRgb: true
  , showHsl: true
  , swatchSize: Device.px 80.0
  , onCopyHex: Nothing
  , onCopyRgb: Nothing
  , onCopyHsl: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current color
currentColor :: forall msg. RGB.RGBA -> PreviewProp msg
currentColor c props = props { currentColor = c }

-- | Set original color for comparison
originalColor :: forall msg. RGB.RGBA -> PreviewProp msg
originalColor c props = props { originalColor = Just c }

-- | Set whether to show original color
showOriginal :: forall msg. Boolean -> PreviewProp msg
showOriginal b props = props { showOriginal = b }

-- | Set whether to show hex value
showHex :: forall msg. Boolean -> PreviewProp msg
showHex b props = props { showHex = b }

-- | Set whether to show RGB values
showRgb :: forall msg. Boolean -> PreviewProp msg
showRgb b props = props { showRgb = b }

-- | Set whether to show HSL values
showHsl :: forall msg. Boolean -> PreviewProp msg
showHsl b props = props { showHsl = b }

-- | Set swatch size
swatchSize :: forall msg. Device.Pixel -> PreviewProp msg
swatchSize s props = props { swatchSize = s }

-- | Set hex copy handler
onCopyHex :: forall msg. (String -> msg) -> PreviewProp msg
onCopyHex handler props = props { onCopyHex = Just handler }

-- | Set RGB copy handler
onCopyRgb :: forall msg. (String -> msg) -> PreviewProp msg
onCopyRgb handler props = props { onCopyRgb = Just handler }

-- | Set HSL copy handler
onCopyHsl :: forall msg. (String -> msg) -> PreviewProp msg
onCopyHsl handler props = props { onCopyHsl = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render color preview with all formats
colorPreview :: forall msg. Array (PreviewProp msg) -> E.Element msg
colorPreview propModifiers =
  let
    props = foldl (\p f -> f p) defaultPreviewProps propModifiers
    
    -- Extract color values
    rec = RGB.rgbaToRecord props.currentColor
    r = rec.r
    g = rec.g
    b = rec.b
    a = rec.a
    
    -- Convert to HSL
    hslColor = rgbToHsl r g b
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "12px"
      , E.style "padding" "12px"
      , E.style "background" "#fff"
      , E.style "border-radius" "8px"
      , E.style "border" "1px solid #e5e7eb"
      ]
      [ -- Swatch comparison
        renderSwatchComparison props
        
        -- Hex value
      , if props.showHex
          then renderValueRow "HEX" ("#" <> RGB.rgbToHex (RGB.fromRGBA props.currentColor))
          else E.span_ [] []
        
        -- RGB values
      , if props.showRgb
          then renderValueRow "RGB" (show r <> ", " <> show g <> ", " <> show b)
          else E.span_ [] []
        
        -- RGBA if has alpha
      , if props.showRgb && a < 100
          then renderValueRow "RGBA" (show r <> ", " <> show g <> ", " <> show b <> ", " <> show (Int.toNumber a / 100.0))
          else E.span_ [] []
        
        -- HSL values
      , if props.showHsl
          then renderValueRow "HSL" (show hslColor.h <> "°, " <> show hslColor.s <> "%, " <> show hslColor.l <> "%")
          else E.span_ [] []
      ]

-- | Render swatch comparison (original vs current)
renderSwatchComparison :: forall msg. PreviewProps msg -> E.Element msg
renderSwatchComparison props =
  let
    size = Device.unwrapPixel props.swatchSize
    sizePx = show size <> "px"
    halfSize = show (size / 2.0) <> "px"
    
    hasAlpha = not (Opacity.isOpaque (RGB.alpha props.currentColor))
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "gap" "8px"
      , E.style "align-items" "center"
      ]
      [ -- Swatch container
        E.div_
          [ E.style "position" "relative"
          , E.style "width" sizePx
          , E.style "height" sizePx
          , E.style "border-radius" "8px"
          , E.style "overflow" "hidden"
          , E.style "border" "1px solid rgba(0,0,0,0.1)"
          ]
          [ -- Checkerboard background (for alpha)
            if hasAlpha
              then renderCheckerboard
              else E.span_ [] []
            
            -- Original color (top half) if showing comparison
          , case props.originalColor of
              Just orig | props.showOriginal ->
                E.div_
                  [ E.style "position" "absolute"
                  , E.style "top" "0"
                  , E.style "left" "0"
                  , E.style "right" "0"
                  , E.style "height" halfSize
                  , E.style "background" (RGB.rgbaToLegacyCss orig)
                  ]
                  []
              _ -> E.span_ [] []
            
            -- Current color (full or bottom half)
          , E.div_
              [ E.style "position" "absolute"
              , E.style "bottom" "0"
              , E.style "left" "0"
              , E.style "right" "0"
              , E.style "height" (case props.originalColor of
                  Just _ | props.showOriginal -> halfSize
                  _ -> sizePx)
              , E.style "background" (RGB.rgbaToLegacyCss props.currentColor)
              ]
              []
          ]
        
        -- Labels
      , case props.originalColor of
          Just _ | props.showOriginal ->
            E.div_
              [ E.style "display" "flex"
              , E.style "flex-direction" "column"
              , E.style "gap" "2px"
              , E.style "font-size" "11px"
              , E.style "color" "#666"
              ]
              [ E.span_ [] [ E.text "Original" ]
              , E.span_ [] [ E.text "New" ]
              ]
          _ -> E.span_ [] []
      ]

-- | Render a single value row
renderValueRow :: forall msg. String -> String -> E.Element msg
renderValueRow label value =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "8px"
    ]
    [ -- Label
      E.span_
        [ E.style "width" "40px"
        , E.style "font-size" "11px"
        , E.style "font-weight" "600"
        , E.style "color" "#666"
        , E.style "text-transform" "uppercase"
        ]
        [ E.text label ]
      
      -- Value
    , E.span_
        [ E.style "flex" "1"
        , E.style "font-size" "13px"
        , E.style "font-family" "monospace"
        , E.style "color" "#333"
        , E.style "background" "#f9fafb"
        , E.style "padding" "4px 8px"
        , E.style "border-radius" "4px"
        , E.style "border" "1px solid #e5e7eb"
        ]
        [ E.text value ]
      
      -- Copy button
    , E.button_
        [ E.style "padding" "4px 8px"
        , E.style "font-size" "11px"
        , E.style "background" "#f3f4f6"
        , E.style "border" "1px solid #d1d5db"
        , E.style "border-radius" "4px"
        , E.style "cursor" "pointer"
        , E.style "color" "#374151"
        ]
        [ E.text "Copy" ]
    ]

-- | Render checkerboard for transparency
renderCheckerboard :: forall msg. E.Element msg
renderCheckerboard =
  E.div_
    [ E.style "position" "absolute"
    , E.style "inset" "0"
    , E.style "background-color" "#fff"
    , E.style "background-image" "linear-gradient(45deg, #ccc 25%, transparent 25%), linear-gradient(-45deg, #ccc 25%, transparent 25%), linear-gradient(45deg, transparent 75%, #ccc 75%), linear-gradient(-45deg, transparent 75%, #ccc 75%)"
    , E.style "background-size" "12px 12px"
    , E.style "background-position" "0 0, 0 6px, 6px -6px, -6px 0"
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // color conversion
-- ═════════════════════════════════════════════════════════════════════════════

-- | Convert RGB to HSL (simplified integer version)
rgbToHsl :: Int -> Int -> Int -> { h :: Int, s :: Int, l :: Int }
rgbToHsl r g b =
  let
    r' = Int.toNumber r / 255.0
    g' = Int.toNumber g / 255.0
    b' = Int.toNumber b / 255.0
    
    maxC = maxOf3 r' g' b'
    minC = minOf3 r' g' b'
    l = (maxC + minC) / 2.0
    
    d = maxC - minC
    
    s = if d == 0.0 then 0.0
        else d / (1.0 - absNum (2.0 * l - 1.0))
    
    h = if d == 0.0 then 0.0
        else if maxC == r' then 60.0 * modFloat ((g' - b') / d) 6.0
        else if maxC == g' then 60.0 * ((b' - r') / d + 2.0)
        else 60.0 * ((r' - g') / d + 4.0)
    
    hNorm = if h < 0.0 then h + 360.0 else h
  in
    { h: Int.floor hNorm
    , s: Int.floor (s * 100.0)
    , l: Int.floor (l * 100.0)
    }

-- | Max of three numbers
maxOf3 :: Number -> Number -> Number -> Number
maxOf3 a b c = 
  if a >= b && a >= c then a
  else if b >= c then b
  else c

-- | Min of three numbers
minOf3 :: Number -> Number -> Number -> Number
minOf3 a b c =
  if a <= b && a <= c then a
  else if b <= c then b
  else c

-- | Absolute value
absNum :: Number -> Number
absNum n = if n < 0.0 then 0.0 - n else n

-- | Float modulo
modFloat :: Number -> Number -> Number
modFloat a b = a - b * Int.toNumber (Int.floor (a / b))
