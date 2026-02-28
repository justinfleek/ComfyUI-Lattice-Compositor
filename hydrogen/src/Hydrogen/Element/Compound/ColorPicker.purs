-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                        // hydrogen // element // color picker
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorPicker — Schema-native color selection component.
-- |
-- | ## Design Philosophy
-- |
-- | This component is a **compound** of Schema atoms. It composes Slider and
-- | Checkbox sub-components to allow interactive color selection across
-- | multiple color spaces:
-- |
-- | - **HSL**: Hue (0-359), Saturation (0-100), Lightness (0-100)
-- | - **RGB**: Red (0-255), Green (0-255), Blue (0-255)
-- | - **HWB**: Hue (0-359), Whiteness (0-100), Blackness (0-100)
-- | - **OKLAB**: L (0-1), a (-0.4 to 0.4), b (-0.4 to 0.4)
-- | - **OKLCH**: L (0-1), Chroma (0-0.4), Hue (0-359)
-- |
-- | All color math uses the Schema conversion functions, ensuring consistency
-- | across all representations.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property               | Pillar     | Type                      | CSS Output              |
-- | |------------------------|------------|---------------------------|-------------------------|
-- | | backgroundColor        | Color      | Color.RGB                 | panel background        |
-- | | borderColor            | Color      | Color.RGB                 | panel border            |
-- | | labelColor             | Color      | Color.RGB                 | mode/slider labels      |
-- | | primaryColor           | Color      | Color.RGB                 | accent elements         |
-- | | sliderTrackColor       | Color      | Color.RGB                 | slider track bg         |
-- | | previewBorderRadius    | Geometry   | Geometry.Radius           | color preview rounding  |
-- | | panelBorderRadius      | Geometry   | Geometry.Radius           | panel rounding          |
-- | | padding                | Dimension  | Device.Pixel              | internal padding        |
-- | | gap                    | Dimension  | Device.Pixel              | spacing between sections|
-- | | borderWidth            | Dimension  | Device.Pixel              | panel border width      |
-- | | previewHeight          | Dimension  | Device.Pixel              | color preview height    |
-- | | labelFontSize          | Typography | Typography.FontSize       | label font size         |
-- | | labelFontWeight        | Typography | Typography.FontWeight     | label font weight       |
-- | | headerFontSize         | Typography | Typography.FontSize       | mode header font size   |
-- | | headerFontWeight       | Typography | Typography.FontWeight     | mode header font weight |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.ColorPicker as ColorPicker
-- | import Hydrogen.Schema.Color.RGB as Color
-- |
-- | -- Basic color picker
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.color (Color.rgb 100 150 200)
-- |   , ColorPicker.onChange HandleColorChange
-- |   ]
-- |
-- | -- With enabled modes and brand atoms
-- | ColorPicker.colorPicker
-- |   [ ColorPicker.color state.currentColor
-- |   , ColorPicker.onChange HandleColorChange
-- |   , ColorPicker.enabledModes [ColorPicker.ModeHSL, ColorPicker.ModeRGB]
-- |   , ColorPicker.backgroundColor brand.surfaceColor
-- |   , ColorPicker.primaryColor brand.primaryColor
-- |   ]
-- | ```

module Hydrogen.Element.Compound.ColorPicker
  ( -- * Component
    colorPicker
  
  -- * Props
  , ColorPickerProps
  , ColorPickerProp
  , defaultProps
  
  -- * State Props
  , color
  , enabledModes
  
  -- * Color Atoms
  , backgroundColor
  , borderColor
  , labelColor
  , primaryColor
  , sliderTrackColor
  
  -- * Geometry Atoms
  , previewBorderRadius
  , panelBorderRadius
  
  -- * Dimension Atoms
  , padding
  , gap
  , borderWidth
  , previewHeight
  
  -- * Typography Atoms
  , labelFontSize
  , labelFontWeight
  , headerFontSize
  , headerFontWeight
  
  -- * Behavior Props
  , onChange
  , onModeToggle
  
  -- * Types
  , ColorMode(ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH)
  , modeName
  ) where

import Prelude
  ( class Eq
  , map
  , negate
  , not
  , show
  , (<>)
  )

import Data.Array (foldl, elem)
import Data.Int (round, toNumber)
import Data.Maybe (Maybe(Nothing, Just), maybe)
import Data.Number.Format (fixed, toStringWith)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.HSL as HSL
import Hydrogen.Schema.Color.HWB as HWB
import Hydrogen.Schema.Color.OKLAB as OKLAB
import Hydrogen.Schema.Color.OKLCH as OKLCH
import Hydrogen.Schema.Color.Conversion as Convert
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Typography.FontSize as FontSize
import Hydrogen.Schema.Typography.FontWeight as FontWeight

import Hydrogen.Element.Compound.Slider as Slider
import Hydrogen.Element.Compound.Checkbox as Checkbox

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Color picker mode
data ColorMode
  = ModeHSL
  | ModeRGB
  | ModeHWB
  | ModeOKLAB
  | ModeOKLCH

derive instance eqColorMode :: Eq ColorMode

-- | Get display name for mode
modeName :: ColorMode -> String
modeName = case _ of
  ModeHSL -> "HSL"
  ModeRGB -> "RGB"
  ModeHWB -> "HWB"
  ModeOKLAB -> "OKLAB"
  ModeOKLCH -> "OKLCH"

-- | All available modes
allModes :: Array ColorMode
allModes = [ModeHSL, ModeRGB, ModeHWB, ModeOKLAB, ModeOKLCH]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | ColorPicker properties
-- |
-- | All visual properties accept Schema atoms directly.
type ColorPickerProps msg =
  { -- State
    color :: Color.RGB
  , enabledModes :: Array ColorMode
  
  -- Color atoms
  , backgroundColor :: Maybe Color.RGB
  , borderColor :: Maybe Color.RGB
  , labelColor :: Maybe Color.RGB
  , primaryColor :: Maybe Color.RGB
  , sliderTrackColor :: Maybe Color.RGB
  
  -- Geometry atoms
  , previewBorderRadius :: Maybe Geometry.Radius
  , panelBorderRadius :: Maybe Geometry.Radius
  
  -- Dimension atoms
  , padding :: Maybe Device.Pixel
  , gap :: Maybe Device.Pixel
  , borderWidth :: Maybe Device.Pixel
  , previewHeight :: Maybe Device.Pixel
  
  -- Typography atoms
  , labelFontSize :: Maybe FontSize.FontSize
  , labelFontWeight :: Maybe FontWeight.FontWeight
  , headerFontSize :: Maybe FontSize.FontSize
  , headerFontWeight :: Maybe FontWeight.FontWeight
  
  -- Behavior
  , onChange :: Maybe (Color.RGB -> msg)
  , onModeToggle :: Maybe (ColorMode -> Boolean -> msg)
  }

-- | Property modifier function
type ColorPickerProp msg = ColorPickerProps msg -> ColorPickerProps msg

-- | Default properties
defaultProps :: forall msg. ColorPickerProps msg
defaultProps =
  { color: Color.rgb 128 128 128
  , enabledModes: allModes
  , backgroundColor: Nothing
  , borderColor: Nothing
  , labelColor: Nothing
  , primaryColor: Nothing
  , sliderTrackColor: Nothing
  , previewBorderRadius: Nothing
  , panelBorderRadius: Nothing
  , padding: Nothing
  , gap: Nothing
  , borderWidth: Nothing
  , previewHeight: Nothing
  , labelFontSize: Nothing
  , labelFontWeight: Nothing
  , headerFontSize: Nothing
  , headerFontWeight: Nothing
  , onChange: Nothing
  , onModeToggle: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set current color
color :: forall msg. Color.RGB -> ColorPickerProp msg
color c props = props { color = c }

-- | Set which color modes are enabled
enabledModes :: forall msg. Array ColorMode -> ColorPickerProp msg
enabledModes modes props = props { enabledModes = modes }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set panel background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> ColorPickerProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set panel border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> ColorPickerProp msg
borderColor c props = props { borderColor = Just c }

-- | Set label text color (Color.RGB atom)
labelColor :: forall msg. Color.RGB -> ColorPickerProp msg
labelColor c props = props { labelColor = Just c }

-- | Set primary/accent color (Color.RGB atom)
primaryColor :: forall msg. Color.RGB -> ColorPickerProp msg
primaryColor c props = props { primaryColor = Just c }

-- | Set slider track color (Color.RGB atom)
sliderTrackColor :: forall msg. Color.RGB -> ColorPickerProp msg
sliderTrackColor c props = props { sliderTrackColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set color preview border radius (Geometry.Radius atom)
previewBorderRadius :: forall msg. Geometry.Radius -> ColorPickerProp msg
previewBorderRadius r props = props { previewBorderRadius = Just r }

-- | Set panel border radius (Geometry.Radius atom)
panelBorderRadius :: forall msg. Geometry.Radius -> ColorPickerProp msg
panelBorderRadius r props = props { panelBorderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set internal padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> ColorPickerProp msg
padding p props = props { padding = Just p }

-- | Set gap between sections (Device.Pixel atom)
gap :: forall msg. Device.Pixel -> ColorPickerProp msg
gap g props = props { gap = Just g }

-- | Set panel border width (Device.Pixel atom)
borderWidth :: forall msg. Device.Pixel -> ColorPickerProp msg
borderWidth w props = props { borderWidth = Just w }

-- | Set color preview height (Device.Pixel atom)
previewHeight :: forall msg. Device.Pixel -> ColorPickerProp msg
previewHeight h props = props { previewHeight = Just h }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // prop builders: typography
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set label font size (Typography.FontSize atom)
labelFontSize :: forall msg. FontSize.FontSize -> ColorPickerProp msg
labelFontSize s props = props { labelFontSize = Just s }

-- | Set label font weight (Typography.FontWeight atom)
labelFontWeight :: forall msg. FontWeight.FontWeight -> ColorPickerProp msg
labelFontWeight w props = props { labelFontWeight = Just w }

-- | Set mode header font size (Typography.FontSize atom)
headerFontSize :: forall msg. FontSize.FontSize -> ColorPickerProp msg
headerFontSize s props = props { headerFontSize = Just s }

-- | Set mode header font weight (Typography.FontWeight atom)
headerFontWeight :: forall msg. FontWeight.FontWeight -> ColorPickerProp msg
headerFontWeight w props = props { headerFontWeight = Just w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set color change handler
onChange :: forall msg. (Color.RGB -> msg) -> ColorPickerProp msg
onChange handler props = props { onChange = Just handler }

-- | Set mode toggle handler
onModeToggle :: forall msg. (ColorMode -> Boolean -> msg) -> ColorPickerProp msg
onModeToggle handler props = props { onModeToggle = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

-- | Default background color (dark surface)
defaultBackgroundColor :: Color.RGB
defaultBackgroundColor = Color.rgb 30 30 30

-- | Default border color (subtle)
defaultBorderColor :: Color.RGB
defaultBorderColor = Color.rgb 64 64 64

-- | Default label color (muted white)
defaultLabelColor :: Color.RGB
defaultLabelColor = Color.rgb 156 163 175

-- | Default primary color (blue)
defaultPrimaryColor :: Color.RGB
defaultPrimaryColor = Color.rgb 59 130 246

-- | Default slider track color (dark gray)
defaultSliderTrackColor :: Color.RGB
defaultSliderTrackColor = Color.rgb 64 64 64

-- | Default preview border radius
defaultPreviewRadius :: Geometry.Radius
defaultPreviewRadius = Geometry.px 4.0

-- | Default panel border radius
defaultPanelRadius :: Geometry.Radius
defaultPanelRadius = Geometry.px 8.0

-- | Default padding
defaultPadding :: Device.Pixel
defaultPadding = Device.px 16.0

-- | Default gap
defaultGap :: Device.Pixel
defaultGap = Device.px 16.0

-- | Default border width
defaultBorderWidth :: Device.Pixel
defaultBorderWidth = Device.px 1.0

-- | Default preview height
defaultPreviewHeight :: Device.Pixel
defaultPreviewHeight = Device.px 64.0

-- | Default label font size (11px)
defaultLabelFontSize :: FontSize.FontSize
defaultLabelFontSize = FontSize.fontSize 11.0

-- | Default label font weight (500 = medium)
defaultLabelFontWeight :: FontWeight.FontWeight
defaultLabelFontWeight = FontWeight.medium

-- | Default header font size (12px)
defaultHeaderFontSize :: FontSize.FontSize
defaultHeaderFontSize = FontSize.fontSize 12.0

-- | Default header font weight (700 = bold)
defaultHeaderFontWeight :: FontWeight.FontWeight
defaultHeaderFontWeight = FontWeight.bold

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get effective value with fallback
getColor :: Maybe Color.RGB -> Color.RGB -> Color.RGB
getColor maybeC fallback = maybe fallback (\c -> c) maybeC

getRadius :: Maybe Geometry.Radius -> Geometry.Radius -> Geometry.Radius
getRadius maybeR fallback = maybe fallback (\r -> r) maybeR

getPixel :: Maybe Device.Pixel -> Device.Pixel -> Device.Pixel
getPixel maybeP fallback = maybe fallback (\p -> p) maybeP

getFontSize :: Maybe FontSize.FontSize -> FontSize.FontSize -> FontSize.FontSize
getFontSize maybeS fallback = maybe fallback (\s -> s) maybeS

getFontWeight :: Maybe FontWeight.FontWeight -> FontWeight.FontWeight -> FontWeight.FontWeight
getFontWeight maybeW fallback = maybe fallback (\w -> w) maybeW

-- | Resolved styling configuration (passed to render functions)
type ResolvedConfig =
  { lblColor :: Color.RGB
  , primColor :: Color.RGB
  , trkColor :: Color.RGB
  , lblFontSize :: FontSize.FontSize
  , lblFontWeight :: FontWeight.FontWeight
  , hdrFontSize :: FontSize.FontSize
  , hdrFontWeight :: FontWeight.FontWeight
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // main component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a color picker
-- |
-- | Pure Element — renders to DOM, Halogen, Static HTML, or any target.
colorPicker :: forall msg. Array (ColorPickerProp msg) -> E.Element msg
colorPicker propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Resolve colors
    bgColor = getColor props.backgroundColor defaultBackgroundColor
    brdColor = getColor props.borderColor defaultBorderColor
    lblColor = getColor props.labelColor defaultLabelColor
    primColor = getColor props.primaryColor defaultPrimaryColor
    trkColor = getColor props.sliderTrackColor defaultSliderTrackColor
    
    -- Resolve geometry
    prevRadius = getRadius props.previewBorderRadius defaultPreviewRadius
    pnlRadius = getRadius props.panelBorderRadius defaultPanelRadius
    
    -- Resolve dimensions
    pad = getPixel props.padding defaultPadding
    gapVal = getPixel props.gap defaultGap
    brdWidth = getPixel props.borderWidth defaultBorderWidth
    prevHeight = getPixel props.previewHeight defaultPreviewHeight
    
    -- Resolve typography
    lblFontSize = getFontSize props.labelFontSize defaultLabelFontSize
    lblFontWeight = getFontWeight props.labelFontWeight defaultLabelFontWeight
    hdrFontSize = getFontSize props.headerFontSize defaultHeaderFontSize
    hdrFontWeight = getFontWeight props.headerFontWeight defaultHeaderFontWeight
    
    -- Container styles
    containerStyles =
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" (show gapVal)
      , E.style "padding" (show pad)
      , E.style "background-color" (Color.toLegacyCss bgColor)
      , E.style "border-width" (show brdWidth)
      , E.style "border-style" "solid"
      , E.style "border-color" (Color.toLegacyCss brdColor)
      , E.style "border-radius" (Geometry.toLegacyCss pnlRadius)
      ]
    
    -- Resolved config for render functions
    resolvedConfig =
      { lblColor
      , primColor
      , trkColor
      , lblFontSize
      , lblFontWeight
      , hdrFontSize
      , hdrFontWeight
      }
  in
    E.div_
      containerStyles
      [ -- Color preview
        renderColorPreview props.color prevRadius prevHeight brdColor brdWidth
      
      -- Mode toggles
      , renderModeToggles props resolvedConfig
      
      -- Enabled mode sections
      , E.div_
          [ E.style "display" "flex"
          , E.style "flex-direction" "column"
          , E.style "gap" (show gapVal)
          ]
          ( map (renderModeSection props resolvedConfig) props.enabledModes )
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // color preview
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render color preview swatch
renderColorPreview :: forall msg. Color.RGB -> Geometry.Radius -> Device.Pixel -> Color.RGB -> Device.Pixel -> E.Element msg
renderColorPreview currentColor radius height borderClr borderWdth =
  E.div_
    [ E.style "width" "100%"
    , E.style "height" (show height)
    , E.style "background-color" (Color.toLegacyCss currentColor)
    , E.style "border-radius" (Geometry.toLegacyCss radius)
    , E.style "border-width" (show borderWdth)
    , E.style "border-style" "solid"
    , E.style "border-color" (Color.toLegacyCss borderClr)
    ]
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // mode toggles
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render mode toggle checkboxes
renderModeToggles :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderModeToggles props cfg =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-wrap" "wrap"
    , E.style "gap" "12px"
    , E.style "padding-bottom" "8px"
    , E.style "border-bottom" "1px solid rgba(255, 255, 255, 0.1)"
    ]
    ( map (renderModeCheckbox props cfg) allModes )

-- | Render a single mode checkbox
renderModeCheckbox :: forall msg. ColorPickerProps msg -> ResolvedConfig -> ColorMode -> E.Element msg
renderModeCheckbox props cfg mode =
  let
    isEnabled = elem mode props.enabledModes
    
    toggleHandler = case props.onModeToggle of
      Just handler -> Just (handler mode (not isEnabled))
      Nothing -> Nothing
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "8px"
      ]
      [ Checkbox.checkbox
          ( [ Checkbox.isChecked isEnabled
            , Checkbox.backgroundColor cfg.primColor
            , Checkbox.checkColor (Color.rgb 255 255 255)
            , Checkbox.size (Device.px 16.0)
            ] <> case toggleHandler of
                    Just h -> [ Checkbox.onToggle h ]
                    Nothing -> [ Checkbox.isDisabled true ]
          )
      , E.span_
          [ E.style "font-size" (show cfg.hdrFontSize)
          , E.style "font-weight" (FontWeight.toLegacyCss cfg.lblFontWeight)
          , E.style "color" (Color.toLegacyCss cfg.lblColor)
          ]
          [ E.text (modeName mode) ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // mode sections
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a mode section with sliders
renderModeSection :: forall msg. ColorPickerProps msg -> ResolvedConfig -> ColorMode -> E.Element msg
renderModeSection props cfg mode =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "8px"
    ]
    [ -- Mode header
      E.h3_
        [ E.style "font-size" (show cfg.hdrFontSize)
        , E.style "font-weight" (FontWeight.toLegacyCss cfg.hdrFontWeight)
        , E.style "color" (Color.toLegacyCss cfg.lblColor)
        , E.style "text-transform" "uppercase"
        , E.style "letter-spacing" "0.05em"
        , E.style "margin" "0"
        ]
        [ E.text (modeName mode) ]
    
    -- Sliders
    , case mode of
        ModeHSL -> renderHSLSliders props cfg
        ModeRGB -> renderRGBSliders props cfg
        ModeHWB -> renderHWBSliders props cfg
        ModeOKLAB -> renderOKLABSliders props cfg
        ModeOKLCH -> renderOKLCHSliders props cfg
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hsl sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render HSL sliders
renderHSLSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderHSLSliders props cfg =
  let
    hslColor = Convert.rgbToHsl props.color
    hslRec = HSL.hslToRecord hslColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRow "Hue" (toNumber hslRec.h) 0.0 359.0 1.0 cfg
          (buildHSLHandler props hslRec (\v -> HSL.hsl (round v) hslRec.s hslRec.l))
      , renderSliderRow "Saturation" (toNumber hslRec.s) 0.0 100.0 1.0 cfg
          (buildHSLHandler props hslRec (\v -> HSL.hsl hslRec.h (round v) hslRec.l))
      , renderSliderRow "Lightness" (toNumber hslRec.l) 0.0 100.0 1.0 cfg
          (buildHSLHandler props hslRec (\v -> HSL.hsl hslRec.h hslRec.s (round v)))
      ]

-- | Build HSL change handler
buildHSLHandler :: forall msg. ColorPickerProps msg -> { h :: Int, s :: Int, l :: Int } -> (Number -> HSL.HSL) -> Maybe (Number -> msg)
buildHSLHandler props _ mkHsl = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.hslToRgb (mkHsl v)))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // rgb sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render RGB sliders
renderRGBSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderRGBSliders props cfg =
  let
    rgbRec = Color.rgbToRecord props.color
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRow "Red" (toNumber rgbRec.r) 0.0 255.0 1.0 cfg
          (buildRGBHandler props (\v -> Color.rgb (round v) rgbRec.g rgbRec.b))
      , renderSliderRow "Green" (toNumber rgbRec.g) 0.0 255.0 1.0 cfg
          (buildRGBHandler props (\v -> Color.rgb rgbRec.r (round v) rgbRec.b))
      , renderSliderRow "Blue" (toNumber rgbRec.b) 0.0 255.0 1.0 cfg
          (buildRGBHandler props (\v -> Color.rgb rgbRec.r rgbRec.g (round v)))
      ]

-- | Build RGB change handler
buildRGBHandler :: forall msg. ColorPickerProps msg -> (Number -> Color.RGB) -> Maybe (Number -> msg)
buildRGBHandler props mkRgb = case props.onChange of
  Just handler -> Just (\v -> handler (mkRgb v))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // hwb sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render HWB sliders
renderHWBSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderHWBSliders props cfg =
  let
    hwbColor = Convert.rgbToHwb props.color
    hwbRec = HWB.hwbToRecord hwbColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRow "Hue" (toNumber hwbRec.h) 0.0 359.0 1.0 cfg
          (buildHWBHandler props hwbRec (\v -> HWB.hwb (round v) hwbRec.w hwbRec.b))
      , renderSliderRow "Whiteness" (toNumber hwbRec.w) 0.0 100.0 1.0 cfg
          (buildHWBHandler props hwbRec (\v -> HWB.hwb hwbRec.h (round v) hwbRec.b))
      , renderSliderRow "Blackness" (toNumber hwbRec.b) 0.0 100.0 1.0 cfg
          (buildHWBHandler props hwbRec (\v -> HWB.hwb hwbRec.h hwbRec.w (round v)))
      ]

-- | Build HWB change handler
buildHWBHandler :: forall msg. ColorPickerProps msg -> { h :: Int, w :: Int, b :: Int } -> (Number -> HWB.HWB) -> Maybe (Number -> msg)
buildHWBHandler props _ mkHwb = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.hwbToRgb (mkHwb v)))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // oklab sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render OKLAB sliders
renderOKLABSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderOKLABSliders props cfg =
  let
    oklabColor = Convert.rgbToOklab props.color
    oklabRec = OKLAB.oklabToRecord oklabColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRowFloat "L" oklabRec.l 0.0 1.0 0.01 cfg
          (buildOKLABHandler props oklabRec (\v -> OKLAB.oklab v oklabRec.a oklabRec.b))
      , renderSliderRowFloat "a" oklabRec.a (-0.4) 0.4 0.01 cfg
          (buildOKLABHandler props oklabRec (\v -> OKLAB.oklab oklabRec.l v oklabRec.b))
      , renderSliderRowFloat "b" oklabRec.b (-0.4) 0.4 0.01 cfg
          (buildOKLABHandler props oklabRec (\v -> OKLAB.oklab oklabRec.l oklabRec.a v))
      ]

-- | Build OKLAB change handler
buildOKLABHandler :: forall msg. ColorPickerProps msg -> { l :: Number, a :: Number, b :: Number } -> (Number -> OKLAB.OKLAB) -> Maybe (Number -> msg)
buildOKLABHandler props _ mkOklab = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.oklabToRgb (mkOklab v)))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // oklch sliders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render OKLCH sliders
renderOKLCHSliders :: forall msg. ColorPickerProps msg -> ResolvedConfig -> E.Element msg
renderOKLCHSliders props cfg =
  let
    oklchColor = Convert.rgbToOklch props.color
    oklchRec = OKLCH.oklchToRecord oklchColor
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" "8px"
      ]
      [ renderSliderRowFloat "L" oklchRec.l 0.0 1.0 0.01 cfg
          (buildOKLCHHandler props oklchRec (\v -> OKLCH.oklch v oklchRec.c oklchRec.h))
      , renderSliderRowFloat "C" oklchRec.c 0.0 0.4 0.01 cfg
          (buildOKLCHHandler props oklchRec (\v -> OKLCH.oklch oklchRec.l v oklchRec.h))
      , renderSliderRow "H" (toNumber oklchRec.h) 0.0 359.0 1.0 cfg
          (buildOKLCHHueHandler props oklchRec)
      ]

-- | Build OKLCH change handler
buildOKLCHHandler :: forall msg. ColorPickerProps msg -> { l :: Number, c :: Number, h :: Int } -> (Number -> OKLCH.OKLCH) -> Maybe (Number -> msg)
buildOKLCHHandler props _ mkOklch = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.oklchToRgb (mkOklch v)))
  Nothing -> Nothing

-- | Build OKLCH hue handler (Int-based)
buildOKLCHHueHandler :: forall msg. ColorPickerProps msg -> { l :: Number, c :: Number, h :: Int } -> Maybe (Number -> msg)
buildOKLCHHueHandler props oklchRec = case props.onChange of
  Just handler -> Just (\v -> handler (Convert.oklchToRgb (OKLCH.oklch oklchRec.l oklchRec.c (round v))))
  Nothing -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // slider row
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a labeled slider row (Int values)
renderSliderRow :: forall msg. String -> Number -> Number -> Number -> Number -> ResolvedConfig -> Maybe (Number -> msg) -> E.Element msg
renderSliderRow label val minVal maxVal stepVal cfg handler =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "4px"
    ]
    [ E.label_
        [ E.style "font-size" (show cfg.lblFontSize)
        , E.style "font-weight" (FontWeight.toLegacyCss cfg.lblFontWeight)
        , E.style "color" (Color.toLegacyCss cfg.lblColor)
        ]
        [ E.text (label <> ": " <> show (round val)) ]
    , Slider.slider
        ( [ Slider.value val
          , Slider.minValue minVal
          , Slider.maxValue maxVal
          , Slider.step stepVal
          , Slider.trackColor cfg.trkColor
          , Slider.rangeColor cfg.primColor
          , Slider.thumbBorderColor cfg.primColor
          , Slider.trackHeight (Device.px 6.0)
          , Slider.thumbSize (Device.px 16.0)
          ] <> case handler of
                  Just h -> [ Slider.onChange h ]
                  Nothing -> [ Slider.sliderDisabled true ]
        )
    ]

-- | Render a labeled slider row (Float values)
renderSliderRowFloat :: forall msg. String -> Number -> Number -> Number -> Number -> ResolvedConfig -> Maybe (Number -> msg) -> E.Element msg
renderSliderRowFloat label val minVal maxVal stepVal cfg handler =
  E.div_
    [ E.style "display" "flex"
    , E.style "flex-direction" "column"
    , E.style "gap" "4px"
    ]
    [ E.label_
        [ E.style "font-size" (show cfg.lblFontSize)
        , E.style "font-weight" (FontWeight.toLegacyCss cfg.lblFontWeight)
        , E.style "color" (Color.toLegacyCss cfg.lblColor)
        ]
        [ E.text (label <> ": " <> toStringWith (fixed 3) val) ]
    , Slider.slider
        ( [ Slider.value val
          , Slider.minValue minVal
          , Slider.maxValue maxVal
          , Slider.step stepVal
          , Slider.trackColor cfg.trkColor
          , Slider.rangeColor cfg.primColor
          , Slider.thumbBorderColor cfg.primColor
          , Slider.trackHeight (Device.px 6.0)
          , Slider.thumbSize (Device.px 16.0)
          ] <> case handler of
                  Just h -> [ Slider.onChange h ]
                  Nothing -> [ Slider.sliderDisabled true ]
        )
    ]
