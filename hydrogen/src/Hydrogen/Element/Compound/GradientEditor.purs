-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                     // hydrogen // element // gradient editor
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | GradientEditor — Schema-native gradient editing component.
-- |
-- | ## Design Philosophy
-- |
-- | This component accepts **concrete Schema atoms**, not semantic tokens.
-- | All visual properties map directly to Schema pillar atoms.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      | CSS Output              |
-- | |----------------------|------------|---------------------------|-------------------------|
-- | | borderColor          | Color      | Color.RGB                 | border-color            |
-- | | backgroundColor      | Color      | Color.RGB                 | background-color        |
-- | | textColor            | Color      | Color.RGB                 | color                   |
-- | | stopMarkerBorder     | Color      | Color.RGB                 | border-color (marker)   |
-- | | borderRadius         | Geometry   | Geometry.Radius           | border-radius           |
-- | | previewHeight        | Dimension  | Device.Pixel              | height (preview)        |
-- | | barHeight            | Dimension  | Device.Pixel              | height (bar)            |
-- | | markerWidth          | Dimension  | Device.Pixel              | width (stop marker)     |
-- | | padding              | Dimension  | Device.Pixel              | padding                 |
-- | | spacing              | Dimension  | Device.Pixel              | gap                     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.GradientEditor as GradientEditor
-- | import Hydrogen.Schema.Color.Gradient (linearGradient, colorStop, Gradient(Linear))
-- | import Hydrogen.Schema.Color.RGB (rgb)
-- |
-- | GradientEditor.gradientEditor
-- |   [ GradientEditor.gradient (Linear $ linearGradient
-- |       [ colorStop (rgb 255 0 0) 0.0
-- |       , colorStop (rgb 0 0 255) 1.0
-- |       ])
-- |   , GradientEditor.onChange HandleGradientChange
-- |   , GradientEditor.borderColor brand.borderColor
-- |   , GradientEditor.borderRadius brand.cardRadius
-- |   ]
-- | ```

module Hydrogen.Element.Compound.GradientEditor
  ( gradientEditor
  , GradientEditorProps
  , GradientEditorProp
  , defaultProps
  , gradient
  , onChange
  , showPreview
  , borderColor
  , backgroundColor
  , textColor
  , stopMarkerBorderColor
  , borderRadius
  , previewHeight
  , barHeight
  , markerWidth
  , padding
  , spacing
  ) where

import Prelude
  ( show
  , (<>)
  , (+)
  , (*)
  )

import Data.Array (foldl, mapWithIndex)
import Data.Maybe (Maybe(Nothing, Just), maybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Color.Gradient as Gradient
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Geometry

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | GradientEditor properties
-- |
-- | All visual properties accept Schema atoms directly.
type GradientEditorProps msg =
  { gradient :: Gradient.Gradient
  , showPreview :: Boolean
  , onChange :: Maybe (Gradient.Gradient -> msg)
  
  , borderColor :: Maybe Color.RGB
  , backgroundColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , stopMarkerBorderColor :: Maybe Color.RGB
  
  , borderRadius :: Maybe Geometry.Radius
  
  , previewHeight :: Maybe Device.Pixel
  , barHeight :: Maybe Device.Pixel
  , markerWidth :: Maybe Device.Pixel
  , padding :: Maybe Device.Pixel
  , spacing :: Maybe Device.Pixel
  }

-- | Property modifier function
type GradientEditorProp msg = GradientEditorProps msg -> GradientEditorProps msg

-- | Default properties
defaultProps :: forall msg. GradientEditorProps msg
defaultProps =
  { gradient: Gradient.Linear (Gradient.linearGradient
      [ Gradient.colorStop (Color.rgb 255 0 0) 0.0
      , Gradient.colorStop (Color.rgb 0 0 255) 1.0
      ])
  , showPreview: true
  , onChange: Nothing
  , borderColor: Nothing
  , backgroundColor: Nothing
  , textColor: Nothing
  , stopMarkerBorderColor: Nothing
  , borderRadius: Nothing
  , previewHeight: Nothing
  , barHeight: Nothing
  , markerWidth: Nothing
  , padding: Nothing
  , spacing: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set gradient value
gradient :: forall msg. Gradient.Gradient -> GradientEditorProp msg
gradient g props = props { gradient = g }

-- | Set change handler
onChange :: forall msg. (Gradient.Gradient -> msg) -> GradientEditorProp msg
onChange handler props = props { onChange = Just handler }

-- | Show/hide preview
showPreview :: forall msg. Boolean -> GradientEditorProp msg
showPreview s props = props { showPreview = s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border color (Color.RGB atom)
borderColor :: forall msg. Color.RGB -> GradientEditorProp msg
borderColor c props = props { borderColor = Just c }

-- | Set background color (Color.RGB atom)
backgroundColor :: forall msg. Color.RGB -> GradientEditorProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set text color (Color.RGB atom)
textColor :: forall msg. Color.RGB -> GradientEditorProp msg
textColor c props = props { textColor = Just c }

-- | Set stop marker border color (Color.RGB atom)
stopMarkerBorderColor :: forall msg. Color.RGB -> GradientEditorProp msg
stopMarkerBorderColor c props = props { stopMarkerBorderColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius (Geometry.Radius atom)
borderRadius :: forall msg. Geometry.Radius -> GradientEditorProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set preview section height (Device.Pixel atom)
previewHeight :: forall msg. Device.Pixel -> GradientEditorProp msg
previewHeight h props = props { previewHeight = Just h }

-- | Set gradient bar height (Device.Pixel atom)
barHeight :: forall msg. Device.Pixel -> GradientEditorProp msg
barHeight h props = props { barHeight = Just h }

-- | Set stop marker width (Device.Pixel atom)
markerWidth :: forall msg. Device.Pixel -> GradientEditorProp msg
markerWidth w props = props { markerWidth = Just w }

-- | Set padding (Device.Pixel atom)
padding :: forall msg. Device.Pixel -> GradientEditorProp msg
padding p props = props { padding = Just p }

-- | Set spacing between elements (Device.Pixel atom)
spacing :: forall msg. Device.Pixel -> GradientEditorProp msg
spacing s props = props { spacing = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // defaults
-- ═════════════════════════════════════════════════════════════════════════════

defaultBorderColor :: Color.RGB
defaultBorderColor = Color.rgb 255 255 255

defaultBackgroundColor :: Color.RGB
defaultBackgroundColor = Color.rgb 0 0 0

defaultTextColor :: Color.RGB
defaultTextColor = Color.rgb 255 255 255

defaultStopMarkerBorderColor :: Color.RGB
defaultStopMarkerBorderColor = Color.rgb 255 255 255

defaultBorderRadius :: Geometry.Radius
defaultBorderRadius = Geometry.px 8.0

defaultPreviewHeight :: Device.Pixel
defaultPreviewHeight = Device.px 96.0

defaultBarHeight :: Device.Pixel
defaultBarHeight = Device.px 48.0

defaultMarkerWidth :: Device.Pixel
defaultMarkerWidth = Device.px 4.0

defaultPadding :: Device.Pixel
defaultPadding = Device.px 16.0

defaultSpacing :: Device.Pixel
defaultSpacing = Device.px 16.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

getColor :: Maybe Color.RGB -> Color.RGB -> Color.RGB
getColor maybeColor fallback = maybe fallback (\c -> c) maybeColor

getPixel :: Maybe Device.Pixel -> Device.Pixel -> Device.Pixel
getPixel maybePixel fallback = maybe fallback (\p -> p) maybePixel

getRadius :: Maybe Geometry.Radius -> Geometry.Radius -> Geometry.Radius
getRadius maybeRadius fallback = maybe fallback (\r -> r) maybeRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Gradient editor component
-- |
-- | Renders a gradient editor with:
-- | - Optional large preview
-- | - Gradient bar with stop markers
-- | - Stop list with position info
gradientEditor :: forall msg. Array (GradientEditorProp msg) -> E.Element msg
gradientEditor propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    stops = Gradient.getStops props.gradient
    
    bdrColor = getColor props.borderColor defaultBorderColor
    bgColor = getColor props.backgroundColor defaultBackgroundColor
    txtColor = getColor props.textColor defaultTextColor
    markerBdrColor = getColor props.stopMarkerBorderColor defaultStopMarkerBorderColor
    
    radius = getRadius props.borderRadius defaultBorderRadius
    
    prvHeight = getPixel props.previewHeight defaultPreviewHeight
    barH = getPixel props.barHeight defaultBarHeight
    mrkWidth = getPixel props.markerWidth defaultMarkerWidth
    pad = getPixel props.padding defaultPadding
    spc = getPixel props.spacing defaultSpacing
    
    containerStyles =
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" (show spc)
      , E.style "padding" (show pad)
      , E.style "border" ("1px solid " <> Color.toLegacyCss bdrColor)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      , E.style "background-color" (Color.toLegacyCss bgColor)
      ]
  in
    E.div_ containerStyles
      ([ if props.showPreview
           then renderPreview props.gradient radius prvHeight bdrColor
           else E.empty
       , renderGradientBar props.gradient radius barH mrkWidth markerBdrColor bdrColor
       , renderStopList stops txtColor spc
       ])

-- | Render the large gradient preview
renderPreview 
  :: forall msg
   . Gradient.Gradient 
  -> Geometry.Radius 
  -> Device.Pixel 
  -> Color.RGB 
  -> E.Element msg
renderPreview grad radius height bdrColor =
  E.div_
    [ E.style "width" "100%"
    , E.style "height" (show height)
    , E.style "border-radius" (Geometry.toLegacyCss radius)
    , E.style "border" ("1px solid " <> Color.toLegacyCss bdrColor)
    , E.style "background" (Gradient.toLegacyCss grad)
    ]
    []

-- | Render the gradient bar with stop markers
renderGradientBar 
  :: forall msg
   . Gradient.Gradient 
  -> Geometry.Radius 
  -> Device.Pixel 
  -> Device.Pixel 
  -> Color.RGB 
  -> Color.RGB 
  -> E.Element msg
renderGradientBar grad radius height markerW markerBdrColor bdrColor =
  let
    stops = Gradient.getStops grad
    
    barStyles =
      [ E.style "position" "relative"
      , E.style "width" "100%"
      , E.style "height" (show height)
      , E.style "border-radius" (Geometry.toLegacyCss radius)
      , E.style "border" ("1px solid " <> Color.toLegacyCss bdrColor)
      , E.style "overflow" "hidden"
      ]
    
    gradientBgStyles =
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "background" (Gradient.toLegacyCss grad)
      ]
    
    markersContainerStyles =
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      ]
  in
    E.div_ barStyles
      [ E.div_ gradientBgStyles []
      , E.div_ markersContainerStyles
          (mapWithIndex (\idx stop -> renderStopMarker idx stop markerW markerBdrColor) stops)
      ]

-- | Render a single stop marker on the bar
renderStopMarker 
  :: forall msg
   . Int 
  -> Gradient.ColorStop 
  -> Device.Pixel 
  -> Color.RGB 
  -> E.Element msg
renderStopMarker idx (Gradient.ColorStop cs) markerW markerBdrColor =
  let
    position = Gradient.unwrapRatio cs.position * 100.0
    
    markerStyles =
      [ E.style "position" "absolute"
      , E.style "top" "0"
      , E.style "bottom" "0"
      , E.style "width" (show markerW)
      , E.style "left" (show position <> "%")
      , E.style "transform" "translateX(-50%)"
      , E.style "background-color" (Color.rgbToLegacyCss cs.color)
      , E.style "border" ("2px solid " <> Color.toLegacyCss markerBdrColor)
      , E.style "cursor" "pointer"
      , E.title ("Stop " <> show idx <> " at " <> show position <> "%")
      ]
  in
    E.div_ markerStyles []

-- | Render the list of stops with their positions
renderStopList 
  :: forall msg
   . Array Gradient.ColorStop 
  -> Color.RGB 
  -> Device.Pixel 
  -> E.Element msg
renderStopList stops txtColor spc =
  let
    listStyles =
      [ E.style "display" "flex"
      , E.style "flex-direction" "column"
      , E.style "gap" (show spc)
      ]
  in
    E.div_ listStyles
      (mapWithIndex (\idx stop -> renderStopInfo idx stop txtColor) stops)

-- | Render info for a single stop
renderStopInfo 
  :: forall msg
   . Int 
  -> Gradient.ColorStop 
  -> Color.RGB 
  -> E.Element msg
renderStopInfo idx (Gradient.ColorStop cs) txtColor =
  let
    position = Gradient.unwrapRatio cs.position * 100.0
    
    rowStyles =
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "12px"
      , E.style "padding" "8px"
      , E.style "border-radius" "4px"
      ]
    
    swatchStyles =
      [ E.style "width" "32px"
      , E.style "height" "32px"
      , E.style "border-radius" "4px"
      , E.style "background-color" (Color.rgbToLegacyCss cs.color)
      , E.style "border" "1px solid rgba(255,255,255,0.2)"
      ]
    
    labelStyles =
      [ E.style "color" (Color.toLegacyCss txtColor)
      , E.style "font-size" "14px"
      ]
  in
    E.div_ rowStyles
      [ E.div_ swatchStyles []
      , E.span_ labelStyles
          [ E.text ("Stop " <> show (idx + 1) <> " at " <> show position <> "%") ]
      ]
