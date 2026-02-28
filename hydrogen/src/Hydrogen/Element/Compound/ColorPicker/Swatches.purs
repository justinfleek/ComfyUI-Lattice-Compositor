-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // element // colorpicker // swatches
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ColorSwatches — Saved color palette display and selection.
-- |
-- | ## Design Philosophy
-- |
-- | Swatches provide quick access to saved/favorite colors. They render as
-- | a grid of clickable color squares with optional labels. Supports:
-- |
-- | - **Preset palettes**: Material, Tailwind, custom brand colors
-- | - **Recent colors**: Auto-saved recently used colors
-- | - **Favorites**: User-saved color collection
-- |
-- | Each swatch shows its color with a transparency checkerboard background
-- | for colors with alpha < 100%.
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property      | Pillar    | Type              | Purpose                |
-- | |---------------|-----------|-------------------|------------------------|
-- | | colors        | Color     | Array RGBA        | Swatch colors          |
-- | | swatchSize    | Dimension | SwatchSize        | Individual swatch size |
-- | | gap           | Dimension | Pixel             | Space between swatches |
-- | | columns       | Dimension | Int               | Grid columns           |
-- | | borderRadius  | Geometry  | Radius            | Swatch corner rounding |

module Hydrogen.Element.Compound.ColorPicker.Swatches
  ( -- * Component
    swatchGrid
  , swatchRow
  
  -- * Props
  , SwatchGridProps
  , SwatchGridProp
  , defaultGridProps
  
  -- * Swatch Data
  , SwatchData
  , swatch
  , swatchWithLabel
  
  -- * Prop Builders
  , swatches
  , swatchSize
  , gap
  , columns
  , borderRadius
  , onSelect
  , showLabels
  
  -- * Preset Palettes
  , materialPrimary
  , materialAccent
  , tailwindGrays
  , webSafeColors
  
  -- * Utility Functions
  , swatchCount
  , swatchColors
  , averageOpacity
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , map
  , not
  , (<>)
  , ($)
  , (/)
  , (+)
  , (==)
  )

import Data.Array (foldl, length, mapWithIndex)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Color.Opacity as Opacity
import Hydrogen.Schema.Dimension.Swatch as SwatchDim
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Geometry.Radius as Radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // swatch data
-- ═════════════════════════════════════════════════════════════════════════════

-- | Individual swatch data
type SwatchData =
  { color :: RGB.RGBA
  , label :: Maybe String
  }

-- | Create a swatch from a color
swatch :: RGB.RGBA -> SwatchData
swatch c = { color: c, label: Nothing }

-- | Create a swatch with a label
swatchWithLabel :: RGB.RGBA -> String -> SwatchData
swatchWithLabel c l = { color: c, label: Just l }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swatch grid properties
type SwatchGridProps msg =
  { -- Data
    swatches :: Array SwatchData
  
  -- Dimensions
  , swatchSize :: SwatchDim.SwatchSize
  , gap :: Device.Pixel
  , columns :: Int
  
  -- Appearance
  , borderRadius :: Maybe Radius.Radius
  , showLabels :: Boolean
  
  -- Behavior
  , onSelect :: Maybe (RGB.RGBA -> msg)
  }

-- | Property modifier
type SwatchGridProp msg = SwatchGridProps msg -> SwatchGridProps msg

-- | Default grid properties
defaultGridProps :: forall msg. SwatchGridProps msg
defaultGridProps =
  { swatches: []
  , swatchSize: SwatchDim.swatchSize 32.0
  , gap: Device.px 4.0
  , columns: 8
  , borderRadius: Nothing
  , showLabels: false
  , onSelect: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set swatch colors
swatches :: forall msg. Array SwatchData -> SwatchGridProp msg
swatches s props = props { swatches = s }

-- | Set individual swatch size
swatchSize :: forall msg. SwatchDim.SwatchSize -> SwatchGridProp msg
swatchSize s props = props { swatchSize = s }

-- | Set gap between swatches
gap :: forall msg. Device.Pixel -> SwatchGridProp msg
gap g props = props { gap = g }

-- | Set number of columns
columns :: forall msg. Int -> SwatchGridProp msg
columns c props = props { columns = c }

-- | Set border radius
borderRadius :: forall msg. Radius.Radius -> SwatchGridProp msg
borderRadius r props = props { borderRadius = Just r }

-- | Set selection handler
onSelect :: forall msg. (RGB.RGBA -> msg) -> SwatchGridProp msg
onSelect handler props = props { onSelect = Just handler }

-- | Set whether to show labels
showLabels :: forall msg. Boolean -> SwatchGridProp msg
showLabels b props = props { showLabels = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // grid component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a grid of color swatches
-- |
-- | Displays swatches in a CSS grid with configurable columns.
-- | Each swatch is clickable and shows transparency checkerboard.
swatchGrid :: forall msg. Array (SwatchGridProp msg) -> E.Element msg
swatchGrid propModifiers =
  let
    props = foldl (\p f -> f p) defaultGridProps propModifiers
    
    -- Dimensions
    sizePx = show (SwatchDim.swatchSizeValue props.swatchSize) <> "px"
    gapPx = show (Device.unwrapPixel props.gap) <> "px"
    
    -- Grid template
    gridCols = "repeat(" <> show props.columns <> ", " <> sizePx <> ")"
  in
    E.div_
      [ E.style "display" "grid"
      , E.style "grid-template-columns" gridCols
      , E.style "gap" gapPx
      ]
      (mapWithIndex (renderSwatch props) props.swatches)

-- | Render a horizontal row of swatches
-- |
-- | Displays swatches in a flexbox row (no wrapping).
swatchRow :: forall msg. Array (SwatchGridProp msg) -> E.Element msg
swatchRow propModifiers =
  let
    props = foldl (\p f -> f p) defaultGridProps propModifiers
    gapPx = show (Device.unwrapPixel props.gap) <> "px"
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "flex-wrap" "nowrap"
      , E.style "gap" gapPx
      ]
      (mapWithIndex (renderSwatch props) props.swatches)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // swatch rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single swatch
renderSwatch :: forall msg. SwatchGridProps msg -> Int -> SwatchData -> E.Element msg
renderSwatch props swatchIndex swatchData =
  let
    sizePx = show (SwatchDim.swatchSizeValue props.swatchSize) <> "px"
    
    radiusStyle = case props.borderRadius of
      Just r -> Radius.toLegacyCss r
      Nothing -> "4px"
    
    -- Check if color has transparency
    hasAlpha = not (Opacity.isOpaque (RGB.alpha swatchData.color))
    
    -- Checkerboard background for transparent colors
    checkerBg = if hasAlpha
      then "linear-gradient(45deg, #ccc 25%, transparent 25%), linear-gradient(-45deg, #ccc 25%, transparent 25%), linear-gradient(45deg, transparent 75%, #ccc 75%), linear-gradient(-45deg, transparent 75%, #ccc 75%)"
      else "none"
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "width" sizePx
      , E.style "height" sizePx
      , E.dataAttr "swatch-index" $ show swatchIndex
      ]
      [ -- Checkerboard layer (for transparency)
        E.div_
          [ E.style "position" "absolute"
          , E.style "inset" "0"
          , E.style "background" checkerBg
          , E.style "background-size" "8px 8px"
          , E.style "background-position" "0 0, 0 4px, 4px -4px, -4px 0"
          , E.style "border-radius" radiusStyle
          ]
          []
        
        -- Color layer
      , E.div_
          [ E.style "position" "absolute"
          , E.style "inset" "0"
          , E.style "background" (RGB.rgbaToLegacyCss swatchData.color)
          , E.style "border-radius" radiusStyle
          , E.style "border" "1px solid rgba(0,0,0,0.1)"
          , E.style "cursor" "pointer"
          , E.style "transition" "transform 0.1s, box-shadow 0.1s"
          ]
          []
        
        -- Label (if shown and present)
      , case swatchData.label of
          Just label | props.showLabels ->
            E.div_
              [ E.style "position" "absolute"
              , E.style "bottom" "-18px"
              , E.style "left" "0"
              , E.style "right" "0"
              , E.style "text-align" "center"
              , E.style "font-size" "10px"
              , E.style "color" "#666"
              , E.style "white-space" "nowrap"
              , E.style "overflow" "hidden"
              , E.style "text-overflow" "ellipsis"
              ]
              [ E.text label ]
          _ -> E.span_ [] []
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // preset palettes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Material Design primary colors
materialPrimary :: Array SwatchData
materialPrimary =
  [ swatchWithLabel (RGB.rgba 244 67 54 100) "Red"
  , swatchWithLabel (RGB.rgba 233 30 99 100) "Pink"
  , swatchWithLabel (RGB.rgba 156 39 176 100) "Purple"
  , swatchWithLabel (RGB.rgba 103 58 183 100) "Deep Purple"
  , swatchWithLabel (RGB.rgba 63 81 181 100) "Indigo"
  , swatchWithLabel (RGB.rgba 33 150 243 100) "Blue"
  , swatchWithLabel (RGB.rgba 3 169 244 100) "Light Blue"
  , swatchWithLabel (RGB.rgba 0 188 212 100) "Cyan"
  , swatchWithLabel (RGB.rgba 0 150 136 100) "Teal"
  , swatchWithLabel (RGB.rgba 76 175 80 100) "Green"
  , swatchWithLabel (RGB.rgba 139 195 74 100) "Light Green"
  , swatchWithLabel (RGB.rgba 205 220 57 100) "Lime"
  , swatchWithLabel (RGB.rgba 255 235 59 100) "Yellow"
  , swatchWithLabel (RGB.rgba 255 193 7 100) "Amber"
  , swatchWithLabel (RGB.rgba 255 152 0 100) "Orange"
  , swatchWithLabel (RGB.rgba 255 87 34 100) "Deep Orange"
  ]

-- | Material Design accent colors
materialAccent :: Array SwatchData
materialAccent =
  [ swatchWithLabel (RGB.rgba 255 82 82 100) "Red A200"
  , swatchWithLabel (RGB.rgba 255 64 129 100) "Pink A200"
  , swatchWithLabel (RGB.rgba 224 64 251 100) "Purple A200"
  , swatchWithLabel (RGB.rgba 124 77 255 100) "Deep Purple A200"
  , swatchWithLabel (RGB.rgba 83 109 254 100) "Indigo A200"
  , swatchWithLabel (RGB.rgba 68 138 255 100) "Blue A200"
  , swatchWithLabel (RGB.rgba 64 196 255 100) "Light Blue A200"
  , swatchWithLabel (RGB.rgba 24 255 255 100) "Cyan A200"
  , swatchWithLabel (RGB.rgba 100 255 218 100) "Teal A200"
  , swatchWithLabel (RGB.rgba 105 240 174 100) "Green A200"
  , swatchWithLabel (RGB.rgba 178 255 89 100) "Light Green A200"
  , swatchWithLabel (RGB.rgba 238 255 65 100) "Lime A200"
  , swatchWithLabel (RGB.rgba 255 255 0 100) "Yellow A200"
  , swatchWithLabel (RGB.rgba 255 215 64 100) "Amber A200"
  , swatchWithLabel (RGB.rgba 255 171 64 100) "Orange A200"
  , swatchWithLabel (RGB.rgba 255 110 64 100) "Deep Orange A200"
  ]

-- | Tailwind gray scale
tailwindGrays :: Array SwatchData
tailwindGrays =
  [ swatchWithLabel (RGB.rgba 249 250 251 100) "Gray 50"
  , swatchWithLabel (RGB.rgba 243 244 246 100) "Gray 100"
  , swatchWithLabel (RGB.rgba 229 231 235 100) "Gray 200"
  , swatchWithLabel (RGB.rgba 209 213 219 100) "Gray 300"
  , swatchWithLabel (RGB.rgba 156 163 175 100) "Gray 400"
  , swatchWithLabel (RGB.rgba 107 114 128 100) "Gray 500"
  , swatchWithLabel (RGB.rgba 75 85 99 100) "Gray 600"
  , swatchWithLabel (RGB.rgba 55 65 81 100) "Gray 700"
  , swatchWithLabel (RGB.rgba 31 41 55 100) "Gray 800"
  , swatchWithLabel (RGB.rgba 17 24 39 100) "Gray 900"
  ]

-- | Web safe colors (subset)
webSafeColors :: Array SwatchData
webSafeColors =
  [ swatch (RGB.rgba 0 0 0 100)
  , swatch (RGB.rgba 128 128 128 100)
  , swatch (RGB.rgba 192 192 192 100)
  , swatch (RGB.rgba 255 255 255 100)
  , swatch (RGB.rgba 255 0 0 100)
  , swatch (RGB.rgba 0 255 0 100)
  , swatch (RGB.rgba 0 0 255 100)
  , swatch (RGB.rgba 255 255 0 100)
  , swatch (RGB.rgba 0 255 255 100)
  , swatch (RGB.rgba 255 0 255 100)
  , swatch (RGB.rgba 128 0 0 100)
  , swatch (RGB.rgba 0 128 0 100)
  , swatch (RGB.rgba 0 0 128 100)
  , swatch (RGB.rgba 128 128 0 100)
  , swatch (RGB.rgba 0 128 128 100)
  , swatch (RGB.rgba 128 0 128 100)
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // utility functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get the number of swatches in a palette
-- | Useful for validation and layout calculations
swatchCount :: Array SwatchData -> Int
swatchCount palette = length palette

-- | Extract just the colors from a swatch palette
-- | Useful for color analysis or export
swatchColors :: Array SwatchData -> Array RGB.RGBA
swatchColors palette = map (\s -> s.color) palette

-- | Calculate the average opacity across all swatches
-- | Returns a value from 0.0 to 1.0
-- | Useful for determining if a palette is mostly transparent
averageOpacity :: Array SwatchData -> Number
averageOpacity palette =
  let
    count = length palette
  in
    if count == 0
      then 1.0
      else
        let
          opacities = map (\s -> Opacity.toUnitInterval (RGB.alpha s.color)) palette
          totalOpacity = foldl addNum 0.0 opacities
        in
          totalOpacity / Int.toNumber count
  where
    addNum :: Number -> Number -> Number
    addNum a b = a + b

