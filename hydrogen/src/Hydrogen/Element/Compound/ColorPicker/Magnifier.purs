-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // colorpicker // magnifier
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Magnifier — Zoom loupe for pixel-level color precision.
-- |
-- | ## Design Philosophy
-- |
-- | The magnifier shows an enlarged view of the area around the cursor,
-- | allowing precise pixel-level color selection. Features:
-- |
-- | - Configurable zoom level (2x - 20x)
-- | - Circular or square loupe shape
-- | - Crosshair overlay showing exact center pixel
-- | - Pixel grid lines at high zoom
-- | - Current pixel color highlight
-- |
-- | ## Usage
-- |
-- | The magnifier follows the cursor position and displays a zoomed
-- | view of the underlying content. It's typically positioned near
-- | the cursor but offset to avoid obscuring the selection point.

module Hydrogen.Element.Compound.ColorPicker.Magnifier
  ( -- * Component
    magnifier
  
  -- * Props
  , MagnifierProps
  , MagnifierProp
  , defaultMagnifierProps
  
  -- * Prop Builders
  , zoomLevel
  , loupeSize
  , loupeShape
  , cursorX
  , cursorY
  , showGrid
  , showCrosshair
  , gridColor
  , crosshairColor
  , borderColor
  , centerColor
  
  -- * Shape Type
  , LoupeShape(Circle, Square)
  
  -- * Zoom Bounds
  , ZoomLevel
  , mkZoomLevel
  , zoomLevelValue
  , zoom2x
  , zoom5x
  , zoom10x
  , zoom20x
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (-)
  , (*)
  , (/)
  , (>=)
  , (&&)
  )

import Data.Array (foldl)
import Data.Int (floor) as Int
import Data.Maybe (Maybe(Nothing, Just))

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as RGB
import Hydrogen.Schema.Dimension.Device as Device
import Hydrogen.Schema.Bounded as Bounded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // zoom level
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom magnification level (2x - 20x)
newtype ZoomLevel = ZoomLevel Number

derive instance eqZoomLevel :: Eq ZoomLevel

instance showZoomLevel :: Show ZoomLevel where
  show (ZoomLevel z) = show z <> "x"

-- | Create zoom level, clamped to 2-20
mkZoomLevel :: Number -> ZoomLevel
mkZoomLevel n = ZoomLevel (Bounded.clampNumber 2.0 20.0 n)

-- | Get raw zoom value
zoomLevelValue :: ZoomLevel -> Number
zoomLevelValue (ZoomLevel z) = z

-- | 2x zoom (minimal)
zoom2x :: ZoomLevel
zoom2x = ZoomLevel 2.0

-- | 5x zoom (moderate)
zoom5x :: ZoomLevel
zoom5x = ZoomLevel 5.0

-- | 10x zoom (high detail)
zoom10x :: ZoomLevel
zoom10x = ZoomLevel 10.0

-- | 20x zoom (pixel-level)
zoom20x :: ZoomLevel
zoom20x = ZoomLevel 20.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // loupe shape
-- ═════════════════════════════════════════════════════════════════════════════

-- | Shape of the magnifier loupe
data LoupeShape
  = Circle
  | Square

derive instance eqLoupeShape :: Eq LoupeShape

instance showLoupeShape :: Show LoupeShape where
  show Circle = "circle"
  show Square = "square"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Magnifier properties
-- |
-- | The `msg` parameter is phantom — it exists to unify with Element's msg type
-- | when composing components, even though this particular props record has no
-- | event handlers that would use msg directly.
type MagnifierProps :: Type -> Type
type MagnifierProps msg =
  { -- Zoom
    zoomLevel :: ZoomLevel
  
  -- Dimensions
  , loupeSize :: Device.Pixel
  , shape :: LoupeShape
  
  -- Position (cursor coordinates in source)
  , cursorX :: Number
  , cursorY :: Number
  
  -- Features
  , showGrid :: Boolean
  , showCrosshair :: Boolean
  
  -- Colors
  , gridColor :: Maybe RGB.RGB
  , crosshairColor :: Maybe RGB.RGB
  , borderColor :: Maybe RGB.RGB
  , centerColor :: Maybe RGB.RGB
  }

-- | Property modifier
type MagnifierProp :: Type -> Type
type MagnifierProp msg = MagnifierProps msg -> MagnifierProps msg

-- | Default properties
defaultMagnifierProps :: forall msg. MagnifierProps msg
defaultMagnifierProps =
  { zoomLevel: zoom10x
  , loupeSize: Device.px 120.0
  , shape: Circle
  , cursorX: 0.0
  , cursorY: 0.0
  , showGrid: true
  , showCrosshair: true
  , gridColor: Nothing
  , crosshairColor: Nothing
  , borderColor: Nothing
  , centerColor: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set zoom level
zoomLevel :: forall msg. ZoomLevel -> MagnifierProp msg
zoomLevel z props = props { zoomLevel = z }

-- | Set loupe size
loupeSize :: forall msg. Device.Pixel -> MagnifierProp msg
loupeSize s props = props { loupeSize = s }

-- | Set loupe shape
loupeShape :: forall msg. LoupeShape -> MagnifierProp msg
loupeShape s props = props { shape = s }

-- | Set cursor X position
cursorX :: forall msg. Number -> MagnifierProp msg
cursorX x props = props { cursorX = x }

-- | Set cursor Y position
cursorY :: forall msg. Number -> MagnifierProp msg
cursorY y props = props { cursorY = y }

-- | Set whether to show pixel grid
showGrid :: forall msg. Boolean -> MagnifierProp msg
showGrid b props = props { showGrid = b }

-- | Set whether to show crosshair
showCrosshair :: forall msg. Boolean -> MagnifierProp msg
showCrosshair b props = props { showCrosshair = b }

-- | Set grid color
gridColor :: forall msg. RGB.RGB -> MagnifierProp msg
gridColor c props = props { gridColor = Just c }

-- | Set crosshair color
crosshairColor :: forall msg. RGB.RGB -> MagnifierProp msg
crosshairColor c props = props { crosshairColor = Just c }

-- | Set border color
borderColor :: forall msg. RGB.RGB -> MagnifierProp msg
borderColor c props = props { borderColor = Just c }

-- | Set center pixel highlight color
centerColor :: forall msg. RGB.RGB -> MagnifierProp msg
centerColor c props = props { centerColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render magnifier loupe
magnifier :: forall msg. Array (MagnifierProp msg) -> E.Element msg
magnifier propModifiers =
  let
    props = foldl (\p f -> f p) defaultMagnifierProps propModifiers
    
    -- Dimensions
    size = Device.unwrapPixel props.loupeSize
    sizePx = show size <> "px"
    zoom = zoomLevelValue props.zoomLevel
    
    -- Border radius based on shape
    radiusStyle = case props.shape of
      Circle -> "50%"
      Square -> "4px"
    
    -- Colors
    borderStyle = case props.borderColor of
      Just c -> "2px solid " <> RGB.toLegacyCss c
      Nothing -> "2px solid #333"
    
    gridColorStr = case props.gridColor of
      Just c -> RGB.toLegacyCss c
      Nothing -> "rgba(128, 128, 128, 0.3)"
    
    crosshairColorStr = case props.crosshairColor of
      Just c -> RGB.toLegacyCss c
      Nothing -> "rgba(255, 0, 0, 0.8)"
    
    centerColorStr = case props.centerColor of
      Just c -> RGB.toLegacyCss c
      Nothing -> "rgba(255, 255, 255, 0.9)"
  in
    E.div_
      [ E.style "position" "relative"
      , E.style "width" sizePx
      , E.style "height" sizePx
      , E.style "border-radius" radiusStyle
      , E.style "border" borderStyle
      , E.style "overflow" "hidden"
      , E.style "box-shadow" "0 4px 12px rgba(0,0,0,0.3)"
      , E.style "pointer-events" "none"
      ]
      [ -- Zoomed content area (placeholder - actual zoom requires canvas)
        renderZoomPlaceholder size zoom
        
        -- Pixel grid overlay
      , if props.showGrid && zoom >= 5.0
          then renderPixelGrid size zoom gridColorStr
          else E.span_ [] []
        
        -- Crosshair overlay
      , if props.showCrosshair
          then renderCrosshair size crosshairColorStr centerColorStr
          else E.span_ [] []
        
        -- Coordinates display
      , renderCoordinates props.cursorX props.cursorY
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // zoom rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Placeholder for zoomed content
-- |
-- | Note: Actual pixel-level zoom requires canvas rendering or CSS 
-- | image-rendering: pixelated on a scaled image. This is a visual placeholder.
renderZoomPlaceholder :: forall msg. Number -> Number -> E.Element msg
renderZoomPlaceholder _size zoom =
  E.div_
    [ E.style "position" "absolute"
    , E.style "inset" "0"
    , E.style "background" "linear-gradient(135deg, #f0f0f0 25%, #e0e0e0 25%, #e0e0e0 50%, #f0f0f0 50%, #f0f0f0 75%, #e0e0e0 75%)"
    , E.style "background-size" (show (zoom * 2.0) <> "px " <> show (zoom * 2.0) <> "px")
    ]
    []

-- | Render pixel grid lines
renderPixelGrid :: forall msg. Number -> Number -> String -> E.Element msg
renderPixelGrid _size zoom gridColorStr =
  let
    -- Pixel size at this zoom level
    pixelSize = zoom
    gridSize = show pixelSize <> "px"
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "background-image" 
          ("linear-gradient(to right, " <> gridColorStr <> " 1px, transparent 1px), " <>
           "linear-gradient(to bottom, " <> gridColorStr <> " 1px, transparent 1px)")
      , E.style "background-size" (gridSize <> " " <> gridSize)
      , E.style "pointer-events" "none"
      ]
      []

-- | Render crosshair at center
renderCrosshair :: forall msg. Number -> String -> String -> E.Element msg
renderCrosshair size crosshairColorStr centerColorStr =
  let
    center = size / 2.0
    centerPx = show center <> "px"
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "inset" "0"
      , E.style "pointer-events" "none"
      ]
      [ -- Horizontal line
        E.div_
          [ E.style "position" "absolute"
          , E.style "left" "0"
          , E.style "right" "0"
          , E.style "top" centerPx
          , E.style "height" "1px"
          , E.style "background" crosshairColorStr
          , E.style "transform" "translateY(-0.5px)"
          ]
          []
        
        -- Vertical line
      , E.div_
          [ E.style "position" "absolute"
          , E.style "top" "0"
          , E.style "bottom" "0"
          , E.style "left" centerPx
          , E.style "width" "1px"
          , E.style "background" crosshairColorStr
          , E.style "transform" "translateX(-0.5px)"
          ]
          []
        
        -- Center pixel highlight
      , E.div_
          [ E.style "position" "absolute"
          , E.style "left" (show (center - 5.0) <> "px")
          , E.style "top" (show (center - 5.0) <> "px")
          , E.style "width" "10px"
          , E.style "height" "10px"
          , E.style "border" ("2px solid " <> centerColorStr)
          , E.style "border-radius" "2px"
          ]
          []
      ]

-- | Render coordinate display
renderCoordinates :: forall msg. Number -> Number -> E.Element msg
renderCoordinates x y =
  let
    xInt = Int.floor x
    yInt = Int.floor y
  in
    E.div_
      [ E.style "position" "absolute"
      , E.style "bottom" "4px"
      , E.style "left" "0"
      , E.style "right" "0"
      , E.style "text-align" "center"
      , E.style "font-size" "10px"
      , E.style "font-family" "monospace"
      , E.style "color" "#fff"
      , E.style "text-shadow" "0 1px 2px rgba(0,0,0,0.8)"
      ]
      [ E.text (show xInt <> ", " <> show yInt) ]
