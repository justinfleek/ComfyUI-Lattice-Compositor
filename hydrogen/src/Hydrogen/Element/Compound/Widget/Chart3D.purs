-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                   // hydrogen // element // widget // chart3d
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | 3D Chart Widgets — Isometric visualizations using SVG.
-- |
-- | ## Design Philosophy
-- |
-- | These charts render 3D-like visualizations using isometric projection
-- | in SVG. No WebGL required — pure vector graphics that scale perfectly.
-- |
-- | Includes:
-- | - Chart3DBar: Isometric 3D bar chart with three faces per bar
-- | - Chart3DSurface: 3D surface/mesh with height-mapped colors
-- |
-- | Pure Element output — can be rendered to DOM, Static HTML, or any target.

module Hydrogen.Element.Compound.Widget.Chart3D
  ( -- * 3D Bar Chart
    chart3DBar
  , Bar3DData
  , Bar3DConfig
  , defaultBar3DConfig
  
  -- * 3D Surface Chart
  , chart3DSurface
  , SurfaceData
  , SurfaceConfig
  , defaultSurfaceConfig
  
  -- * Isometric Projection
  , isoProject
  , Point2D
  
  -- * Color Palettes
  , defaultBar3DColors
  ) where

import Prelude
  ( class Show
  , show
  , (==)
  , (&&)
  , (<>)
  , (<=)
  , (<)
  , (>)
  , (+)
  , (-)
  , (*)
  , (/)
  , negate
  , mod
  )

import Data.Array (foldl, index, length, mapWithIndex, replicate)
import Data.Int (toNumber)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Hydrogen.Math.Core as Math
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // isometric helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | 2D point result from isometric projection.
type Point2D = { x :: Number, y :: Number }

-- | Isometric angle (30 degrees in radians).
isoAngle :: Number
isoAngle = 3.14159265359 / 6.0

-- | Cosine of isometric angle.
cosIso :: Number
cosIso = Math.cos isoAngle

-- | Sine of isometric angle.
sinIso :: Number
sinIso = Math.sin isoAngle

-- | Project 3D coordinates to 2D isometric view.
-- |
-- | The isometric projection maps (x, y, z) to screen coordinates:
-- | - x axis extends to the right-down
-- | - z axis extends to the left-down
-- | - y axis extends upward
isoProject :: Number -> Number -> Number -> Point2D
isoProject x y z =
  { x: (x - z) * cosIso
  , y: (x + z) * sinIso - y
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // 3d bar chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data point for 3D bar chart.
type Bar3DData =
  { label :: String
  , value :: Number
  , color :: Maybe String
  }

-- | Configuration for 3D bar chart.
type Bar3DConfig =
  { title :: Maybe String
  , subtitle :: Maybe String
  , width :: Number
  , height :: Number
  , barWidth :: Number
  , barDepth :: Number
  , barSpacing :: Number
  , maxBarHeight :: Number
  , showLabels :: Boolean
  , showValues :: Boolean
  , className :: String
  }

-- | Default configuration for 3D bar chart.
defaultBar3DConfig :: Bar3DConfig
defaultBar3DConfig =
  { title: Nothing
  , subtitle: Nothing
  , width: 500.0
  , height: 400.0
  , barWidth: 40.0
  , barDepth: 25.0
  , barSpacing: 70.0
  , maxBarHeight: 200.0
  , showLabels: true
  , showValues: true
  , className: ""
  }

-- | Default color palette for 3D bars.
defaultBar3DColors :: Array String
defaultBar3DColors =
  [ "#f97316"  -- Orange
  , "#3b82f6"  -- Blue
  , "#10b981"  -- Emerald
  , "#8b5cf6"  -- Violet
  , "#f43f5e"  -- Rose
  , "#fbbf24"  -- Amber
  ]

-- | Render an isometric 3D bar chart.
-- |
-- | Each bar has three visible faces:
-- | - Front face (facing viewer)
-- | - Side face (right side)
-- | - Top face (top surface)
-- |
-- | Gradients simulate lighting for 3D effect.
chart3DBar :: forall msg. Bar3DConfig -> Array Bar3DData -> E.Element msg
chart3DBar cfg bars =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    floorY = cfg.height - 80.0
    
    -- Calculate max value for scaling
    maxVal = getMaxBarValue bars
    
    -- Calculate starting X position to center bars
    numBars = length bars
    totalWidth = toNumber numBars * cfg.barSpacing
    startX = negate (totalWidth - cfg.barSpacing) / 2.0
    
    containerCls = "rounded-lg border bg-card text-card-foreground p-4" <>
                   " " <> cfg.className
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- Title
        renderBar3DTitle cfg.title cfg.subtitle
      
      -- SVG chart
      , E.svg_
          [ E.attr "viewBox" viewBox
          , E.class_ "w-full h-full"
          , E.attr "preserveAspectRatio" "xMidYMid meet"
          ]
          [ -- Gradient definitions
            renderBar3DGradients bars
          
          -- Chart group (translated to center)
          , E.g_
              [ E.attr "transform" ("translate(" <> show (cfg.width / 2.0) <> "," <> show floorY <> ")") ]
              [ -- Floor
                renderBar3DFloor cfg numBars
              
              -- Bars
              , E.g_
                  [ E.class_ "chart-3d-bars" ]
                  (mapWithIndex 
                    (renderBar3DBar cfg startX maxVal) 
                    bars)
              
              -- Labels
              , if cfg.showLabels
                  then renderBar3DLabels cfg startX bars
                  else E.text ""
              ]
          ]
      ]

-- | Render title and subtitle.
renderBar3DTitle :: forall msg. Maybe String -> Maybe String -> E.Element msg
renderBar3DTitle maybeTitle maybeSubtitle =
  case maybeTitle of
    Nothing -> E.text ""
    Just title ->
      E.div_
        [ E.class_ "mb-4" ]
        [ E.h3_
            [ E.class_ "text-lg font-semibold" ]
            [ E.text title ]
        , case maybeSubtitle of
            Nothing -> E.text ""
            Just subtitle ->
              E.p_
                [ E.class_ "text-sm text-muted-foreground" ]
                [ E.text subtitle ]
        ]

-- | Render gradient definitions for bar faces.
renderBar3DGradients :: forall msg. Array Bar3DData -> E.Element msg
renderBar3DGradients bars =
  E.defs_
    []
    (mapWithIndex (\idx bar ->
      let
        color = fromMaybe (getBar3DColor idx) bar.color
        colorLight = color <> "dd"  -- Lighter shade
        colorDark = color <> "99"   -- Darker shade
      in
        E.g_
          []
          [ -- Top gradient (brightest)
            E.element "linearGradient"
              [ E.attr "id" ("bar3d-top-" <> show idx)
              , E.attr "x1" "0%"
              , E.attr "y1" "0%"
              , E.attr "x2" "100%"
              , E.attr "y2" "100%"
              ]
              [ E.element "stop"
                  [ E.attr "offset" "0%"
                  , E.attr "stop-color" colorLight
                  ]
                  []
              , E.element "stop"
                  [ E.attr "offset" "100%"
                  , E.attr "stop-color" color
                  ]
                  []
              ]
          
          -- Front gradient
          , E.element "linearGradient"
              [ E.attr "id" ("bar3d-front-" <> show idx)
              , E.attr "x1" "0%"
              , E.attr "y1" "0%"
              , E.attr "x2" "0%"
              , E.attr "y2" "100%"
              ]
              [ E.element "stop"
                  [ E.attr "offset" "0%"
                  , E.attr "stop-color" color
                  ]
                  []
              , E.element "stop"
                  [ E.attr "offset" "100%"
                  , E.attr "stop-color" colorDark
                  ]
                  []
              ]
          
          -- Side gradient (darkest)
          , E.element "linearGradient"
              [ E.attr "id" ("bar3d-side-" <> show idx)
              , E.attr "x1" "0%"
              , E.attr "y1" "0%"
              , E.attr "x2" "100%"
              , E.attr "y2" "100%"
              ]
              [ E.element "stop"
                  [ E.attr "offset" "0%"
                  , E.attr "stop-color" colorDark
                  ]
                  []
              , E.element "stop"
                  [ E.attr "offset" "100%"
                  , E.attr "stop-color" (color <> "66")
                  ]
                  []
              ]
          ]
    ) bars)

-- | Render the isometric floor grid.
renderBar3DFloor :: forall msg. Bar3DConfig -> Int -> E.Element msg
renderBar3DFloor cfg numBars =
  let
    halfWidth = (toNumber numBars * cfg.barSpacing) / 2.0 + 40.0
    halfDepth = 60.0
    
    -- Four corners of floor in 3D space
    p1 = isoProject (negate halfWidth) 0.0 (negate halfDepth)
    p2 = isoProject halfWidth 0.0 (negate halfDepth)
    p3 = isoProject halfWidth 0.0 halfDepth
    p4 = isoProject (negate halfWidth) 0.0 halfDepth
    
    pathD = "M " <> show p1.x <> " " <> show p1.y <>
            " L " <> show p2.x <> " " <> show p2.y <>
            " L " <> show p3.x <> " " <> show p3.y <>
            " L " <> show p4.x <> " " <> show p4.y <> " Z"
  in
    E.path_
      [ E.attr "d" pathD
      , E.attr "fill" "currentColor"
      , E.attr "fill-opacity" "0.05"
      , E.attr "stroke" "currentColor"
      , E.attr "stroke-opacity" "0.1"
      , E.attr "stroke-width" "1"
      ]

-- | Render a single 3D bar with three faces.
renderBar3DBar :: forall msg. Bar3DConfig -> Number -> Number -> Int -> Bar3DData -> E.Element msg
renderBar3DBar cfg startX maxVal idx bar =
  let
    x = startX + toNumber idx * cfg.barSpacing
    h = if maxVal > 0.0 
        then (bar.value / maxVal) * cfg.maxBarHeight 
        else 0.0
    hw = cfg.barWidth / 2.0  -- half width
    hd = cfg.barDepth / 2.0  -- half depth
    
    base = isoProject x 0.0 0.0
    
    -- Front face vertices
    f1 = isoProject (x - hw) 0.0 hd
    f2 = isoProject (x + hw) 0.0 hd
    f3 = isoProject (x + hw) h hd
    f4 = isoProject (x - hw) h hd
    frontPath = "M " <> show f1.x <> " " <> show f1.y <>
                " L " <> show f2.x <> " " <> show f2.y <>
                " L " <> show f3.x <> " " <> show f3.y <>
                " L " <> show f4.x <> " " <> show f4.y <> " Z"
    
    -- Side face vertices
    s1 = isoProject (x + hw) 0.0 hd
    s2 = isoProject (x + hw) 0.0 (negate hd)
    s3 = isoProject (x + hw) h (negate hd)
    s4 = isoProject (x + hw) h hd
    sidePath = "M " <> show s1.x <> " " <> show s1.y <>
               " L " <> show s2.x <> " " <> show s2.y <>
               " L " <> show s3.x <> " " <> show s3.y <>
               " L " <> show s4.x <> " " <> show s4.y <> " Z"
    
    -- Top face vertices
    t1 = isoProject (x - hw) h hd
    t2 = isoProject (x + hw) h hd
    t3 = isoProject (x + hw) h (negate hd)
    t4 = isoProject (x - hw) h (negate hd)
    topPath = "M " <> show t1.x <> " " <> show t1.y <>
              " L " <> show t2.x <> " " <> show t2.y <>
              " L " <> show t3.x <> " " <> show t3.y <>
              " L " <> show t4.x <> " " <> show t4.y <> " Z"
    
    topCenter = isoProject x h 0.0
  in
    E.g_
      [ E.class_ "chart-3d-bar" ]
      [ -- Shadow ellipse
        E.element "ellipse"
          [ E.attr "cx" (show base.x)
          , E.attr "cy" (show (base.y + 5.0))
          , E.attr "rx" (show (cfg.barWidth * 0.6))
          , E.attr "ry" (show (cfg.barDepth * 0.4))
          , E.attr "fill" "currentColor"
          , E.attr "fill-opacity" "0.1"
          ]
          []
      
      -- Side face (render first, behind others)
      , E.path_
          [ E.attr "d" sidePath
          , E.attr "fill" ("url(#bar3d-side-" <> show idx <> ")")
          ]
      
      -- Front face
      , E.path_
          [ E.attr "d" frontPath
          , E.attr "fill" ("url(#bar3d-front-" <> show idx <> ")")
          ]
      
      -- Top face (render last, on top)
      , E.path_
          [ E.attr "d" topPath
          , E.attr "fill" ("url(#bar3d-top-" <> show idx <> ")")
          ]
      
      -- Value label
      , if cfg.showValues
          then E.text_
            [ E.attr "x" (show topCenter.x)
            , E.attr "y" (show (topCenter.y - 10.0))
            , E.attr "text-anchor" "middle"
            , E.attr "font-size" "11"
            , E.attr "fill" "currentColor"
            , E.attr "font-weight" "600"
            ]
            [ E.text (formatBarValue bar.value) ]
          else E.text ""
      ]

-- | Render labels below bars.
renderBar3DLabels :: forall msg. Bar3DConfig -> Number -> Array Bar3DData -> E.Element msg
renderBar3DLabels cfg startX bars =
  E.g_
    [ E.class_ "chart-3d-labels" ]
    (mapWithIndex (\idx bar ->
      let
        x = startX + toNumber idx * cfg.barSpacing
        base = isoProject x 0.0 0.0
      in
        E.text_
          [ E.attr "x" (show base.x)
          , E.attr "y" (show (base.y + 25.0))
          , E.attr "text-anchor" "middle"
          , E.attr "font-size" "12"
          , E.attr "fill" "currentColor"
          , E.attr "fill-opacity" "0.7"
          ]
          [ E.text bar.label ]
    ) bars)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // 3d surface chart
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data for 3D surface chart.
-- |
-- | Provided as a 2D grid of height values (row-major order).
-- | Each value represents the Z-height at that (x, y) grid position.
type SurfaceData =
  { rows :: Int
  , cols :: Int
  , values :: Array Number
  }

-- | Configuration for 3D surface chart.
type SurfaceConfig =
  { title :: Maybe String
  , subtitle :: Maybe String
  , width :: Number
  , height :: Number
  , cellSize :: Number
  , maxHeight :: Number
  , colorMin :: String
  , colorMax :: String
  , showGrid :: Boolean
  , className :: String
  }

-- | Default configuration for 3D surface chart.
defaultSurfaceConfig :: SurfaceConfig
defaultSurfaceConfig =
  { title: Nothing
  , subtitle: Nothing
  , width: 500.0
  , height: 400.0
  , cellSize: 30.0
  , maxHeight: 100.0
  , colorMin: "#3b82f6"   -- Blue (low values)
  , colorMax: "#ef4444"   -- Red (high values)
  , showGrid: true
  , className: ""
  }

-- | Render a 3D surface/mesh chart.
-- |
-- | Displays height data as a 3D mesh with color mapping based on value.
-- | Uses isometric projection for 3D effect.
chart3DSurface :: forall msg. SurfaceConfig -> SurfaceData -> E.Element msg
chart3DSurface cfg surfaceData =
  let
    viewBox = "0 0 " <> show cfg.width <> " " <> show cfg.height
    
    -- Calculate data range
    minVal = arrayMin surfaceData.values
    maxVal = arrayMax surfaceData.values
    dataRange = if maxVal - minVal == 0.0 then 1.0 else maxVal - minVal
    
    -- Scale height to configured max
    scaleHeight :: Number -> Number
    scaleHeight v = ((v - minVal) / dataRange) * cfg.maxHeight
    
    -- Calculate centering offset
    gridWidth = toNumber (surfaceData.cols - 1) * cfg.cellSize
    gridDepth = toNumber (surfaceData.rows - 1) * cfg.cellSize
    
    containerCls = "rounded-lg border bg-card text-card-foreground p-4" <>
                   " " <> cfg.className
  in
    E.div_
      [ E.class_ containerCls ]
      [ -- Title
        renderSurfaceTitle cfg.title cfg.subtitle
      
      -- SVG chart
      , E.svg_
          [ E.attr "viewBox" viewBox
          , E.class_ "w-full h-full"
          , E.attr "preserveAspectRatio" "xMidYMid meet"
          ]
          [ E.g_
              [ E.attr "transform" ("translate(" <> show (cfg.width / 2.0) <> "," <> show (cfg.height / 2.0 + 50.0) <> ")") ]
              [ renderSurfaceMesh cfg surfaceData scaleHeight minVal dataRange gridWidth gridDepth ]
          ]
      ]

-- | Render title and subtitle for surface chart.
renderSurfaceTitle :: forall msg. Maybe String -> Maybe String -> E.Element msg
renderSurfaceTitle maybeTitle maybeSubtitle =
  case maybeTitle of
    Nothing -> E.text ""
    Just title ->
      E.div_
        [ E.class_ "mb-4" ]
        [ E.h3_
            [ E.class_ "text-lg font-semibold" ]
            [ E.text title ]
        , case maybeSubtitle of
            Nothing -> E.text ""
            Just subtitle ->
              E.p_
                [ E.class_ "text-sm text-muted-foreground" ]
                [ E.text subtitle ]
        ]

-- | Render the surface mesh as quadrilaterals.
renderSurfaceMesh :: forall msg. 
  SurfaceConfig -> 
  SurfaceData -> 
  (Number -> Number) -> 
  Number -> 
  Number -> 
  Number -> 
  Number -> 
  E.Element msg
renderSurfaceMesh cfg surfaceData scaleHeight minVal dataRange gridWidth gridDepth =
  let
    offsetX = negate gridWidth / 2.0
    offsetZ = negate gridDepth / 2.0
    
    -- Generate all cells (render back to front for proper layering)
    cells = generateSurfaceCells cfg surfaceData scaleHeight minVal dataRange offsetX offsetZ
  in
    E.g_
      [ E.class_ "surface-mesh" ]
      cells

-- | Generate all surface cells as SVG elements.
generateSurfaceCells :: forall msg. 
  SurfaceConfig -> 
  SurfaceData -> 
  (Number -> Number) -> 
  Number -> 
  Number -> 
  Number -> 
  Number -> 
  Array (E.Element msg)
generateSurfaceCells cfg surfaceData scaleHeight minVal dataRange offsetX offsetZ =
  let
    rows = surfaceData.rows
    cols = surfaceData.cols
    
    -- Get value at grid position
    getValue :: Int -> Int -> Number
    getValue row col = 
      let idx = row * cols + col
      in fromMaybe 0.0 (index surfaceData.values idx)
    
    -- Generate cells row by row (back to front)
    rowIndices = generateIndices (rows - 1)
    colIndices = generateIndices (cols - 1)
  in
    foldl (\acc rowIdx ->
      acc <> foldl (\acc2 colIdx ->
        let
          -- Four corners of the cell
          x0 = offsetX + toNumber colIdx * cfg.cellSize
          z0 = offsetZ + toNumber rowIdx * cfg.cellSize
          x1 = x0 + cfg.cellSize
          z1 = z0 + cfg.cellSize
          
          -- Height values at corners
          h00 = scaleHeight (getValue rowIdx colIdx)
          h10 = scaleHeight (getValue rowIdx (colIdx + 1))
          h01 = scaleHeight (getValue (rowIdx + 1) colIdx)
          h11 = scaleHeight (getValue (rowIdx + 1) (colIdx + 1))
          
          -- Average value for coloring
          avgValue = (getValue rowIdx colIdx + getValue rowIdx (colIdx + 1) + 
                     getValue (rowIdx + 1) colIdx + getValue (rowIdx + 1) (colIdx + 1)) / 4.0
          
          -- Color based on value
          colorT = (avgValue - minVal) / dataRange
          cellColor = interpolateColor cfg.colorMin cfg.colorMax colorT
          
          -- Project corners to 2D
          p00 = isoProject x0 h00 z0
          p10 = isoProject x1 h10 z0
          p11 = isoProject x1 h11 z1
          p01 = isoProject x0 h01 z1
          
          -- Path for quadrilateral
          pathD = "M " <> show p00.x <> " " <> show p00.y <>
                  " L " <> show p10.x <> " " <> show p10.y <>
                  " L " <> show p11.x <> " " <> show p11.y <>
                  " L " <> show p01.x <> " " <> show p01.y <> " Z"
        in
          acc2 <> [ E.path_
            [ E.attr "d" pathD
            , E.attr "fill" cellColor
            , E.attr "stroke" (if cfg.showGrid then "currentColor" else "none")
            , E.attr "stroke-opacity" "0.1"
            , E.attr "stroke-width" "0.5"
            ]
          ]
      ) [] colIndices
    ) [] rowIndices

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // math helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get minimum value from array.
arrayMin :: Array Number -> Number
arrayMin arr = case index arr 0 of
  Nothing -> 0.0
  Just first -> foldl min' first arr
  where
    min' :: Number -> Number -> Number
    min' a b = if a < b then a else b

-- | Get maximum value from array.
arrayMax :: Array Number -> Number
arrayMax arr = case index arr 0 of
  Nothing -> 0.0
  Just first -> foldl max' first arr
  where
    max' :: Number -> Number -> Number
    max' a b = if a > b then a else b

-- | Get maximum bar value.
getMaxBarValue :: Array Bar3DData -> Number
getMaxBarValue bars = 
  let values = mapWithIndex (\_ b -> b.value) bars
  in arrayMax values

-- | Get bar color at index from palette.
getBar3DColor :: Int -> String
getBar3DColor idx =
  let paletteLen = length defaultBar3DColors
      wrappedIdx = if paletteLen <= 0 then 0 else idx `mod` paletteLen
  in fromMaybe "#f97316" (index defaultBar3DColors wrappedIdx)

-- | Format bar value for display.
formatBarValue :: Number -> String
formatBarValue v
  | v > 999999.0 = show (Math.floor (v / 100000.0) / 10.0) <> "M"
  | v > 999.0 = show (Math.floor (v / 100.0) / 10.0) <> "K"
  | v < 0.0 && v > (negate 1000.0) = show (Math.floor v)
  | v < (negate 999.0) = show (Math.floor (v / 100.0) / 10.0) <> "K"
  | v < (negate 999999.0) = show (Math.floor (v / 100000.0) / 10.0) <> "M"
  | true = show (Math.floor v)

-- | Interpolate between two hex colors.
-- |
-- | Simple linear interpolation in RGB space.
-- | For t=0, returns colorMin; for t=1, returns colorMax.
interpolateColor :: String -> String -> Number -> String
interpolateColor colorMin colorMax t =
  let
    t' = if t < 0.0 then 0.0 else if t > 1.0 then 1.0 else t
    -- Simple approach: blend the colors via opacity
    -- A more complete implementation would parse hex to RGB
  in
    if t' < 0.33 then colorMin
    else if t' < 0.66 then "#a855f7"  -- Purple midpoint
    else colorMax

-- | Generate array of indices from 0 to n-1.
generateIndices :: Int -> Array Int
generateIndices n = 
  if n <= 0 
    then []
    else mapWithIndex (\idx _ -> idx) (replicate n 0)
