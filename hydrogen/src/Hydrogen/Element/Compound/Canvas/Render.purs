-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                       // hydrogen // element // compound // canvas // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Canvas Render — Pure render function for infinite canvas.
-- |
-- | ## Design Philosophy
-- |
-- | The render function is pure: CanvasState -> Element.
-- | It composes all canvas sub-modules to produce the final UI.
-- | No side effects, no DOM manipulation — just Element construction.
-- |
-- | ## Render Structure
-- |
-- | ```
-- | .canvas-container
-- |   .canvas-background
-- |   .canvas-grid-layer
-- |   .canvas-objects-layer
-- |     .canvas-object[n]
-- |   .canvas-guides-layer
-- |   .canvas-selection-layer
-- |     .selection-frame
-- |     .selection-handles
-- |   .canvas-rulers
-- |     .ruler-horizontal
-- |     .ruler-vertical
-- | ```
-- |
-- | ## Compositing Order
-- |
-- | Objects are rendered in zIndex order (lowest first).
-- | Each object applies its compositing settings:
-- | 1. Clip path (binary mask)
-- | 2. Soft mask (alpha)
-- | 3. Track matte (if referenced)
-- | 4. Blend mode
-- | 5. Opacity
-- |
-- | ## Dependencies
-- |
-- | - Canvas.State (CanvasState)
-- | - Canvas.Types (CanvasObject, GridConfig, etc.)
-- | - Canvas.Selection (SelectionFrame, handles)
-- | - Canvas.Grid (GridGeometry)
-- | - Hydrogen.Render.Element (Element constructors)

module Hydrogen.Element.Compound.Canvas.Render
  ( -- * Main Render Function
    canvas
  , canvasWithConfig
  
  -- * Layer Render Functions
  , renderBackground
  , renderGrid
  , renderObjects
  , renderGuides
  , renderSelection
  , renderRulers
  
  -- * Object Rendering
  , renderObject
  , renderObjectWithCompositing
  
  -- * Selection Rendering
  , renderSelectionFrame
  , renderSelectionHandles
  , renderMarquee
  , renderLasso
  
  -- * Grid Rendering
  , renderGridLines
  , renderGridDots
  
  -- * Guide Rendering
  , renderGuide
  
  -- * Ruler Rendering
  , renderHorizontalRuler
  , renderVerticalRuler
  
  -- * Render Config
  , RenderConfig
  , defaultRenderConfig
  , withHandleSize
  , withGridOpacity
  , withSelectionColor
  , withGuideColor
  
  -- * Canvas Messages
  , CanvasMsg(..)
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Show
  , show
  , (<>)
  , (==)
  , (/=)
  , (&&)
  , (||)
  , (>=)
  , (<=)
  , (>)
  , (<)
  , (+)
  , (-)
  , (*)
  , (/)
  , ($)
  , map
  , max
  , min
  , negate
  )

import Data.Array (length, filter, sortBy, foldl, snoc)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Ordering (Ordering(GT, LT, EQ))
import Data.Tuple (Tuple(Tuple))

import Hydrogen.Render.Element as E
import Hydrogen.Element.Compound.Canvas.Types as Types
import Hydrogen.Element.Compound.Canvas.State as State
import Hydrogen.Element.Compound.Canvas.Selection as Selection
import Hydrogen.Schema.Gestural.Selection as GSelection
import Hydrogen.Schema.Color.Blend as Blend
import Hydrogen.Schema.Graph.Viewport as VP

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // canvas messages
-- ═════════════════════════════════════════════════════════════════════════════

-- | Messages the canvas can emit.
data CanvasMsg
  = CanvasMouseDown { x :: Number, y :: Number, button :: Int }
  | CanvasMouseMove { x :: Number, y :: Number }
  | CanvasMouseUp { x :: Number, y :: Number, button :: Int }
  | CanvasWheel { deltaX :: Number, deltaY :: Number, ctrlKey :: Boolean }
  | CanvasKeyDown { key :: String, ctrlKey :: Boolean, shiftKey :: Boolean, altKey :: Boolean }
  | CanvasKeyUp { key :: String }
  | CanvasTouchStart { touches :: Array { x :: Number, y :: Number } }
  | CanvasTouchMove { touches :: Array { x :: Number, y :: Number } }
  | CanvasTouchEnd { touches :: Array { x :: Number, y :: Number } }
  | CanvasToolChange Types.CanvasTool
  | CanvasObjectSelect Types.CanvasObjectId
  | CanvasObjectDeselect Types.CanvasObjectId
  | CanvasZoomIn
  | CanvasZoomOut
  | CanvasZoomFit
  | CanvasPanStart { x :: Number, y :: Number }
  | CanvasPanEnd
  | CanvasUndo
  | CanvasRedo

derive instance eqCanvasMsg :: Eq CanvasMsg

instance showCanvasMsg :: Show CanvasMsg where
  show (CanvasMouseDown p) = "MouseDown(" <> show p.x <> "," <> show p.y <> ")"
  show (CanvasMouseMove p) = "MouseMove(" <> show p.x <> "," <> show p.y <> ")"
  show (CanvasMouseUp p) = "MouseUp(" <> show p.x <> "," <> show p.y <> ")"
  show (CanvasWheel w) = "Wheel(" <> show w.deltaY <> ")"
  show (CanvasKeyDown k) = "KeyDown(" <> k.key <> ")"
  show (CanvasKeyUp k) = "KeyUp(" <> k.key <> ")"
  show (CanvasTouchStart _) = "TouchStart"
  show (CanvasTouchMove _) = "TouchMove"
  show (CanvasTouchEnd _) = "TouchEnd"
  show (CanvasToolChange t) = "ToolChange(" <> show t <> ")"
  show (CanvasObjectSelect id) = "ObjectSelect(" <> show id <> ")"
  show (CanvasObjectDeselect id) = "ObjectDeselect(" <> show id <> ")"
  show CanvasZoomIn = "ZoomIn"
  show CanvasZoomOut = "ZoomOut"
  show CanvasZoomFit = "ZoomFit"
  show (CanvasPanStart p) = "PanStart(" <> show p.x <> "," <> show p.y <> ")"
  show CanvasPanEnd = "PanEnd"
  show CanvasUndo = "Undo"
  show CanvasRedo = "Redo"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // render config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for rendering.
type RenderConfig =
  { handleSize :: Number           -- Size of selection handles in pixels
  , gridOpacity :: Number          -- Opacity of grid lines (0.0-1.0)
  , selectionColor :: String       -- Color of selection outline (hex)
  , selectionWidth :: Number       -- Width of selection outline
  , guideColor :: String           -- Color of guides (hex)
  , marqueeColor :: String         -- Color of marquee rectangle
  , marqueeOpacity :: Number       -- Opacity of marquee fill
  , showRulers :: Boolean          -- Whether to render rulers
  , rulerSize :: Number            -- Size of rulers in pixels
  , antialiased :: Boolean         -- Whether to use antialiasing
  }

-- | Default render configuration.
defaultRenderConfig :: RenderConfig
defaultRenderConfig =
  { handleSize: 8.0
  , gridOpacity: 0.3
  , selectionColor: "#3b82f6"      -- Blue-500
  , selectionWidth: 1.0
  , guideColor: "#06b6d4"          -- Cyan-500
  , marqueeColor: "#3b82f6"        -- Blue-500
  , marqueeOpacity: 0.1
  , showRulers: true
  , rulerSize: 20.0
  , antialiased: true
  }

-- | Set handle size.
withHandleSize :: Number -> RenderConfig -> RenderConfig
withHandleSize size config = config { handleSize = size }

-- | Set grid opacity.
withGridOpacity :: Number -> RenderConfig -> RenderConfig
withGridOpacity opacity config = config { gridOpacity = clamp01 opacity }

-- | Set selection color.
withSelectionColor :: String -> RenderConfig -> RenderConfig
withSelectionColor color config = config { selectionColor = color }

-- | Set guide color.
withGuideColor :: String -> RenderConfig -> RenderConfig
withGuideColor color config = config { guideColor = color }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // main render function
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the canvas with default configuration.
canvas :: State.CanvasState -> E.Element CanvasMsg
canvas = canvasWithConfig defaultRenderConfig

-- | Render the canvas with custom configuration.
canvasWithConfig :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
canvasWithConfig config state =
  E.div_
    ([ E.class_ "canvas-container" ] <> E.styles 
        [ Tuple "position" "relative"
        , Tuple "overflow" "hidden"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        ])
    [ renderBackground state
    , renderGrid config state
    , renderObjects config state
    , renderGuides config state
    , renderSelection config state
    , renderRulersIfEnabled config state
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layer render functions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render canvas background.
renderBackground :: State.CanvasState -> E.Element CanvasMsg
renderBackground state =
  let config = State.getConfig state
  in E.div_
    ([ E.class_ "canvas-background" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "background-color" config.backgroundColor
        ])
    []

-- | Render grid layer.
renderGrid :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderGrid config state =
  let gridConfig = State.getGridConfig state
  in if Types.gridVisible gridConfig
     then E.div_
       ([ E.class_ "canvas-grid-layer" ] <> E.styles
           [ Tuple "position" "absolute"
           , Tuple "top" "0"
           , Tuple "left" "0"
           , Tuple "width" "100%"
           , Tuple "height" "100%"
           , Tuple "pointer-events" "none"
           , Tuple "opacity" (show config.gridOpacity)
           ])
       [ renderGridLines gridConfig state ]
     else E.empty

-- | Render objects layer.
renderObjects :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderObjects config state =
  let 
    objects = State.getObjects state
    sortedObjects = sortByZIndex objects
    viewport = State.getViewport state
  in E.div_
    ([ E.class_ "canvas-objects-layer" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "transform" (viewportTransform viewport)
        , Tuple "transform-origin" "0 0"
        ])
    (map (renderObjectWithCompositing config) sortedObjects)

-- | Render guides layer.
renderGuides :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderGuides config state =
  let guides = State.getGuides state
  in E.div_
    ([ E.class_ "canvas-guides-layer" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "pointer-events" "none"
        ])
    (map (renderGuide config) guides)

-- | Render selection layer (frame, handles, marquee).
renderSelection :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderSelection config state =
  let 
    selection = State.getSelection state
    objects = State.getObjects state
    selectedObjects = filter (\o -> Types.isSelected (Types.objectId o) selection) objects
    frame = Selection.computeSelectionFrame config.handleSize selectedObjects
  in E.div_
    ([ E.class_ "canvas-selection-layer" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" "0"
        , Tuple "width" "100%"
        , Tuple "height" "100%"
        , Tuple "pointer-events" "none"
        ])
    (case frame of
      Nothing -> []
      Just f -> 
        [ renderSelectionFrame config f
        , renderSelectionHandles config f
        ])

-- | Render rulers if enabled.
renderRulersIfEnabled :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderRulersIfEnabled config state =
  if config.showRulers
    then renderRulers config state
    else E.empty

-- | Render rulers.
renderRulers :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderRulers config state =
  E.div_
    [ E.class_ "canvas-rulers"
    ]
    [ renderHorizontalRuler config state
    , renderVerticalRuler config state
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // object rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single object.
renderObject :: Types.CanvasObject -> E.Element CanvasMsg
renderObject obj =
  let bounds = Types.objectBounds obj
  in E.div_
    ([ E.class_ "canvas-object"
     , E.attr "data-object-id" $ showObjectId $ Types.objectId obj
     ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show bounds.x <> "px")
        , Tuple "top" (show bounds.y <> "px")
        , Tuple "width" (show bounds.width <> "px")
        , Tuple "height" (show bounds.height <> "px")
        ])
    []

-- | Render object with full compositing.
renderObjectWithCompositing :: RenderConfig -> Types.CanvasObject -> E.Element CanvasMsg
renderObjectWithCompositing _config obj =
  let 
    bounds = Types.objectBounds obj
    blendMode = Types.objectBlendMode obj
    opacity = Types.objectOpacity obj
    visible = Types.objectVisible obj
  in E.div_
    ([ E.class_ "canvas-object"
     , E.attr "data-object-id" $ showObjectId $ Types.objectId obj
     ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show bounds.x <> "px")
        , Tuple "top" (show bounds.y <> "px")
        , Tuple "width" (show bounds.width <> "px")
        , Tuple "height" (show bounds.height <> "px")
        , Tuple "mix-blend-mode" (blendModeToCSS blendMode)
        , Tuple "opacity" (show opacity)
        , Tuple "visibility" (if visible then "visible" else "hidden")
        ])
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // selection rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render selection frame (bounding box outline).
renderSelectionFrame :: RenderConfig -> Selection.SelectionFrame -> E.Element CanvasMsg
renderSelectionFrame config frame =
  let bounds = Selection.frameBounds frame
  in E.div_
    ([ E.class_ "selection-frame" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show bounds.x <> "px")
        , Tuple "top" (show bounds.y <> "px")
        , Tuple "width" (show bounds.width <> "px")
        , Tuple "height" (show bounds.height <> "px")
        , Tuple "border" (show config.selectionWidth <> "px solid " <> config.selectionColor)
        , Tuple "pointer-events" "none"
        ])
    []

-- | Render selection handles.
renderSelectionHandles :: RenderConfig -> Selection.SelectionFrame -> E.Element CanvasMsg
renderSelectionHandles config frame =
  let handles = Selection.frameHandles frame
  in E.div_
    [ E.class_ "selection-handles" ]
    (map (renderHandle config) handles)

-- | Render a single handle.
renderHandle :: RenderConfig -> Selection.SelectionHandle -> E.Element CanvasMsg
renderHandle config handle =
  let 
    pos = Selection.handlePosition handle
    size = Selection.handleSize handle
    halfSize = size / 2.0
  in E.div_
    ([ E.class_ ("selection-handle handle-" <> show (Selection.handleType handle)) ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "left" (show (pos.x - halfSize) <> "px")
        , Tuple "top" (show (pos.y - halfSize) <> "px")
        , Tuple "width" (show size <> "px")
        , Tuple "height" (show size <> "px")
        , Tuple "background-color" "#ffffff"
        , Tuple "border" ("1px solid " <> config.selectionColor)
        , Tuple "cursor" (handleCursor (Selection.handleType handle))
        ])
    []

-- | Render marquee selection rectangle.
renderMarquee :: RenderConfig -> Selection.MarqueeState -> E.Element CanvasMsg
renderMarquee config marquee =
  if Selection.marqueeActive marquee
    then 
      let rect = Selection.marqueeRect marquee
      in E.div_
        ([ E.class_ "selection-marquee" ] <> E.styles
            [ Tuple "position" "absolute"
            , Tuple "left" (show (GSelection.rectX rect) <> "px")
            , Tuple "top" (show (GSelection.rectY rect) <> "px")
            , Tuple "width" (show (GSelection.rectWidth rect) <> "px")
            , Tuple "height" (show (GSelection.rectHeight rect) <> "px")
            , Tuple "border" ("1px dashed " <> config.marqueeColor)
            , Tuple "background-color" config.marqueeColor
            , Tuple "opacity" (show config.marqueeOpacity)
            , Tuple "pointer-events" "none"
            ])
        []
    else E.empty

-- | Render lasso selection path.
renderLasso :: RenderConfig -> Selection.LassoPath -> E.Element CanvasMsg
renderLasso config lasso =
  let points = Selection.lassoPoints lasso
  in if length points < 2
     then E.empty
     else E.svg_
       ([ E.class_ "selection-lasso" ] <> E.styles
           [ Tuple "position" "absolute"
           , Tuple "top" "0"
           , Tuple "left" "0"
           , Tuple "width" "100%"
           , Tuple "height" "100%"
           , Tuple "pointer-events" "none"
           ])
       [ E.path_
           [ E.attr "d" (lassoToPath points)
           , E.attr "fill" config.marqueeColor
           , E.attr "fill-opacity" (show config.marqueeOpacity)
           , E.attr "stroke" config.marqueeColor
           , E.attr "stroke-width" "1"
           , E.attr "stroke-dasharray" "4 2"
           ]
       ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // grid rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render grid as lines.
renderGridLines :: Types.GridConfig -> State.CanvasState -> E.Element CanvasMsg
renderGridLines gridConfig _state =
  E.svg_
    ([ E.class_ "canvas-grid-lines" ] <> E.styles
        [ Tuple "width" "100%"
        , Tuple "height" "100%"
        ])
    [ E.defs_
        []
        [ E.svgElement "pattern"
            [ E.attr "id" "grid-pattern"
            , E.attr "width" (show gridConfig.size)
            , E.attr "height" (show gridConfig.size)
            , E.attr "patternUnits" "userSpaceOnUse"
            ]
            [ E.line_
                [ E.attr "x1" "0"
                , E.attr "y1" "0"
                , E.attr "x2" (show gridConfig.size)
                , E.attr "y2" "0"
                , E.attr "stroke" gridConfig.minorColor
                , E.attr "stroke-width" (show gridConfig.minorWidth)
                ]
            , E.line_
                [ E.attr "x1" "0"
                , E.attr "y1" "0"
                , E.attr "x2" "0"
                , E.attr "y2" (show gridConfig.size)
                , E.attr "stroke" gridConfig.minorColor
                , E.attr "stroke-width" (show gridConfig.minorWidth)
                ]
            ]
        ]
    , E.rect_
        [ E.attr "width" "100%"
        , E.attr "height" "100%"
        , E.attr "fill" "url(#grid-pattern)"
        ]
    ]

-- | Render grid as dots.
renderGridDots :: Types.GridConfig -> State.CanvasState -> E.Element CanvasMsg
renderGridDots gridConfig _state =
  E.svg_
    ([ E.class_ "canvas-grid-dots" ] <> E.styles
        [ Tuple "width" "100%"
        , Tuple "height" "100%"
        ])
    [ E.defs_
        []
        [ E.svgElement "pattern"
            [ E.attr "id" "dot-pattern"
            , E.attr "width" (show gridConfig.size)
            , E.attr "height" (show gridConfig.size)
            , E.attr "patternUnits" "userSpaceOnUse"
            ]
            [ E.circle_
                [ E.attr "cx" "0"
                , E.attr "cy" "0"
                , E.attr "r" "1"
                , E.attr "fill" gridConfig.minorColor
                ]
            ]
        ]
    , E.rect_
        [ E.attr "width" "100%"
        , E.attr "height" "100%"
        , E.attr "fill" "url(#dot-pattern)"
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // guide rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single guide.
renderGuide :: RenderConfig -> Types.Guide -> E.Element CanvasMsg
renderGuide config guide =
  let 
    pos = Types.guidePosition guide
    isHorizontal = case guide of
      Types.Guide g -> g.orientation == Types.GuideHorizontal
    guideStyles = if isHorizontal
      then
        [ Tuple "position" "absolute"
        , Tuple "left" "0"
        , Tuple "top" (show pos <> "px")
        , Tuple "width" "100%"
        , Tuple "height" "1px"
        , Tuple "background-color" config.guideColor
        ]
      else
        [ Tuple "position" "absolute"
        , Tuple "left" (show pos <> "px")
        , Tuple "top" "0"
        , Tuple "width" "1px"
        , Tuple "height" "100%"
        , Tuple "background-color" config.guideColor
        ]
  in E.div_
    ([ E.class_ (if isHorizontal then "guide guide-horizontal" else "guide guide-vertical") ] <> E.styles guideStyles)
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // ruler rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render horizontal ruler.
renderHorizontalRuler :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderHorizontalRuler config _state =
  E.div_
    ([ E.class_ "ruler ruler-horizontal" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" "0"
        , Tuple "left" (show config.rulerSize <> "px")
        , Tuple "right" "0"
        , Tuple "height" (show config.rulerSize <> "px")
        , Tuple "background-color" "#2a2a2a"
        , Tuple "border-bottom" "1px solid #404040"
        ])
    []

-- | Render vertical ruler.
renderVerticalRuler :: RenderConfig -> State.CanvasState -> E.Element CanvasMsg
renderVerticalRuler config _state =
  E.div_
    ([ E.class_ "ruler ruler-vertical" ] <> E.styles
        [ Tuple "position" "absolute"
        , Tuple "top" (show config.rulerSize <> "px")
        , Tuple "left" "0"
        , Tuple "bottom" "0"
        , Tuple "width" (show config.rulerSize <> "px")
        , Tuple "background-color" "#2a2a2a"
        , Tuple "border-right" "1px solid #404040"
        ])
    []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Clamp value to 0.0-1.0 range.
clamp01 :: Number -> Number
clamp01 n = max 0.0 (min 1.0 n)

-- | Sort objects by zIndex ascending.
sortByZIndex :: Array Types.CanvasObject -> Array Types.CanvasObject
sortByZIndex = sortBy compareZIndex
  where
    compareZIndex a b =
      let za = Types.objectZIndex a
          zb = Types.objectZIndex b
      in if za < zb then LT
         else if za > zb then GT
         else EQ

-- | Convert blend mode to CSS mix-blend-mode value.
blendModeToCSS :: Blend.BlendMode -> String
blendModeToCSS Blend.Normal = "normal"
blendModeToCSS Blend.Multiply = "multiply"
blendModeToCSS Blend.Screen = "screen"
blendModeToCSS Blend.Overlay = "overlay"
blendModeToCSS Blend.Darken = "darken"
blendModeToCSS Blend.Lighten = "lighten"
blendModeToCSS Blend.ColorDodge = "color-dodge"
blendModeToCSS Blend.ColorBurn = "color-burn"
blendModeToCSS Blend.HardLight = "hard-light"
blendModeToCSS Blend.SoftLight = "soft-light"
blendModeToCSS Blend.Difference = "difference"
blendModeToCSS Blend.Exclusion = "exclusion"
blendModeToCSS _ = "normal"  -- Fallback for non-CSS blend modes (Hue, Saturation, Color, Luminosity not in BlendMode ADT)

-- | Generate viewport transform CSS.
viewportTransform :: VP.ViewportState -> String
viewportTransform vp = 
  let 
    zoom = VP.zoomLevel (VP.viewportZoomLevel vp)
    pan = VP.viewportPan vp
  in "translate(" <> show (VP.panX pan) <> "px, " <> show (VP.panY pan) <> "px) " <>
     "scale(" <> show zoom <> ")"

-- | Show object ID as string.
showObjectId :: Types.CanvasObjectId -> String
showObjectId (Types.CanvasObjectId id) = id

-- | Get cursor for handle type.
handleCursor :: Selection.HandleType -> String
handleCursor Selection.HandleTopLeft = "nwse-resize"
handleCursor Selection.HandleTopCenter = "ns-resize"
handleCursor Selection.HandleTopRight = "nesw-resize"
handleCursor Selection.HandleMiddleLeft = "ew-resize"
handleCursor Selection.HandleMiddleRight = "ew-resize"
handleCursor Selection.HandleBottomLeft = "nesw-resize"
handleCursor Selection.HandleBottomCenter = "ns-resize"
handleCursor Selection.HandleBottomRight = "nwse-resize"
handleCursor Selection.HandleRotation = "grab"
handleCursor Selection.HandleCenter = "move"

-- | Convert lasso points to SVG path.
lassoToPath :: Array { x :: Number, y :: Number } -> String
lassoToPath points =
  foldl buildPath "" (indexPoints points)
  where
    buildPath acc item =
      if item.idx == 0
        then "M " <> show item.point.x <> " " <> show item.point.y
        else acc <> " L " <> show item.point.x <> " " <> show item.point.y
    
    indexPoints pts = indexHelper pts 0 []
    
    indexHelper pts idx acc =
      case arrayIndex pts idx of
        Nothing -> acc
        Just p -> indexHelper pts (idx + 1) (snoc acc { idx, point: p })

-- | Safe array index.
arrayIndex :: forall a. Array a -> Int -> Maybe a
arrayIndex arr idx =
  if idx < 0 || idx >= length arr
    then Nothing
    else arrayIndexUnsafe arr idx

-- | Array index (using foldl for safety).
arrayIndexUnsafe :: forall a. Array a -> Int -> Maybe a
arrayIndexUnsafe arr idx =
  let result = foldl (\acc item ->
        case acc of
          { found: Just _, i: _ } -> acc
          { found: Nothing, i } ->
            if i == idx 
              then { found: Just item, i: i + 1 }
              else { found: Nothing, i: i + 1 }
      ) { found: Nothing, i: 0 } arr
  in result.found
