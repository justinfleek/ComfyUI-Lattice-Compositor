-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                              // hydrogen // element // treeview // connection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Connection — Render visual connections between parent and child nodes.
-- |
-- | ## Design Philosophy
-- |
-- | Connections are SVG elements that visually link nodes. They support:
-- | - Multiple routing algorithms (straight, curved, orthogonal)
-- | - Terminals (arrows, dots, custom markers)
-- | - Stroke patterns (solid, dashed, dotted)
-- | - Animations (draw, flow, pulse)
-- |
-- | ## SVG Path Generation
-- |
-- | Each routing style generates an SVG path (`d` attribute):
-- | - Straight: `M x1 y1 L x2 y2`
-- | - Curved: `M x1 y1 C cx1 cy1, cx2 cy2, x2 y2`
-- | - Orthogonal: `M x1 y1 H mx V y2 H x2` (or similar)
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Layout (LayoutResult, positions)
-- | - TreeView.Node (Tree, parent-child relationships)
-- | - Schema.Graph.Connection (ConnectionStyle, routing)
-- | - Schema.Graph.Layout (NodePosition)

module Hydrogen.Element.Compound.TreeView.Connection
  ( -- * Connection Rendering
    renderConnections
  , renderConnection
  
  -- * Path Generation
  , connectionPath
  , straightPath
  , curvedPath
  , orthogonalPath
  , stepPath
  
  -- * Connection Points
  , ConnectionPoint
  , connectionPoint
  , nodeConnectionPoints
  , anchorPoint
  
  -- * Terminal Markers
  , renderTerminal
  , arrowMarker
  , dotMarker
  
  -- * Connection Props
  , ConnectionProps
  , defaultConnectionProps
  , withConnectionStyle
  , withShowConnections
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (-)
  , (+)
  , (/)
  , (*)
  , (&&)
  , (<)
  , (>)
  , map
  , not
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Foldable (foldl)

import Hydrogen.Render.Element as E

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeChildren
  , getNode
  , rootNodes
  )

import Hydrogen.Element.Compound.TreeView.State
  ( ExpandedState
  , isExpanded
  )

import Hydrogen.Element.Compound.TreeView.Layout
  ( LayoutResult
  , nodePosition
  )

import Hydrogen.Schema.Graph.Layout
  ( NodePosition
  ) as Schema

import Hydrogen.Schema.Graph.Connection
  ( ConnectionStyle
  , ConnectionRouting(RoutingStraight, RoutingCurved, RoutingOrthogonal, RoutingDiagonal, RoutingStep, RoutingBundle, RoutingArc, RoutingSpline)
  , TerminalStyle(TerminalNone, TerminalArrow, TerminalArrowFilled, TerminalArrowOpen, TerminalDot, TerminalDotFilled, TerminalDiamond, TerminalSquare, TerminalBar)
  , StrokePattern(StrokeSolid, StrokeDashed, StrokeDotted, StrokeDashDot, StrokeCustom)
  , defaultConnectionStyle
  ) as Schema

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // connection props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Properties for connection rendering
type ConnectionProps =
  { style :: Schema.ConnectionStyle
  , showConnections :: Boolean
  , animateOnExpand :: Boolean
  }

-- | Default connection properties
defaultConnectionProps :: ConnectionProps
defaultConnectionProps =
  { style: Schema.defaultConnectionStyle
  , showConnections: true
  , animateOnExpand: false
  }

-- | Set connection style
withConnectionStyle :: Schema.ConnectionStyle -> ConnectionProps -> ConnectionProps
withConnectionStyle s p = p { style = s }

-- | Set whether to show connections
withShowConnections :: Boolean -> ConnectionProps -> ConnectionProps
withShowConnections b p = p { showConnections = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // connection points
-- ═════════════════════════════════════════════════════════════════════════════

-- | A point where a connection attaches to a node
type ConnectionPoint =
  { x :: Number
  , y :: Number
  , side :: String  -- ^ "top", "bottom", "left", "right", "center"
  }

-- | Create a connection point
connectionPoint :: Number -> Number -> String -> ConnectionPoint
connectionPoint x y side = { x, y, side }

-- | Get connection points for a node based on its position
-- |
-- | Returns anchor points for all four sides plus center.
nodeConnectionPoints :: Schema.NodePosition -> { top :: ConnectionPoint, bottom :: ConnectionPoint, left :: ConnectionPoint, right :: ConnectionPoint, center :: ConnectionPoint }
nodeConnectionPoints pos =
  { top: connectionPoint pos.x (pos.y - pos.height / 2.0) "top"
  , bottom: connectionPoint pos.x (pos.y + pos.height / 2.0) "bottom"
  , left: connectionPoint (pos.x - pos.width / 2.0) pos.y "left"
  , right: connectionPoint (pos.x + pos.width / 2.0) pos.y "right"
  , center: connectionPoint pos.x pos.y "center"
  }

-- | Get the anchor point for a specific side
anchorPoint :: String -> Schema.NodePosition -> ConnectionPoint
anchorPoint side pos =
  let points = nodeConnectionPoints pos
  in case side of
    "top" -> points.top
    "bottom" -> points.bottom
    "left" -> points.left
    "right" -> points.right
    _ -> points.center

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // connection rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render all connections for a tree
-- |
-- | Creates an SVG layer with all parent-child connection lines.
renderConnections ::
  forall msg.
  ConnectionProps ->
  Tree ->
  ExpandedState ->
  LayoutResult ->
  E.Element msg
renderConnections props tree expanded layout =
  if not props.showConnections
    then E.empty
    else
      let
        -- Collect all parent-child pairs from expanded nodes
        connections = collectConnections tree expanded layout
      in
        E.element "svg"
          [ E.class_ "tree-connections"
          , E.attr "width" "100%"
          , E.attr "height" "100%"
          , E.style "position" "absolute"
          , E.style "top" "0"
          , E.style "left" "0"
          , E.style "pointer-events" "none"
          , E.style "overflow" "visible"
          ]
          (map (renderConnectionPair props) connections)

-- | A pair of positions for parent and child
type ConnectionPair =
  { parentPos :: Schema.NodePosition
  , childPos :: Schema.NodePosition
  , parentId :: NodeId
  , childId :: NodeId
  }

-- | Collect all connection pairs from tree
collectConnections :: Tree -> ExpandedState -> LayoutResult -> Array ConnectionPair
collectConnections tree expanded layout =
  let
    roots = rootNodes tree
  in
    foldl (collectNodeConnections tree expanded layout) [] roots

-- | Collect connections for a node and its descendants
collectNodeConnections ::
  Tree ->
  ExpandedState ->
  LayoutResult ->
  Array ConnectionPair ->
  TreeNode ->
  Array ConnectionPair
collectNodeConnections tree expanded layout acc node =
  let
    nid = nodeId node
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        case nodePosition nid layout of
          Nothing -> acc
          Just parentPos ->
            let
              -- Create pairs for each child
              childPairs = Array.mapMaybe
                (\cid -> 
                  case nodePosition cid layout of
                    Nothing -> Nothing
                    Just childPos -> Just
                      { parentPos
                      , childPos
                      , parentId: nid
                      , childId: cid
                      }
                )
                children
              
              -- Recurse into children
              accWithPairs = acc <> childPairs
              
              childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
            in
              foldl (collectNodeConnections tree expanded layout) accWithPairs childNodes
      else
        acc

-- | Render a single connection
renderConnectionPair ::
  forall msg.
  ConnectionProps ->
  ConnectionPair ->
  E.Element msg
renderConnectionPair props pair =
  renderConnection props.style pair.parentPos pair.childPos

-- | Render a connection line between two positions
renderConnection ::
  forall msg.
  Schema.ConnectionStyle ->
  Schema.NodePosition ->
  Schema.NodePosition ->
  E.Element msg
renderConnection style parentPos childPos =
  let
    path = connectionPath style.routing parentPos childPos
    
    strokeDashArray = case style.strokePattern of
      Schema.StrokeSolid -> []
      Schema.StrokeDashed dash gap -> 
        [ E.attr "stroke-dasharray" (show dash <> " " <> show gap) ]
      Schema.StrokeDotted -> 
        [ E.attr "stroke-dasharray" "2 4" ]
      Schema.StrokeDashDot -> 
        [ E.attr "stroke-dasharray" "8 4 2 4" ]
      Schema.StrokeCustom arr -> 
        [ E.attr "stroke-dasharray" (Array.intercalate " " (map show arr)) ]
    
    opacityAttr = if style.opacity < 1.0
      then [ E.attr "opacity" (show style.opacity) ]
      else []
  in
    E.element "g"
      [ E.class_ "tree-connection" ]
      [ E.element "path"
          ([ E.attr "d" path
           , E.attr "fill" "none"
           , E.attr "stroke" style.strokeColor
           , E.attr "stroke-width" (show style.strokeWidth)
           , E.attr "stroke-linecap" "round"
           , E.attr "stroke-linejoin" "round"
           ] <> strokeDashArray <> opacityAttr)
          []
      , renderTerminal style.endTerminal childPos.x childPos.y style.strokeColor style.terminalSize
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // path generation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate SVG path for a connection
connectionPath :: Schema.ConnectionRouting -> Schema.NodePosition -> Schema.NodePosition -> String
connectionPath routing parentPos childPos =
  case routing of
    Schema.RoutingStraight -> straightPath parentPos childPos
    Schema.RoutingCurved -> curvedPath parentPos childPos
    Schema.RoutingOrthogonal -> orthogonalPath parentPos childPos
    Schema.RoutingStep -> stepPath parentPos childPos
    Schema.RoutingDiagonal -> diagonalPath parentPos childPos
    Schema.RoutingArc -> arcPath parentPos childPos
    Schema.RoutingSpline -> curvedPath parentPos childPos  -- Fall back to curved
    Schema.RoutingBundle -> curvedPath parentPos childPos  -- Bundle handled separately

-- | Generate a straight line path
straightPath :: Schema.NodePosition -> Schema.NodePosition -> String
straightPath from to =
  let
    -- Connect from bottom of parent to top of child
    x1 = from.x
    y1 = from.y + from.height / 2.0
    x2 = to.x
    y2 = to.y - to.height / 2.0
  in
    "M " <> show x1 <> " " <> show y1 <> " L " <> show x2 <> " " <> show y2

-- | Generate a curved bezier path
curvedPath :: Schema.NodePosition -> Schema.NodePosition -> String
curvedPath from to =
  let
    -- Start from bottom of parent
    x1 = from.x
    y1 = from.y + from.height / 2.0
    -- End at top of child
    x2 = to.x
    y2 = to.y - to.height / 2.0
    -- Control points for smooth curve
    midY = (y1 + y2) / 2.0
    cx1 = x1
    cy1 = midY
    cx2 = x2
    cy2 = midY
  in
    "M " <> show x1 <> " " <> show y1 <> 
    " C " <> show cx1 <> " " <> show cy1 <> 
    ", " <> show cx2 <> " " <> show cy2 <> 
    ", " <> show x2 <> " " <> show y2

-- | Generate an orthogonal (right-angle) path
orthogonalPath :: Schema.NodePosition -> Schema.NodePosition -> String
orthogonalPath from to =
  let
    x1 = from.x
    y1 = from.y + from.height / 2.0
    x2 = to.x
    y2 = to.y - to.height / 2.0
    midY = (y1 + y2) / 2.0
  in
    -- Down from parent, horizontal, then down to child
    "M " <> show x1 <> " " <> show y1 <>
    " V " <> show midY <>
    " H " <> show x2 <>
    " V " <> show y2

-- | Generate a step path (staircase)
stepPath :: Schema.NodePosition -> Schema.NodePosition -> String
stepPath from to =
  let
    x1 = from.x
    y1 = from.y + from.height / 2.0
    x2 = to.x
    y2 = to.y - to.height / 2.0
  in
    -- Horizontal first, then vertical
    "M " <> show x1 <> " " <> show y1 <>
    " H " <> show x2 <>
    " V " <> show y2

-- | Generate a diagonal path
diagonalPath :: Schema.NodePosition -> Schema.NodePosition -> String
diagonalPath from to =
  let
    x1 = from.x
    y1 = from.y + from.height / 2.0
    x2 = to.x
    y2 = to.y - to.height / 2.0
    stepY = (y2 - y1) / 3.0
  in
    "M " <> show x1 <> " " <> show y1 <>
    " L " <> show x1 <> " " <> show (y1 + stepY) <>
    " L " <> show x2 <> " " <> show (y2 - stepY) <>
    " L " <> show x2 <> " " <> show y2

-- | Generate an arc path
arcPath :: Schema.NodePosition -> Schema.NodePosition -> String
arcPath from to =
  let
    x1 = from.x
    y1 = from.y + from.height / 2.0
    x2 = to.x
    y2 = to.y - to.height / 2.0
    dx = x2 - x1
    dy = y2 - y1
    -- Arc radius based on distance
    r = (dx * dx + dy * dy) / (4.0 * dy)
  in
    "M " <> show x1 <> " " <> show y1 <>
    " A " <> show r <> " " <> show r <> " 0 0 1 " <> show x2 <> " " <> show y2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // terminal markers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a terminal marker at a position
renderTerminal ::
  forall msg.
  Schema.TerminalStyle ->
  Number ->        -- x
  Number ->        -- y
  String ->        -- color
  Number ->        -- size
  E.Element msg
renderTerminal terminal x y color size =
  case terminal of
    Schema.TerminalNone -> E.empty
    Schema.TerminalArrow -> arrowMarker x y color size false
    Schema.TerminalArrowFilled -> arrowMarker x y color size true
    Schema.TerminalArrowOpen -> arrowMarker x y color size false
    Schema.TerminalDot -> dotMarker x y color size false
    Schema.TerminalDotFilled -> dotMarker x y color size true
    Schema.TerminalDiamond -> diamondMarker x y color size
    Schema.TerminalSquare -> squareMarker x y color size
    Schema.TerminalBar -> barMarker x y color size

-- | Render an arrow marker
arrowMarker ::
  forall msg.
  Number -> Number -> String -> Number -> Boolean ->
  E.Element msg
arrowMarker x y color size filled =
  let
    halfSize = size / 2.0
    -- Arrow pointing down
    points = 
      show (x - halfSize) <> "," <> show (y - size) <> " " <>
      show x <> "," <> show y <> " " <>
      show (x + halfSize) <> "," <> show (y - size)
    fill = if filled then color else "none"
  in
    E.element "polygon"
      [ E.attr "points" points
      , E.attr "fill" fill
      , E.attr "stroke" color
      , E.attr "stroke-width" "1"
      ]
      []

-- | Render a dot marker
dotMarker ::
  forall msg.
  Number -> Number -> String -> Number -> Boolean ->
  E.Element msg
dotMarker x y color size filled =
  let
    radius = size / 2.0
    fill = if filled then color else "none"
  in
    E.element "circle"
      [ E.attr "cx" (show x)
      , E.attr "cy" (show y)
      , E.attr "r" (show radius)
      , E.attr "fill" fill
      , E.attr "stroke" color
      , E.attr "stroke-width" "1"
      ]
      []

-- | Render a diamond marker
diamondMarker ::
  forall msg.
  Number -> Number -> String -> Number ->
  E.Element msg
diamondMarker x y color size =
  let
    halfSize = size / 2.0
    points = 
      show x <> "," <> show (y - halfSize) <> " " <>
      show (x + halfSize) <> "," <> show y <> " " <>
      show x <> "," <> show (y + halfSize) <> " " <>
      show (x - halfSize) <> "," <> show y
  in
    E.element "polygon"
      [ E.attr "points" points
      , E.attr "fill" color
      , E.attr "stroke" color
      , E.attr "stroke-width" "1"
      ]
      []

-- | Render a square marker
squareMarker ::
  forall msg.
  Number -> Number -> String -> Number ->
  E.Element msg
squareMarker x y color size =
  let
    halfSize = size / 2.0
  in
    E.element "rect"
      [ E.attr "x" (show (x - halfSize))
      , E.attr "y" (show (y - halfSize))
      , E.attr "width" (show size)
      , E.attr "height" (show size)
      , E.attr "fill" color
      , E.attr "stroke" color
      , E.attr "stroke-width" "1"
      ]
      []

-- | Render a bar marker
barMarker ::
  forall msg.
  Number -> Number -> String -> Number ->
  E.Element msg
barMarker x y color size =
  let
    halfSize = size / 2.0
  in
    E.element "line"
      [ E.attr "x1" (show (x - halfSize))
      , E.attr "y1" (show y)
      , E.attr "x2" (show (x + halfSize))
      , E.attr "y2" (show y)
      , E.attr "stroke" color
      , E.attr "stroke-width" "2"
      ]
      []
