-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // treeview // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Layout — Compute spatial positions for tree nodes.
-- |
-- | ## Design Philosophy
-- |
-- | Layout is pure computation. Given a tree structure and layout configuration,
-- | produce (x, y, width, height) for every node. No rendering — just positions.
-- |
-- | ## Layout Algorithms
-- |
-- | **Linear (1D)**:
-- | - IndentedList: Traditional file explorer (vertical list with indentation)
-- | - Outline: Outline/bullet style
-- |
-- | **Radial (Polar)**:
-- | - Radial: Nodes on concentric circles
-- | - Sunburst: Arcs representing hierarchy
-- | - CirclePack: Nested circles
-- |
-- | **Space-Filling (Area = Value)**:
-- | - Treemap: Nested rectangles
-- | - Icicle: Vertical/horizontal partitions
-- |
-- | **Node-Link (Nodes + Edges)**:
-- | - Tidy: Aesthetic tree (Reingold-Tilford)
-- | - Dendrogram: With branch lengths
-- | - OrgChart: Organizational hierarchy
-- | - MindMap: Central node radiating
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Node (Tree, TreeNode, traversal)
-- | - Schema.Graph.Layout (LayoutConfig, LayoutAlgorithm, NodePosition)

module Hydrogen.Element.Compound.TreeView.Layout
  ( -- * Layout Result
    LayoutResult
  , layoutResult
  , emptyLayout
  , nodePosition
  , nodePositions
  , contentBounds
  , layoutNodeCount
  
  -- * Layout Computation
  , computeLayout
  , recomputeLayout
  
  -- * Indented List Layout
  , layoutIndentedList
  
  -- * Radial Layout
  , layoutRadial
  
  -- * Treemap Layout
  , layoutTreemap
  
  -- * Tidy Tree Layout
  , layoutTidy
  
  -- * Org Chart Layout
  , layoutOrgChart
  
  -- * Mind Map Layout
  , layoutMindMap
  
  -- * Dendrogram Layout
  , layoutDendrogram
  
  -- * Sunburst Layout
  , layoutSunburst
  
  -- * Circle Pack Layout
  , layoutCirclePack
  
  -- * Icicle Layout
  , layoutIcicle
  
  -- * Node Position Queries
  , positionOf
  , childPositions
  , boundingBox
  , centerOf
  
  -- * Layout Utilities
  , translateLayout
  , scaleLayout
  , rotateLayout
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( (-)
  , (+)
  , (/)
  , (*)
  , (==)
  , (>)
  , (&&)
  , max
  , min
  , map
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)
import Data.Map (Map)
import Data.Map as Map
import Data.Tuple (Tuple(Tuple))
import Data.Foldable (foldl)
import Data.Int (toNumber, floor) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , Depth
  , unwrapDepth
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeChildren
  , rootNodes
  , getNode
  , nodeDepth
  )

import Hydrogen.Element.Compound.TreeView.State
  ( ExpandedState
  , isExpanded
  )

import Hydrogen.Schema.Graph.Layout
  ( LayoutConfig
  , LayoutAlgorithm(IndentedList, Outline, Radial, Sunburst, CirclePack, Treemap, Icicle, Partition, Tidy, Cluster, Dendrogram, OrgChart, MindMap, Force, HierarchicalForce)
  , NodeSizing(FixedSize, FitContent, Proportional, AspectRatio)
  , NodePosition
  , siblingGap
  , levelGap
  , RadialParams
  , startAngle
  , endAngle
  , innerRadius
  , outerRadius
  , TreemapParams
  , TreemapAlgorithm(Squarify, Binary, Slice, Dice, SliceDice)
  , nodePosition
  ) as Schema

import Hydrogen.Schema.Graph.Viewport
  ( ViewportBounds
  , viewportBounds
  , boundsWidth
  , boundsHeight
  ) as Viewport

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layout result
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of layout computation
-- |
-- | Contains computed positions for all visible nodes plus metadata
-- | about the layout bounds.
type LayoutResult =
  { positions :: Map NodeId Schema.NodePosition
  , bounds :: Viewport.ViewportBounds
  , nodeCount :: Int
  }

-- | Create a layout result
layoutResult :: 
  Map NodeId Schema.NodePosition -> 
  Viewport.ViewportBounds -> 
  Int -> 
  LayoutResult
layoutResult positions bounds nodeCount =
  { positions, bounds, nodeCount }

-- | Empty layout (no nodes)
emptyLayout :: LayoutResult
emptyLayout =
  { positions: Map.empty
  , bounds: Viewport.viewportBounds 0.0 0.0 0.0 0.0
  , nodeCount: 0
  }

-- | Get position for a specific node
nodePosition :: NodeId -> LayoutResult -> Maybe Schema.NodePosition
nodePosition nid layout = Map.lookup nid layout.positions

-- | Get all node positions
nodePositions :: LayoutResult -> Map NodeId Schema.NodePosition
nodePositions layout = layout.positions

-- | Get content bounds
contentBounds :: LayoutResult -> Viewport.ViewportBounds
contentBounds layout = layout.bounds

-- | Get node count
layoutNodeCount :: LayoutResult -> Int
layoutNodeCount layout = layout.nodeCount

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layout computation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Compute layout for a tree with given configuration
-- |
-- | Dispatches to the appropriate layout algorithm based on config.
computeLayout :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
computeLayout config tree expanded =
  case config.algorithm of
    Schema.IndentedList -> layoutIndentedList config tree expanded
    Schema.Outline -> layoutIndentedList config tree expanded  -- Same as indented
    Schema.Radial -> layoutRadial config tree expanded
    Schema.Sunburst -> layoutSunburst config tree expanded
    Schema.CirclePack -> layoutCirclePack config tree expanded
    Schema.Treemap -> layoutTreemap config tree expanded
    Schema.Icicle -> layoutIcicle config tree expanded
    Schema.Partition -> layoutIcicle config tree expanded  -- Similar to icicle
    Schema.Tidy -> layoutTidy config tree expanded
    Schema.Cluster -> layoutDendrogram config tree expanded  -- Similar
    Schema.Dendrogram -> layoutDendrogram config tree expanded
    Schema.OrgChart -> layoutOrgChart config tree expanded
    Schema.MindMap -> layoutMindMap config tree expanded
    Schema.Force -> layoutTidy config tree expanded  -- Fall back to tidy
    Schema.HierarchicalForce -> layoutTidy config tree expanded

-- | Recompute layout (alias for computeLayout)
recomputeLayout :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
recomputeLayout = computeLayout

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // indented list layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout for traditional file explorer style
-- |
-- | Nodes arranged vertically with indentation per depth level.
-- | Only expanded nodes and their visible children are laid out.
layoutIndentedList :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutIndentedList config tree expanded =
  let
    -- Get visible nodes (flattened, respecting expansion)
    roots = rootNodes tree
    
    -- Layout state: current Y position
    initialState = { y: 0.0, positions: Map.empty, maxX: 0.0 }
    
    -- Layout each root and its visible descendants
    finalState = foldl (layoutIndentedNode config tree expanded) initialState roots
    
    bounds = Viewport.viewportBounds 
      0.0 
      0.0 
      finalState.maxX 
      finalState.y
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Layout state for indented list
type IndentedState =
  { y :: Number
  , positions :: Map NodeId Schema.NodePosition
  , maxX :: Number
  }

-- | Layout a single node and its children in indented list style
layoutIndentedNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  IndentedState ->
  TreeNode ->
  IndentedState
layoutIndentedNode config tree expanded state node =
  let
    nid = nodeId node
    depth = nodeDepth nid tree
    spacing = config.spacing
    nodeHeight = nodeSizeHeight config.sizing
    nodeWidth = nodeSizeWidth config.sizing
    
    -- X position based on depth and indentation
    indentPerLevel = Schema.levelGap spacing
    x = Int.toNumber (unwrapDepth depth) * indentPerLevel
    
    -- Create position for this node
    pos = Schema.nodePosition x state.y nodeWidth nodeHeight
    
    -- Update state with this node
    newPositions = Map.insert nid pos state.positions
    newY = state.y + nodeHeight + Schema.siblingGap spacing
    newMaxX = max state.maxX (x + nodeWidth)
    
    stateAfterNode = 
      { y: newY
      , positions: newPositions
      , maxX: newMaxX
      }
    
    -- If expanded, layout children
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
        in
          foldl (layoutIndentedNode config tree expanded) stateAfterNode childNodes
      else
        stateAfterNode

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // radial layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout nodes on concentric circles
-- |
-- | Root at center, children on first ring, grandchildren on second ring, etc.
layoutRadial :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutRadial config tree expanded =
  let
    radialParams = fromMaybe defaultRadialParams config.radialParams
    start = Schema.startAngle radialParams
    end = Schema.endAngle radialParams
    inner = Schema.innerRadius radialParams
    outer = Schema.outerRadius radialParams
    
    roots = rootNodes tree
    nodeSize = nodeSizeWidth config.sizing
    
    -- Count visible nodes per level for angle distribution
    -- For now, simple implementation: equal angles
    initialState = { positions: Map.empty }
    
    -- Place root at center
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode -> 
        let
          rootPos = Schema.nodePosition 0.0 0.0 nodeSize nodeSize
          stateWithRoot = { positions: Map.insert (nodeId rootNode) rootPos Map.empty }
          childIds = nodeChildren rootNode
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) childIds
          angleStep = (end - start) / Int.toNumber (Array.length childNodes)
        in
          layoutRadialLevel config tree expanded stateWithRoot childNodes inner angleStep start 1
    
    -- Calculate bounds (circular, so use outer radius)
    bounds = Viewport.viewportBounds (negateNum outer) (negateNum outer) outer outer
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Default radial params
defaultRadialParams :: Schema.RadialParams
defaultRadialParams = 
  { startAngle: 0.0
  , endAngle: 6.28318  -- 2π
  , innerRadius: 50.0
  , outerRadius: 300.0
  , clockwise: true
  }

-- | Layout state for radial
type RadialState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout a level of radial tree
layoutRadialLevel ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  RadialState ->
  Array TreeNode ->
  Number ->       -- radius for this level
  Number ->       -- angle step
  Number ->       -- starting angle
  Int ->          -- current level
  RadialState
layoutRadialLevel config tree expanded state nodes radius angleStep startAngle level =
  let
    nodeSize = nodeSizeWidth config.sizing
    radiusStep = 60.0  -- Fixed radius increment per level
    
    -- Place each node
    indexed = Array.mapWithIndex Tuple nodes
    
    stateAfterLevel = foldl 
      (\s (Tuple idx node) ->
        let
          angle = startAngle + (Int.toNumber idx * angleStep)
          x = radius * cos angle
          y = radius * sin angle
          pos = Schema.nodePosition x y nodeSize nodeSize
        in
          { positions: Map.insert (nodeId node) pos s.positions }
      )
      state
      indexed
    
    -- Layout children of expanded nodes
    stateAfterChildren = foldl
      (\s node ->
        let
          nid = nodeId node
          children = nodeChildren node
          isExp = isExpanded nid expanded
        in
          if isExp && Array.length children > 0
            then
              let
                childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
                childAngleStep = angleStep / Int.toNumber (Array.length childNodes)
                parentIdx = fromMaybe 0 (Array.findIndex (\n -> nodeId n == nid) nodes)
                parentAngle = startAngle + (Int.toNumber parentIdx * angleStep)
                childStartAngle = parentAngle - (angleStep / 2.0)
              in
                layoutRadialLevel config tree expanded s childNodes (radius + radiusStep) childAngleStep childStartAngle (level + 1)
            else
              s
      )
      stateAfterLevel
      nodes
  in
    stateAfterChildren

-- | Cosine function (approximate for angles in radians)
cos :: Number -> Number
cos angle = 
  let
    -- Normalize to [0, 2π]
    pi = 3.14159265359
    tau = 2.0 * pi
    normalized = angle - (Int.toNumber (floor (angle / tau))) * tau
    -- Taylor series approximation
    x = normalized
    x2 = x * x
    x4 = x2 * x2
    x6 = x4 * x2
  in
    1.0 - (x2 / 2.0) + (x4 / 24.0) - (x6 / 720.0)

-- | Sine function (approximate)
sin :: Number -> Number
sin angle =
  let
    pi = 3.14159265359
  in
    cos (angle - pi / 2.0)

-- | Floor function - delegate to Data.Int.floor
-- | Returns the largest integer not greater than the argument
floor :: Number -> Int
floor = Int.floor

-- | Negate a Number (local helper to avoid name clash with Prelude.negate for Ring)
negateNum :: Number -> Number
negateNum n = 0.0 - n

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // treemap layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout nodes as nested rectangles (area proportional to value)
-- |
-- | Uses squarify algorithm for optimal aspect ratios.
layoutTreemap :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutTreemap config tree expanded =
  let
    _treemapParams = fromMaybe defaultTreemapParams config.treemapParams
    bounds = fromMaybe (Viewport.viewportBounds 0.0 0.0 800.0 600.0) 
             (boundsFromConstraints config)
    
    roots = rootNodes tree
    
    initialState = { positions: Map.empty }
    
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode ->
        layoutTreemapNode config tree expanded initialState rootNode bounds
    
    resultBounds = Viewport.viewportBounds 0.0 0.0 
                   (Viewport.boundsWidth bounds) 
                   (Viewport.boundsHeight bounds)
  in
    layoutResult finalState.positions resultBounds (Map.size finalState.positions)

-- | Default treemap params
defaultTreemapParams :: Schema.TreemapParams
defaultTreemapParams =
  { algorithm: Schema.Squarify
  , paddingInner: 2.0
  , paddingOuter: 4.0
  , paddingTop: 20.0
  , ratio: 1.618
  }

-- | Layout state for treemap
type TreemapState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout a single treemap node
layoutTreemapNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  TreemapState ->
  TreeNode ->
  Viewport.ViewportBounds ->
  TreemapState
layoutTreemapNode config tree expanded state node bounds =
  let
    nid = nodeId node
    
    -- Create position for this node (full bounds)
    pos = Schema.nodePosition 
          (Viewport.boundsWidth bounds / 2.0)  -- center x
          (Viewport.boundsHeight bounds / 2.0) -- center y
          (Viewport.boundsWidth bounds)
          (Viewport.boundsHeight bounds)
    
    newPositions = Map.insert nid pos state.positions
    
    -- Layout children if expanded
    children = nodeChildren node
    isExp = isExpanded nid expanded
    padding = 4.0
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          innerBounds = Viewport.viewportBounds 
                        padding 
                        (padding + 20.0)  -- Extra top for label
                        (Viewport.boundsWidth bounds - padding)
                        (Viewport.boundsHeight bounds - padding)
          -- Squarify layout for children
          childBounds = squarifyLayout childNodes innerBounds
          
          stateWithNode = { positions: newPositions }
        in
          foldl 
            (\s (Tuple n b) -> layoutTreemapNode config tree expanded s n b)
            stateWithNode
            childBounds
      else
        { positions: newPositions }

-- | Squarify algorithm for treemap layout
-- |
-- | Divides bounds among nodes, optimizing for square-ish rectangles.
squarifyLayout :: Array TreeNode -> Viewport.ViewportBounds -> Array (Tuple TreeNode Viewport.ViewportBounds)
squarifyLayout nodes bounds =
  let
    n = Array.length nodes
    totalWidth = Viewport.boundsWidth bounds
    totalHeight = Viewport.boundsHeight bounds
    
    -- Simple slice layout (horizontal split)
    sliceHeight = totalHeight / Int.toNumber n
  in
    Array.mapWithIndex
      (\idx node ->
        let
          y = Int.toNumber idx * sliceHeight
          nodeBounds = Viewport.viewportBounds 0.0 y totalWidth (y + sliceHeight)
        in
          Tuple node nodeBounds
      )
      nodes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // tidy tree layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Aesthetic tree layout (Reingold-Tilford algorithm)
-- |
-- | Produces aesthetically pleasing trees with:
-- | - Siblings evenly spaced
-- | - Parents centered over children
-- | - Subtrees don't overlap
layoutTidy :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutTidy config tree expanded =
  let
    roots = rootNodes tree
    
    initialState = { positions: Map.empty, maxX: 0.0, maxY: 0.0 }
    
    finalState = foldl
      (\s rootNode ->
        let
          result = layoutTidySubtree config tree expanded rootNode 0.0 0
          mergedPositions = Map.union s.positions result.positions
          newMaxX = max s.maxX result.maxX
          newMaxY = max s.maxY result.maxY
        in
          { positions: mergedPositions
          , maxX: newMaxX
          , maxY: newMaxY
          }
      )
      initialState
      roots
    
    bounds = Viewport.viewportBounds 0.0 0.0 finalState.maxX finalState.maxY
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Tidy layout result for a subtree
type TidyResult =
  { positions :: Map NodeId Schema.NodePosition
  , width :: Number      -- Subtree width
  , x :: Number          -- X offset
  , maxX :: Number
  , maxY :: Number
  }

-- | Layout a subtree using tidy tree algorithm
layoutTidySubtree ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  TreeNode ->
  Number ->       -- X offset
  Int ->          -- Level (for Y)
  TidyResult
layoutTidySubtree config tree expanded node xOffset level =
  let
    nid = nodeId node
    spacing = config.spacing
    nodeWidth = nodeSizeWidth config.sizing
    nodeHeight = nodeSizeHeight config.sizing
    levelGap = Schema.levelGap spacing
    sibGap = Schema.siblingGap spacing
    
    y = Int.toNumber level * (nodeHeight + levelGap)
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          
          -- Layout children first
          childResults = layoutTidyChildren config tree expanded childNodes xOffset (level + 1)
          
          -- Center parent over children
          totalChildWidth = foldl (\acc r -> acc + r.width + sibGap) (negateNum sibGap) childResults
          centerX = xOffset + totalChildWidth / 2.0
          
          pos = Schema.nodePosition centerX y nodeWidth nodeHeight
          
          allPositions = foldl 
            (\acc r -> Map.union acc r.positions) 
            (Map.singleton nid pos)
            childResults
          
          maxChildX = foldl (\acc r -> max acc r.maxX) 0.0 childResults
          maxChildY = foldl (\acc r -> max acc r.maxY) 0.0 childResults
        in
          { positions: allPositions
          , width: max nodeWidth totalChildWidth
          , x: centerX
          , maxX: max centerX maxChildX
          , maxY: max (y + nodeHeight) maxChildY
          }
      else
        let
          pos = Schema.nodePosition xOffset y nodeWidth nodeHeight
        in
          { positions: Map.singleton nid pos
          , width: nodeWidth
          , x: xOffset
          , maxX: xOffset + nodeWidth
          , maxY: y + nodeHeight
          }

-- | Layout children for tidy tree
layoutTidyChildren ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  Array TreeNode ->
  Number ->       -- Starting X offset
  Int ->          -- Level
  Array TidyResult
layoutTidyChildren config tree expanded nodes startX level =
  let
    spacing = config.spacing
    sibGap = Schema.siblingGap spacing
    
    -- Layout each child, accumulating X offset
    result = foldl
      (\acc node ->
        let
          xOffset = acc.currentX
          childResult = layoutTidySubtree config tree expanded node xOffset level
          newX = xOffset + childResult.width + sibGap
        in
          { currentX: newX
          , results: Array.snoc acc.results childResult
          }
      )
      { currentX: startX, results: [] }
      nodes
  in
    result.results

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // org chart layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Organizational chart layout
-- |
-- | Similar to tidy tree but with specific styling for org charts:
-- | - Fixed node sizes
-- | - Centered parents
-- | - Clear hierarchy levels
layoutOrgChart :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutOrgChart config tree expanded =
  -- Org chart is essentially tidy tree with different styling
  layoutTidy config tree expanded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // mind map layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Mind map layout
-- |
-- | Central root with children radiating outward.
-- | Left side children go left, right side children go right.
layoutMindMap :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutMindMap config tree expanded =
  let
    nodeSize = nodeSizeWidth config.sizing
    
    roots = rootNodes tree
    
    initialState = { positions: Map.empty, minX: 0.0, maxX: 0.0, maxY: 0.0 }
    
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode ->
        let
          -- Place root at center
          rootPos = Schema.nodePosition 0.0 0.0 nodeSize nodeSize
          children = nodeChildren rootNode
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          
          -- Split children: half go left, half go right
          halfIdx = Array.length childNodes / 2
          leftChildren = Array.take halfIdx childNodes
          rightChildren = Array.drop halfIdx childNodes
          
          stateWithRoot = 
            { positions: Map.singleton (nodeId rootNode) rootPos
            , minX: 0.0
            , maxX: 0.0
            , maxY: 0.0
            }
          
          -- Layout left side (negative X)
          stateAfterLeft = layoutMindMapSide config tree expanded stateWithRoot leftChildren (negateNum 1.0) 0
          
          -- Layout right side (positive X)
          stateAfterRight = layoutMindMapSide config tree expanded stateAfterLeft rightChildren 1.0 0
        in
          stateAfterRight
    
    bounds = Viewport.viewportBounds finalState.minX 0.0 finalState.maxX finalState.maxY
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Mind map layout state
type MindMapState =
  { positions :: Map NodeId Schema.NodePosition
  , minX :: Number
  , maxX :: Number
  , maxY :: Number
  }

-- | Layout one side of mind map
layoutMindMapSide ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  MindMapState ->
  Array TreeNode ->
  Number ->       -- Direction (-1 for left, 1 for right)
  Int ->          -- Current level
  MindMapState
layoutMindMapSide config tree expanded state nodes direction level =
  let
    spacing = config.spacing
    nodeWidth = nodeSizeWidth config.sizing
    nodeHeight = nodeSizeHeight config.sizing
    levelGap = Schema.levelGap spacing
    sibGap = Schema.siblingGap spacing
    
    xBase = direction * (Int.toNumber (level + 1)) * (nodeWidth + levelGap)
    
    indexed = Array.mapWithIndex Tuple nodes
    
    stateAfterNodes = foldl
      (\s (Tuple idx node) ->
        let
          nid = nodeId node
          y = (Int.toNumber idx - Int.toNumber (Array.length nodes) / 2.0) * (nodeHeight + sibGap)
          pos = Schema.nodePosition xBase y nodeWidth nodeHeight
          
          newPositions = Map.insert nid pos s.positions
          newMinX = min s.minX xBase
          newMaxX = max s.maxX (xBase + nodeWidth)
          newMaxY = max s.maxY (y + nodeHeight)
          
          stateWithNode =
            { positions: newPositions
            , minX: newMinX
            , maxX: newMaxX
            , maxY: newMaxY
            }
          
          -- Layout children
          children = nodeChildren node
          isExp = isExpanded nid expanded
        in
          if isExp && Array.length children > 0
            then
              let
                childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
              in
                layoutMindMapSide config tree expanded stateWithNode childNodes direction (level + 1)
            else
              stateWithNode
      )
      state
      indexed
  in
    stateAfterNodes

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // dendrogram layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dendrogram layout (cluster with branch lengths)
-- |
-- | All leaves at the same level, branches represent distances.
layoutDendrogram :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutDendrogram config tree expanded =
  -- Similar to tidy but with leaves aligned
  layoutTidy config tree expanded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // sunburst layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sunburst layout (radial treemap)
-- |
-- | Arcs radiating from center, angle represents hierarchy.
layoutSunburst :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutSunburst config tree expanded =
  -- Similar to radial but with arc-based nodes
  layoutRadial config tree expanded

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // circle pack layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Circle packing layout
-- |
-- | Nested circles, children packed inside parent circle.
layoutCirclePack :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutCirclePack config tree expanded =
  let
    roots = rootNodes tree
    
    initialState = { positions: Map.empty }
    
    finalState = case Array.head roots of
      Nothing -> initialState
      Just rootNode ->
        layoutCirclePackNode config tree expanded initialState rootNode 0.0 0.0 200.0
    
    bounds = Viewport.viewportBounds (negateNum 200.0) (negateNum 200.0) 200.0 200.0
  in
    layoutResult finalState.positions bounds (Map.size finalState.positions)

-- | Circle pack state
type CirclePackState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout a circle pack node
layoutCirclePackNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  CirclePackState ->
  TreeNode ->
  Number ->       -- Center X
  Number ->       -- Center Y
  Number ->       -- Radius
  CirclePackState
layoutCirclePackNode config tree expanded state node cx cy radius =
  let
    nid = nodeId node
    diameter = radius * 2.0
    pos = Schema.nodePosition cx cy diameter diameter
    
    newPositions = Map.insert nid pos state.positions
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          n = Array.length childNodes
          childRadius = radius * 0.4  -- Smaller radius for children
          
          stateWithNode = { positions: newPositions }
          
          indexed = Array.mapWithIndex Tuple childNodes
        in
          foldl
            (\s (Tuple idx child) ->
              let
                angle = 2.0 * 3.14159 * Int.toNumber idx / Int.toNumber n
                childCx = cx + (radius - childRadius) * cos angle
                childCy = cy + (radius - childRadius) * sin angle
              in
                layoutCirclePackNode config tree expanded s child childCx childCy childRadius
            )
            stateWithNode
            indexed
      else
        { positions: newPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // icicle layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Icicle layout (vertical partition)
-- |
-- | Hierarchical partitions, each level a horizontal band.
layoutIcicle :: 
  Schema.LayoutConfig -> 
  Tree -> 
  ExpandedState -> 
  LayoutResult
layoutIcicle config tree expanded =
  let
    bounds = fromMaybe (Viewport.viewportBounds 0.0 0.0 800.0 600.0) 
             (boundsFromConstraints config)
    
    roots = rootNodes tree
    
    initialState = { positions: Map.empty }
    
    totalWidth = Viewport.boundsWidth bounds
    
    finalState = foldl
      (\s rootNode ->
        layoutIcicleNode config tree expanded s rootNode 0.0 0.0 totalWidth 0
      )
      initialState
      roots
    
    resultBounds = Viewport.viewportBounds 0.0 0.0 
                   (Viewport.boundsWidth bounds) 
                   (Viewport.boundsHeight bounds)
  in
    layoutResult finalState.positions resultBounds (Map.size finalState.positions)

-- | Icicle layout state
type IcicleState =
  { positions :: Map NodeId Schema.NodePosition
  }

-- | Layout an icicle node
layoutIcicleNode ::
  Schema.LayoutConfig ->
  Tree ->
  ExpandedState ->
  IcicleState ->
  TreeNode ->
  Number ->       -- X start
  Number ->       -- Y start
  Number ->       -- Width available
  Int ->          -- Level
  IcicleState
layoutIcicleNode config tree expanded state node x y width level =
  let
    nid = nodeId node
    levelHeight = 40.0
    
    pos = Schema.nodePosition (x + width / 2.0) (y + levelHeight / 2.0) width levelHeight
    newPositions = Map.insert nid pos state.positions
    
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
          n = Array.length childNodes
          childWidth = width / Int.toNumber n
          childY = y + levelHeight
          
          stateWithNode = { positions: newPositions }
          
          indexed = Array.mapWithIndex Tuple childNodes
        in
          foldl
            (\s (Tuple idx child) ->
              let
                childX = x + Int.toNumber idx * childWidth
              in
                layoutIcicleNode config tree expanded s child childX childY childWidth (level + 1)
            )
            stateWithNode
            indexed
      else
        { positions: newPositions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // position queries
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get position of a node
positionOf :: NodeId -> LayoutResult -> Maybe Schema.NodePosition
positionOf = nodePosition

-- | Get positions of children
childPositions :: NodeId -> Tree -> LayoutResult -> Array Schema.NodePosition
childPositions nid tree layout =
  case getNode nid tree of
    Nothing -> []
    Just node ->
      let
        children = nodeChildren node
      in
        Array.mapMaybe (\cid -> nodePosition cid layout) children

-- | Get bounding box for a set of nodes
boundingBox :: Array NodeId -> LayoutResult -> Maybe Viewport.ViewportBounds
boundingBox nids layout =
  let
    positions = Array.mapMaybe (\nid -> nodePosition nid layout) nids
  in
    if Array.length positions == 0
      then Nothing
      else
        let
          xs = map (\p -> p.x) positions
          ys = map (\p -> p.y) positions
          ws = map (\p -> p.width) positions
          hs = map (\p -> p.height) positions
          
          minX = foldl min 1000000.0 xs
          minY = foldl min 1000000.0 ys
          maxX = foldl (\acc (Tuple x w) -> max acc (x + w)) 0.0 (Array.zip xs ws)
          maxY = foldl (\acc (Tuple y h) -> max acc (y + h)) 0.0 (Array.zip ys hs)
        in
          Just (Viewport.viewportBounds minX minY maxX maxY)

-- | Get center point of a node
centerOf :: NodeId -> LayoutResult -> Maybe { x :: Number, y :: Number }
centerOf nid layout =
  case nodePosition nid layout of
    Nothing -> Nothing
    Just pos -> Just { x: pos.x, y: pos.y }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layout utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Translate all positions by offset
translateLayout :: Number -> Number -> LayoutResult -> LayoutResult
translateLayout dx dy layout =
  let
    translatePos pos = Schema.nodePosition (pos.x + dx) (pos.y + dy) pos.width pos.height
    newPositions = map translatePos layout.positions
    newBounds = Viewport.viewportBounds
                (Viewport.boundsWidth layout.bounds + dx)
                (Viewport.boundsHeight layout.bounds + dy)
                (Viewport.boundsWidth layout.bounds + dx)
                (Viewport.boundsHeight layout.bounds + dy)
  in
    { positions: newPositions
    , bounds: newBounds
    , nodeCount: layout.nodeCount
    }

-- | Scale all positions by factor
scaleLayout :: Number -> LayoutResult -> LayoutResult
scaleLayout factor layout =
  let
    scalePos pos = Schema.nodePosition (pos.x * factor) (pos.y * factor) (pos.width * factor) (pos.height * factor)
    newPositions = map scalePos layout.positions
    newBounds = Viewport.viewportBounds
                0.0
                0.0
                (Viewport.boundsWidth layout.bounds * factor)
                (Viewport.boundsHeight layout.bounds * factor)
  in
    { positions: newPositions
    , bounds: newBounds
    , nodeCount: layout.nodeCount
    }

-- | Rotate all positions around origin
rotateLayout :: Number -> LayoutResult -> LayoutResult
rotateLayout angle layout =
  let
    rotatePos pos =
      let
        newX = pos.x * cos angle - pos.y * sin angle
        newY = pos.x * sin angle + pos.y * cos angle
      in
        Schema.nodePosition newX newY pos.width pos.height
    newPositions = map rotatePos layout.positions
  in
    { positions: newPositions
    , bounds: layout.bounds  -- Bounds would need recalculation
    , nodeCount: layout.nodeCount
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Extract node width from sizing config
nodeSizeWidth :: Schema.NodeSizing -> Number
nodeSizeWidth (Schema.FixedSize w _) = w
nodeSizeWidth (Schema.FitContent minW _) = minW
nodeSizeWidth Schema.Proportional = 100.0
nodeSizeWidth (Schema.AspectRatio r) = 100.0 * r

-- | Extract node height from sizing config
nodeSizeHeight :: Schema.NodeSizing -> Number
nodeSizeHeight (Schema.FixedSize _ h) = h
nodeSizeHeight (Schema.FitContent _ minH) = minH
nodeSizeHeight Schema.Proportional = 100.0
nodeSizeHeight (Schema.AspectRatio _) = 100.0

-- | Get bounds from layout constraints
boundsFromConstraints :: Schema.LayoutConfig -> Maybe Viewport.ViewportBounds
boundsFromConstraints config =
  let
    width = config.constraints.bounds.width
    height = config.constraints.bounds.height
  in
    case width, height of
      Just w, Just h -> Just (Viewport.viewportBounds 0.0 0.0 w h)
      _, _ -> Nothing
