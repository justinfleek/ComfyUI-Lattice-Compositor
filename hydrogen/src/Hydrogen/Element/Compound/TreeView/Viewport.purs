-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                // hydrogen // element // treeview // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Viewport — Virtualization for rendering 100k+ node trees.
-- |
-- | ## Design Philosophy
-- |
-- | Large trees cannot render all nodes. The viewport system:
-- | 1. Tracks the visible region (zoom, pan)
-- | 2. Culls nodes outside the viewport
-- | 3. Uses level-of-detail to simplify distant nodes
-- | 4. Progressively loads nodes as they become visible
-- |
-- | ## Virtualization Strategy
-- |
-- | **For 100k+ nodes:**
-- | - Only render nodes in viewport + overscan buffer
-- | - Use spatial indexing for O(log n) visibility queries
-- | - Progressive disclosure (lazy children)
-- | - Chunked rendering (render in batches per frame)
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Layout (LayoutResult, positions)
-- | - TreeView.Node (Tree structure)
-- | - Schema.Graph.Viewport (zoom, pan, bounds)

module Hydrogen.Element.Compound.TreeView.Viewport
  ( -- * Viewport State
    TreeViewport
  , treeViewport
  , initialViewport
  , viewportZoom
  , viewportPan
  , viewportScreenSize
  
  -- * Viewport Updates
  , setViewportZoom
  , setViewportPan
  , panViewport
  , zoomViewport
  , zoomToPoint
  , fitToContent
  
  -- * Visible Nodes
  , visibleNodes
  , visibleNodeIds
  , isNodeVisible
  , nodeVisibility
  
  -- * Virtualization
  , VirtualizedTree
  , virtualizedTree
  , virtualNodeCount
  , renderWindow
  , shouldRenderNode
  
  -- * Chunked Rendering
  , RenderChunk
  , renderChunks
  , chunkNodes
  , nextChunk
  , isRenderComplete
  
  -- * Progressive Loading
  , LoadRequest
  , loadRequest
  , pendingLoads
  , acknowledgeLoad
  
  -- * Level of Detail
  , nodeLOD
  , shouldShowLabel
  , shouldShowIcon
  , simplifiedNode
  
  -- * Viewport Events
  , ViewportEvent(Pan, Zoom, ZoomToLevel, FitAll, CenterOn, ResetView)
  , handleViewportEvent
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
  , (==)
  , (/=)
  , (>)
  , (>=)
  , (<)
  , (<=)
  , (&&)
  , (||)
  , max
  , min
  , map
  , not
  )

import Data.Array as Array
import Data.Maybe (Maybe(Just, Nothing))
import Data.Map (Map)
import Data.Map as Map
import Data.Foldable (foldl)
import Data.Int (toNumber) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeChildren
  , rootNodes
  , getNode
  )

import Hydrogen.Element.Compound.TreeView.State
  ( ExpandedState
  , isExpanded
  )

import Hydrogen.Element.Compound.TreeView.Layout
  ( LayoutResult
  , nodePosition
  , contentBounds
  )

import Hydrogen.Schema.Graph.Viewport 
  ( ViewportZoom
  , ViewportPosition
  , ViewportBounds
  , ViewportState
  , LevelOfDetail(LOD_Full, LOD_Simplified, LOD_Minimal, LOD_Dot, LOD_Hidden)
  , CullResult(Visible, PartiallyVisible, Culled)
  )

import Hydrogen.Schema.Graph.Viewport as Schema

import Hydrogen.Schema.Graph.Layout (NodePosition) as Layout

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // viewport state
-- ═════════════════════════════════════════════════════════════════════════════

-- | TreeView-specific viewport state
type TreeViewport =
  { state :: Schema.ViewportState
  , overscan :: Number              -- ^ Extra pixels to render beyond viewport
  , chunkSize :: Int                -- ^ Nodes per render chunk
  , maxVisibleNodes :: Int          -- ^ Cap on visible nodes
  }

-- | Create a tree viewport
treeViewport :: Number -> Number -> TreeViewport
treeViewport screenWidth screenHeight =
  let
    defaultZoom = Schema.viewportZoom 1.0
  in
    { state: Schema.viewportState defaultZoom Schema.origin screenWidth screenHeight
    , overscan: 200.0
    , chunkSize: 100
    , maxVisibleNodes: 1000
    }

-- | Initial viewport centered with default zoom
initialViewport :: Number -> Number -> TreeViewport
initialViewport = treeViewport

-- | Get current zoom
viewportZoom :: TreeViewport -> Schema.ViewportZoom
viewportZoom vp = vp.state.zoom

-- | Get current pan position
viewportPan :: TreeViewport -> Schema.ViewportPosition
viewportPan vp = vp.state.pan

-- | Get screen size
viewportScreenSize :: TreeViewport -> { width :: Number, height :: Number }
viewportScreenSize vp = { width: vp.state.screenWidth, height: vp.state.screenHeight }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // viewport updates
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set zoom level
setViewportZoom :: Schema.ViewportZoom -> TreeViewport -> TreeViewport
setViewportZoom zoom vp = 
  vp { state = vp.state { zoom = zoom } }

-- | Set pan position
setViewportPan :: Schema.ViewportPosition -> TreeViewport -> TreeViewport
setViewportPan pan vp = 
  vp { state = vp.state { pan = pan } }

-- | Pan viewport by pixel delta
panViewport :: Number -> Number -> TreeViewport -> TreeViewport
panViewport dx dy vp =
  vp { state = Schema.applyPan dx dy vp.state }

-- | Zoom viewport by step
zoomViewport :: Boolean -> TreeViewport -> TreeViewport
zoomViewport zoomingIn vp =
  let
    currentZoom = vp.state.zoom
    newZoom = if zoomingIn then Schema.zoomIn currentZoom else Schema.zoomOut currentZoom
  in
    vp { state = Schema.applyZoom newZoom vp.state }

-- | Zoom centered on a specific point
zoomToPoint :: Number -> Number -> Boolean -> TreeViewport -> TreeViewport
zoomToPoint targetX targetY zoomingIn vp =
  let
    -- Get the current zoom and calculate point position in viewport
    oldZoom = Schema.zoomLevel vp.state.zoom
    
    -- Zoom first
    zoomed = zoomViewport zoomingIn vp
    newZoom = Schema.zoomLevel zoomed.state.zoom
    
    -- Calculate the pan adjustment to keep targetX, targetY at the same screen position
    -- Point in old viewport: (targetX - pan.x) * oldZoom = screenX
    -- We want: (targetX - newPan.x) * newZoom = screenX (same screen position)
    -- So: newPan.x = targetX - (targetX - oldPan.x) * (oldZoom / newZoom)
    zoomRatio = oldZoom / newZoom
    newPanX = targetX - (targetX - vp.state.pan.x) * zoomRatio
    newPanY = targetY - (targetY - vp.state.pan.y) * zoomRatio
  in
    setViewportPan (Schema.viewportPosition newPanX newPanY) zoomed

-- | Fit viewport to content bounds
fitToContent :: LayoutResult -> TreeViewport -> TreeViewport
fitToContent layout vp =
  let
    content = contentBounds layout
  in
    vp { state = Schema.fitContent content vp.state }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // visible nodes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get all visible nodes in viewport order
visibleNodes :: Tree -> ExpandedState -> LayoutResult -> TreeViewport -> Array TreeNode
visibleNodes tree expanded layout vp =
  let
    bounds = getVisibleBounds vp
    allNodes = collectVisibleNodes tree expanded layout bounds
    limited = Array.take vp.maxVisibleNodes allNodes
  in
    limited

-- | Get visible node IDs
visibleNodeIds :: Tree -> ExpandedState -> LayoutResult -> TreeViewport -> Array NodeId
visibleNodeIds tree expanded layout vp =
  map nodeId (visibleNodes tree expanded layout vp)

-- | Check if a specific node is visible
isNodeVisible :: NodeId -> LayoutResult -> TreeViewport -> Boolean
isNodeVisible nid layout vp =
  case nodePosition nid layout of
    Nothing -> false
    Just pos ->
      let
        bounds = getVisibleBounds vp
        cullResult = Schema.cullNode bounds pos.x pos.y pos.width pos.height
      in
        cullResult == Visible || cullResult == PartiallyVisible

-- | Get visibility status for a node
nodeVisibility :: NodeId -> LayoutResult -> TreeViewport -> Schema.CullResult
nodeVisibility nid layout vp =
  case nodePosition nid layout of
    Nothing -> Culled
    Just pos ->
      let
        bounds = getVisibleBounds vp
      in
        Schema.cullNode bounds pos.x pos.y pos.width pos.height

-- | Get visible bounds including overscan
getVisibleBounds :: TreeViewport -> Schema.ViewportBounds
getVisibleBounds vp =
  Schema.expandBounds vp.overscan (Schema.viewportBoundsAt vp.state)

-- | Collect visible nodes from tree
collectVisibleNodes :: Tree -> ExpandedState -> LayoutResult -> Schema.ViewportBounds -> Array TreeNode
collectVisibleNodes tree expanded layout bounds =
  let
    roots = rootNodes tree
  in
    foldl (collectIfVisible tree expanded layout bounds) [] roots

-- | Collect a node if visible
collectIfVisible ::
  Tree ->
  ExpandedState ->
  LayoutResult ->
  Schema.ViewportBounds ->
  Array TreeNode ->
  TreeNode ->
  Array TreeNode
collectIfVisible tree expanded layout bounds acc node =
  let
    nid = nodeId node
    isVisible = case nodePosition nid layout of
      Nothing -> false
      Just pos -> 
        let result = Schema.cullNode bounds pos.x pos.y pos.width pos.height
        in result == Visible || result == PartiallyVisible
    
    newAcc = if isVisible then Array.snoc acc node else acc
    
    -- Check children if expanded
    children = nodeChildren node
    isExp = isExpanded nid expanded
  in
    if isExp && Array.length children > 0
      then
        let
          childNodes = Array.mapMaybe (\cid -> getNode cid tree) children
        in
          foldl (collectIfVisible tree expanded layout bounds) newAcc childNodes
      else
        newAcc

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // virtualization
-- ═════════════════════════════════════════════════════════════════════════════

-- | Virtualized tree state
type VirtualizedTree =
  { visibleNodeIds :: Array NodeId
  , totalNodes :: Int
  , renderedNodes :: Int
  , pendingLoads :: Array NodeId  -- Nodes that need lazy loading
  }

-- | Create virtualized tree state
virtualizedTree :: Tree -> ExpandedState -> LayoutResult -> TreeViewport -> VirtualizedTree
virtualizedTree tree expanded layout vp =
  let
    visible = visibleNodeIds tree expanded layout vp
  in
    { visibleNodeIds: visible
    , totalNodes: Array.length visible  -- Simplified: would need full tree count
    , renderedNodes: 0
    , pendingLoads: []
    }

-- | Get count of virtual nodes
virtualNodeCount :: VirtualizedTree -> Int
virtualNodeCount vt = vt.totalNodes

-- | Get the render window (which nodes to render)
renderWindow :: VirtualizedTree -> Array NodeId
renderWindow vt = vt.visibleNodeIds

-- | Should a specific node be rendered?
shouldRenderNode :: NodeId -> VirtualizedTree -> Boolean
shouldRenderNode nid vt =
  Array.elem nid vt.visibleNodeIds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // chunked rendering
-- ═════════════════════════════════════════════════════════════════════════════

-- | A chunk of nodes to render in one frame
type RenderChunk =
  { nodes :: Array NodeId
  , chunkIndex :: Int
  , totalChunks :: Int
  , isLast :: Boolean
  }

-- | Split visible nodes into render chunks
renderChunks :: Int -> VirtualizedTree -> Array RenderChunk
renderChunks chunkSize vt =
  let
    allNodes = vt.visibleNodeIds
    totalNodes = Array.length allNodes
    totalChunks = (totalNodes + chunkSize - 1) / chunkSize  -- Ceiling division
    
    makeChunk idx =
      let
        start = idx * chunkSize
        nodes = Array.slice start (start + chunkSize) allNodes
        isLast = idx == totalChunks - 1
      in
        { nodes, chunkIndex: idx, totalChunks, isLast }
  in
    map makeChunk (Array.range 0 (totalChunks - 1))

-- | Get nodes for a specific chunk
chunkNodes :: Int -> Int -> VirtualizedTree -> Array NodeId
chunkNodes chunkIndex chunkSize vt =
  let
    start = chunkIndex * chunkSize
  in
    Array.slice start (start + chunkSize) vt.visibleNodeIds

-- | Get next chunk to render
nextChunk :: Int -> Int -> VirtualizedTree -> Maybe RenderChunk
nextChunk currentChunk chunkSize vt =
  let
    allNodes = vt.visibleNodeIds
    totalNodes = Array.length allNodes
    totalChunks = (totalNodes + chunkSize - 1) / chunkSize
    nextIdx = currentChunk + 1
  in
    if nextIdx >= totalChunks
      then Nothing
      else Just
        { nodes: chunkNodes nextIdx chunkSize vt
        , chunkIndex: nextIdx
        , totalChunks
        , isLast: nextIdx == totalChunks - 1
        }

-- | Check if all chunks have been rendered
isRenderComplete :: Int -> Int -> VirtualizedTree -> Boolean
isRenderComplete renderedChunks chunkSize vt =
  let
    totalNodes = Array.length vt.visibleNodeIds
    totalChunks = (totalNodes + chunkSize - 1) / chunkSize
  in
    renderedChunks >= totalChunks

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // progressive loading
-- ═════════════════════════════════════════════════════════════════════════════

-- | Request to load lazy node data
type LoadRequest =
  { nodeId :: NodeId
  , priority :: Int  -- Lower = higher priority
  }

-- | Create a load request
loadRequest :: NodeId -> Int -> LoadRequest
loadRequest nodeId priority = { nodeId, priority }

-- | Get pending load requests
pendingLoads :: VirtualizedTree -> Array LoadRequest
pendingLoads vt =
  Array.mapWithIndex (\idx nid -> loadRequest nid idx) vt.pendingLoads

-- | Acknowledge that a load completed
-- | Removes the node from pending loads after its children have been loaded
acknowledgeLoad :: NodeId -> VirtualizedTree -> VirtualizedTree
acknowledgeLoad nid vt =
  vt { pendingLoads = Array.filter (\id -> id /= nid) vt.pendingLoads }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // level of detail
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get LOD for a node based on viewport
nodeLOD :: NodeId -> LayoutResult -> TreeViewport -> Schema.LevelOfDetail
nodeLOD nid layout vp =
  case nodePosition nid layout of
    Nothing -> LOD_Hidden
    Just pos ->
      let
        nodeSize = max pos.width pos.height
      in
        Schema.lodForZoom vp.state.zoom nodeSize

-- | Should label be shown at this LOD?
shouldShowLabel :: NodeId -> LayoutResult -> TreeViewport -> Boolean
shouldShowLabel nid layout vp =
  Schema.shouldRenderLabel (nodeLOD nid layout vp)

-- | Should icon be shown at this LOD?
shouldShowIcon :: NodeId -> LayoutResult -> TreeViewport -> Boolean
shouldShowIcon nid layout vp =
  let
    lod = nodeLOD nid layout vp
  in
    lod == LOD_Full || lod == LOD_Simplified

-- | Get simplified node representation for low LOD
simplifiedNode :: NodeId -> LayoutResult -> TreeViewport -> { showLabel :: Boolean, showIcon :: Boolean, showDot :: Boolean }
simplifiedNode nid layout vp =
  let
    lod = nodeLOD nid layout vp
  in
    { showLabel: lod == LOD_Full || lod == LOD_Simplified
    , showIcon: lod == LOD_Full || lod == LOD_Simplified
    , showDot: lod == LOD_Dot
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // viewport events
-- ═════════════════════════════════════════════════════════════════════════════

-- | Events that affect the viewport
data ViewportEvent
  = Pan Number Number           -- ^ Pan by (dx, dy) pixels
  | Zoom Boolean                -- ^ Zoom in (true) or out (false)
  | ZoomToLevel Number          -- ^ Zoom to specific level (0-1)
  | FitAll                      -- ^ Fit all content in viewport
  | CenterOn NodeId             -- ^ Center on a specific node
  | ResetView                   -- ^ Reset to initial view

-- | Handle a viewport event
handleViewportEvent :: ViewportEvent -> LayoutResult -> TreeViewport -> TreeViewport
handleViewportEvent event layout vp =
  case event of
    Pan dx dy -> panViewport dx dy vp
    Zoom zoomingIn -> zoomViewport zoomingIn vp
    ZoomToLevel level -> 
      setViewportZoom (Schema.viewportZoom level) vp
    FitAll -> fitToContent layout vp
    CenterOn nid -> centerOnNode nid layout vp
    ResetView -> initialViewport vp.state.screenWidth vp.state.screenHeight

-- | Center viewport on a node
centerOnNode :: NodeId -> LayoutResult -> TreeViewport -> TreeViewport
centerOnNode nid layout vp =
  case nodePosition nid layout of
    Nothing -> vp
    Just pos ->
      let
        -- Calculate pan to center node
        centerX = pos.x
        centerY = pos.y
        z = Schema.zoomLevel vp.state.zoom
        newPanX = centerX - (vp.state.screenWidth / z) / 2.0
        newPanY = centerY - (vp.state.screenHeight / z) / 2.0
      in
        setViewportPan (Schema.viewportPosition newPanX newPanY) vp
