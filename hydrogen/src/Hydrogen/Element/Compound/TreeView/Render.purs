-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // treeview // render
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView Render — Pure Element rendering for tree components.
-- |
-- | ## Design Philosophy
-- |
-- | This module renders tree state to pure Element values. No side effects.
-- | The Element can be interpreted to any target (DOM, Halogen, Static HTML).
-- |
-- | ## Integration with TreeView Modules
-- |
-- | This module integrates with:
-- | - Layout: For computing node positions
-- | - Content: For slot-based node content rendering
-- | - Connection: For SVG connection lines between nodes
-- | - Accessibility: For ARIA attributes and announcements
-- | - Viewport: For virtualization of large trees
-- |
-- | ## Schema Atoms Accepted
-- |
-- | | Property             | Pillar     | Type                      |
-- | |----------------------|------------|---------------------------|
-- | | backgroundColor      | Color      | Color.RGB                 |
-- | | selectedColor        | Color      | Color.RGB                 |
-- | | focusRingColor       | Color      | Color.RGB                 |
-- | | iconColor            | Color      | Color.RGB                 |
-- | | textColor            | Color      | Color.RGB                 |
-- | | indentSize           | Dimension  | Device.Pixel              |
-- | | nodeHeight           | Dimension  | Device.Pixel              |
-- | | iconSize             | Dimension  | Device.Pixel              |
-- | | borderRadius         | Geometry   | Geometry.Corners          |
-- | | hoverBackground      | Color      | Color.RGB                 |
-- |
-- | ## Dependencies
-- |
-- | - TreeView.Types (NodeId, TreeViewMsg, etc.)
-- | - TreeView.State (TreeViewState, ExpandedState, etc.)
-- | - TreeView.Node (Tree, TreeNode, traversal functions)
-- | - TreeView.Layout (computeLayout, LayoutResult)
-- | - TreeView.Content (renderNodeContent)
-- | - TreeView.Connection (renderConnections)
-- | - TreeView.Accessibility (containerAriaAttrs, nodeAriaAttrs)
-- | - Hydrogen.Render.Element (Element, Attribute)

module Hydrogen.Element.Compound.TreeView.Render
  ( -- * Main Renderer
    renderTreeView
  , renderTreeViewAdvanced
  , renderNode
  
  -- * State-Specific Renderers
  , renderExpandedNodes
  , renderSelectedNodes
  , renderCheckedNodes
  , renderFocusedNode
  
  -- * Subtree Renderers
  , renderSubtree
  , renderRootNodes
  , renderChildNodes
  
  -- * Props
  , TreeViewProps
  , TreeViewProp
  , defaultProps
  
  -- * Prop Builders: Color
  , backgroundColor
  , selectedColor
  , focusRingColor
  , iconColor
  , textColor
  , hoverBackground
  , expandIconColor
  
  -- * Prop Builders: Dimension
  , indentSize
  , nodeHeight
  , iconSize
  , expandIconSize
  
  -- * Prop Builders: Geometry
  , borderRadius
  
  -- * Prop Builders: Behavior
  , onNodeClick
  , onNodeExpand
  , onNodeSelect
  , onNodeCheck
  , onNodeDoubleClick
  , onNodeDragStart
  , onNodeDragEnd
  , onNodeDragOver
  , onNodeDrop
  , onKeyDown
  , onNodeHover
  , onNodeHoverEnd
  , withPropsCheckable
  
  -- * Prop Builders: Layout
  , withLayoutConfig
  , withConnectionProps
  , withPropsConnectionStyle
  , withContentProps
  , withAccessibilityConfig
  , withPropsShowConnections
  
  -- * Node Renderers
  , renderExpandIcon
  , renderNodeIcon
  , renderNodeLabel
  , renderCheckbox
  , renderCheckboxReadOnly
  , renderDropIndicator
  
  -- * Advanced Rendering
  , renderNodeWithLayout
  , renderNodeAtPosition
  
  -- * Default Message Props
  -- | Convenience prop builders using default TreeViewMsg constructors
  , withDefaultExpandHandler
  , withDefaultSelectHandler
  , withDefaultCheckHandler
  , withDefaultFocusHandler
  , withDefaultActivateHandler
  , withDefaultDragStartHandler
  , withDefaultDragEndHandler
  , withDefaultDragOverHandler
  , withDefaultDropHandler
  , withDefaultHoverHandlers
  , withDefaultKeyboardHandler
  , withAllDefaultHandlers
  , keyToNavigationMsg
  
  -- * Utilities
  , isNodeDisabled
  , computeIndentPixels
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( show
  , (<>)
  , (*)
  , ($)
  , (#)
  , (==)
  , (+)
  , (&&)
  , map
  , not
  , negate
  )

import Data.Array as Array
import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing), maybe, fromMaybe)

import Hydrogen.Render.Element as E
import Hydrogen.Schema.Color.RGB as Color
import Hydrogen.Schema.Geometry.Radius as Geometry
import Hydrogen.Schema.Dimension.Device (Pixel, unwrapPixel)
import Hydrogen.Schema.Dimension.Device as Device
import Data.Int (toNumber) as Int

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , Depth
  , unwrapDepth
  , CheckState(Checked, Unchecked, Indeterminate)
  , NodeIcon(IconFolder, IconFolderOpen)
  , iconToEmoji
  , iconToAria
  , SelectionMode(SingleSelect)
  , DropPosition(DropBefore, DropAfter, DropInside)
  , TreeViewMsg
      ( ToggleExpand
      , SelectNode
      , ToggleCheck
      , SetFocus
      , ActivateNode
      -- Drag/drop messages
      , BeginDrag
      , EndDrag
      , DragOver
      , DropNode
      -- Navigation messages
      , NavigateUp
      , NavigateDown
      , NavigateLeft
      , NavigateRight
      , NavigateHome
      , NavigateEnd
      -- Hover messages
      , SetHover
      , ClearHover
      )
  )

import Hydrogen.Element.Compound.TreeView.State
  ( TreeViewState
  , ExpandedState
  , SelectedState
  , CheckedState
  , FocusState
  , DragState
  , SearchState
  , LoadingState
  , EditState
  , HoverState
  , isExpanded
  , isSelected
  , getCheckState
  , getFocusedNode
  , isHoveringNode
  , getDragTarget
  , getDragPosition
  , selectedNodes
  , checkedNodes
  , emptySelected
  , emptyChecked
  , noFocus
  , noDrag
  , emptySearch
  , emptyLoading
  , noEdit
  , noHover
  )

import Hydrogen.Element.Compound.TreeView.Node
  ( Tree
  , TreeNode
  , nodeId
  , nodeLabel
  , nodeIcon
  , nodeChildren
  , nodeDisabled
  , nodeHasChildren
  , childNodes
  , nodeDepth
  , siblingNodes
  , rootNodes
  , getNode
  )

import Hydrogen.Element.Compound.TreeView.Navigation
  ( visibleNodes
  )

-- Integration with new modules
import Hydrogen.Element.Compound.TreeView.Layout as Layout
import Hydrogen.Element.Compound.TreeView.Content as Content
import Hydrogen.Element.Compound.TreeView.Connection as Connection
import Hydrogen.Element.Compound.TreeView.Accessibility as A11y

import Hydrogen.Schema.Graph.Layout as LayoutSchema
import Hydrogen.Schema.Graph.Connection as ConnectionSchema
import Hydrogen.Schema.Graph.Viewport as ViewportSchema

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | TreeView rendering properties
-- |
-- | Extended to support Layout, Connection, Content, and Accessibility integration.
type TreeViewProps msg =
  { -- Color atoms
    backgroundColor :: Maybe Color.RGB
  , selectedColor :: Maybe Color.RGB
  , focusRingColor :: Maybe Color.RGB
  , iconColor :: Maybe Color.RGB
  , textColor :: Maybe Color.RGB
  , hoverBackground :: Maybe Color.RGB
  , expandIconColor :: Maybe Color.RGB
  
  -- Dimension atoms
  , indentSize :: Maybe Device.Pixel
  , nodeHeight :: Maybe Device.Pixel
  , iconSize :: Maybe Device.Pixel
  , expandIconSize :: Maybe Device.Pixel
  
  -- Geometry atoms
  , borderRadius :: Maybe Geometry.Corners
  
  -- Behavior configuration
  , checkable :: Boolean
  
  -- Behavior callbacks (wrapped in TreeViewMsg)
  , onNodeClick :: Maybe (NodeId -> msg)
  , onNodeExpand :: Maybe (NodeId -> msg)
  , onNodeSelect :: Maybe (NodeId -> msg)
  , onNodeCheck :: Maybe (NodeId -> msg)
  , onNodeDoubleClick :: Maybe (NodeId -> msg)
  , onNodeDragStart :: Maybe (NodeId -> msg)
  , onNodeDragEnd :: Maybe msg
  , onNodeDragOver :: Maybe (NodeId -> msg)
  , onNodeDrop :: Maybe (NodeId -> msg)
  
  -- Keyboard navigation callbacks
  , onKeyDown :: Maybe (String -> msg)
  
  -- Hover callbacks
  , onNodeHover :: Maybe (NodeId -> msg)
  , onNodeHoverEnd :: Maybe msg
  
  -- Layout configuration
  , layoutConfig :: Maybe LayoutSchema.LayoutConfig
  
  -- Connection configuration
  , connectionProps :: Maybe Connection.ConnectionProps
  , connectionStyle :: Maybe ConnectionSchema.ConnectionStyle
  , showConnections :: Boolean
  
  -- Content configuration
  , contentProps :: Maybe (Content.ContentProps msg)
  
  -- Accessibility configuration
  , a11yConfig :: Maybe A11y.A11yConfig
  , ariaLabel :: String
  }

-- | Property modifier
type TreeViewProp msg = TreeViewProps msg -> TreeViewProps msg

-- | Default properties
defaultProps :: forall msg. TreeViewProps msg
defaultProps =
  { backgroundColor: Nothing
  , selectedColor: Nothing
  , focusRingColor: Nothing
  , iconColor: Nothing
  , textColor: Nothing
  , hoverBackground: Nothing
  , expandIconColor: Nothing
  , indentSize: Nothing
  , nodeHeight: Nothing
  , iconSize: Nothing
  , expandIconSize: Nothing
  , borderRadius: Nothing
  , checkable: false
  , onNodeClick: Nothing
  , onNodeExpand: Nothing
  , onNodeSelect: Nothing
  , onNodeCheck: Nothing
  , onNodeDoubleClick: Nothing
  , onNodeDragStart: Nothing
  , onNodeDragEnd: Nothing
  , onNodeDragOver: Nothing
  , onNodeDrop: Nothing
  , onKeyDown: Nothing
  , onNodeHover: Nothing
  , onNodeHoverEnd: Nothing
  , layoutConfig: Nothing
  , connectionProps: Nothing
  , connectionStyle: Nothing
  , showConnections: false
  , contentProps: Nothing
  , a11yConfig: Nothing
  , ariaLabel: "Tree view"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop builders: color
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set tree background color
backgroundColor :: forall msg. Color.RGB -> TreeViewProp msg
backgroundColor c props = props { backgroundColor = Just c }

-- | Set selected node background color
selectedColor :: forall msg. Color.RGB -> TreeViewProp msg
selectedColor c props = props { selectedColor = Just c }

-- | Set focus ring color
focusRingColor :: forall msg. Color.RGB -> TreeViewProp msg
focusRingColor c props = props { focusRingColor = Just c }

-- | Set icon color
iconColor :: forall msg. Color.RGB -> TreeViewProp msg
iconColor c props = props { iconColor = Just c }

-- | Set text color
textColor :: forall msg. Color.RGB -> TreeViewProp msg
textColor c props = props { textColor = Just c }

-- | Set hover background color
hoverBackground :: forall msg. Color.RGB -> TreeViewProp msg
hoverBackground c props = props { hoverBackground = Just c }

-- | Set expand icon color
expandIconColor :: forall msg. Color.RGB -> TreeViewProp msg
expandIconColor c props = props { expandIconColor = Just c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop builders: dimension
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set indent size per depth level
indentSize :: forall msg. Device.Pixel -> TreeViewProp msg
indentSize s props = props { indentSize = Just s }

-- | Set node row height
nodeHeight :: forall msg. Device.Pixel -> TreeViewProp msg
nodeHeight h props = props { nodeHeight = Just h }

-- | Set icon size
iconSize :: forall msg. Device.Pixel -> TreeViewProp msg
iconSize s props = props { iconSize = Just s }

-- | Set expand icon size
expandIconSize :: forall msg. Device.Pixel -> TreeViewProp msg
expandIconSize s props = props { expandIconSize = Just s }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: geometry
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set border radius for selected/hover states
borderRadius :: forall msg. Geometry.Corners -> TreeViewProp msg
borderRadius r props = props { borderRadius = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop builders: behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set node click handler
onNodeClick :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeClick f props = props { onNodeClick = Just f }

-- | Set node expand/collapse handler
onNodeExpand :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeExpand f props = props { onNodeExpand = Just f }

-- | Set node select handler
onNodeSelect :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeSelect f props = props { onNodeSelect = Just f }

-- | Set node checkbox toggle handler
onNodeCheck :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeCheck f props = props { onNodeCheck = Just f }

-- | Set node double-click handler (for inline edit)
onNodeDoubleClick :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDoubleClick f props = props { onNodeDoubleClick = Just f }

-- | Set node drag start handler
onNodeDragStart :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDragStart f props = props { onNodeDragStart = Just f }

-- | Set node drag end handler
onNodeDragEnd :: forall msg. msg -> TreeViewProp msg
onNodeDragEnd m props = props { onNodeDragEnd = Just m }

-- | Set node drag over handler
onNodeDragOver :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDragOver f props = props { onNodeDragOver = Just f }

-- | Set node drop handler
onNodeDrop :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeDrop f props = props { onNodeDrop = Just f }

-- | Set keyboard event handler
-- | Receives the key name (e.g., "ArrowUp", "ArrowDown", "Enter", "Escape")
onKeyDown :: forall msg. (String -> msg) -> TreeViewProp msg
onKeyDown f props = props { onKeyDown = Just f }

-- | Set node hover handler
onNodeHover :: forall msg. (NodeId -> msg) -> TreeViewProp msg
onNodeHover f props = props { onNodeHover = Just f }

-- | Set node hover end handler
onNodeHoverEnd :: forall msg. msg -> TreeViewProp msg
onNodeHoverEnd m props = props { onNodeHoverEnd = Just m }

-- | Enable/disable checkboxes on nodes
-- | Enable/disable checkboxes on nodes (in render props)
-- |
-- | Note: Named withPropsCheckable to avoid conflict with State.withCheckable.
withPropsCheckable :: forall msg. Boolean -> TreeViewProp msg
withPropsCheckable b props = props { checkable = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop builders: layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set layout configuration
withLayoutConfig :: forall msg. LayoutSchema.LayoutConfig -> TreeViewProp msg
withLayoutConfig config props = props { layoutConfig = Just config }

-- | Set connection properties
withConnectionProps :: forall msg. Connection.ConnectionProps -> TreeViewProp msg
withConnectionProps cprops props = props { connectionProps = Just cprops }

-- | Set connection style directly (convenience for accessing Schema atoms)
-- | Set connection style directly (in render props)
-- |
-- | Note: Named withPropsConnectionStyle to avoid conflict with Connection.withConnectionStyle.
withPropsConnectionStyle :: forall msg. ConnectionSchema.ConnectionStyle -> TreeViewProp msg
withPropsConnectionStyle style props = props { connectionStyle = Just style }

-- | Set content properties
withContentProps :: forall msg. Content.ContentProps msg -> TreeViewProp msg
withContentProps cprops props = props { contentProps = Just cprops }

-- | Set accessibility configuration
withAccessibilityConfig :: forall msg. A11y.A11yConfig -> TreeViewProp msg
withAccessibilityConfig config props = props { a11yConfig = Just config }

-- | Enable/disable connection line rendering (in render props)
-- |
-- | Note: Named withPropsShowConnections to avoid conflict with Connection.withShowConnections.
withPropsShowConnections :: forall msg. Boolean -> TreeViewProp msg
withPropsShowConnections b props = props { showConnections = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // main renderer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render the complete tree view
-- |
-- | Takes the tree data, current state, and rendering props.
-- | Returns a pure Element that can be rendered to any target.
-- |
-- | This is the simple API that renders an indented list style.
-- | For advanced layouts (radial, treemap, etc.), use renderTreeViewAdvanced.
renderTreeView :: 
  forall msg.
  Array (TreeViewProp msg) ->
  Tree ->
  TreeViewState ->
  E.Element msg
renderTreeView propMods tree state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    visible = visibleNodes tree state.expanded
    
    -- Container ARIA attributes using Accessibility module
    containerAria = A11y.containerAriaAttrs
      { multiselectable: false
      , label: props.ariaLabel
      , activeDescendant: getFocusedNode state.focus
      }
    
    -- Container styles
    containerStyles = buildContainerStyles props
    
    -- Keyboard handler for navigation
    keyboardHandler = buildKeyboardHandler props
  in
    E.element "div"
      ([ E.class_ "tree-view"
       , E.attr "tabindex" "0"  -- Make focusable for keyboard events
       ] <> containerAria <> containerStyles <> keyboardHandler)
      (map (renderNodeRow props tree state) visible)

-- | Render the tree view with full layout computation
-- |
-- | Uses the Layout module to compute positions, Connection module for lines,
-- | and Content module for node content. This supports all layout algorithms.
renderTreeViewAdvanced :: 
  forall msg.
  Array (TreeViewProp msg) ->
  Tree ->
  TreeViewState ->
  E.Element msg
renderTreeViewAdvanced propMods tree state =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Get layout config or use default indented list
    layoutConfig = fromMaybe LayoutSchema.indentedListLayout props.layoutConfig
    
    -- Compute layout positions
    layoutResult = Layout.computeLayout layoutConfig tree state.expanded
    
    -- Get visible nodes
    visible = visibleNodes tree state.expanded
    
    -- Container ARIA attributes
    containerAria = A11y.containerAriaAttrs
      { multiselectable: false
      , label: props.ariaLabel
      , activeDescendant: getFocusedNode state.focus
      }
    
    -- Get content bounds for container sizing
    bounds = Layout.contentBounds layoutResult
    boundsW = ViewportSchema.boundsWidth bounds
    boundsH = ViewportSchema.boundsHeight bounds
    
    -- Container styles with computed bounds for proper sizing
    containerStyles = buildContainerStyles props
    sizeStyles = 
      [ E.style "min-width" (show boundsW <> "px")
      , E.style "min-height" (show boundsH <> "px")
      ]
    
    -- Resolve connection style (from connectionStyle or connectionProps)
    resolvedConnProps = case props.connectionStyle of
      Just style -> Connection.withConnectionStyle style Connection.defaultConnectionProps
      Nothing -> fromMaybe Connection.defaultConnectionProps props.connectionProps
    
    -- Render connection lines layer (if enabled)
    connectionLayer = if props.showConnections
      then [ Connection.renderConnections resolvedConnProps tree state.expanded layoutResult ]
      else []
    
    -- Render nodes layer
    nodeLayer = map (renderNodeWithLayout props tree state layoutResult) visible
    
    -- Keyboard handler for navigation
    keyboardHandler = buildKeyboardHandler props
  in
    E.element "div"
      ([ E.class_ "tree-view tree-view-advanced"
       , E.style "position" "relative"
       , E.attr "tabindex" "0"  -- Make focusable for keyboard events
       ] <> containerAria <> containerStyles <> sizeStyles <> keyboardHandler)
      (connectionLayer <> nodeLayer)

-- | Build container styles from props
-- |
-- | Includes accessibility configuration for direction, motion, and contrast.
buildContainerStyles :: forall msg. TreeViewProps msg -> Array (E.Attribute msg)
buildContainerStyles props =
  let
    bgStyle = case props.backgroundColor of
      Nothing -> []
      Just c -> [ E.style "background-color" (Color.toHex c) ]
    
    -- Apply a11yConfig settings when provided
    a11yStyles = case props.a11yConfig of
      Nothing -> []
      Just config ->
        let
          -- Text direction (LTR/RTL/Auto)
          directionStyle = case config.direction of
            A11y.LTR -> [ E.style "direction" "ltr" ]
            A11y.RTL -> [ E.style "direction" "rtl" ]
            A11y.Auto -> [ E.attr "dir" "auto" ]
          
          -- Reduced motion preference (CSS respects prefers-reduced-motion,
          -- but we can also disable transitions explicitly)
          motionStyle = if config.reducedMotion
            then [ E.attr "data-reduced-motion" "true"
                 , E.style "transition" "none"
                 ]
            else []
          
          -- High contrast mode indicator
          contrastAttr = if config.highContrast
            then [ E.attr "data-high-contrast" "true" ]
            else []
          
          -- Labelled-by for accessibility
          labelledByAttr = case config.labelledBy of
            Nothing -> []
            Just labelId -> [ E.attr "aria-labelledby" labelId ]
        in
          directionStyle <> motionStyle <> contrastAttr <> labelledByAttr
  in
    bgStyle <> a11yStyles

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // state-specific renders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render only the expanded nodes
-- |
-- | Useful for rendering a summary of expanded branches or for
-- | state visualization/debugging.
renderExpandedNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  ExpandedState ->
  E.Element msg
renderExpandedNodes props tree expandedState =
  let
    visible = visibleNodes tree expandedState
    -- Create minimal state just for expansion
    minimalState = 
      { expanded: expandedState
      , selected: initialSelectedState
      , checked: initialCheckedState
      , focus: initialFocusState
      , drag: initialDragState
      , search: initialSearchState
      , loading: initialLoadingState
      , edit: initialEditState
      , hover: initialHoverState
      , selectionMode: singleSelectMode
      , checkable: props.checkable
      , draggable: false
      , searchable: false
      , editable: false
      }
  in
    E.div_
      [ E.class_ "tree-view-expanded-nodes" ]
      (map (renderNodeRow props tree minimalState) visible)

-- | Render only the selected nodes as a flat list
-- |
-- | Useful for showing selection summary or for clipboard operations.
renderSelectedNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  SelectedState ->
  E.Element msg
renderSelectedNodes props tree selectedState =
  let
    selectedIds = selectedNodes selectedState
    selectedNodeList = Array.mapMaybe (\nid -> getNode nid tree) selectedIds
  in
    E.div_
      [ E.class_ "tree-view-selected-nodes"
      , E.attr "aria-label" "Selected items"
      ]
      (map (renderSelectedNodeSummary props) selectedNodeList)

-- | Render a summary of a selected node
renderSelectedNodeSummary :: forall msg. TreeViewProps msg -> TreeNode -> E.Element msg
renderSelectedNodeSummary props node =
  E.div_
    [ E.class_ "tree-selected-summary"
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "padding" "4px 8px"
    ]
    [ renderNodeIcon props node false
    , renderNodeLabel props node
    ]

-- | Render only the checked nodes as a flat list
-- |
-- | Useful for showing checked items summary or for batch operations.
renderCheckedNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  CheckedState ->
  E.Element msg
renderCheckedNodes props tree checkedState =
  let
    checkedIds = checkedNodes checkedState
    checkedNodeList = Array.mapMaybe (\nid -> getNode nid tree) checkedIds
  in
    E.div_
      [ E.class_ "tree-view-checked-nodes"
      , E.attr "aria-label" "Checked items"
      ]
      (map (renderCheckedNodeSummary props) checkedNodeList)

-- | Render a summary of a checked node
-- |
-- | Uses renderCheckboxReadOnly since this is a display-only summary.
renderCheckedNodeSummary :: forall msg. TreeViewProps msg -> TreeNode -> E.Element msg
renderCheckedNodeSummary props node =
  E.div_
    [ E.class_ "tree-checked-summary"
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "padding" "4px 8px"
    ]
    [ renderCheckboxReadOnly Checked
    , renderNodeIcon props node false
    , renderNodeLabel props node
    ]

-- | Render the currently focused node (if any)
-- |
-- | Useful for focus indicators or accessibility announcements.
renderFocusedNode ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  FocusState ->
  E.Element msg
renderFocusedNode props tree focusState =
  case getFocusedNode focusState of
    Nothing -> E.empty
    Just focusedId ->
      case getNode focusedId tree of
        Nothing -> E.empty
        Just node ->
          E.div_
            [ E.class_ "tree-view-focused-node"
            , E.attr "aria-live" "polite"
            ]
            [ renderNodeIcon props node false
            , renderNodeLabel props node
            ]

-- Minimal state constructors for state-specific renders
-- These use the empty/initial state constructors from State module
initialSelectedState :: SelectedState
initialSelectedState = emptySelected

initialCheckedState :: CheckedState  
initialCheckedState = emptyChecked

initialFocusState :: FocusState
initialFocusState = noFocus

initialDragState :: DragState
initialDragState = noDrag

initialSearchState :: SearchState
initialSearchState = emptySearch

initialLoadingState :: LoadingState
initialLoadingState = emptyLoading

initialEditState :: EditState
initialEditState = noEdit

initialHoverState :: HoverState
initialHoverState = noHover

singleSelectMode :: SelectionMode
singleSelectMode = SingleSelect

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // subtree renderers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a subtree starting from a specific node
-- |
-- | Useful for lazy loading sections or rendering partial trees.
-- | Recursively renders children if the node is expanded.
renderSubtree ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  NodeId ->
  E.Element msg
renderSubtree props tree state rootId =
  case getNode rootId tree of
    Nothing -> E.empty
    Just rootNode ->
      let
        -- Get all children IDs
        children = nodeChildren rootNode
        -- Resolve to actual nodes for rendering count indicator
        childNodesList = Array.mapMaybe (\cid -> getNode cid tree) children
        childCount = Array.length childNodesList
        isExp = isExpanded rootId state.expanded
        
        -- Build the subtree container with metadata
        subtreeAttrs = 
          [ E.class_ "tree-subtree"
          , E.attr "data-root-id" (show rootId)
          , E.attr "data-child-count" (show childCount)
          ]
      in
        E.div_
          subtreeAttrs
          ([ renderNodeRow props tree state rootNode ] <>
           if isExp
             then map (renderSubtree props tree state) children
             else [])

-- | Render only root-level nodes (not expanded children)
-- |
-- | Useful for initial render before lazy loading.
renderRootNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  E.Element msg
renderRootNodes props tree state =
  let
    roots = rootNodes tree
  in
    E.div_
      [ E.class_ "tree-root-nodes" ]
      (map (renderNodeRow props tree state) roots)

-- | Render child nodes of a specific parent
-- |
-- | Used by lazy loading to render newly loaded children.
renderChildNodes ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  NodeId ->
  E.Element msg
renderChildNodes props tree state parentId =
  let
    children = childNodes parentId tree
  in
    E.div_
      [ E.class_ "tree-child-nodes"
      , E.attr "data-parent-id" (show parentId)
      ]
      (map (renderNodeRow props tree state) children)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // node renderer
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render a single node row (indented list style)
renderNodeRow ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  TreeNode ->
  E.Element msg
renderNodeRow props tree state node =
  let
    nid = nodeId node
    depth = nodeDepth nid tree
    
    -- State queries
    expanded = isExpanded nid state.expanded
    selected = isSelected nid state.selected
    focused = getFocusedNode state.focus == Just nid
    hovered = isHoveringNode nid state.hover
    checkState = getCheckState nid state.checked
    disabled = nodeDisabled node
    hasChildren = nodeHasChildren node
    
    -- Drop state queries
    isDropTarget = getDragTarget state.drag == Just nid
    dropPosition = getDragPosition state.drag
    
    -- Get siblings for ARIA setsize/posinset
    siblings = siblingNodes nid tree
    siblingCount = Array.length siblings
    position = findPosition nid siblings
    
    -- ARIA attributes using Accessibility module
    ariaAttrs = A11y.nodeAriaAttrs
      { expanded: if hasChildren then Just expanded else Nothing
      , selected: selected
      , level: unwrapDepth depth + 1
      , setSize: siblingCount
      , posInSet: position
      , hasChildren: hasChildren
      , disabled: disabled
      }
    
    -- Styles (now includes hover state)
    -- Add drop-inside styling when this node is a DropInside target
    isDropInside = isDropTarget && dropPosition == Just DropInside
    nodeStyles = buildNodeStyles props depth selected focused hovered <>
      if isDropInside
        then [ E.style "outline" "2px dashed #3b82f6", E.style "outline-offset" "-2px" ]
        else []
    
    -- All event handlers (click, double-click, drag, hover)
    allHandlers = buildAllNodeHandlers props nid
    
    -- Content rendering using Content module or fallback
    content = case props.contentProps of
      Just contentConfig ->
        Content.renderNodeContent contentConfig node expanded selected focused checkState false
      Nothing ->
        renderNodeContentFallback props node nid expanded checkState hasChildren
    
    -- Build the node element
    nodeElement = E.element "div"
      ([ E.class_ "tree-node"
       , E.attr "data-node-id" (show nid)
       , E.tabIndex (if focused then 0 else (negate 1))
       ] <> ariaAttrs <> nodeStyles <> allHandlers)
      [ content ]
    
    -- Render drop indicator if this node is the drop target
    dropIndicatorBefore = if isDropTarget && dropPosition == Just DropBefore
      then [ renderDropIndicator props depth DropBefore ]
      else []
    
    dropIndicatorAfter = if isDropTarget && dropPosition == Just DropAfter
      then [ renderDropIndicator props depth DropAfter ]
      else []
  in
    -- Wrap in a container to hold indicator + node
    E.div_
      [ E.class_ "tree-node-row" ]
      (dropIndicatorBefore <> [ nodeElement ] <> dropIndicatorAfter)

-- | Find position of node in siblings array (1-indexed)
findPosition :: NodeId -> Array TreeNode -> Int
findPosition nid siblings =
  case Array.findIndex (\n -> nodeId n == nid) siblings of
    Just idx -> idx + 1
    Nothing -> 1

-- | Render a node with layout positioning
renderNodeWithLayout ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  Layout.LayoutResult ->
  TreeNode ->
  E.Element msg
renderNodeWithLayout props tree state layoutResult node =
  let
    nid = nodeId node
    
    -- Get position from layout
    positionMaybe = Layout.nodePosition nid layoutResult
  in
    case positionMaybe of
      Nothing -> 
        -- Fallback to regular rendering if no position
        renderNodeRow props tree state node
      Just position ->
        renderNodeAtPosition props tree state node position

-- | Render a node at a specific position
renderNodeAtPosition ::
  forall msg.
  TreeViewProps msg ->
  Tree ->
  TreeViewState ->
  TreeNode ->
  LayoutSchema.NodePosition ->
  E.Element msg
renderNodeAtPosition props tree state node position =
  let
    nid = nodeId node
    depth = nodeDepth nid tree
    
    -- State queries
    expanded = isExpanded nid state.expanded
    selected = isSelected nid state.selected
    focused = getFocusedNode state.focus == Just nid
    hovered = isHoveringNode nid state.hover
    checkState = getCheckState nid state.checked
    disabled = nodeDisabled node
    hasChildren = nodeHasChildren node
    
    -- Get siblings for ARIA
    siblings = siblingNodes nid tree
    siblingCount = Array.length siblings
    posInSet = findPosition nid siblings
    
    -- ARIA attributes
    ariaAttrs = A11y.nodeAriaAttrs
      { expanded: if hasChildren then Just expanded else Nothing
      , selected: selected
      , level: unwrapDepth depth + 1
      , setSize: siblingCount
      , posInSet: posInSet
      , hasChildren: hasChildren
      , disabled: disabled
      }
    
    -- Position styles from layout
    x = LayoutSchema.positionX position
    y = LayoutSchema.positionY position
    w = LayoutSchema.positionWidth position
    h = LayoutSchema.positionHeight position
    
    positionStyles = 
      [ E.style "position" "absolute"
      , E.style "left" (show x <> "px")
      , E.style "top" (show y <> "px")
      , E.style "width" (show w <> "px")
      , E.style "height" (show h <> "px")
      ]
    
    -- Visual styles (includes hover background)
    visualStyles = buildNodeVisualStyles props selected focused hovered
    
    -- All event handlers (click, double-click, drag, hover)
    allHandlers = buildAllNodeHandlers props nid
    
    -- Content rendering
    content = case props.contentProps of
      Just contentConfig ->
        Content.renderNodeContent contentConfig node expanded selected focused checkState false
      Nothing ->
        renderNodeContentFallback props node nid expanded checkState hasChildren
  in
    E.element "div"
      ([ E.class_ "tree-node tree-node-positioned"
       , E.attr "data-node-id" (show nid)
       , E.tabIndex (if focused then 0 else (negate 1))
       ] <> ariaAttrs <> positionStyles <> visualStyles <> allHandlers)
      [ content ]

-- | Render the actual node (legacy API, kept for backwards compatibility)
-- |
-- | This is the original render function that takes explicit parameters.
-- | The `checkable` parameter determines if a checkbox should be rendered.
-- |
-- | Note: This legacy API doesn't support hover state. For hover support,
-- | use renderNodeRow or renderNodeAtPosition with TreeViewState.
renderNode ::
  forall msg.
  TreeViewProps msg ->
  TreeNode ->
  Depth ->
  Boolean ->     -- expanded
  Boolean ->     -- selected
  Boolean ->     -- focused
  CheckState ->
  Boolean ->     -- checkable
  E.Element msg
renderNode props node depth expanded selected focused checkState checkable =
  let
    nid = nodeId node
    hasChildren = nodeHasChildren node
    -- Render checkbox if checkable is true
    checkboxElement = if checkable
      then [ renderCheckbox props nid checkState ]
      else []
    -- Legacy API: no hover state available, pass false
    hovered = false
  in
    E.div_
      (buildNodeStyles props depth selected focused hovered)
      (checkboxElement <> [ renderNodeContentWithCheckState props node nid expanded checkState hasChildren ])

-- | Build node row styles (for indented list)
buildNodeStyles :: 
  forall msg.
  TreeViewProps msg -> 
  Depth -> 
  Boolean ->  -- selected
  Boolean ->  -- focused
  Boolean ->  -- hovered
  Array (E.Attribute msg)
buildNodeStyles props depth selected focused hovered =
  let
    -- Indentation based on depth
    indentPx = maybe 20.0 unwrapPixel props.indentSize
    paddingLeft = show (Int.toNumber (unwrapDepth depth) * indentPx) <> "px"
    
    -- Height
    heightStyle = case props.nodeHeight of
      Nothing -> []
      Just h -> [ E.style "height" (show h) ]
  in
    [ E.style "padding-left" paddingLeft
    , E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "cursor" "pointer"
    ] <> heightStyle <> buildNodeVisualStyles props selected focused hovered

-- | Build visual styles for a node (background, focus ring, border radius)
-- |
-- | Priority order for background: selected > hovered > default
buildNodeVisualStyles ::
  forall msg.
  TreeViewProps msg ->
  Boolean ->  -- selected
  Boolean ->  -- focused
  Boolean ->  -- hovered
  Array (E.Attribute msg)
buildNodeVisualStyles props selected focused hovered =
  let
    -- Background: selected takes priority, then hovered
    bgStyle = if selected
      then case props.selectedColor of
        Nothing -> [ E.style "background-color" "rgba(59, 130, 246, 0.1)" ]
        Just c -> [ E.style "background-color" (Color.toHex c) ]
      else if hovered
        then case props.hoverBackground of
          Nothing -> [ E.style "background-color" "rgba(0, 0, 0, 0.04)" ]
          Just c -> [ E.style "background-color" (Color.toHex c) ]
        else []
    
    -- Focus ring
    focusStyle = if focused
      then case props.focusRingColor of
        Nothing -> [ E.style "outline" "2px solid #3b82f6", E.style "outline-offset" "-2px" ]
        Just c -> [ E.style "outline" ("2px solid " <> Color.toHex c), E.style "outline-offset" "-2px" ]
      else []
    
    -- Border radius
    radiusStyle = case props.borderRadius of
      Nothing -> [ E.style "border-radius" "4px" ]
      Just r -> [ E.style "border-radius" (Geometry.cornersToLegacyCss r) ]
  in
    bgStyle <> focusStyle <> radiusStyle

-- | Build click handlers
buildClickHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildClickHandlers props nid =
  case props.onNodeClick of
    Nothing -> []
    Just handler -> [ E.onClick (handler nid) ]

-- | Build double-click handlers
buildDoubleClickHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildDoubleClickHandlers props nid =
  case props.onNodeDoubleClick of
    Nothing -> []
    Just handler -> [ E.onDoubleClick (handler nid) ]

-- | Build drag handlers for a node
-- |
-- | Includes drag start, drag end, drag over, and drop handlers.
buildDragHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildDragHandlers props nid =
  let
    dragStartAttr = case props.onNodeDragStart of
      Nothing -> []
      Just handler -> [ E.attr "draggable" "true", E.onDragStart (handler nid) ]
    
    dragEndAttr = case props.onNodeDragEnd of
      Nothing -> []
      Just msg -> [ E.onDragEnd msg ]
    
    dragOverAttr = case props.onNodeDragOver of
      Nothing -> []
      Just handler -> [ E.onDragOver (handler nid) ]
    
    dropAttr = case props.onNodeDrop of
      Nothing -> []
      Just handler -> [ E.onDrop (handler nid) ]
  in
    dragStartAttr <> dragEndAttr <> dragOverAttr <> dropAttr

-- | Build keyboard handler for the tree container
-- |
-- | Attaches onKeyDown to handle arrow key navigation.
buildKeyboardHandler :: forall msg. TreeViewProps msg -> Array (E.Attribute msg)
buildKeyboardHandler props =
  case props.onKeyDown of
    Nothing -> []
    Just handler -> [ E.onKeyDown handler ]

-- | Build hover handlers for a node
-- |
-- | Includes mouse enter and mouse leave handlers.
buildHoverHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildHoverHandlers props nid =
  let
    enterAttr = case props.onNodeHover of
      Nothing -> []
      Just handler -> [ E.onMouseEnter (handler nid) ]
    
    leaveAttr = case props.onNodeHoverEnd of
      Nothing -> []
      Just msg -> [ E.onMouseLeave msg ]
  in
    enterAttr <> leaveAttr

-- | Build all event handlers for a node
-- |
-- | Combines click, double-click, drag, and hover handlers.
buildAllNodeHandlers :: forall msg. TreeViewProps msg -> NodeId -> Array (E.Attribute msg)
buildAllNodeHandlers props nid =
  buildClickHandlers props nid <>
  buildDoubleClickHandlers props nid <>
  buildDragHandlers props nid <>
  buildHoverHandlers props nid

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // node content parts
-- ═════════════════════════════════════════════════════════════════════════════

-- | Fallback node content rendering (when Content module not configured)
-- |
-- | Renders checkbox if checkable is enabled in props.
renderNodeContentFallback ::
  forall msg.
  TreeViewProps msg ->
  TreeNode ->
  NodeId ->      -- node identifier for handlers
  Boolean ->     -- expanded
  CheckState ->
  Boolean ->     -- hasChildren
  E.Element msg
renderNodeContentFallback props node nid expanded checkState hasChildren =
  let
    -- Render checkbox if checkable is enabled
    checkboxElement = if props.checkable
      then [ renderCheckbox props nid checkState ]
      else []
  in
    E.div_
      [ E.style "display" "flex"
      , E.style "align-items" "center"
      , E.style "gap" "4px"
      , E.style "flex" "1"
      ]
      ([ renderExpandIcon props nid hasChildren expanded ] <>
       checkboxElement <>
       [ renderNodeIcon props node expanded
       , renderNodeLabel props node
       ])

-- | Render node content with explicit checkState (used by renderNode legacy API)
-- |
-- | Unlike renderNodeContentFallback, this always shows the checkbox with the
-- | provided checkState, regardless of props.checkable setting.
renderNodeContentWithCheckState ::
  forall msg.
  TreeViewProps msg ->
  TreeNode ->
  NodeId ->      -- node identifier for handlers
  Boolean ->     -- expanded
  CheckState ->
  Boolean ->     -- hasChildren
  E.Element msg
renderNodeContentWithCheckState props node nid expanded checkState hasChildren =
  E.div_
    [ E.style "display" "flex"
    , E.style "align-items" "center"
    , E.style "gap" "4px"
    , E.style "flex" "1"
    ]
    [ renderExpandIcon props nid hasChildren expanded
    , renderCheckbox props nid checkState  -- Always render checkbox with the provided state
    , renderNodeIcon props node expanded
    , renderNodeLabel props node
    ]

-- | Render expand/collapse icon with click handler
-- |
-- | Uses expandIconColor and expandIconSize from props for customization.
-- | Wires the onNodeExpand handler when provided.
renderExpandIcon :: forall msg. TreeViewProps msg -> NodeId -> Boolean -> Boolean -> E.Element msg
renderExpandIcon props nid hasChildren expanded =
  if hasChildren
    then
      let
        -- Use expandIconColor if set, otherwise fall back to iconColor
        colorStyle = case props.expandIconColor of
          Just c -> [ E.style "color" (Color.toHex c) ]
          Nothing -> case props.iconColor of
            Just c -> [ E.style "color" (Color.toHex c) ]
            Nothing -> []
        
        -- Use expandIconSize if set
        sizeStyle = case props.expandIconSize of
          Just s -> 
            let px = show (unwrapPixel s) <> "px"
            in [ E.style "width" px, E.style "height" px, E.style "font-size" px ]
          Nothing -> 
            [ E.style "width" "16px", E.style "height" "16px" ]
        
        -- Wire onNodeExpand handler if provided
        expandHandler = case props.onNodeExpand of
          Just handler -> [ E.onClick (handler nid) ]
          Nothing -> []
      in
        E.span_
          ([ E.class_ "tree-expand-icon"
           , E.style "display" "inline-flex"
           , E.style "align-items" "center"
           , E.style "justify-content" "center"
           , E.style "transition" "transform 150ms"
           , E.style "transform" (if expanded then "rotate(90deg)" else "rotate(0deg)")
           , E.style "cursor" "pointer"
           , E.role "button"
           , E.attr "aria-expanded" (if expanded then "true" else "false")
           , E.attr "aria-label" (if expanded then "Collapse" else "Expand")
           ] <> colorStyle <> sizeStyle <> expandHandler)
          [ E.text "▶" ]
    else
      -- Spacer for leaf nodes to maintain alignment
      E.span_
        [ E.style "width" "16px"
        , E.style "display" "inline-block"
        ]
        []

-- | Render node icon (folder, file, etc.)
-- |
-- | Shows IconFolderOpen instead of IconFolder when node is expanded.
renderNodeIcon :: forall msg. TreeViewProps msg -> TreeNode -> Boolean -> E.Element msg
renderNodeIcon props node expanded =
  case nodeIcon node of
    Nothing -> E.empty
    Just icon ->
      let
        -- Use open folder icon if expanded and icon is folder
        displayIcon = case icon of
          IconFolder -> if expanded then IconFolderOpen else IconFolder
          other -> other
        
        colorStyle = case props.iconColor of
          Nothing -> []
          Just c -> [ E.style "color" (Color.toHex c) ]
        
        sizeStyle = case props.iconSize of
          Nothing -> [ E.style "font-size" "16px" ]
          Just s -> [ E.style "font-size" (show (unwrapPixel s) <> "px") ]
      in
        E.span_
          ([ E.class_ "tree-node-icon"
           , E.attr "aria-label" (iconToAria displayIcon)
           , E.style "flex-shrink" "0"
           ] <> colorStyle <> sizeStyle)
          [ E.text (iconToEmoji displayIcon) ]

-- | Render node label text
renderNodeLabel :: forall msg. TreeViewProps msg -> TreeNode -> E.Element msg
renderNodeLabel props node =
  let
    colorStyle = case props.textColor of
      Nothing -> []
      Just c -> [ E.style "color" (Color.toHex c) ]
  in
    E.span_
      ([ E.class_ "tree-node-label"
       , E.style "flex" "1"
       , E.style "overflow" "hidden"
       , E.style "text-overflow" "ellipsis"
       , E.style "white-space" "nowrap"
       ] <> colorStyle)
      [ E.text (nodeLabel node) ]

-- | Render a checkbox with the given state and click handler
-- |
-- | Wires the onNodeCheck handler when provided in props.
renderCheckbox :: forall msg. TreeViewProps msg -> NodeId -> CheckState -> E.Element msg
renderCheckbox props nid checkState =
  let
    icon = case checkState of
      Checked -> "☑"
      Unchecked -> "☐"
      Indeterminate -> "▣"
    
    ariaChecked = case checkState of
      Checked -> "true"
      Unchecked -> "false"
      Indeterminate -> "mixed"
    
    -- Wire onNodeCheck handler if provided
    checkHandler = case props.onNodeCheck of
      Just handler -> [ E.onClick (handler nid) ]
      Nothing -> []
  in
    E.span_
      ([ E.class_ "tree-checkbox"
       , E.role "checkbox"
       , E.attr "aria-checked" ariaChecked
       , E.attr "aria-label" "Toggle selection"
       , E.style "width" "16px"
       , E.style "height" "16px"
       , E.style "display" "inline-flex"
       , E.style "align-items" "center"
       , E.style "justify-content" "center"
       , E.style "cursor" "pointer"
       , E.style "flex-shrink" "0"
       ] <> checkHandler)
      [ E.text icon ]

-- | Render a read-only checkbox for display-only contexts (summaries, previews)
-- |
-- | Unlike renderCheckbox, this doesn't wire any click handlers.
renderCheckboxReadOnly :: forall msg. CheckState -> E.Element msg
renderCheckboxReadOnly checkState =
  let
    icon = case checkState of
      Checked -> "☑"
      Unchecked -> "☐"
      Indeterminate -> "▣"
    
    ariaChecked = case checkState of
      Checked -> "true"
      Unchecked -> "false"
      Indeterminate -> "mixed"
  in
    E.span_
      [ E.class_ "tree-checkbox tree-checkbox-readonly"
      , E.role "checkbox"
      , E.attr "aria-checked" ariaChecked
      , E.attr "aria-readonly" "true"
      , E.style "width" "16px"
      , E.style "height" "16px"
      , E.style "display" "inline-flex"
      , E.style "align-items" "center"
      , E.style "justify-content" "center"
      , E.style "flex-shrink" "0"
      ]
      [ E.text icon ]

-- | Render drop indicator based on drop position
-- |
-- | - DropBefore: Line above the node
-- | - DropAfter: Line below the node  
-- | - DropInside: Highlight border around node (for dropping as child)
renderDropIndicator :: 
  forall msg.
  TreeViewProps msg -> 
  Depth ->
  DropPosition ->
  E.Element msg
renderDropIndicator props depth position =
  let
    indentPx = maybe 20.0 unwrapPixel props.indentSize
    marginLeft = show (Int.toNumber (unwrapDepth depth) * indentPx) <> "px"
  in
    case position of
      DropBefore ->
        E.div_
          [ E.class_ "tree-drop-indicator tree-drop-before"
          , E.style "height" "2px"
          , E.style "background-color" "#3b82f6"
          , E.style "margin-left" marginLeft
          , E.style "margin-bottom" "-2px"
          , E.style "position" "relative"
          , E.style "z-index" "10"
          ]
          []
      DropAfter ->
        E.div_
          [ E.class_ "tree-drop-indicator tree-drop-after"
          , E.style "height" "2px"
          , E.style "background-color" "#3b82f6"
          , E.style "margin-left" marginLeft
          , E.style "margin-top" "-2px"
          , E.style "position" "relative"
          , E.style "z-index" "10"
          ]
          []
      DropInside ->
        -- For DropInside, we render a visual cue (empty element, styling is on node)
        E.div_
          [ E.class_ "tree-drop-indicator tree-drop-inside"
          , E.style "display" "none"  -- Placeholder; actual styling is via node border
          ]
          []

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // default message props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set expand handler using default TreeViewMsg
-- |
-- | Uses ToggleExpand from TreeViewMsg for standard tree behavior.
withDefaultExpandHandler :: TreeViewProp TreeViewMsg
withDefaultExpandHandler props = props { onNodeExpand = Just ToggleExpand }

-- | Set select handler using default TreeViewMsg
-- |
-- | Uses SelectNode from TreeViewMsg for standard selection behavior.
withDefaultSelectHandler :: TreeViewProp TreeViewMsg
withDefaultSelectHandler props = props { onNodeSelect = Just SelectNode }

-- | Set check handler using default TreeViewMsg
-- |
-- | Uses ToggleCheck from TreeViewMsg for standard checkbox behavior.
withDefaultCheckHandler :: TreeViewProp TreeViewMsg
withDefaultCheckHandler props = props { onNodeCheck = Just ToggleCheck }

-- | Set focus handler using default TreeViewMsg
-- |
-- | Uses SetFocus from TreeViewMsg for standard focus behavior.
withDefaultFocusHandler :: TreeViewProp TreeViewMsg
withDefaultFocusHandler props = props { onNodeClick = Just SetFocus }

-- | Set activate handler using default TreeViewMsg
-- |
-- | Uses ActivateNode from TreeViewMsg for double-click activation.
withDefaultActivateHandler :: TreeViewProp TreeViewMsg
withDefaultActivateHandler props = props { onNodeDoubleClick = Just ActivateNode }

-- | Set drag start handler using default TreeViewMsg
-- |
-- | Uses BeginDrag from TreeViewMsg for standard drag behavior.
withDefaultDragStartHandler :: TreeViewProp TreeViewMsg
withDefaultDragStartHandler props = props { onNodeDragStart = Just BeginDrag }

-- | Set drag end handler using default TreeViewMsg
-- |
-- | Uses EndDrag from TreeViewMsg for standard drag behavior.
withDefaultDragEndHandler :: TreeViewProp TreeViewMsg
withDefaultDragEndHandler props = props { onNodeDragEnd = Just EndDrag }

-- | Set drag over handler using default TreeViewMsg
-- |
-- | Uses DragOver from TreeViewMsg. Note: This default handler uses DropInside
-- | as the drop position. For precise position detection (before/after/inside)
-- | based on mouse coordinates, provide a custom handler that computes
-- | DropPosition from the drag event's offsetY.
withDefaultDragOverHandler :: TreeViewProp TreeViewMsg
withDefaultDragOverHandler props = props 
  { onNodeDragOver = Just (\nid -> DragOver nid DropInside) }

-- | Set drop handler using default TreeViewMsg
-- |
-- | Uses DropNode from TreeViewMsg. Note: This handler creates a DropNode
-- | message with a placeholder source NodeId. The actual source should be
-- | read from DragState by the update handler. Uses DropInside as position.
-- |
-- | For full drag/drop with proper source tracking, use a custom handler
-- | that accesses DragState to get the source node.
withDefaultDropHandler :: TreeViewProp TreeViewMsg
withDefaultDropHandler props = props
  { onNodeDrop = Just (\targetId -> DropNode targetId targetId DropInside) }

-- | Set hover handlers using default TreeViewMsg
-- |
-- | Uses SetHover and ClearHover from TreeViewMsg for standard hover behavior.
withDefaultHoverHandlers :: TreeViewProp TreeViewMsg
withDefaultHoverHandlers props = props 
  { onNodeHover = Just SetHover
  , onNodeHoverEnd = Just ClearHover
  }

-- | Set keyboard navigation handler using default TreeViewMsg
-- |
-- | Maps arrow keys to NavigateUp/Down/Left/Right messages.
-- | Maps Home/End to NavigateHome/NavigateEnd.
-- | Maps Escape to ClearHover (deselection context).
withDefaultKeyboardHandler :: TreeViewProp TreeViewMsg
withDefaultKeyboardHandler props = props { onKeyDown = Just keyToNavigationMsg }

-- | Map keyboard key names to navigation messages
-- |
-- | Key mapping:
-- | - ArrowUp → NavigateUp (move focus up)
-- | - ArrowDown → NavigateDown (move focus down)
-- | - ArrowLeft → NavigateLeft (collapse node)
-- | - ArrowRight → NavigateRight (expand node)
-- | - Home → NavigateHome (first visible node)
-- | - End → NavigateEnd (last visible node)
-- | - Other keys → NavigateDown (fallback, no-op for most cases)
keyToNavigationMsg :: String -> TreeViewMsg
keyToNavigationMsg key = case key of
  "ArrowUp" -> NavigateUp
  "ArrowDown" -> NavigateDown
  "ArrowLeft" -> NavigateLeft
  "ArrowRight" -> NavigateRight
  "Home" -> NavigateHome
  "End" -> NavigateEnd
  _ -> NavigateDown  -- Fallback (effectively no-op for navigation)

-- | Apply all standard handlers at once
-- |
-- | Convenience function that wires up expand, select, check, focus,
-- | activate, drag, hover, and keyboard handlers.
withAllDefaultHandlers :: TreeViewProp TreeViewMsg
withAllDefaultHandlers props = 
  props
    # withDefaultExpandHandler
    # withDefaultSelectHandler
    # withDefaultCheckHandler
    # withDefaultFocusHandler
    # withDefaultActivateHandler
    # withDefaultDragStartHandler
    # withDefaultDragEndHandler
    # withDefaultHoverHandlers
    # withDefaultKeyboardHandler

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Check if a node is disabled
-- |
-- | Returns true if the node has the disabled flag set.
-- | Uses `not` and `$` to properly negate the disabled check.
isNodeDisabled :: TreeNode -> Boolean
isNodeDisabled node = not $ (nodeDisabled node == false)

-- | Compute indentation in pixels for a given depth
-- |
-- | Takes the indentSize from props (or default 20px) and multiplies
-- | by depth level. Returns the value as a Pixel type.
computeIndentPixels :: forall msg. TreeViewProps msg -> Depth -> Pixel
computeIndentPixels props depth =
  let
    baseIndent = maybe (Device.px 20.0) (\p -> p) props.indentSize
    depthMultiplier = Int.toNumber (unwrapDepth depth)
    indentValue = unwrapPixel baseIndent * depthMultiplier
  in
    Device.px indentValue
