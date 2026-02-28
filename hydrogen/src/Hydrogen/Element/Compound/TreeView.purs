-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                           // hydrogen // element // tree-view
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | TreeView — Schema-native hierarchical tree component.
-- |
-- | ## Design Philosophy
-- |
-- | This component is a **compound** of Schema atoms, composed from:
-- | - Color: icon colors, selection highlight, focus ring
-- | - Dimension: indent spacing per depth level, node height
-- | - Geometry: selection corners/radius
-- | - Reactive: SelectionState, FocusManagement for selection/focus
-- | - Gestural: keyboard navigation, drag-drop
-- | - Graph: layout algorithms, connections, viewport
-- |
-- | ## Architecture
-- |
-- | TreeView is organized into submodules following the Carousel pattern:
-- |
-- | | Module        | Purpose                                    |
-- | |---------------|--------------------------------------------|
-- | | Types         | NodeId, SelectionMode, CheckState, etc.    |
-- | | State         | Runtime state (expanded, selected, etc.)   |
-- | | Node          | Tree data structure and queries            |
-- | | Navigation    | Keyboard navigation logic                  |
-- | | Selection     | Selection and checkbox logic               |
-- | | DragDrop      | Drag and drop reordering                   |
-- | | Layout        | Position computation for all layout types  |
-- | | Connection    | Visual connections between nodes           |
-- | | Content       | Slot-based content rendering               |
-- | | Viewport      | Virtualization for 100k+ nodes             |
-- | | Animation     | Motion and transitions                     |
-- | | Accessibility | ARIA, announcements, RTL support           |
-- | | Render        | Pure Element rendering                     |
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.TreeView as TreeView
-- |
-- | -- Build tree data
-- | let tree = TreeView.emptyTree
-- |              # TreeView.insertNode (TreeView.branchNode (TreeView.nodeId "root") "Root" [])
-- |              # TreeView.insertNode (TreeView.leafNode (TreeView.nodeId "child1") "Child 1")
-- |
-- | -- Initial state
-- | let state = TreeView.initialState
-- |
-- | -- Render
-- | TreeView.renderTreeView
-- |   [ TreeView.selectedColor brand.primaryLight
-- |   , TreeView.focusRingColor brand.primaryColor
-- |   , TreeView.indentSize (Device.pixel 24)
-- |   ]
-- |   tree
-- |   state
-- | ```

module Hydrogen.Element.Compound.TreeView
  ( -- * Re-exports: Types
    module Types
  
  -- * Re-exports: State
  , module State
  
  -- * Re-exports: Node
  , module Node
  
  -- * Re-exports: Navigation
  , module Navigation
  
  -- * Re-exports: Selection
  , module Selection
  
  -- * Re-exports: DragDrop
  , module DragDrop
  
  -- * Re-exports: Layout
  , module Layout
  
  -- * Re-exports: Connection
  , module Connection
  
  -- * Re-exports: Content
  , module Content
  
  -- * Re-exports: Viewport
  , module Viewport
  
  -- * Re-exports: Animation
  , module Animation
  
  -- * Re-exports: Accessibility
  , module Accessibility
  
  -- * Re-exports: Render
  , module Render
  
  -- * Re-exports: InlineEdit
  , module InlineEdit
  ) where

import Hydrogen.Element.Compound.TreeView.Types
  ( NodeId
  , nodeId
  , unwrapNodeId
  , rootNodeId
  , Depth
  , depth
  , unwrapDepth
  , rootDepth
  , incrementDepth
  , SelectionMode(SingleSelect, MultiSelect, NoSelect)
  , CheckState(Unchecked, Checked, Indeterminate)
  , toggleCheckState
  , isChecked
  , isIndeterminate
  , DropPosition(DropBefore, DropAfter, DropInside)
  , NodeIcon
      ( IconFolder
      , IconFolderOpen
      , IconFile
      , IconFileText
      , IconFileCode
      , IconFileImage
      , IconFileVideo
      , IconFileAudio
      , IconFileArchive
      , IconFileConfig
      , IconDatabase
      , IconGit
      , IconPackage
      , IconCustom
      )
  , iconToEmoji
  , iconToAria
  , TreePath
  , treePath
  , unwrapTreePath
  , emptyPath
  , appendToPath
  , parentPath
  , pathDepth
  , TreeViewMsg
      ( ToggleExpand
      , SelectNode
      , DeselectNode
      , ToggleCheck
      , SetFocus
      , ClearFocus
      , BeginDrag
      , EndDrag
      , DragOver
      , DropNode
      , LoadChildren
      , SearchChange
      , NavigateUp
      , NavigateDown
      , NavigateLeft
      , NavigateRight
      , NavigateHome
      , NavigateEnd
      , ActivateNode
      , BeginEdit
      , UpdateEditBuffer
      , ConfirmEdit
      , CancelEdit
      , SetHover
      , ClearHover
      )
  ) as Types

import Hydrogen.Element.Compound.TreeView.State
  ( ExpandedState
  , emptyExpanded
  , isExpanded
  , setExpanded
  , toggleExpanded
  , expandAll
  , collapseAll
  , expandedCount
  , SelectedState
  , emptySelected
  , isSelected
  , selectNode
  , deselectNode
  , toggleSelected
  , clearSelection
  , selectAll
  , selectedNodes
  , selectedCount
  , CheckedState
  , emptyChecked
  , getCheckState
  , setCheckState
  , clearChecked
  , checkedNodes
  , checkedCount
  , FocusState
  , noFocus
  , focusOn
  , getFocusedNode
  , hasFocus
  , clearFocusState
  , DragState
  , noDrag
  , beginDrag
  , updateDragOver
  , endDrag
  , isDragging
  , getDragSource
  , getDragTarget
  , getDragPosition
  , SearchState
  , emptySearch
  , setSearchQuery
  , getSearchQuery
  , hasSearchQuery
  , clearSearch
  , LoadingState
  , emptyLoading
  , isLoading
  , setLoading
  , clearLoading
  , loadingNodes
  , EditState
  , noEdit
  , beginEditState
  , updateEditBuffer
  , getEditingNode
  , getEditBuffer
  , isEditing
  , isEditingNode
  , clearEditState
  , HoverState
  , noHover
  , setHover
  , getHoveredNode
  , isHovering
  , isHoveringNode
  , clearHover
  , TreeViewState
  , initialState
  , withSelectionMode
  , withCheckable
  , withDraggable
  , withSearchable
  , withEditable
  ) as State

import Hydrogen.Element.Compound.TreeView.Node
  ( TreeNode
  , treeNode
  -- nodeId is re-exported from Types
  , nodeLabel
  , nodeIcon
  , nodeChildren
  , nodeParent
  , nodeDisabled
  , nodeHasChildren
  , node
  , leafNode
  , branchNode
  , withLabel
  , withIcon
  , withChildren
  , withParent
  , withDisabled
  , markHasChildren
  , Tree
  , emptyTree
  , insertNode
  , removeNode
  , getNode
  , hasNode
  , updateNode
  , treeNodes
  , treeSize
  , rootNodes
  , childNodes
  , parentNode
  , ancestorNodes
  , descendantNodes
  , siblingNodes
  , nodeDepth
  , nodePath
  , moveNode
  , isAncestorOf
  , isDescendantOf
  , flattenTree
  , filterTree
  ) as Node

import Hydrogen.Element.Compound.TreeView.Navigation
  ( visibleNodes
  , visibleNodeIds
  , navigateUp
  , navigateDown
  , navigateLeft
  , navigateRight
  , navigateHome
  , navigateEnd
  , NavResult(FocusNode, ExpandNode, CollapseNode, NoOp)
  , applyNavResult
  , findByPrefix
  , findNextByPrefix
  ) as Navigation

import Hydrogen.Element.Compound.TreeView.Selection
  ( handleSelect
  , handleDeselect
  , handleToggleSelect
  , handleSelectRange
  , handleSelectAll
  , handleSelectSubtree
  , handleClearSelection
  , handleCheck
  , handleUncheck
  , handleToggleCheck
  , handleCheckSubtree
  , handleClearChecked
  , propagateCheckToChildren
  , propagateCheckToParent
  , recomputeAllCheckStates
  , nodeHierarchicalStatus
  , checkStateToHierarchical
  , hierarchicalToCheckState
  , isNodeSelected
  , isNodeChecked
  , getSelectedNodes
  , getCheckedNodes
  , getPartiallyCheckedNodes
  , subtreeNodes
  ) as Selection

import Hydrogen.Element.Compound.TreeView.DragDrop
  ( canStartDrag
  , startNodeDrag
  , updateNodeDrag
  , endNodeDrag
  , cancelNodeDrag
  , canDropOn
  , computeDropPosition
  , isValidDrop
  , performDrop
  , moveNodeTo
  , DropIndicator
  , dropIndicator
  , indicatorTarget
  , indicatorPosition
  , indicatorDepth
  , noIndicator
  , hasIndicator
  , isDraggingNode
  , getDraggedNode
  , getDropTarget
  , getCurrentDropPosition
  ) as DragDrop

import Hydrogen.Element.Compound.TreeView.Layout
  ( LayoutResult
  , layoutResult
  , emptyLayout
  , nodePosition
  , nodePositions
  , contentBounds
  , layoutNodeCount
  , computeLayout
  , recomputeLayout
  , layoutIndentedList
  , layoutRadial
  , layoutTreemap
  , layoutTidy
  , layoutOrgChart
  , layoutMindMap
  , layoutDendrogram
  , layoutSunburst
  , layoutCirclePack
  , layoutIcicle
  , positionOf
  , childPositions
  , boundingBox
  , centerOf
  , translateLayout
  , scaleLayout
  , rotateLayout
  ) as Layout

import Hydrogen.Element.Compound.TreeView.Connection
  ( renderConnections
  , renderConnection
  , connectionPath
  , straightPath
  , curvedPath
  , orthogonalPath
  , stepPath
  , ConnectionPoint
  , connectionPoint
  , nodeConnectionPoints
  , anchorPoint
  , renderTerminal
  , arrowMarker
  , dotMarker
  , ConnectionProps
  , defaultConnectionProps
  , withConnectionStyle
  , withShowConnections
  ) as Connection

import Hydrogen.Element.Compound.TreeView.Content
  ( renderNodeContent
  , renderSlot
  , renderLeadingSlot
  , renderIconSlot
  , renderMainSlot
  , renderSubtitleSlot
  , renderTrailingSlot
  , renderActionsSlot
  , renderBelowSlot
  , ContentProps
  , defaultContentProps
  , withTemplate
  , withSlotRenderer
  , withExpandIcon
  , withCheckbox
  , SlotRenderer
  , emptySlot
  , textSlot
  , iconSlot
  , badgeSlot
  , buttonSlot
  , customSlot
  , applyTemplate
  , textOnlyTemplate
  , iconTextTemplate
  , cardTemplate
  , avatarTemplate
  ) as Content

import Hydrogen.Element.Compound.TreeView.Viewport
  ( TreeViewport
  , treeViewport
  , initialViewport
  , viewportZoom
  , viewportPan
  , viewportScreenSize
  , setViewportZoom
  , setViewportPan
  , panViewport
  , zoomViewport
  , zoomToPoint
  , fitToContent
  -- visibleNodes and visibleNodeIds are exported from Navigation
  , isNodeVisible
  , nodeVisibility
  , VirtualizedTree
  , virtualizedTree
  , virtualNodeCount
  , renderWindow
  , shouldRenderNode
  , RenderChunk
  , renderChunks
  , chunkNodes
  , nextChunk
  , isRenderComplete
  , LoadRequest
  , loadRequest
  , pendingLoads
  , acknowledgeLoad
  , nodeLOD
  , shouldShowLabel
  , shouldShowIcon
  , simplifiedNode
  , ViewportEvent(Pan, Zoom, ZoomToLevel, FitAll, CenterOn, ResetView)
  , handleViewportEvent
  ) as Viewport

import Hydrogen.Element.Compound.TreeView.Animation
  ( AnimationState
  , animationState
  , initialAnimation
  , isAnimating
  , animationProgress
  , ExpandAnimation
  , expandAnimation
  , collapseAnimation
  , toggleAnimation
  , expandProgress
  , isExpandComplete
  , PositionAnimation
  , positionAnimation
  , animatePosition
  , currentPosition
  , targetPosition
  , positionProgress
  , SelectionAnimation
  , selectAnimation
  , deselectAnimation
  , selectionOpacity
  , FocusAnimation
  , focusAnimation
  , focusProgress
  , focusRingScale
  , LayoutTransition
  , layoutTransition
  , transitionProgress
  , interpolatePosition
  , AnimationConfig
  , animationConfig
  , defaultAnimationConfig
  , fastAnimations
  , slowAnimations
  , noAnimations
  , withDuration
  , withEasing
  , Easing(Linear, EaseIn, EaseOut, EaseInOut, EaseSpring, EaseBounce, EaseElastic)
  , easeLinear
  , easeInOut
  , easeOut
  , easeSpring
  , applyEasing
  , updateAnimations
  , stepAnimation
  , cancelAnimation
  , completeAnimation
  ) as Animation

import Hydrogen.Element.Compound.TreeView.Accessibility
  ( AriaAttrs
  , ariaAttrs
  , containerAriaAttrs
  , nodeAriaAttrs
  , ariaExpanded
  , ariaSelected
  , ariaLevel
  , ariaSetSize
  , ariaPosInSet
  , ariaLabel
  , ariaDescribedBy
  , ariaActiveDescendant
  , Announcement
  , announcement
  , expandAnnouncement
  , collapseAnnouncement
  , selectAnnouncement
  , loadingAnnouncement
  , errorAnnouncement
  , LiveRegion
  , liveRegion
  , politeRegion
  , assertiveRegion
  , liveRegionAttrs
  , Direction(LTR, RTL, Auto)
  , isRTL
  , flipNavigationKey
  , directionAttr
  , focusableAttrs
  , rovingTabIndex
  , focusFirst
  , focusLast
  , A11yConfig
  , a11yConfig
  , defaultA11yConfig
  , withReducedMotion
  , withHighContrast
  , withDirection
  ) as Accessibility

import Hydrogen.Element.Compound.TreeView.Render
  ( renderTreeView
  , renderTreeViewAdvanced
  , renderNode
  , renderExpandedNodes
  , renderSelectedNodes
  , renderCheckedNodes
  , renderFocusedNode
  , renderSubtree
  , renderRootNodes
  , renderChildNodes
  , TreeViewProps
  , TreeViewProp
  , defaultProps
  , backgroundColor
  , selectedColor
  , focusRingColor
  , iconColor
  , textColor
  , hoverBackground
  , expandIconColor
  , indentSize
  , nodeHeight
  , iconSize
  , expandIconSize
  , borderRadius
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
  , withLayoutConfig
  , withConnectionProps
  , withPropsConnectionStyle
  , withContentProps
  , withAccessibilityConfig
  , withPropsShowConnections
  , renderExpandIcon
  , renderNodeIcon
  , renderNodeLabel
  , renderCheckbox
  , renderDropIndicator
  , renderNodeWithLayout
  , renderNodeAtPosition
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
  , isNodeDisabled
  , computeIndentPixels
  ) as Render

import Hydrogen.Element.Compound.TreeView.InlineEdit
  ( renderEditInput
  , renderEditableLabel
  , EditProps
  , defaultEditProps
  , withInputClass
  , withPlaceholder
  , withMaxLength
  , withAutoFocus
  , withSelectOnFocus
  , handleEditKeyDown
  , handleEditInput
  , handleEditBlur
  , beginEdit
  , updateEdit
  , confirmEdit
  , cancelEdit
  , EditValidation
  , validateNotEmpty
  , validateMaxLength
  , validatePattern
  , runValidation
  , isValidEdit
  , getEditResult
  , hasEditChanged
  ) as InlineEdit
