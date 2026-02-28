-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                      // hydrogen // schema // graph // layout
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph Layout — Spatial arrangement algorithms for hierarchical data.
-- |
-- | ## Design Philosophy
-- |
-- | Layout is pure geometry. Given a tree structure and constraints, a layout
-- | algorithm produces (x, y) positions for every node. No rendering — just math.
-- |
-- | ## Layout Categories
-- |
-- | **Linear**: IndentedList, Outline
-- | **Radial**: Radial, Sunburst, CirclePack
-- | **Space-Filling**: Treemap, Icicle, Partition
-- | **Node-Link**: Tidy, Dendrogram, Cluster, OrgChart
-- | **Force-Directed**: Force, Hierarchical Force
-- | **Custom**: Via layout function
-- |
-- | ## Algorithm Sources
-- |
-- | Many algorithms based on academic work:
-- | - Reingold-Tilford (1981): Tidy tree drawing
-- | - Walker (1990): Improving on R-T
-- | - Buchheim (2002): Linear time implementation
-- | - Shneiderman (1992): Treemaps
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Dimension.Device (Pixel measurements)

module Hydrogen.Schema.Graph.Layout
  ( -- * Layout Algorithm
    LayoutAlgorithm(..)
  , isLinearLayout
  , isRadialLayout
  , isSpaceFillingLayout
  , isNodeLinkLayout
  , isForceLayout
  
  -- * Layout Direction
  , LayoutDirection(..)
  , isHorizontal
  , isVertical
  , flipDirection
  
  -- * Layout Orientation  
  , LayoutOrientation(..)
  , isTopDown
  , isBottomUp
  , isLeftRight
  , isRightLeft
  
  -- * Spacing Configuration
  , LayoutSpacing
  , layoutSpacing
  , defaultSpacing
  , compactSpacing
  , spaciousSpacing
  , siblingGap
  , levelGap
  , subtreeGap
  , withSiblingGap
  , withLevelGap
  , withSubtreeGap
  
  -- * Node Sizing
  , NodeSizing(..)
  , isFixedSize
  , isFitContent
  , isProportional
  
  -- * Layout Bounds
  , LayoutBounds
  , layoutBounds
  , unbounded
  , boundsWidth
  , boundsHeight
  , hasBounds
  
  -- * Layout Constraints
  , LayoutConstraints
  , layoutConstraints
  , defaultConstraints
  , withBounds
  , withMinNodeSize
  , withMaxNodeSize
  , withAspectRatio
  
  -- * Layout Result
  , NodePosition
  , nodePosition
  , positionX
  , positionY
  , positionWidth
  , positionHeight
  
  -- * Treemap Specific
  , TreemapAlgorithm(..)
  , TreemapParams
  , treemapParams
  , defaultTreemapParams
  
  -- * Radial Specific
  , RadialParams
  , radialParams
  , defaultRadialParams
  , startAngle
  , endAngle
  , innerRadius
  , outerRadius
  
  -- * Force Specific
  , ForceParams
  , forceParams
  , defaultForceParams
  , repulsion
  , attraction
  , gravity
  , damping
  
  -- * Layout Configuration (Compound)
  , LayoutConfig
  , layoutConfig
  , indentedListLayout
  , radialLayout
  , sunburstLayout
  , treemapLayout
  , dendrogramLayout
  , orgChartLayout
  , mindMapLayout
  , circlePackLayout
  , forceLayout
  , tidyLayout
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (==)
  , (<>)
  , (-)
  , (/)
  , (*)
  , (||)
  , negate
  )

import Data.Maybe (Maybe(Just, Nothing), isJust)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layout algorithm
-- ═════════════════════════════════════════════════════════════════════════════

-- | Layout algorithm determines spatial arrangement
data LayoutAlgorithm
  -- Linear layouts (1D with nesting)
  = IndentedList       -- ^ Traditional file explorer style
  | Outline            -- ^ Outline/bullet list style
  
  -- Radial layouts (polar coordinates)
  | Radial             -- ^ Nodes on concentric circles
  | Sunburst           -- ^ Arcs representing hierarchy
  | CirclePack         -- ^ Nested circles
  
  -- Space-filling layouts (area = value)
  | Treemap            -- ^ Nested rectangles
  | Icicle             -- ^ Vertical/horizontal partitions
  | Partition          -- ^ Generic partition layout
  
  -- Node-link layouts (nodes + edges)
  | Tidy               -- ^ Aesthetic tree (Reingold-Tilford)
  | Cluster            -- ^ Leaves at same level
  | Dendrogram         -- ^ With branch lengths
  | OrgChart           -- ^ Organizational hierarchy
  | MindMap            -- ^ Central node radiating
  
  -- Force-directed layouts
  | Force              -- ^ Physics simulation
  | HierarchicalForce  -- ^ Force with hierarchy constraints

derive instance eqLayoutAlgorithm :: Eq LayoutAlgorithm
derive instance ordLayoutAlgorithm :: Ord LayoutAlgorithm

instance showLayoutAlgorithm :: Show LayoutAlgorithm where
  show IndentedList = "indented-list"
  show Outline = "outline"
  show Radial = "radial"
  show Sunburst = "sunburst"
  show CirclePack = "circle-pack"
  show Treemap = "treemap"
  show Icicle = "icicle"
  show Partition = "partition"
  show Tidy = "tidy"
  show Cluster = "cluster"
  show Dendrogram = "dendrogram"
  show OrgChart = "org-chart"
  show MindMap = "mind-map"
  show Force = "force"
  show HierarchicalForce = "hierarchical-force"

-- | Is this a linear (list-based) layout?
isLinearLayout :: LayoutAlgorithm -> Boolean
isLinearLayout IndentedList = true
isLinearLayout Outline = true
isLinearLayout _ = false

-- | Is this a radial (polar) layout?
isRadialLayout :: LayoutAlgorithm -> Boolean
isRadialLayout Radial = true
isRadialLayout Sunburst = true
isRadialLayout CirclePack = true
isRadialLayout _ = false

-- | Is this a space-filling layout?
isSpaceFillingLayout :: LayoutAlgorithm -> Boolean
isSpaceFillingLayout Treemap = true
isSpaceFillingLayout Icicle = true
isSpaceFillingLayout Partition = true
isSpaceFillingLayout _ = false

-- | Is this a node-link layout?
isNodeLinkLayout :: LayoutAlgorithm -> Boolean
isNodeLinkLayout Tidy = true
isNodeLinkLayout Cluster = true
isNodeLinkLayout Dendrogram = true
isNodeLinkLayout OrgChart = true
isNodeLinkLayout MindMap = true
isNodeLinkLayout _ = false

-- | Is this a force-directed layout?
isForceLayout :: LayoutAlgorithm -> Boolean
isForceLayout Force = true
isForceLayout HierarchicalForce = true
isForceLayout _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // layout direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Primary axis direction for linear layouts
data LayoutDirection
  = Horizontal  -- ^ Nodes arranged left-to-right
  | Vertical    -- ^ Nodes arranged top-to-bottom

derive instance eqLayoutDirection :: Eq LayoutDirection
derive instance ordLayoutDirection :: Ord LayoutDirection

instance showLayoutDirection :: Show LayoutDirection where
  show Horizontal = "horizontal"
  show Vertical = "vertical"

isHorizontal :: LayoutDirection -> Boolean
isHorizontal Horizontal = true
isHorizontal _ = false

isVertical :: LayoutDirection -> Boolean
isVertical Vertical = true
isVertical _ = false

flipDirection :: LayoutDirection -> LayoutDirection
flipDirection Horizontal = Vertical
flipDirection Vertical = Horizontal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layout orientation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Flow direction for hierarchical layouts
data LayoutOrientation
  = TopDown    -- ^ Root at top, children below
  | BottomUp   -- ^ Root at bottom, children above
  | LeftRight  -- ^ Root at left, children to right
  | RightLeft  -- ^ Root at right, children to left

derive instance eqLayoutOrientation :: Eq LayoutOrientation
derive instance ordLayoutOrientation :: Ord LayoutOrientation

instance showLayoutOrientation :: Show LayoutOrientation where
  show TopDown = "top-down"
  show BottomUp = "bottom-up"
  show LeftRight = "left-right"
  show RightLeft = "right-left"

isTopDown :: LayoutOrientation -> Boolean
isTopDown TopDown = true
isTopDown _ = false

isBottomUp :: LayoutOrientation -> Boolean
isBottomUp BottomUp = true
isBottomUp _ = false

isLeftRight :: LayoutOrientation -> Boolean
isLeftRight LeftRight = true
isLeftRight _ = false

isRightLeft :: LayoutOrientation -> Boolean
isRightLeft RightLeft = true
isRightLeft _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // layout spacing
-- ═════════════════════════════════════════════════════════════════════════════

-- | Spacing between nodes at various levels
type LayoutSpacing =
  { siblingGap :: Number   -- ^ Gap between siblings (same parent)
  , levelGap :: Number     -- ^ Gap between hierarchy levels
  , subtreeGap :: Number   -- ^ Gap between subtrees
  , padding :: Number      -- ^ Padding around entire tree
  }

-- | Create layout spacing
layoutSpacing :: Number -> Number -> Number -> Number -> LayoutSpacing
layoutSpacing sib lvl sub pad =
  { siblingGap: sib
  , levelGap: lvl
  , subtreeGap: sub
  , padding: pad
  }

-- | Default spacing (balanced)
defaultSpacing :: LayoutSpacing
defaultSpacing = layoutSpacing 16.0 24.0 32.0 16.0

-- | Compact spacing (minimal gaps)
compactSpacing :: LayoutSpacing
compactSpacing = layoutSpacing 4.0 8.0 12.0 8.0

-- | Spacious spacing (generous gaps)
spaciousSpacing :: LayoutSpacing
spaciousSpacing = layoutSpacing 24.0 40.0 56.0 32.0

-- | Get sibling gap
siblingGap :: LayoutSpacing -> Number
siblingGap s = s.siblingGap

-- | Get level gap
levelGap :: LayoutSpacing -> Number
levelGap s = s.levelGap

-- | Get subtree gap
subtreeGap :: LayoutSpacing -> Number
subtreeGap s = s.subtreeGap

-- | Modify sibling gap
withSiblingGap :: Number -> LayoutSpacing -> LayoutSpacing
withSiblingGap gap s = s { siblingGap = gap }

-- | Modify level gap
withLevelGap :: Number -> LayoutSpacing -> LayoutSpacing
withLevelGap gap s = s { levelGap = gap }

-- | Modify subtree gap
withSubtreeGap :: Number -> LayoutSpacing -> LayoutSpacing
withSubtreeGap gap s = s { subtreeGap = gap }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // node sizing
-- ═════════════════════════════════════════════════════════════════════════════

-- | How node sizes are determined
data NodeSizing
  = FixedSize Number Number          -- ^ Fixed width × height
  | FitContent Number Number         -- ^ Fit to content with min size
  | Proportional                     -- ^ Size proportional to value
  | AspectRatio Number               -- ^ Maintain aspect ratio

derive instance eqNodeSizing :: Eq NodeSizing

instance showNodeSizing :: Show NodeSizing where
  show (FixedSize w h) = "fixed(" <> show w <> "×" <> show h <> ")"
  show (FitContent minW minH) = "fit-content(" <> show minW <> "," <> show minH <> ")"
  show Proportional = "proportional"
  show (AspectRatio r) = "aspect-ratio(" <> show r <> ")"

isFixedSize :: NodeSizing -> Boolean
isFixedSize (FixedSize _ _) = true
isFixedSize _ = false

isFitContent :: NodeSizing -> Boolean
isFitContent (FitContent _ _) = true
isFitContent _ = false

isProportional :: NodeSizing -> Boolean
isProportional Proportional = true
isProportional _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // layout bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Bounding box for layout
type LayoutBounds =
  { width :: Maybe Number
  , height :: Maybe Number
  }

-- | Create bounded layout
layoutBounds :: Number -> Number -> LayoutBounds
layoutBounds w h = { width: Just w, height: Just h }

-- | Unbounded layout (grow to fit)
unbounded :: LayoutBounds
unbounded = { width: Nothing, height: Nothing }

-- | Get width if bounded
boundsWidth :: LayoutBounds -> Maybe Number
boundsWidth b = b.width

-- | Get height if bounded
boundsHeight :: LayoutBounds -> Maybe Number
boundsHeight b = b.height

-- | Check if bounds are specified
hasBounds :: LayoutBounds -> Boolean
hasBounds b = isJust b.width || isJust b.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // layout constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraints for layout algorithm
type LayoutConstraints =
  { bounds :: LayoutBounds
  , minNodeWidth :: Number
  , minNodeHeight :: Number
  , maxNodeWidth :: Maybe Number
  , maxNodeHeight :: Maybe Number
  , aspectRatio :: Maybe Number
  }

-- | Create layout constraints
layoutConstraints :: LayoutBounds -> Number -> Number -> LayoutConstraints
layoutConstraints bounds minW minH =
  { bounds
  , minNodeWidth: minW
  , minNodeHeight: minH
  , maxNodeWidth: Nothing
  , maxNodeHeight: Nothing
  , aspectRatio: Nothing
  }

-- | Default constraints
defaultConstraints :: LayoutConstraints
defaultConstraints = layoutConstraints unbounded 50.0 24.0

-- | Set bounds
withBounds :: LayoutBounds -> LayoutConstraints -> LayoutConstraints
withBounds b c = c { bounds = b }

-- | Set minimum node size
withMinNodeSize :: Number -> Number -> LayoutConstraints -> LayoutConstraints
withMinNodeSize w h c = c { minNodeWidth = w, minNodeHeight = h }

-- | Set maximum node size
withMaxNodeSize :: Number -> Number -> LayoutConstraints -> LayoutConstraints
withMaxNodeSize w h c = c { maxNodeWidth = Just w, maxNodeHeight = Just h }

-- | Set aspect ratio constraint
withAspectRatio :: Number -> LayoutConstraints -> LayoutConstraints
withAspectRatio r c = c { aspectRatio = Just r }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // node position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Computed position and size for a node
type NodePosition =
  { x :: Number       -- ^ X coordinate (center or left, depends on layout)
  , y :: Number       -- ^ Y coordinate (center or top)
  , width :: Number   -- ^ Computed width
  , height :: Number  -- ^ Computed height
  , rotation :: Number  -- ^ Rotation in degrees (for radial)
  }

-- | Create node position
nodePosition :: Number -> Number -> Number -> Number -> NodePosition
nodePosition x y w h =
  { x, y, width: w, height: h, rotation: 0.0 }

-- | Get X coordinate
positionX :: NodePosition -> Number
positionX p = p.x

-- | Get Y coordinate
positionY :: NodePosition -> Number
positionY p = p.y

-- | Get computed width
positionWidth :: NodePosition -> Number
positionWidth p = p.width

-- | Get computed height
positionHeight :: NodePosition -> Number
positionHeight p = p.height

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // treemap specific
-- ═════════════════════════════════════════════════════════════════════════════

-- | Treemap tiling algorithm
data TreemapAlgorithm
  = Squarify       -- ^ Optimal squareness (Bruls et al.)
  | Binary         -- ^ Binary split
  | Slice          -- ^ Horizontal slices
  | Dice           -- ^ Vertical slices
  | SliceDice      -- ^ Alternating slice/dice per level

derive instance eqTreemapAlgorithm :: Eq TreemapAlgorithm

instance showTreemapAlgorithm :: Show TreemapAlgorithm where
  show Squarify = "squarify"
  show Binary = "binary"
  show Slice = "slice"
  show Dice = "dice"
  show SliceDice = "slice-dice"

-- | Treemap-specific parameters
type TreemapParams =
  { algorithm :: TreemapAlgorithm
  , paddingInner :: Number    -- ^ Padding between siblings
  , paddingOuter :: Number    -- ^ Padding around groups
  , paddingTop :: Number      -- ^ Extra top padding (for labels)
  , ratio :: Number           -- ^ Target aspect ratio for squarify
  }

-- | Create treemap params
treemapParams :: TreemapAlgorithm -> TreemapParams
treemapParams alg =
  { algorithm: alg
  , paddingInner: 2.0
  , paddingOuter: 4.0
  , paddingTop: 20.0
  , ratio: 1.618  -- Golden ratio
  }

-- | Default treemap params (squarify)
defaultTreemapParams :: TreemapParams
defaultTreemapParams = treemapParams Squarify

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // radial specific
-- ═════════════════════════════════════════════════════════════════════════════

-- | Radial layout parameters
type RadialParams =
  { startAngle :: Number      -- ^ Start angle in radians (0 = right)
  , endAngle :: Number        -- ^ End angle in radians
  , innerRadius :: Number     -- ^ Inner radius (root position)
  , outerRadius :: Number     -- ^ Outer radius (leaf positions)
  , clockwise :: Boolean      -- ^ Direction of layout
  }

-- | Create radial params
radialParams :: Number -> Number -> Number -> Number -> RadialParams
radialParams start end inner outer =
  { startAngle: start
  , endAngle: end
  , innerRadius: inner
  , outerRadius: outer
  , clockwise: true
  }

-- | Default radial params (full circle)
defaultRadialParams :: RadialParams
defaultRadialParams = radialParams 0.0 (2.0 * pi) 50.0 300.0
  where
    pi = 3.14159265359

-- | Get start angle
startAngle :: RadialParams -> Number
startAngle p = p.startAngle

-- | Get end angle
endAngle :: RadialParams -> Number
endAngle p = p.endAngle

-- | Get inner radius
innerRadius :: RadialParams -> Number
innerRadius p = p.innerRadius

-- | Get outer radius
outerRadius :: RadialParams -> Number
outerRadius p = p.outerRadius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // force specific
-- ═════════════════════════════════════════════════════════════════════════════

-- | Force-directed layout parameters
type ForceParams =
  { repulsion :: Number       -- ^ Node repulsion strength
  , attraction :: Number      -- ^ Edge attraction strength
  , gravity :: Number         -- ^ Center gravity
  , damping :: Number         -- ^ Velocity damping (0-1)
  , iterations :: Int         -- ^ Simulation iterations
  , linkDistance :: Number    -- ^ Ideal edge length
  }

-- | Create force params
forceParams :: Number -> Number -> Number -> ForceParams
forceParams rep att grav =
  { repulsion: rep
  , attraction: att
  , gravity: grav
  , damping: 0.9
  , iterations: 300
  , linkDistance: 100.0
  }

-- | Default force params
defaultForceParams :: ForceParams
defaultForceParams = forceParams 100.0 0.1 0.05

-- | Get repulsion strength
repulsion :: ForceParams -> Number
repulsion p = p.repulsion

-- | Get attraction strength
attraction :: ForceParams -> Number
attraction p = p.attraction

-- | Get gravity strength
gravity :: ForceParams -> Number
gravity p = p.gravity

-- | Get damping factor
damping :: ForceParams -> Number
damping p = p.damping

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // layout config compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete layout configuration
type LayoutConfig =
  { algorithm :: LayoutAlgorithm
  , orientation :: LayoutOrientation
  , spacing :: LayoutSpacing
  , sizing :: NodeSizing
  , constraints :: LayoutConstraints
  
  -- Algorithm-specific params (only one applies per algorithm)
  , treemapParams :: Maybe TreemapParams
  , radialParams :: Maybe RadialParams
  , forceParams :: Maybe ForceParams
  }

-- | Create base layout config
layoutConfig :: LayoutAlgorithm -> LayoutOrientation -> LayoutConfig
layoutConfig alg orient =
  { algorithm: alg
  , orientation: orient
  , spacing: defaultSpacing
  , sizing: FitContent 100.0 32.0
  , constraints: defaultConstraints
  , treemapParams: Nothing
  , radialParams: Nothing
  , forceParams: Nothing
  }

-- | Indented list layout (file explorer)
indentedListLayout :: LayoutConfig
indentedListLayout = layoutConfig IndentedList TopDown

-- | Radial tree layout
radialLayout :: LayoutConfig
radialLayout = (layoutConfig Radial TopDown)
  { radialParams = Just defaultRadialParams }

-- | Sunburst layout
sunburstLayout :: LayoutConfig
sunburstLayout = (layoutConfig Sunburst TopDown)
  { radialParams = Just defaultRadialParams
  , sizing = Proportional
  }

-- | Treemap layout
treemapLayout :: LayoutConfig
treemapLayout = (layoutConfig Treemap TopDown)
  { treemapParams = Just defaultTreemapParams
  , sizing = Proportional
  }

-- | Dendrogram layout (biological tree)
dendrogramLayout :: LayoutConfig
dendrogramLayout = (layoutConfig Dendrogram LeftRight)
  { spacing = spaciousSpacing }

-- | Org chart layout
orgChartLayout :: LayoutConfig
orgChartLayout = (layoutConfig OrgChart TopDown)
  { spacing = spaciousSpacing
  , sizing = FixedSize 180.0 80.0
  }

-- | Mind map layout
mindMapLayout :: LayoutConfig
mindMapLayout = layoutConfig MindMap LeftRight

-- | Circle pack layout
circlePackLayout :: LayoutConfig
circlePackLayout = (layoutConfig CirclePack TopDown)
  { sizing = Proportional }

-- | Force-directed layout
forceLayout :: LayoutConfig
forceLayout = (layoutConfig Force TopDown)
  { forceParams = Just defaultForceParams }

-- | Tidy tree layout (Reingold-Tilford)
tidyLayout :: LayoutConfig
tidyLayout = layoutConfig Tidy TopDown
