-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // geometry // position
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Position - spatial placement atoms for layout and anchoring.
-- |
-- | Defines where elements are positioned relative to a reference:
-- |
-- | ## Edge Position (1D)
-- | - Top, Bottom, Left, Right
-- | - Start, End (logical for LTR/RTL)
-- |
-- | ## Corner Position (2D)
-- | - TopLeft, TopRight, BottomLeft, BottomRight
-- |
-- | ## Axis
-- | - Horizontal, Vertical
-- |
-- | ## Alignment
-- | - Start, Center, End, Stretch, Baseline
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- |
-- | ## Dependents
-- | - Component.Carousel (thumbnail position)
-- | - Component.Tooltip (placement)
-- | - Component.Popover (anchor position)
-- | - Component.Drawer (edge position)
-- | - Component.Toast (notification position)
-- | - Layout.* (alignment utilities)

module Hydrogen.Schema.Geometry.Position
  ( -- * Edge Position
    Edge(Top, Bottom, Left, Right)
  , isVerticalEdge
  , isHorizontalEdge
  , oppositeEdge
  , edgeToAxis
  
  -- * Logical Edge (LTR/RTL aware)
  , LogicalEdge(Start, End, BlockStart, BlockEnd)
  , resolveLogicalEdge
  
  -- * Corner Position
  , Corner(TopLeft, TopRight, BottomLeft, BottomRight)
  , cornerEdges
  , oppositeCorner
  , horizontalEdge
  , verticalEdge
  
  -- * Axis
  , Axis(Horizontal, Vertical)
  , isHorizontal
  , isVertical
  , perpendicular
  
  -- * Alignment
  , Alignment(AlignStart, AlignCenter, AlignEnd, AlignStretch, AlignBaseline)
  , isStretch
  , alignmentToCss
  
  -- * Placement (Edge + Alignment)
  , Placement
  , placement
  , placementEdge
  , placementAlignment
  , placementTop
  , placementBottom
  , placementLeft
  , placementRight
  , placementTopStart
  , placementTopEnd
  , placementBottomStart
  , placementBottomEnd
  
  -- * Equality Checks
  , areSameEdge
  , areSameCorner
  , areSameAlignment
  , areSamePlacement
  , areSameAxis
  
  -- * Anchor Reference
  , AnchorReference(AnchorViewport, AnchorParent, AnchorElement)
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (&&)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // edge position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Edge of a rectangular region
-- |
-- | The four cardinal edges, used for:
-- | - Drawer slide-in direction
-- | - Tooltip/popover placement
-- | - Thumbnail bar position
-- | - Notification anchoring
data Edge
  = Top
  | Bottom
  | Left
  | Right

derive instance eqEdge :: Eq Edge
derive instance ordEdge :: Ord Edge

instance showEdge :: Show Edge where
  show Top = "(Edge Top)"
  show Bottom = "(Edge Bottom)"
  show Left = "(Edge Left)"
  show Right = "(Edge Right)"

-- | Is this a vertical edge (top or bottom)?
isVerticalEdge :: Edge -> Boolean
isVerticalEdge Top = true
isVerticalEdge Bottom = true
isVerticalEdge _ = false

-- | Is this a horizontal edge (left or right)?
isHorizontalEdge :: Edge -> Boolean
isHorizontalEdge Left = true
isHorizontalEdge Right = true
isHorizontalEdge _ = false

-- | Get the opposite edge
oppositeEdge :: Edge -> Edge
oppositeEdge Top = Bottom
oppositeEdge Bottom = Top
oppositeEdge Left = Right
oppositeEdge Right = Left

-- | Get the axis perpendicular to this edge
edgeToAxis :: Edge -> Axis
edgeToAxis Top = Horizontal
edgeToAxis Bottom = Horizontal
edgeToAxis Left = Vertical
edgeToAxis Right = Vertical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // logical edge
-- ═════════════════════════════════════════════════════════════════════════════

-- | Logical edge position (LTR/RTL aware)
-- |
-- | - Start/End: Inline direction (horizontal in LTR/RTL)
-- | - BlockStart/BlockEnd: Block direction (vertical)
data LogicalEdge
  = Start      -- ^ Inline start (left in LTR, right in RTL)
  | End        -- ^ Inline end (right in LTR, left in RTL)
  | BlockStart -- ^ Block start (top in horizontal writing)
  | BlockEnd   -- ^ Block end (bottom in horizontal writing)

derive instance eqLogicalEdge :: Eq LogicalEdge
derive instance ordLogicalEdge :: Ord LogicalEdge

instance showLogicalEdge :: Show LogicalEdge where
  show Start = "(LogicalEdge Start)"
  show End = "(LogicalEdge End)"
  show BlockStart = "(LogicalEdge BlockStart)"
  show BlockEnd = "(LogicalEdge BlockEnd)"

-- | Resolve logical edge to physical edge
-- |
-- | Takes a boolean for RTL mode.
resolveLogicalEdge :: Boolean -> LogicalEdge -> Edge
resolveLogicalEdge isRtl edge = case edge of
  Start -> if isRtl then Right else Left
  End -> if isRtl then Left else Right
  BlockStart -> Top
  BlockEnd -> Bottom

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // corner position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Corner of a rectangular region
-- |
-- | For positioning at specific corners:
-- | - Notification badges
-- | - Resize handles
-- | - Corner anchoring
data Corner
  = TopLeft
  | TopRight
  | BottomLeft
  | BottomRight

derive instance eqCorner :: Eq Corner
derive instance ordCorner :: Ord Corner

instance showCorner :: Show Corner where
  show TopLeft = "(Corner TopLeft)"
  show TopRight = "(Corner TopRight)"
  show BottomLeft = "(Corner BottomLeft)"
  show BottomRight = "(Corner BottomRight)"

-- | Get the two edges that form this corner
cornerEdges :: Corner -> { horizontal :: Edge, vertical :: Edge }
cornerEdges TopLeft = { horizontal: Left, vertical: Top }
cornerEdges TopRight = { horizontal: Right, vertical: Top }
cornerEdges BottomLeft = { horizontal: Left, vertical: Bottom }
cornerEdges BottomRight = { horizontal: Right, vertical: Bottom }

-- | Get the diagonally opposite corner
oppositeCorner :: Corner -> Corner
oppositeCorner TopLeft = BottomRight
oppositeCorner TopRight = BottomLeft
oppositeCorner BottomLeft = TopRight
oppositeCorner BottomRight = TopLeft

-- | Get horizontal edge component
horizontalEdge :: Corner -> Edge
horizontalEdge c = (cornerEdges c).horizontal

-- | Get vertical edge component
verticalEdge :: Corner -> Edge
verticalEdge c = (cornerEdges c).vertical

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                       // axis
-- ═════════════════════════════════════════════════════════════════════════════

-- | Axis for direction and layout
-- |
-- | Fundamental for:
-- | - Flex direction
-- | - Scroll direction
-- | - Swipe detection
-- | - Resize constraints
data Axis
  = Horizontal
  | Vertical

derive instance eqAxis :: Eq Axis
derive instance ordAxis :: Ord Axis

instance showAxis :: Show Axis where
  show Horizontal = "(Axis Horizontal)"
  show Vertical = "(Axis Vertical)"

-- | Is horizontal axis?
isHorizontal :: Axis -> Boolean
isHorizontal Horizontal = true
isHorizontal Vertical = false

-- | Is vertical axis?
isVertical :: Axis -> Boolean
isVertical Vertical = true
isVertical Horizontal = false

-- | Get the perpendicular axis
perpendicular :: Axis -> Axis
perpendicular Horizontal = Vertical
perpendicular Vertical = Horizontal

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // alignment
-- ═════════════════════════════════════════════════════════════════════════════

-- | Alignment along an axis
-- |
-- | Maps to CSS alignment values:
-- | - flex-start, center, flex-end, stretch, baseline
data Alignment
  = AlignStart
  | AlignCenter
  | AlignEnd
  | AlignStretch
  | AlignBaseline

derive instance eqAlignment :: Eq Alignment
derive instance ordAlignment :: Ord Alignment

instance showAlignment :: Show Alignment where
  show AlignStart = "(Alignment Start)"
  show AlignCenter = "(Alignment Center)"
  show AlignEnd = "(Alignment End)"
  show AlignStretch = "(Alignment Stretch)"
  show AlignBaseline = "(Alignment Baseline)"

-- | Is stretch alignment?
isStretch :: Alignment -> Boolean
isStretch AlignStretch = true
isStretch _ = false

-- | Convert to CSS value
alignmentToCss :: Alignment -> String
alignmentToCss AlignStart = "flex-start"
alignmentToCss AlignCenter = "center"
alignmentToCss AlignEnd = "flex-end"
alignmentToCss AlignStretch = "stretch"
alignmentToCss AlignBaseline = "baseline"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // placement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Placement combining edge and alignment
-- |
-- | For tooltips, popovers, and other floating elements:
-- | - "top" + "center" = centered above
-- | - "left" + "start" = left edge, aligned to top
type Placement =
  { edge :: Edge
  , alignment :: Alignment
  }

-- | Create a placement
placement :: Edge -> Alignment -> Placement
placement e a = { edge: e, alignment: a }

-- | Get placement edge
placementEdge :: Placement -> Edge
placementEdge p = p.edge

-- | Get placement alignment
placementAlignment :: Placement -> Alignment
placementAlignment p = p.alignment

-- | Top center placement
placementTop :: Placement
placementTop = placement Top AlignCenter

-- | Bottom center placement
placementBottom :: Placement
placementBottom = placement Bottom AlignCenter

-- | Left center placement
placementLeft :: Placement
placementLeft = placement Left AlignCenter

-- | Right center placement
placementRight :: Placement
placementRight = placement Right AlignCenter

-- | Top start placement
placementTopStart :: Placement
placementTopStart = placement Top AlignStart

-- | Top end placement
placementTopEnd :: Placement
placementTopEnd = placement Top AlignEnd

-- | Bottom start placement
placementBottomStart :: Placement
placementBottomStart = placement Bottom AlignStart

-- | Bottom end placement
placementBottomEnd :: Placement
placementBottomEnd = placement Bottom AlignEnd

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // equality checks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Are two edges the same?
areSameEdge :: Edge -> Edge -> Boolean
areSameEdge e1 e2 = e1 == e2

-- | Are two corners the same?
areSameCorner :: Corner -> Corner -> Boolean
areSameCorner c1 c2 = c1 == c2

-- | Are two alignments the same?
areSameAlignment :: Alignment -> Alignment -> Boolean
areSameAlignment a1 a2 = a1 == a2

-- | Are two placements the same?
areSamePlacement :: Placement -> Placement -> Boolean
areSamePlacement p1 p2 = p1.edge == p2.edge && p1.alignment == p2.alignment

-- | Are two axes the same?
areSameAxis :: Axis -> Axis -> Boolean
areSameAxis a1 a2 = a1 == a2

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // anchor reference
-- ═════════════════════════════════════════════════════════════════════════════

-- | What to anchor relative to
-- |
-- | For floating elements that need a reference point:
-- | - Viewport: position relative to screen
-- | - Parent: position relative to containing element
-- | - Element: position relative to a specific trigger element
data AnchorReference
  = AnchorViewport
  | AnchorParent
  | AnchorElement

derive instance eqAnchorReference :: Eq AnchorReference
derive instance ordAnchorReference :: Ord AnchorReference

instance showAnchorReference :: Show AnchorReference where
  show AnchorViewport = "(AnchorReference Viewport)"
  show AnchorParent = "(AnchorReference Parent)"
  show AnchorElement = "(AnchorReference Element)"
