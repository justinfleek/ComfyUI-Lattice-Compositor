-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // graph // viewport
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph Viewport — Zoom, pan, and virtualization for large graph/tree displays.
-- |
-- | ## Design Philosophy
-- |
-- | Large graphs (100k+ nodes) cannot render all elements. The viewport defines
-- | what portion of the graph is visible, enabling:
-- |
-- | - **Culling**: Only render nodes within viewport bounds
-- | - **Level of Detail**: Simplify nodes at low zoom levels
-- | - **Progressive Loading**: Load nodes as they enter viewport
-- | - **Smooth Navigation**: Pan and zoom with animation
-- |
-- | ## Coordinate System
-- |
-- | Graph space is infinite. Viewport defines a window into that space:
-- |
-- | ```
-- | ┌──────────────────────────────┐  Graph Space (infinite)
-- | │                              │
-- | │   ┌──────────────┐           │
-- | │   │   Viewport   │           │
-- | │   │   (visible)  │           │
-- | │   └──────────────┘           │
-- | │                              │
-- | └──────────────────────────────┘
-- | ```
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Data.Maybe

module Hydrogen.Schema.Graph.Viewport
  ( -- * Viewport Zoom
    ViewportZoom
  , viewportZoom
  , defaultZoom
  , zoomIn
  , zoomOut
  , zoomTo
  , zoomToFit
  , zoomLevel
  , zoomPercentage
  , minZoom
  , maxZoom
  , isMinZoom
  , isMaxZoom
  
  -- * Viewport Position (Pan)
  , ViewportPosition
  , viewportPosition
  , origin
  , panX
  , panY
  , panBy
  , panTo
  , centerOn
  
  -- * Viewport Bounds
  , ViewportBounds
  , viewportBounds
  , boundsFromCenter
  , boundsLeft
  , boundsTop
  , boundsRight
  , boundsBottom
  , boundsWidth
  , boundsHeight
  , boundsCenter
  , containsPoint
  , boundsIntersect
  , expandBounds
  
  -- * Viewport State (Compound)
  , ViewportState
  , viewportState
  , initialViewport
  , viewportZoomLevel
  , viewportPan
  , viewportBoundsAt
  , setZoom
  , setPan
  , applyZoom
  , applyPan
  , fitContent
  
  -- * Level of Detail
  , LevelOfDetail(..)
  , lodForZoom
  , shouldRenderNode
  , shouldRenderLabel
  , shouldRenderConnection
  
  -- * Viewport Culling
  , CullResult(..)
  , cullNode
  , cullConnection
  
  -- * Virtualization Window
  , VirtualWindow
  , virtualWindow
  , windowNodes
  , windowConnections
  , windowOverscan
  , expandWindow
  , isInWindow
  
  -- * Progressive Loading
  , LoadingPriority(..)
  , loadingPriority
  , LoadingRegion
  , loadingRegion
  , priorityRegion
  , backgroundRegion
  , regionPriority
  , regionBounds
  
  -- * Viewport Animation
  , ViewportTransition
  , viewportTransition
  , instantTransition
  , smoothTransition
  , springTransition
  , transitionDuration
  , isAnimating
  
  -- * Viewport Constraints
  , ViewportConstraints
  , viewportConstraints
  , unconstrainedViewport
  , constrainZoom
  , constrainPan
  , withMinZoom
  , withMaxZoom
  , withPanBounds
  
  -- * Zoom Presets
  , zoomFit
  , zoom25
  , zoom50
  , zoom100
  , zoom200
  , zoom400
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  , (-)
  , (+)
  , (/)
  , (*)
  , (<=)
  , (>=)
  , (<)
  , (&&)
  , max
  , min
  , not
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // viewport zoom
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom level for graph viewport.
-- |
-- | - 1.0 = 100% (default, 1:1 mapping)
-- | - 0.5 = 50% (zoomed out, see more)
-- | - 2.0 = 200% (zoomed in, see less)
-- |
-- | Bounded to [0.01, 100.0] to prevent degenerate states.
newtype ViewportZoom = ViewportZoom Number

derive instance eqViewportZoom :: Eq ViewportZoom
derive instance ordViewportZoom :: Ord ViewportZoom

instance showViewportZoom :: Show ViewportZoom where
  show (ViewportZoom z) = show (z * 100.0) <> "%"

-- | Create a zoom level, clamped to valid range
viewportZoom :: Number -> ViewportZoom
viewportZoom z = ViewportZoom (max 0.01 (min 100.0 z))

-- | Default zoom (100%)
defaultZoom :: ViewportZoom
defaultZoom = ViewportZoom 1.0

-- | Minimum allowed zoom
minZoom :: ViewportZoom
minZoom = ViewportZoom 0.01

-- | Maximum allowed zoom
maxZoom :: ViewportZoom
maxZoom = ViewportZoom 100.0

-- | Standard zoom step multiplier
zoomStep :: Number
zoomStep = 1.2

-- | Zoom in by one step
zoomIn :: ViewportZoom -> ViewportZoom
zoomIn (ViewportZoom z) = viewportZoom (z * zoomStep)

-- | Zoom out by one step
zoomOut :: ViewportZoom -> ViewportZoom
zoomOut (ViewportZoom z) = viewportZoom (z / zoomStep)

-- | Zoom to exact level
zoomTo :: Number -> ViewportZoom
zoomTo = viewportZoom

-- | Calculate zoom to fit content in viewport
zoomToFit :: Number -> Number -> Number -> Number -> ViewportZoom
zoomToFit contentWidth contentHeight viewportWidth viewportHeight =
  let
    zoomX = viewportWidth / contentWidth
    zoomY = viewportHeight / contentHeight
  in
    viewportZoom (min zoomX zoomY)

-- | Get numeric zoom level
zoomLevel :: ViewportZoom -> Number
zoomLevel (ViewportZoom z) = z

-- | Get zoom as percentage
zoomPercentage :: ViewportZoom -> Number
zoomPercentage (ViewportZoom z) = z * 100.0

-- | Check if at minimum zoom
isMinZoom :: ViewportZoom -> Boolean
isMinZoom (ViewportZoom z) = z <= 0.01

-- | Check if at maximum zoom
isMaxZoom :: ViewportZoom -> Boolean
isMaxZoom (ViewportZoom z) = z >= 100.0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // viewport position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pan position in graph space coordinates
type ViewportPosition =
  { x :: Number  -- ^ X offset (positive = right)
  , y :: Number  -- ^ Y offset (positive = down)
  }

-- | Create viewport position
viewportPosition :: Number -> Number -> ViewportPosition
viewportPosition x y = { x, y }

-- | Origin position (no pan)
origin :: ViewportPosition
origin = { x: 0.0, y: 0.0 }

-- | Get X pan
panX :: ViewportPosition -> Number
panX p = p.x

-- | Get Y pan
panY :: ViewportPosition -> Number
panY p = p.y

-- | Pan by delta
panBy :: Number -> Number -> ViewportPosition -> ViewportPosition
panBy dx dy p = { x: p.x + dx, y: p.y + dy }

-- | Pan to absolute position
panTo :: Number -> Number -> ViewportPosition
panTo = viewportPosition

-- | Center viewport on a point
centerOn :: Number -> Number -> Number -> Number -> ViewportPosition
centerOn targetX targetY viewportWidth viewportHeight =
  { x: targetX - viewportWidth / 2.0
  , y: targetY - viewportHeight / 2.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // viewport bounds
-- ═════════════════════════════════════════════════════════════════════════════

-- | Rectangular bounds in graph space
type ViewportBounds =
  { left :: Number
  , top :: Number
  , right :: Number
  , bottom :: Number
  }

-- | Create bounds from edges
viewportBounds :: Number -> Number -> Number -> Number -> ViewportBounds
viewportBounds left top right bottom =
  { left: min left right
  , top: min top bottom
  , right: max left right
  , bottom: max top bottom
  }

-- | Create bounds from center and size
boundsFromCenter :: Number -> Number -> Number -> Number -> ViewportBounds
boundsFromCenter centerX centerY width height =
  { left: centerX - width / 2.0
  , top: centerY - height / 2.0
  , right: centerX + width / 2.0
  , bottom: centerY + height / 2.0
  }

-- | Get left edge
boundsLeft :: ViewportBounds -> Number
boundsLeft b = b.left

-- | Get top edge
boundsTop :: ViewportBounds -> Number
boundsTop b = b.top

-- | Get right edge
boundsRight :: ViewportBounds -> Number
boundsRight b = b.right

-- | Get bottom edge
boundsBottom :: ViewportBounds -> Number
boundsBottom b = b.bottom

-- | Get width
boundsWidth :: ViewportBounds -> Number
boundsWidth b = b.right - b.left

-- | Get height
boundsHeight :: ViewportBounds -> Number
boundsHeight b = b.bottom - b.top

-- | Get center point
boundsCenter :: ViewportBounds -> { x :: Number, y :: Number }
boundsCenter b =
  { x: (b.left + b.right) / 2.0
  , y: (b.top + b.bottom) / 2.0
  }

-- | Check if point is within bounds
containsPoint :: Number -> Number -> ViewportBounds -> Boolean
containsPoint x y b =
  x >= b.left && x <= b.right && y >= b.top && y <= b.bottom

-- | Check if two bounds intersect
boundsIntersect :: ViewportBounds -> ViewportBounds -> Boolean
boundsIntersect a b =
  a.left <= b.right && a.right >= b.left &&
  a.top <= b.bottom && a.bottom >= b.top

-- | Expand bounds by margin
expandBounds :: Number -> ViewportBounds -> ViewportBounds
expandBounds margin b =
  { left: b.left - margin
  , top: b.top - margin
  , right: b.right + margin
  , bottom: b.bottom + margin
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // viewport state compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete viewport state
type ViewportState =
  { zoom :: ViewportZoom
  , pan :: ViewportPosition
  , screenWidth :: Number   -- ^ Viewport width in screen pixels
  , screenHeight :: Number  -- ^ Viewport height in screen pixels
  }

-- | Create viewport state
viewportState :: ViewportZoom -> ViewportPosition -> Number -> Number -> ViewportState
viewportState zoom pan screenWidth screenHeight =
  { zoom, pan, screenWidth, screenHeight }

-- | Initial viewport (centered, 100% zoom)
initialViewport :: Number -> Number -> ViewportState
initialViewport width height =
  { zoom: defaultZoom
  , pan: origin
  , screenWidth: width
  , screenHeight: height
  }

-- | Get zoom level
viewportZoomLevel :: ViewportState -> ViewportZoom
viewportZoomLevel v = v.zoom

-- | Get pan position
viewportPan :: ViewportState -> ViewportPosition
viewportPan v = v.pan

-- | Calculate visible bounds at current state
viewportBoundsAt :: ViewportState -> ViewportBounds
viewportBoundsAt v =
  let
    z = zoomLevel v.zoom
    visibleWidth = v.screenWidth / z
    visibleHeight = v.screenHeight / z
  in
    { left: v.pan.x
    , top: v.pan.y
    , right: v.pan.x + visibleWidth
    , bottom: v.pan.y + visibleHeight
    }

-- | Set zoom level
setZoom :: ViewportZoom -> ViewportState -> ViewportState
setZoom zoom v = v { zoom = zoom }

-- | Set pan position
setPan :: ViewportPosition -> ViewportState -> ViewportState
setPan pan v = v { pan = pan }

-- | Apply zoom delta (preserving center)
-- |
-- | When zooming, the center point of the viewport should remain stable.
-- | This requires recalculating the pan position based on the ratio
-- | between old and new zoom levels.
applyZoom :: ViewportZoom -> ViewportState -> ViewportState
applyZoom newZoom v =
  let
    oldZ = zoomLevel v.zoom
    newZ = zoomLevel newZoom
    -- Calculate center in old viewport
    oldVisibleWidth = v.screenWidth / oldZ
    oldVisibleHeight = v.screenHeight / oldZ
    centerX = v.pan.x + oldVisibleWidth / 2.0
    centerY = v.pan.y + oldVisibleHeight / 2.0
    -- Calculate new pan to keep center stable
    newVisibleWidth = v.screenWidth / newZ
    newVisibleHeight = v.screenHeight / newZ
    newPan =
      { x: centerX - newVisibleWidth / 2.0
      , y: centerY - newVisibleHeight / 2.0
      }
  in
    v { zoom = newZoom, pan = newPan }

-- | Apply pan delta
applyPan :: Number -> Number -> ViewportState -> ViewportState
applyPan dx dy v =
  let
    z = zoomLevel v.zoom
    -- Pan in graph space (account for zoom)
    graphDx = dx / z
    graphDy = dy / z
  in
    v { pan = panBy graphDx graphDy v.pan }

-- | Fit content bounds in viewport
fitContent :: ViewportBounds -> ViewportState -> ViewportState
fitContent contentBounds v =
  let
    contentWidth = boundsWidth contentBounds
    contentHeight = boundsHeight contentBounds
    newZoom = zoomToFit contentWidth contentHeight v.screenWidth v.screenHeight
    center = boundsCenter contentBounds
    newVisibleWidth = v.screenWidth / zoomLevel newZoom
    newVisibleHeight = v.screenHeight / zoomLevel newZoom
    newPan =
      { x: center.x - newVisibleWidth / 2.0
      , y: center.y - newVisibleHeight / 2.0
      }
  in
    v { zoom = newZoom, pan = newPan }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // level of detail
-- ═════════════════════════════════════════════════════════════════════════════

-- | Level of detail for rendering
data LevelOfDetail
  = LOD_Full          -- ^ Full detail (close zoom)
  | LOD_Simplified    -- ^ Simplified shapes
  | LOD_Minimal       -- ^ Minimal representation
  | LOD_Dot           -- ^ Just a dot
  | LOD_Hidden        -- ^ Too small to render

derive instance eqLevelOfDetail :: Eq LevelOfDetail
derive instance ordLevelOfDetail :: Ord LevelOfDetail

instance showLevelOfDetail :: Show LevelOfDetail where
  show LOD_Full = "full"
  show LOD_Simplified = "simplified"
  show LOD_Minimal = "minimal"
  show LOD_Dot = "dot"
  show LOD_Hidden = "hidden"

-- | Determine LOD based on zoom level
lodForZoom :: ViewportZoom -> Number -> LevelOfDetail
lodForZoom (ViewportZoom z) nodeSize =
  let
    screenSize = z * nodeSize
  in
    if screenSize >= 50.0 then LOD_Full
    else if screenSize >= 20.0 then LOD_Simplified
    else if screenSize >= 8.0 then LOD_Minimal
    else if screenSize >= 2.0 then LOD_Dot
    else LOD_Hidden

-- | Should a node be rendered at this LOD?
shouldRenderNode :: LevelOfDetail -> Boolean
shouldRenderNode LOD_Hidden = false
shouldRenderNode _ = true

-- | Should labels be rendered at this LOD?
shouldRenderLabel :: LevelOfDetail -> Boolean
shouldRenderLabel LOD_Full = true
shouldRenderLabel LOD_Simplified = true
shouldRenderLabel _ = false

-- | Should connections be rendered at this LOD?
shouldRenderConnection :: LevelOfDetail -> Boolean
shouldRenderConnection LOD_Hidden = false
shouldRenderConnection LOD_Dot = false
shouldRenderConnection _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // viewport culling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Result of culling check
data CullResult
  = Visible           -- ^ Fully visible
  | PartiallyVisible  -- ^ Partially in viewport
  | Culled            -- ^ Not visible, don't render

derive instance eqCullResult :: Eq CullResult

instance showCullResult :: Show CullResult where
  show Visible = "visible"
  show PartiallyVisible = "partial"
  show Culled = "culled"

-- | Cull a node against viewport bounds
cullNode :: ViewportBounds -> Number -> Number -> Number -> Number -> CullResult
cullNode vp nodeX nodeY nodeWidth nodeHeight =
  let
    nodeBounds =
      { left: nodeX - nodeWidth / 2.0
      , top: nodeY - nodeHeight / 2.0
      , right: nodeX + nodeWidth / 2.0
      , bottom: nodeY + nodeHeight / 2.0
      }
  in
    if not (boundsIntersect vp nodeBounds) then Culled
    else if containsPoint nodeBounds.left nodeBounds.top vp &&
            containsPoint nodeBounds.right nodeBounds.bottom vp
    then Visible
    else PartiallyVisible

-- | Cull a connection against viewport bounds
cullConnection :: ViewportBounds -> Number -> Number -> Number -> Number -> CullResult
cullConnection vp x1 y1 x2 y2 =
  let
    lineBounds =
      { left: min x1 x2
      , top: min y1 y2
      , right: max x1 x2
      , bottom: max y1 y2
      }
  in
    if not (boundsIntersect vp lineBounds) then Culled
    else PartiallyVisible  -- Lines are always partial unless both endpoints visible

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // virtualization window
-- ═════════════════════════════════════════════════════════════════════════════

-- | Virtualization window - what portion of data to load/render
type VirtualWindow =
  { bounds :: ViewportBounds      -- ^ Visible bounds
  , overscan :: Number            -- ^ Extra margin for smooth scrolling
  , nodeCount :: Int              -- ^ Estimated visible nodes
  , connectionCount :: Int        -- ^ Estimated visible connections
  }

-- | Create virtual window from viewport state
virtualWindow :: ViewportState -> Number -> VirtualWindow
virtualWindow v overscan =
  let
    bounds = viewportBoundsAt v
    expandedBounds = expandBounds overscan bounds
  in
    { bounds: expandedBounds
    , overscan
    , nodeCount: 0      -- Will be calculated by layout
    , connectionCount: 0
    }

-- | Get estimated visible node count
windowNodes :: VirtualWindow -> Int
windowNodes w = w.nodeCount

-- | Get estimated visible connection count
windowConnections :: VirtualWindow -> Int
windowConnections w = w.connectionCount

-- | Get overscan amount
windowOverscan :: VirtualWindow -> Number
windowOverscan w = w.overscan

-- | Expand window bounds
expandWindow :: Number -> VirtualWindow -> VirtualWindow
expandWindow extra w =
  w { bounds = expandBounds extra w.bounds
    , overscan = w.overscan + extra
    }

-- | Check if point is in window
isInWindow :: Number -> Number -> VirtualWindow -> Boolean
isInWindow x y w = containsPoint x y w.bounds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // progressive loading
-- ═════════════════════════════════════════════════════════════════════════════

-- | Priority for loading nodes/data
data LoadingPriority
  = Immediate   -- ^ Load immediately (in viewport center)
  | High        -- ^ Load soon (in viewport)
  | Normal      -- ^ Load eventually (in overscan)
  | Low         -- ^ Lazy load (outside viewport)
  | Deferred    -- ^ Don't load until explicitly requested

derive instance eqLoadingPriority :: Eq LoadingPriority
derive instance ordLoadingPriority :: Ord LoadingPriority

instance showLoadingPriority :: Show LoadingPriority where
  show Immediate = "immediate"
  show High = "high"
  show Normal = "normal"
  show Low = "low"
  show Deferred = "deferred"

-- | Determine loading priority based on position
loadingPriority :: ViewportState -> Number -> Number -> LoadingPriority
loadingPriority v x y =
  let
    bounds = viewportBoundsAt v
    center = boundsCenter bounds
    distX = x - center.x
    distY = y - center.y
    dist = (distX * distX + distY * distY)
    halfDiag = (boundsWidth bounds * boundsWidth bounds + 
                boundsHeight bounds * boundsHeight bounds) / 4.0
  in
    if dist < halfDiag * 0.25 then Immediate     -- Center quarter
    else if containsPoint x y bounds then High   -- In viewport
    else if containsPoint x y (expandBounds 200.0 bounds) then Normal  -- Near
    else if containsPoint x y (expandBounds 500.0 bounds) then Low     -- Far
    else Deferred                                                       -- Very far

-- | Region with loading priority
type LoadingRegion =
  { bounds :: ViewportBounds
  , priority :: LoadingPriority
  }

-- | Create loading region
loadingRegion :: ViewportBounds -> LoadingPriority -> LoadingRegion
loadingRegion bounds priority = { bounds, priority }

-- | Priority region (immediate loading)
priorityRegion :: ViewportState -> LoadingRegion
priorityRegion v =
  let
    bounds = viewportBoundsAt v
    center = boundsCenter bounds
    size = min (boundsWidth bounds) (boundsHeight bounds) / 2.0
  in
    { bounds: boundsFromCenter center.x center.y size size
    , priority: Immediate
    }

-- | Background region (deferred loading)
backgroundRegion :: ViewportState -> Number -> LoadingRegion
backgroundRegion v expansion =
  { bounds: expandBounds expansion (viewportBoundsAt v)
  , priority: Low
  }

-- | Get priority from region
regionPriority :: LoadingRegion -> LoadingPriority
regionPriority r = r.priority

-- | Get bounds from region
regionBounds :: LoadingRegion -> ViewportBounds
regionBounds r = r.bounds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // viewport animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Transition style for viewport changes
data ViewportTransition
  = Instant                               -- ^ No animation
  | Linear Number                         -- ^ Linear interpolation (duration ms)
  | EaseInOut Number                      -- ^ Ease in-out (duration ms)
  | Spring Number Number                  -- ^ Spring physics (tension, friction)

derive instance eqViewportTransition :: Eq ViewportTransition

instance showViewportTransition :: Show ViewportTransition where
  show Instant = "instant"
  show (Linear d) = "linear(" <> show d <> "ms)"
  show (EaseInOut d) = "ease-in-out(" <> show d <> "ms)"
  show (Spring t f) = "spring(" <> show t <> "," <> show f <> ")"

-- | Create viewport transition
viewportTransition :: ViewportTransition -> ViewportTransition
viewportTransition t = t  -- Identity for now, could validate

-- | Instant transition (no animation)
instantTransition :: ViewportTransition
instantTransition = Instant

-- | Smooth ease-in-out transition
smoothTransition :: Number -> ViewportTransition
smoothTransition duration = EaseInOut duration

-- | Spring physics transition
springTransition :: Number -> Number -> ViewportTransition
springTransition tension friction = Spring tension friction

-- | Get transition duration in milliseconds
transitionDuration :: ViewportTransition -> Number
transitionDuration Instant = 0.0
transitionDuration (Linear d) = d
transitionDuration (EaseInOut d) = d
transitionDuration (Spring _ _) = 600.0  -- Approximate spring settle time

-- | Check if transition involves animation
isAnimating :: ViewportTransition -> Boolean
isAnimating Instant = false
isAnimating _ = true

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // viewport constraints
-- ═════════════════════════════════════════════════════════════════════════════

-- | Constraints on viewport movement
type ViewportConstraints =
  { minZoom :: ViewportZoom
  , maxZoom :: ViewportZoom
  , panBounds :: Maybe ViewportBounds  -- ^ Nothing = unlimited pan
  }

-- | Create viewport constraints
viewportConstraints :: ViewportZoom -> ViewportZoom -> Maybe ViewportBounds -> ViewportConstraints
viewportConstraints minZ maxZ panB =
  { minZoom: minZ
  , maxZoom: maxZ
  , panBounds: panB
  }

-- | No constraints
unconstrainedViewport :: ViewportConstraints
unconstrainedViewport =
  { minZoom: minZoom
  , maxZoom: maxZoom
  , panBounds: Nothing
  }

-- | Constrain zoom to valid range
constrainZoom :: ViewportConstraints -> ViewportZoom -> ViewportZoom
constrainZoom c (ViewportZoom z) =
  let
    ViewportZoom minZ = c.minZoom
    ViewportZoom maxZ = c.maxZoom
  in
    ViewportZoom (max minZ (min maxZ z))

-- | Constrain pan to valid bounds
constrainPan :: ViewportConstraints -> ViewportState -> ViewportPosition -> ViewportPosition
constrainPan c v pos =
  case c.panBounds of
    Nothing -> pos
    Just bounds ->
      let
        visible = viewportBoundsAt v
        visibleW = boundsWidth visible
        visibleH = boundsHeight visible
        -- Keep viewport within pan bounds
        minX = bounds.left
        maxX = bounds.right - visibleW
        minY = bounds.top
        maxY = bounds.bottom - visibleH
      in
        { x: max minX (min maxX pos.x)
        , y: max minY (min maxY pos.y)
        }

-- | Set minimum zoom constraint
withMinZoom :: ViewportZoom -> ViewportConstraints -> ViewportConstraints
withMinZoom z c = c { minZoom = z }

-- | Set maximum zoom constraint
withMaxZoom :: ViewportZoom -> ViewportConstraints -> ViewportConstraints
withMaxZoom z c = c { maxZoom = z }

-- | Set pan bounds constraint
withPanBounds :: ViewportBounds -> ViewportConstraints -> ViewportConstraints
withPanBounds b c = c { panBounds = Just b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // zoom presets
-- ═════════════════════════════════════════════════════════════════════════════

-- | Zoom to fit content (placeholder, actual value computed)
zoomFit :: ViewportZoom
zoomFit = ViewportZoom 1.0

-- | 25% zoom
zoom25 :: ViewportZoom
zoom25 = ViewportZoom 0.25

-- | 50% zoom
zoom50 :: ViewportZoom
zoom50 = ViewportZoom 0.5

-- | 100% zoom (default)
zoom100 :: ViewportZoom
zoom100 = ViewportZoom 1.0

-- | 200% zoom
zoom200 :: ViewportZoom
zoom200 = ViewportZoom 2.0

-- | 400% zoom
zoom400 :: ViewportZoom
zoom400 = ViewportZoom 4.0
