-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // schema // graph // connection
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Graph Connection — Visual representation of edges between nodes.
-- |
-- | ## Design Philosophy
-- |
-- | Connections are pure visual descriptions of how parent-child relationships
-- | are rendered. They support everything from simple lines to complex bundled
-- | edges with animations.
-- |
-- | ## Connection Categories
-- |
-- | **Routing**: How the line path is computed
-- | **Style**: Visual appearance (stroke, dash, color)
-- | **Terminals**: Arrow heads, dots, custom markers
-- | **Animation**: Line drawing, flow animations
-- |
-- | ## Dependencies
-- |
-- | - Prelude
-- | - Schema.Color.RGB (colors)
-- | - Schema.Geometry.Stroke (stroke patterns)

module Hydrogen.Schema.Graph.Connection
  ( -- * Connection Routing
    ConnectionRouting(..)
  , isStraightRouting
  , isCurvedRouting
  , isOrthogonalRouting
  
  -- * Curve Style
  , CurveStyle(..)
  , curveTension
  
  -- * Connection Terminals
  , TerminalStyle(..)
  , isArrowTerminal
  , isDotTerminal
  , isNoneTerminal
  , TerminalPosition(..)
  
  -- * Stroke Pattern
  , StrokePattern(..)
  , isSolidStroke
  , isDashedStroke
  , isDottedStroke
  
  -- * Connection Style (Molecule)
  , ConnectionStyle
  , connectionStyle
  , defaultConnectionStyle
  , noConnections
  , withRouting
  , withStrokeWidth
  , withStrokeColor
  , withStrokePattern
  , withStartTerminal
  , withEndTerminal
  , withOpacity
  , withCurveTension
  
  -- * Bundle Style
  , BundleStyle
  , bundleStyle
  , defaultBundleStyle
  , bundleStrength
  , bundleRadius
  
  -- * Connection Animation
  , ConnectionAnimation(..)
  , isStaticConnection
  , isDrawConnection
  , isFlowConnection
  , isPulseConnection
  
  -- * Animation Params
  , DrawAnimationParams
  , drawAnimation
  , FlowAnimationParams
  , flowAnimation
  , PulseAnimationParams
  , pulseAnimation
  
  -- * Connection Config (Compound)
  , ConnectionConfig
  , connectionConfig
  , simpleConnections
  , curvedConnections
  , orthogonalConnections
  , bundledConnections
  , animatedConnections
  , noConnectionLines
  
  -- * Per-Edge Styling
  , EdgeStyle
  , edgeStyle
  , defaultEdgeStyle
  , withEdgeColor
  , withEdgeWidth
  , withEdgeLabel
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
  , (<)
  , (>)
  , (==)
  , otherwise
  )

import Data.Maybe (Maybe(Just, Nothing))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // connection routing
-- ═════════════════════════════════════════════════════════════════════════════

-- | How the connection path is computed
data ConnectionRouting
  = RoutingStraight      -- ^ Direct line between nodes
  | RoutingCurved        -- ^ Bezier curve
  | RoutingOrthogonal    -- ^ Right-angle connectors (elbow)
  | RoutingDiagonal      -- ^ Angled segments
  | RoutingStep          -- ^ Step/staircase pattern
  | RoutingBundle        -- ^ Bundled edges (for dense graphs)
  | RoutingArc           -- ^ Arc segments
  | RoutingSpline        -- ^ Smooth spline through control points

derive instance eqConnectionRouting :: Eq ConnectionRouting
derive instance ordConnectionRouting :: Ord ConnectionRouting

instance showConnectionRouting :: Show ConnectionRouting where
  show RoutingStraight = "straight"
  show RoutingCurved = "curved"
  show RoutingOrthogonal = "orthogonal"
  show RoutingDiagonal = "diagonal"
  show RoutingStep = "step"
  show RoutingBundle = "bundle"
  show RoutingArc = "arc"
  show RoutingSpline = "spline"

isStraightRouting :: ConnectionRouting -> Boolean
isStraightRouting RoutingStraight = true
isStraightRouting _ = false

isCurvedRouting :: ConnectionRouting -> Boolean
isCurvedRouting RoutingCurved = true
isCurvedRouting RoutingSpline = true
isCurvedRouting _ = false

isOrthogonalRouting :: ConnectionRouting -> Boolean
isOrthogonalRouting RoutingOrthogonal = true
isOrthogonalRouting RoutingStep = true
isOrthogonalRouting _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // curve style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Curve interpolation style
data CurveStyle
  = CurveBasis          -- ^ B-spline
  | CurveBezier         -- ^ Cubic bezier
  | CurveCardinal       -- ^ Cardinal spline
  | CurveCatmullRom     -- ^ Catmull-Rom spline
  | CurveMonotone       -- ^ Monotone cubic
  | CurveNatural        -- ^ Natural cubic spline
  | CurveLinear         -- ^ Linear interpolation (straight)

derive instance eqCurveStyle :: Eq CurveStyle

instance showCurveStyle :: Show CurveStyle where
  show CurveBasis = "basis"
  show CurveBezier = "bezier"
  show CurveCardinal = "cardinal"
  show CurveCatmullRom = "catmull-rom"
  show CurveMonotone = "monotone"
  show CurveNatural = "natural"
  show CurveLinear = "linear"

-- | Tension parameter for curves (0 = straight, 1 = tight)
curveTension :: Number -> Number
curveTension t
  | t < 0.0 = 0.0
  | t > 1.0 = 1.0
  | otherwise = t

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // connection terminals
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual marker at connection endpoints
data TerminalStyle
  = TerminalNone           -- ^ No marker
  | TerminalArrow          -- ^ Standard arrow head
  | TerminalArrowFilled    -- ^ Filled arrow head
  | TerminalArrowOpen      -- ^ Open arrow head
  | TerminalDot            -- ^ Circle dot
  | TerminalDotFilled      -- ^ Filled circle
  | TerminalDiamond        -- ^ Diamond shape
  | TerminalSquare         -- ^ Square marker
  | TerminalBar            -- ^ Perpendicular bar

derive instance eqTerminalStyle :: Eq TerminalStyle

instance showTerminalStyle :: Show TerminalStyle where
  show TerminalNone = "none"
  show TerminalArrow = "arrow"
  show TerminalArrowFilled = "arrow-filled"
  show TerminalArrowOpen = "arrow-open"
  show TerminalDot = "dot"
  show TerminalDotFilled = "dot-filled"
  show TerminalDiamond = "diamond"
  show TerminalSquare = "square"
  show TerminalBar = "bar"

isArrowTerminal :: TerminalStyle -> Boolean
isArrowTerminal TerminalArrow = true
isArrowTerminal TerminalArrowFilled = true
isArrowTerminal TerminalArrowOpen = true
isArrowTerminal _ = false

isDotTerminal :: TerminalStyle -> Boolean
isDotTerminal TerminalDot = true
isDotTerminal TerminalDotFilled = true
isDotTerminal _ = false

isNoneTerminal :: TerminalStyle -> Boolean
isNoneTerminal TerminalNone = true
isNoneTerminal _ = false

-- | Which end of the connection to apply terminal
data TerminalPosition
  = TerminalStart   -- ^ At source/parent
  | TerminalEnd     -- ^ At target/child
  | TerminalBoth    -- ^ Both ends

derive instance eqTerminalPosition :: Eq TerminalPosition

instance showTerminalPosition :: Show TerminalPosition where
  show TerminalStart = "start"
  show TerminalEnd = "end"
  show TerminalBoth = "both"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // stroke pattern
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stroke dash pattern
data StrokePattern
  = StrokeSolid                    -- ^ Continuous line
  | StrokeDashed Number Number     -- ^ Dash length, gap length
  | StrokeDotted                   -- ^ Dot pattern
  | StrokeDashDot                  -- ^ Dash-dot pattern
  | StrokeCustom (Array Number)    -- ^ Custom dash array

derive instance eqStrokePattern :: Eq StrokePattern

instance showStrokePattern :: Show StrokePattern where
  show StrokeSolid = "solid"
  show (StrokeDashed _ _) = "dashed"
  show StrokeDotted = "dotted"
  show StrokeDashDot = "dash-dot"
  show (StrokeCustom _) = "custom"

isSolidStroke :: StrokePattern -> Boolean
isSolidStroke StrokeSolid = true
isSolidStroke _ = false

isDashedStroke :: StrokePattern -> Boolean
isDashedStroke (StrokeDashed _ _) = true
isDashedStroke _ = false

isDottedStroke :: StrokePattern -> Boolean
isDottedStroke StrokeDotted = true
isDottedStroke _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                  // connection style molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style for connections
type ConnectionStyle =
  { routing :: ConnectionRouting
  , curveStyle :: CurveStyle
  , curveTension :: Number
  , strokeWidth :: Number
  , strokeColor :: String          -- ^ Hex color (should be Color.RGB but avoiding import cycle)
  , strokePattern :: StrokePattern
  , startTerminal :: TerminalStyle
  , endTerminal :: TerminalStyle
  , terminalSize :: Number
  , opacity :: Number
  , visible :: Boolean
  }

-- | Create connection style
connectionStyle :: ConnectionRouting -> ConnectionStyle
connectionStyle routing =
  { routing
  , curveStyle: CurveBezier
  , curveTension: 0.5
  , strokeWidth: 1.0
  , strokeColor: "#94a3b8"  -- Slate 400
  , strokePattern: StrokeSolid
  , startTerminal: TerminalNone
  , endTerminal: TerminalNone
  , terminalSize: 8.0
  , opacity: 1.0
  , visible: true
  }

-- | Default connection style (curved)
defaultConnectionStyle :: ConnectionStyle
defaultConnectionStyle = connectionStyle RoutingCurved

-- | No visible connections
noConnections :: ConnectionStyle
noConnections = (connectionStyle RoutingStraight) { visible = false }

-- | Set routing
withRouting :: ConnectionRouting -> ConnectionStyle -> ConnectionStyle
withRouting r s = s { routing = r }

-- | Set stroke width
withStrokeWidth :: Number -> ConnectionStyle -> ConnectionStyle
withStrokeWidth w s = s { strokeWidth = w }

-- | Set stroke color
withStrokeColor :: String -> ConnectionStyle -> ConnectionStyle
withStrokeColor c s = s { strokeColor = c }

-- | Set stroke pattern
withStrokePattern :: StrokePattern -> ConnectionStyle -> ConnectionStyle
withStrokePattern p s = s { strokePattern = p }

-- | Set start terminal
withStartTerminal :: TerminalStyle -> ConnectionStyle -> ConnectionStyle
withStartTerminal t s = s { startTerminal = t }

-- | Set end terminal
withEndTerminal :: TerminalStyle -> ConnectionStyle -> ConnectionStyle
withEndTerminal t s = s { endTerminal = t }

-- | Set opacity
withOpacity :: Number -> ConnectionStyle -> ConnectionStyle
withOpacity o s = s { opacity = o }

-- | Set curve tension
withCurveTension :: Number -> ConnectionStyle -> ConnectionStyle
withCurveTension t s = s { curveTension = curveTension t }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // bundle style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style for bundled edges
type BundleStyle =
  { strength :: Number    -- ^ Bundle tightness (0 = none, 1 = tight)
  , radius :: Number      -- ^ Bundle corner radius
  , enabled :: Boolean
  }

-- | Create bundle style
bundleStyle :: Number -> Number -> BundleStyle
bundleStyle strength radius =
  { strength
  , radius
  , enabled: true
  }

-- | Default bundle style
defaultBundleStyle :: BundleStyle
defaultBundleStyle = bundleStyle 0.85 30.0

-- | Get bundle strength
bundleStrength :: BundleStyle -> Number
bundleStrength b = b.strength

-- | Get bundle radius
bundleRadius :: BundleStyle -> Number
bundleRadius b = b.radius

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // connection animation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Animation type for connections
data ConnectionAnimation
  = AnimationStatic              -- ^ No animation
  | AnimationDraw                -- ^ Draw line progressively
  | AnimationFlow                -- ^ Animated flow along path
  | AnimationPulse               -- ^ Pulsing effect
  | AnimationDash                -- ^ Moving dashes

derive instance eqConnectionAnimation :: Eq ConnectionAnimation

instance showConnectionAnimation :: Show ConnectionAnimation where
  show AnimationStatic = "static"
  show AnimationDraw = "draw"
  show AnimationFlow = "flow"
  show AnimationPulse = "pulse"
  show AnimationDash = "dash"

isStaticConnection :: ConnectionAnimation -> Boolean
isStaticConnection AnimationStatic = true
isStaticConnection _ = false

isDrawConnection :: ConnectionAnimation -> Boolean
isDrawConnection AnimationDraw = true
isDrawConnection _ = false

isFlowConnection :: ConnectionAnimation -> Boolean
isFlowConnection AnimationFlow = true
isFlowConnection _ = false

isPulseConnection :: ConnectionAnimation -> Boolean
isPulseConnection AnimationPulse = true
isPulseConnection _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // animation params
-- ═════════════════════════════════════════════════════════════════════════════

-- | Draw animation parameters
type DrawAnimationParams =
  { duration :: Number     -- ^ Animation duration in ms
  , delay :: Number        -- ^ Start delay in ms
  , easing :: String       -- ^ Easing function name
  , direction :: String    -- ^ "forward" | "reverse" | "both"
  }

-- | Create draw animation
drawAnimation :: Number -> DrawAnimationParams
drawAnimation duration =
  { duration
  , delay: 0.0
  , easing: "ease-out"
  , direction: "forward"
  }

-- | Flow animation parameters
type FlowAnimationParams =
  { speed :: Number        -- ^ Flow speed (px/s)
  , particleSize :: Number -- ^ Size of flow particles
  , particleGap :: Number  -- ^ Gap between particles
  , color :: Maybe String  -- ^ Override color
  }

-- | Create flow animation
flowAnimation :: Number -> FlowAnimationParams
flowAnimation speed =
  { speed
  , particleSize: 4.0
  , particleGap: 20.0
  , color: Nothing
  }

-- | Pulse animation parameters
type PulseAnimationParams =
  { frequency :: Number    -- ^ Pulses per second
  , minOpacity :: Number   -- ^ Minimum opacity
  , maxOpacity :: Number   -- ^ Maximum opacity
  , minWidth :: Number     -- ^ Minimum stroke width
  , maxWidth :: Number     -- ^ Maximum stroke width
  }

-- | Create pulse animation
pulseAnimation :: Number -> PulseAnimationParams
pulseAnimation frequency =
  { frequency
  , minOpacity: 0.3
  , maxOpacity: 1.0
  , minWidth: 1.0
  , maxWidth: 3.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                 // connection config compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete connection configuration
type ConnectionConfig =
  { style :: ConnectionStyle
  , bundleStyle :: Maybe BundleStyle
  , animation :: ConnectionAnimation
  , drawParams :: Maybe DrawAnimationParams
  , flowParams :: Maybe FlowAnimationParams
  , pulseParams :: Maybe PulseAnimationParams
  , renderOrder :: String    -- ^ "behind" | "front" | "interleaved"
  }

-- | Create connection config
connectionConfig :: ConnectionStyle -> ConnectionConfig
connectionConfig style =
  { style
  , bundleStyle: Nothing
  , animation: AnimationStatic
  , drawParams: Nothing
  , flowParams: Nothing
  , pulseParams: Nothing
  , renderOrder: "behind"
  }

-- | Simple straight connections
simpleConnections :: ConnectionConfig
simpleConnections = connectionConfig (connectionStyle RoutingStraight)

-- | Curved bezier connections
curvedConnections :: ConnectionConfig
curvedConnections = connectionConfig defaultConnectionStyle

-- | Orthogonal (elbow) connections
orthogonalConnections :: ConnectionConfig
orthogonalConnections = connectionConfig (connectionStyle RoutingOrthogonal)

-- | Bundled edge connections (for dense graphs)
bundledConnections :: ConnectionConfig
bundledConnections = (connectionConfig (connectionStyle RoutingBundle))
  { bundleStyle = Just defaultBundleStyle }

-- | Animated flow connections
animatedConnections :: ConnectionConfig
animatedConnections = (connectionConfig defaultConnectionStyle)
  { animation = AnimationFlow
  , flowParams = Just (flowAnimation 50.0)
  }

-- | No connection lines
noConnectionLines :: ConnectionConfig
noConnectionLines = connectionConfig noConnections

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // per-edge styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Style override for individual edges
type EdgeStyle =
  { color :: Maybe String
  , width :: Maybe Number
  , pattern :: Maybe StrokePattern
  , label :: Maybe String
  , labelPosition :: Number    -- ^ 0-1 position along edge
  , visible :: Boolean
  }

-- | Create edge style
edgeStyle :: EdgeStyle
edgeStyle =
  { color: Nothing
  , width: Nothing
  , pattern: Nothing
  , label: Nothing
  , labelPosition: 0.5
  , visible: true
  }

-- | Default edge style (no overrides)
defaultEdgeStyle :: EdgeStyle
defaultEdgeStyle = edgeStyle

-- | Override edge color
withEdgeColor :: String -> EdgeStyle -> EdgeStyle
withEdgeColor c e = e { color = Just c }

-- | Override edge width
withEdgeWidth :: Number -> EdgeStyle -> EdgeStyle
withEdgeWidth w e = e { width = Just w }

-- | Add edge label
withEdgeLabel :: String -> EdgeStyle -> EdgeStyle
withEdgeLabel l e = e { label = Just l }
