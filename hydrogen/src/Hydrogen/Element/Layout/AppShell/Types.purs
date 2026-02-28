-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // element // layout // appshell // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AppShell Types — Pure Element application shell type definitions.
-- |
-- | ## Design Philosophy
-- |
-- | These types define the complete vocabulary for application shell layouts.
-- | All dimensions use Schema atoms (`SpacingValue`) rather than raw strings.
-- | The shell supports three layout variants with configurable responsiveness.
-- |
-- | ## Type Safety
-- |
-- | - Dimensions: `SpacingValue` (not strings)
-- | - Positions: `SidebarPosition` ADT (not "left"/"right" strings)
-- | - Layouts: `Layout` ADT (not strings)
-- | - Breakpoints: `Breakpoint` from Schema (not local re-definition)

module Hydrogen.Element.Layout.AppShell.Types
  ( -- * Layout Variants
    Layout(SidebarFirst, HeaderFirst, Stacked)
  
  -- * Scroll Behavior  
  , ScrollBehavior(PageScroll, ContentOnly, IndependentScroll)
  
  -- * Sidebar Position
  , SidebarPosition(LeftSide, RightSide)
  
  -- * Slots
  , AppShellSlots
  
  -- * Props
  , AppShellProps
  , AppShellProp
  , defaultProps
  
  -- * Prop Setters: Layout
  , layout
  , scrollBehavior
  , mobileBreakpoint
  
  -- * Prop Setters: Fixed Positioning
  , fixedHeader
  , fixedSidebar
  , fixedFooter
  
  -- * Prop Setters: Dimensions
  , headerHeight
  , footerHeight
  , sidebarWidth
  , sidebarMiniWidth
  
  -- * Prop Setters: Sidebar
  , sidebarPosition
  , sidebarCollapsible
  , sidebarCollapsed
  , sidebarMiniMode
  
  -- * Prop Setters: Callbacks
  , onSidebarCollapse
  
  -- * Prop Setters: Custom Styling
  , className
  , headerClassName
  , sidebarClassName
  , contentClassName
  , footerClassName
  ) where

import Prelude
  ( class Eq
  , class Show
  , Unit
  , (<>)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)

import Hydrogen.Render.Element (Element)
import Hydrogen.Schema.Geometry.Spacing (SpacingValue)
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Reactive.Viewport (Breakpoint(Lg))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // layout variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | Application shell layout variants.
-- |
-- | Determines the structural relationship between header, sidebar, and content.
data Layout
  = SidebarFirst    -- ^ Sidebar spans full height, header beside content
  | HeaderFirst     -- ^ Header spans full width, sidebar beside content
  | Stacked         -- ^ No sidebar, vertical stack: header → content → footer

derive instance eqLayout :: Eq Layout

instance showLayout :: Show Layout where
  show SidebarFirst = "sidebar-first"
  show HeaderFirst = "header-first"
  show Stacked = "stacked"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // scroll behavior
-- ═════════════════════════════════════════════════════════════════════════════

-- | How scrolling is handled within the shell.
-- |
-- | Determines which regions scroll and how they interact.
data ScrollBehavior
  = PageScroll         -- ^ Entire page scrolls as one unit
  | ContentOnly        -- ^ Only main content area scrolls, header/sidebar fixed
  | IndependentScroll  -- ^ Sidebar and content scroll independently

derive instance eqScrollBehavior :: Eq ScrollBehavior

instance showScrollBehavior :: Show ScrollBehavior where
  show PageScroll = "page"
  show ContentOnly = "content"
  show IndependentScroll = "independent"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // sidebar position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sidebar positioning relative to main content.
-- |
-- | Note: Named `LeftSide`/`RightSide` to avoid conflicts with
-- | `Hydrogen.Schema.Geometry.Position.Left/Right`.
data SidebarPosition
  = LeftSide   -- ^ Sidebar on left, content on right (default)
  | RightSide  -- ^ Sidebar on right, content on left

derive instance eqSidebarPosition :: Eq SidebarPosition

instance showSidebarPosition :: Show SidebarPosition where
  show LeftSide = "left"
  show RightSide = "right"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // slots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content slots for the application shell.
-- |
-- | The shell provides four regions that can be filled with content.
-- | Only `content` is required; others are optional.
type AppShellSlots msg =
  { header :: Maybe (Element msg)   -- ^ Top navigation / branding
  , sidebar :: Maybe (Element msg)  -- ^ Side navigation / tools
  , content :: Element msg          -- ^ Main content area (required)
  , footer :: Maybe (Element msg)   -- ^ Bottom content / links
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete configuration for application shell.
-- |
-- | All dimensions use `SpacingValue` atoms for type safety.
-- | Breakpoints use Schema `Breakpoint` type.
type AppShellProps =
  { -- Layout
    layout :: Layout
  , scrollBehavior :: ScrollBehavior
  , mobileBreakpoint :: Breakpoint
  
  -- Fixed positioning
  , fixedHeader :: Boolean
  , fixedSidebar :: Boolean
  , fixedFooter :: Boolean
  
  -- Dimensions (using Schema atoms)
  , headerHeight :: SpacingValue
  , footerHeight :: SpacingValue
  , sidebarWidth :: SpacingValue
  , sidebarMiniWidth :: SpacingValue
  
  -- Sidebar behavior
  , sidebarPosition :: SidebarPosition
  , sidebarCollapsible :: Boolean
  , sidebarCollapsed :: Boolean
  , sidebarMiniMode :: Boolean
  
  -- Callbacks
  , onSidebarCollapse :: Maybe (Boolean -> Effect Unit)
  
  -- Custom CSS classes (escape hatch for integration)
  , className :: String
  , headerClassName :: String
  , sidebarClassName :: String
  , contentClassName :: String
  , footerClassName :: String
  }

-- | Property modifier function.
type AppShellProp = AppShellProps -> AppShellProps

-- | Default application shell configuration.
-- |
-- | - HeaderFirst layout (most common)
-- | - Fixed header and sidebar, scrollable content
-- | - 64px header, 256px sidebar (standard dashboard dimensions)
-- | - Mobile breakpoint at Lg (1024px)
defaultProps :: AppShellProps
defaultProps =
  { layout: HeaderFirst
  , scrollBehavior: ContentOnly
  , mobileBreakpoint: Lg
  , fixedHeader: true
  , fixedSidebar: true
  , fixedFooter: false
  , headerHeight: Spacing.spacingValue 64.0   -- 64px
  , footerHeight: Spacing.spacingValue 48.0   -- 48px auto
  , sidebarWidth: Spacing.spacingValue 256.0  -- 256px
  , sidebarMiniWidth: Spacing.spacingValue 64.0  -- 64px
  , sidebarPosition: LeftSide
  , sidebarCollapsible: false
  , sidebarCollapsed: false
  , sidebarMiniMode: false
  , onSidebarCollapse: Nothing
  , className: ""
  , headerClassName: ""
  , sidebarClassName: ""
  , contentClassName: ""
  , footerClassName: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // prop setters: layout
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set layout variant.
layout :: Layout -> AppShellProp
layout l props = props { layout = l }

-- | Set scroll behavior.
scrollBehavior :: ScrollBehavior -> AppShellProp
scrollBehavior s props = props { scrollBehavior = s }

-- | Set mobile breakpoint (sidebar hides below this).
mobileBreakpoint :: Breakpoint -> AppShellProp
mobileBreakpoint b props = props { mobileBreakpoint = b }

-- ═════════════════════════════════════════════════════════════════════════════
--                                            // prop setters: fixed positioning
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set header as fixed (sticky).
fixedHeader :: Boolean -> AppShellProp
fixedHeader f props = props { fixedHeader = f }

-- | Set sidebar as fixed (sticky).
fixedSidebar :: Boolean -> AppShellProp
fixedSidebar f props = props { fixedSidebar = f }

-- | Set footer as fixed (sticky).
fixedFooter :: Boolean -> AppShellProp
fixedFooter f props = props { fixedFooter = f }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                   // prop setters: dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set header height.
headerHeight :: SpacingValue -> AppShellProp
headerHeight h props = props { headerHeight = h }

-- | Set footer height.
footerHeight :: SpacingValue -> AppShellProp
footerHeight h props = props { footerHeight = h }

-- | Set sidebar width.
sidebarWidth :: SpacingValue -> AppShellProp
sidebarWidth w props = props { sidebarWidth = w }

-- | Set mini sidebar width (when collapsed with mini mode).
sidebarMiniWidth :: SpacingValue -> AppShellProp
sidebarMiniWidth w props = props { sidebarMiniWidth = w }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // prop setters: sidebar
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set sidebar position (left or right).
sidebarPosition :: SidebarPosition -> AppShellProp
sidebarPosition p props = props { sidebarPosition = p }

-- | Enable collapsible sidebar.
sidebarCollapsible :: Boolean -> AppShellProp
sidebarCollapsible c props = props { sidebarCollapsible = c }

-- | Set sidebar collapsed state.
sidebarCollapsed :: Boolean -> AppShellProp
sidebarCollapsed c props = props { sidebarCollapsed = c }

-- | Enable mini mode for collapsed sidebar.
-- |
-- | When true, collapsed sidebar shows icons-only (sidebarMiniWidth).
-- | When false, collapsed sidebar is fully hidden.
sidebarMiniMode :: Boolean -> AppShellProp
sidebarMiniMode m props = props { sidebarMiniMode = m }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                    // prop setters: callbacks
-- ═════════════════════════════════════════════════════════════════════════════

-- | Handle sidebar collapse toggle.
onSidebarCollapse :: (Boolean -> Effect Unit) -> AppShellProp
onSidebarCollapse f props = props { onSidebarCollapse = Just f }

-- ═════════════════════════════════════════════════════════════════════════════
--                                               // prop setters: custom styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Add custom class to shell container.
className :: String -> AppShellProp
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to header slot.
headerClassName :: String -> AppShellProp
headerClassName c props = props { headerClassName = props.headerClassName <> " " <> c }

-- | Add custom class to sidebar slot.
sidebarClassName :: String -> AppShellProp
sidebarClassName c props = props { sidebarClassName = props.sidebarClassName <> " " <> c }

-- | Add custom class to content slot.
contentClassName :: String -> AppShellProp
contentClassName c props = props { contentClassName = props.contentClassName <> " " <> c }

-- | Add custom class to footer slot.
footerClassName :: String -> AppShellProp
footerClassName c props = props { footerClassName = props.footerClassName <> " " <> c }
