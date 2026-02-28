-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // layout // side-bar
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Sidebar — Pure Element sidebar layout component.
-- |
-- | ## Design Philosophy
-- |
-- | Fixed sidebar with scrollable content area. Supports collapsible,
-- | mobile drawer mode, and mini (icons-only) mode.
-- | Uses Schema atoms for dimensions and breakpoints.

module Hydrogen.Element.Layout.Sidebar
  ( -- * Component
    sidebar
    
  -- * Types
  , SidebarPosition(LeftSide, RightSide)
  , SidebarSlots
  , SidebarProps
  , SidebarProp
  , defaultProps
  
  -- * Prop Setters
  , position
  , width
  , miniWidth
  , collapsible
  , collapsed
  , miniMode
  , mobileBreakpoint
  , mobileDrawer
  , overlay
  , onCollapse
  , className
  , sidebarClassName
  , contentClassName
  ) where

import Prelude
  ( class Eq
  , class Show
  , Unit
  , (<>)
  , ($)
  , (&&)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))
import Effect (Effect)

import Hydrogen.Render.Element (Element)
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Spacing (SpacingValue)
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Reactive.Viewport (Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sidebar position.
-- |
-- | Named `LeftSide`/`RightSide` to avoid conflict with Schema Position.
data SidebarPosition
  = LeftSide
  | RightSide

derive instance eqSidebarPosition :: Eq SidebarPosition

instance showSidebarPosition :: Show SidebarPosition where
  show LeftSide = "left"
  show RightSide = "right"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // slots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Content for sidebar layout.
type SidebarSlots msg =
  { sidebar :: Element msg   -- ^ Sidebar content
  , content :: Element msg   -- ^ Main content
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sidebar configuration.
type SidebarProps =
  { position :: SidebarPosition
  , width :: SpacingValue
  , miniWidth :: SpacingValue
  , collapsible :: Boolean
  , collapsed :: Boolean
  , miniMode :: Boolean
  , mobileBreakpoint :: Breakpoint
  , mobileDrawer :: Boolean
  , overlay :: Boolean
  , onCollapse :: Maybe (Boolean -> Effect Unit)
  , className :: String
  , sidebarClassName :: String
  , contentClassName :: String
  }

-- | Property modifier.
type SidebarProp = SidebarProps -> SidebarProps

-- | Default sidebar configuration.
defaultProps :: SidebarProps
defaultProps =
  { position: LeftSide
  , width: Spacing.spacingValue 256.0
  , miniWidth: Spacing.spacingValue 64.0
  , collapsible: false
  , collapsed: false
  , miniMode: false
  , mobileBreakpoint: Lg
  , mobileDrawer: true
  , overlay: true
  , onCollapse: Nothing
  , className: ""
  , sidebarClassName: ""
  , contentClassName: ""
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // prop setters
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set sidebar position.
position :: SidebarPosition -> SidebarProp
position p props = props { position = p }

-- | Set sidebar width.
width :: SpacingValue -> SidebarProp
width w props = props { width = w }

-- | Set mini mode width (when collapsed).
miniWidth :: SpacingValue -> SidebarProp
miniWidth w props = props { miniWidth = w }

-- | Enable collapsible behavior.
collapsible :: Boolean -> SidebarProp
collapsible c props = props { collapsible = c }

-- | Set collapsed state.
collapsed :: Boolean -> SidebarProp
collapsed c props = props { collapsed = c }

-- | Enable mini mode (icons only when collapsed).
miniMode :: Boolean -> SidebarProp
miniMode m props = props { miniMode = m }

-- | Set mobile breakpoint.
mobileBreakpoint :: Breakpoint -> SidebarProp
mobileBreakpoint b props = props { mobileBreakpoint = b }

-- | Enable mobile drawer mode.
mobileDrawer :: Boolean -> SidebarProp
mobileDrawer d props = props { mobileDrawer = d }

-- | Enable overlay when drawer open.
overlay :: Boolean -> SidebarProp
overlay o props = props { overlay = o }

-- | Handle collapse events.
onCollapse :: (Boolean -> Effect Unit) -> SidebarProp
onCollapse f props = props { onCollapse = Just f }

-- | Add custom class to container.
className :: String -> SidebarProp
className c props = props { className = props.className <> " " <> c }

-- | Add custom class to sidebar panel.
sidebarClassName :: String -> SidebarProp
sidebarClassName c props = props { sidebarClassName = props.sidebarClassName <> " " <> c }

-- | Add custom class to content area.
contentClassName :: String -> SidebarProp
contentClassName c props = props { contentClassName = props.contentClassName <> " " <> c }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sidebar layout component.
-- |
-- | Creates a fixed sidebar with scrollable main content.
-- | Supports responsive behavior, collapsible states, and mobile drawer mode.
sidebar :: forall msg. Array SidebarProp -> SidebarSlots msg -> Element msg
sidebar propMods slots =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    bp = breakpointPrefix props.mobileBreakpoint
    
    -- Calculate effective width
    effectiveWidth = 
      if props.collapsed 
        then if props.miniMode then props.miniWidth else Spacing.spacingZero
        else props.width
    
    -- Container direction based on position
    containerDirection = case props.position of
      LeftSide -> "flex-row"
      RightSide -> "flex-row-reverse"
    
    -- Border side based on position
    borderSide = case props.position of
      LeftSide -> "border-r"
      RightSide -> "border-l"
  in
    E.div_
      [ E.class_ $ "flex h-full w-full overflow-hidden " <> containerDirection <> " " <> props.className
      , E.dataAttr "sidebar" "true"
      ]
      [ -- Overlay for mobile drawer
        if props.mobileDrawer && props.overlay && not props.collapsed
          then E.div_
            [ E.class_ $ bp <> "hidden fixed inset-0 bg-black/50 z-30 transition-opacity" ]
            []
          else E.empty
        -- Sidebar panel
      , E.aside_
          [ E.class_ $ "flex flex-col bg-background border-border shrink-0 overflow-y-auto overflow-x-hidden z-40 "
              <> borderSide <> " " <> props.sidebarClassName
          , E.style "width" (Spacing.toLegacyCss effectiveWidth)
          , E.style "min-width" (Spacing.toLegacyCss effectiveWidth)
          , E.dataAttr "sidebar-panel" "true"
          , E.dataAttr "collapsed" (if props.collapsed then "true" else "false")
          ]
          [ slots.sidebar ]
        -- Main content
      , E.div_
          [ E.class_ $ "flex-1 overflow-auto min-w-0 " <> props.contentClassName
          , E.dataAttr "sidebar-content" "true"
          , E.role "main"
          ]
          [ slots.content ]
      ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // css helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get breakpoint prefix for Tailwind classes.
breakpointPrefix :: Breakpoint -> String
breakpointPrefix Xs = ""
breakpointPrefix Sm = "sm:"
breakpointPrefix Md = "md:"
breakpointPrefix Lg = "lg:"
breakpointPrefix Xl = "xl:"
breakpointPrefix Xxl = "2xl:"
