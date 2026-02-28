-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // layout // appshell
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AppShell — Pure Element application shell layout.
-- |
-- | ## Design Philosophy
-- |
-- | Complete application layout with header, sidebar, main content, and footer
-- | slots. Uses Schema atoms for all dimensions and generates CSS from type-safe
-- | values. No Halogen dependency — pure Element composition.
-- |
-- | ## Layout Variants
-- |
-- | - **HeaderFirst**: Header spans full width, sidebar beside content (default)
-- | - **SidebarFirst**: Sidebar spans full height, header beside content  
-- | - **Stacked**: No sidebar, vertical stack (header → content → footer)
-- |
-- | ## Scroll Behaviors
-- |
-- | - **PageScroll**: Entire page scrolls as one unit
-- | - **ContentOnly**: Only main content scrolls, header/sidebar fixed
-- | - **IndependentScroll**: Sidebar and content scroll independently
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Layout.AppShell as AppShell
-- |
-- | -- Basic app shell
-- | AppShell.appShell []
-- |   { header: Just navbar
-- |   , sidebar: Just navigation
-- |   , content: mainContent
-- |   , footer: Just footerContent
-- |   }
-- |
-- | -- Collapsible sidebar with custom dimensions
-- | AppShell.appShell
-- |   [ AppShell.sidebarWidth (Spacing.spacingValue 280.0)
-- |   , AppShell.sidebarCollapsible true
-- |   , AppShell.sidebarCollapsed state.collapsed
-- |   , AppShell.onSidebarCollapse \c -> setState { collapsed: c }
-- |   ]
-- |   slots
-- | ```

module Hydrogen.Element.Layout.AppShell
  ( -- * Component
    appShell
  
  -- * Re-exports from Types
  , module Hydrogen.Element.Layout.AppShell.Types
  ) where

import Prelude
  ( (<>)
  , ($)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Just, Nothing))

import Hydrogen.Render.Element (Element)
import Hydrogen.Render.Element as E
import Hydrogen.Schema.Geometry.Spacing as Spacing

import Hydrogen.Element.Layout.AppShell.Types
  ( Layout(SidebarFirst, HeaderFirst, Stacked)
  , ScrollBehavior(PageScroll, ContentOnly, IndependentScroll)
  , SidebarPosition(LeftSide, RightSide)
  , AppShellSlots
  , AppShellProps
  , AppShellProp
  , defaultProps
  , layout
  , scrollBehavior
  , mobileBreakpoint
  , fixedHeader
  , fixedSidebar
  , fixedFooter
  , headerHeight
  , footerHeight
  , sidebarWidth
  , sidebarMiniWidth
  , sidebarPosition
  , sidebarCollapsible
  , sidebarCollapsed
  , sidebarMiniMode
  , onSidebarCollapse
  , className
  , headerClassName
  , sidebarClassName
  , contentClassName
  , footerClassName
  )

import Hydrogen.Element.Layout.AppShell.Styles as Styles
import Hydrogen.Schema.Reactive.Viewport (Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // component
-- ═════════════════════════════════════════════════════════════════════════════

-- | Application shell layout component.
-- |
-- | Provides a complete application layout with configurable header, sidebar,
-- | content, and footer slots. Handles responsive behavior, fixed positioning,
-- | and scroll management.
-- |
-- | All dimensions use Schema atoms (`SpacingValue`) for type safety.
appShell :: forall msg. Array AppShellProp -> AppShellSlots msg -> Element msg
appShell propMods slots =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    -- Calculate effective sidebar width
    effectiveWidth = Styles.effectiveSidebarWidth
      { collapsed: props.sidebarCollapsed
      , miniMode: props.sidebarMiniMode
      , fullWidth: props.sidebarWidth
      , miniWidth: props.sidebarMiniWidth
      }
  in
    case props.layout of
      HeaderFirst -> renderHeaderFirst props effectiveWidth slots
      SidebarFirst -> renderSidebarFirst props effectiveWidth slots
      Stacked -> renderStacked props slots

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // render: header first
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render HeaderFirst layout.
-- |
-- | Structure:
-- | ```
-- | ┌─────────────────────────────────────┐
-- | │             HEADER                  │
-- | ├──────────┬──────────────────────────┤
-- | │          │                          │
-- | │ SIDEBAR  │        CONTENT           │
-- | │          │                          │
-- | ├──────────┴──────────────────────────┤
-- | │             FOOTER                  │
-- | └─────────────────────────────────────┘
-- | ```
renderHeaderFirst 
  :: forall msg. AppShellProps -> Spacing.SpacingValue -> AppShellSlots msg -> Element msg
renderHeaderFirst props sidebarW slots =
  E.div_
    [ E.class_ $ "h-screen w-screen flex flex-col " <> containerOverflowClass props.scrollBehavior <> " " <> props.className
    , E.dataAttr "appshell" "header-first"
    ]
    [ -- Header
      renderHeader props slots.header
      -- Body (sidebar + content)
    , E.div_
        [ E.class_ $ "flex flex-1 min-h-0 " <> flexDirectionClass props.sidebarPosition
        ]
        [ -- Sidebar
          renderSidebar props sidebarW slots.sidebar
          -- Main content wrapper
        , E.div_
            [ E.class_ $ "flex-1 flex flex-col min-w-0 " <> contentOverflowClass props.scrollBehavior <> " " <> props.contentClassName
            , E.dataAttr "appshell-content" "true"
            , E.role "main"
            ]
            [ slots.content
              -- Footer inside content if not fixed
            , case slots.footer of
                Just footer | not props.fixedFooter -> 
                  renderFooterInContent props footer
                _ -> E.empty
            ]
        ]
      -- Fixed footer
    , case slots.footer of
        Just footer | props.fixedFooter -> 
          renderFixedFooter props footer
        _ -> E.empty
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // render: sidebar first
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render SidebarFirst layout.
-- |
-- | Structure:
-- | ```
-- | ┌──────────┬──────────────────────────┐
-- | │          │         HEADER           │
-- | │          ├──────────────────────────┤
-- | │ SIDEBAR  │                          │
-- | │          │        CONTENT           │
-- | │          │                          │
-- | │          ├──────────────────────────┤
-- | │          │         FOOTER           │
-- | └──────────┴──────────────────────────┘
-- | ```
renderSidebarFirst 
  :: forall msg. AppShellProps -> Spacing.SpacingValue -> AppShellSlots msg -> Element msg
renderSidebarFirst props sidebarW slots =
  E.div_
    [ E.class_ $ "h-screen w-screen flex " <> containerOverflowClass props.scrollBehavior <> " " <> flexDirectionClass props.sidebarPosition <> " " <> props.className
    , E.dataAttr "appshell" "sidebar-first"
    ]
    [ -- Sidebar (full height)
      renderSidebarFullHeight props sidebarW slots.sidebar
      -- Right column (header + content + footer)
    , E.div_
        [ E.class_ "flex-1 flex flex-col min-w-0"
        ]
        [ -- Header
          renderHeader props slots.header
          -- Main content
        , E.div_
            [ E.class_ $ "flex-1 min-h-0 " <> contentOverflowClass props.scrollBehavior <> " " <> props.contentClassName
            , E.dataAttr "appshell-content" "true"
            , E.role "main"
            ]
            [ slots.content ]
          -- Footer
        , case slots.footer of
            Just footer -> renderFooterInContent props footer
            Nothing -> E.empty
        ]
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // render: stacked
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render Stacked layout (no sidebar).
-- |
-- | Structure:
-- | ```
-- | ┌─────────────────────────────────────┐
-- | │             HEADER                  │
-- | ├─────────────────────────────────────┤
-- | │                                     │
-- | │            CONTENT                  │
-- | │                                     │
-- | ├─────────────────────────────────────┤
-- | │             FOOTER                  │
-- | └─────────────────────────────────────┘
-- | ```
renderStacked :: forall msg. AppShellProps -> AppShellSlots msg -> Element msg
renderStacked props slots =
  E.div_
    [ E.class_ $ "h-screen w-screen flex flex-col " <> containerOverflowClass props.scrollBehavior <> " " <> props.className
    , E.dataAttr "appshell" "stacked"
    ]
    [ -- Header
      renderHeader props slots.header
      -- Main content
    , E.div_
        [ E.class_ $ "flex-1 min-h-0 " <> contentOverflowClass props.scrollBehavior <> " " <> props.contentClassName
        , E.dataAttr "appshell-content" "true"
        , E.role "main"
        ]
        [ slots.content ]
      -- Footer
    , case slots.footer of
        Just footer | props.fixedFooter -> renderFixedFooter props footer
        Just footer -> renderFooterInContent props footer
        Nothing -> E.empty
    ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // render: slots
-- ═════════════════════════════════════════════════════════════════════════════

-- | Render header slot.
renderHeader :: forall msg. AppShellProps -> Maybe (Element msg) -> Element msg
renderHeader props maybeHeader =
  case maybeHeader of
    Just header ->
      E.header_
        [ E.class_ $ "shrink-0 z-20 bg-background border-b border-border " 
            <> fixedClass props.fixedHeader "top-0" 
            <> " " <> props.headerClassName
        , E.style "height" (Spacing.toLegacyCss props.headerHeight)
        , E.style "min-height" (Spacing.toLegacyCss props.headerHeight)
        ]
        [ header ]
    Nothing -> E.empty

-- | Render sidebar slot (for HeaderFirst layout).
renderSidebar :: forall msg. AppShellProps -> Spacing.SpacingValue -> Maybe (Element msg) -> Element msg
renderSidebar props sidebarW maybeSidebar =
  case maybeSidebar of
    Just sidebarContent ->
      E.aside_
        [ E.class_ $ "shrink-0 bg-background border-border z-10 "
            <> sidebarOverflowClass props.scrollBehavior
            <> " " <> borderClass props.sidebarPosition
            <> " hidden " <> breakpointShowClass props.mobileBreakpoint
            <> " " <> props.sidebarClassName
        , E.style "width" (Spacing.toLegacyCss sidebarW)
        , E.dataAttr "appshell-sidebar" "true"
        ]
        [ sidebarContent ]
    Nothing -> E.empty

-- | Render sidebar slot (for SidebarFirst layout — full height).
renderSidebarFullHeight :: forall msg. AppShellProps -> Spacing.SpacingValue -> Maybe (Element msg) -> Element msg
renderSidebarFullHeight props sidebarW maybeSidebar =
  case maybeSidebar of
    Just sidebarContent ->
      E.aside_
        [ E.class_ $ "shrink-0 flex flex-col bg-background border-border z-20 "
            <> sidebarOverflowClass props.scrollBehavior
            <> " " <> borderClass props.sidebarPosition
            <> " hidden " <> breakpointShowClass props.mobileBreakpoint
            <> " " <> props.sidebarClassName
        , E.style "width" (Spacing.toLegacyCss sidebarW)
        , E.dataAttr "appshell-sidebar" "true"
        ]
        [ sidebarContent ]
    Nothing -> E.empty

-- | Render footer inside content area (non-fixed).
renderFooterInContent :: forall msg. AppShellProps -> Element msg -> Element msg
renderFooterInContent props footer =
  E.footer_
    [ E.class_ $ "shrink-0 bg-background border-t border-border " <> props.footerClassName
    , E.style "min-height" (Spacing.toLegacyCss props.footerHeight)
    ]
    [ footer ]

-- | Render fixed footer (sticky bottom).
renderFixedFooter :: forall msg. AppShellProps -> Element msg -> Element msg
renderFixedFooter props footer =
  E.footer_
    [ E.class_ $ "shrink-0 z-20 bg-background border-t border-border sticky bottom-0 " <> props.footerClassName
    , E.style "min-height" (Spacing.toLegacyCss props.footerHeight)
    ]
    [ footer ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // css helpers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Container overflow class based on scroll behavior.
containerOverflowClass :: ScrollBehavior -> String
containerOverflowClass PageScroll = "overflow-auto"
containerOverflowClass ContentOnly = "overflow-hidden"
containerOverflowClass IndependentScroll = "overflow-hidden"

-- | Content overflow class based on scroll behavior.
contentOverflowClass :: ScrollBehavior -> String
contentOverflowClass PageScroll = ""
contentOverflowClass ContentOnly = "overflow-auto"
contentOverflowClass IndependentScroll = "overflow-auto"

-- | Sidebar overflow class based on scroll behavior.
sidebarOverflowClass :: ScrollBehavior -> String
sidebarOverflowClass PageScroll = ""
sidebarOverflowClass ContentOnly = ""
sidebarOverflowClass IndependentScroll = "overflow-auto"

-- | Flex direction class based on sidebar position.
flexDirectionClass :: SidebarPosition -> String
flexDirectionClass LeftSide = "flex-row"
flexDirectionClass RightSide = "flex-row-reverse"

-- | Border class based on sidebar position.
borderClass :: SidebarPosition -> String
borderClass LeftSide = "border-r"
borderClass RightSide = "border-l"

-- | Fixed positioning class with direction.
fixedClass :: Boolean -> String -> String
fixedClass true direction = "sticky " <> direction
fixedClass false _ = ""

-- | Breakpoint visibility class (show at breakpoint and above).
-- |
-- | Uses Tailwind-style responsive prefixes.
breakpointShowClass :: Breakpoint -> String
breakpointShowClass bp = bpPrefix bp <> "block"
  where
    bpPrefix :: Breakpoint -> String
    bpPrefix Xs = ""
    bpPrefix Sm = "sm:"
    bpPrefix Md = "md:"
    bpPrefix Lg = "lg:"
    bpPrefix Xl = "xl:"
    bpPrefix Xxl = "2xl:"
