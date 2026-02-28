-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                        // hydrogen // element // layout // appshell // styles
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | AppShell Styles — CSS generation from Schema atoms.
-- |
-- | ## Design Philosophy
-- |
-- | All CSS is generated from Schema atoms. This module serves as the bridge
-- | between type-safe Schema values and legacy CSS output. Functions are named
-- | `toLegacyCss` to acknowledge CSS is a legacy output format.
-- |
-- | ## Why Generate CSS?
-- |
-- | Until Hydrogen targets render directly to GPU, we output to CSS as an
-- | intermediate step. The Schema atoms remain the source of truth; CSS is
-- | just a rendering target.

module Hydrogen.Element.Layout.AppShell.Styles
  ( -- * Computed Values
    effectiveSidebarWidth
  
  -- * Overflow CSS
  , containerOverflowCss
  , contentOverflowCss
  , sidebarOverflowCss
  
  -- * Positioning CSS
  , fixedPositionCss
  , stickyTopCss
  , stickyBottomCss
  
  -- * Dimension CSS
  , heightCss
  , widthCss
  , minHeightCss
  
  -- * Flex Direction CSS
  , flexDirectionCss
  
  -- * Border CSS
  , borderSideCss
  
  -- * Responsive CSS
  , breakpointVisibilityCss
  , breakpointClass
  
  -- * Data Attributes
  , dataAttribute
  ) where

import Prelude
  ( (<>)
  , show
  )

import Hydrogen.Schema.Geometry.Spacing (SpacingValue)
import Hydrogen.Schema.Geometry.Spacing as Spacing
import Hydrogen.Schema.Reactive.Viewport (Breakpoint(Xs, Sm, Md, Lg, Xl, Xxl))

import Hydrogen.Element.Layout.AppShell.Types
  ( ScrollBehavior(PageScroll, ContentOnly, IndependentScroll)
  , SidebarPosition(LeftSide, RightSide)
  )

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // computed values
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculate effective sidebar width based on collapse state.
-- |
-- | - Not collapsed: full width
-- | - Collapsed + mini mode: mini width
-- | - Collapsed + no mini mode: zero width
effectiveSidebarWidth 
  :: { collapsed :: Boolean
     , miniMode :: Boolean
     , fullWidth :: SpacingValue
     , miniWidth :: SpacingValue
     }
  -> SpacingValue
effectiveSidebarWidth cfg =
  if cfg.collapsed
    then if cfg.miniMode 
         then cfg.miniWidth
         else Spacing.spacingZero
    else cfg.fullWidth

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // overflow css
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS overflow for shell container based on scroll behavior.
containerOverflowCss :: ScrollBehavior -> String
containerOverflowCss PageScroll = "overflow: auto;"
containerOverflowCss ContentOnly = "overflow: hidden;"
containerOverflowCss IndependentScroll = "overflow: hidden;"

-- | CSS overflow for content area based on scroll behavior.
contentOverflowCss :: ScrollBehavior -> String
contentOverflowCss PageScroll = ""
contentOverflowCss ContentOnly = "overflow-y: auto; overflow-x: hidden;"
contentOverflowCss IndependentScroll = "overflow-y: auto; overflow-x: hidden;"

-- | CSS overflow for sidebar based on scroll behavior.
sidebarOverflowCss :: ScrollBehavior -> String
sidebarOverflowCss PageScroll = ""
sidebarOverflowCss ContentOnly = ""
sidebarOverflowCss IndependentScroll = "overflow-y: auto; overflow-x: hidden;"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // positioning css
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS for fixed positioning.
fixedPositionCss :: Boolean -> String
fixedPositionCss true = "position: sticky;"
fixedPositionCss false = "position: relative;"

-- | CSS for sticky top positioning.
stickyTopCss :: Boolean -> String
stickyTopCss true = "position: sticky; top: 0;"
stickyTopCss false = ""

-- | CSS for sticky bottom positioning.
stickyBottomCss :: Boolean -> String
stickyBottomCss true = "position: sticky; bottom: 0;"
stickyBottomCss false = ""

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // dimension css
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS height from SpacingValue.
heightCss :: SpacingValue -> String
heightCss sv = "height: " <> Spacing.toLegacyCss sv <> ";"

-- | CSS width from SpacingValue.
widthCss :: SpacingValue -> String
widthCss sv = "width: " <> Spacing.toLegacyCss sv <> ";"

-- | CSS min-height from SpacingValue.
minHeightCss :: SpacingValue -> String
minHeightCss sv = "min-height: " <> Spacing.toLegacyCss sv <> ";"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // flex direction css
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS flex-direction based on sidebar position.
-- |
-- | When sidebar is on the right, reverse the flex direction so content
-- | comes first in DOM but sidebar appears on right visually.
flexDirectionCss :: SidebarPosition -> String
flexDirectionCss LeftSide = "flex-direction: row;"
flexDirectionCss RightSide = "flex-direction: row-reverse;"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // border css
-- ═════════════════════════════════════════════════════════════════════════════

-- | CSS border on appropriate side based on sidebar position.
-- |
-- | Sidebar on left gets right border; sidebar on right gets left border.
borderSideCss :: SidebarPosition -> String
borderSideCss LeftSide = "border-right: 1px solid var(--border-color, #e5e7eb);"
borderSideCss RightSide = "border-left: 1px solid var(--border-color, #e5e7eb);"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // responsive css
-- ═════════════════════════════════════════════════════════════════════════════

-- | Generate responsive visibility class for breakpoint.
-- |
-- | Returns CSS that hides element below breakpoint and shows at/above.
-- | Uses CSS media queries with breakpoint values from Schema.
breakpointVisibilityCss :: Breakpoint -> String
breakpointVisibilityCss bp =
  let
    minWidth = breakpointMinWidth bp
  in
    "display: none; " <>
    "@media (min-width: " <> show minWidth <> "px) { display: flex; }"

-- | Get minimum width in pixels for a breakpoint.
-- |
-- | Uses same values as Hydrogen.Schema.Reactive.Viewport.
breakpointMinWidth :: Breakpoint -> Int
breakpointMinWidth Xs = 0
breakpointMinWidth Sm = 640
breakpointMinWidth Md = 768
breakpointMinWidth Lg = 1024
breakpointMinWidth Xl = 1280
breakpointMinWidth Xxl = 1536

-- | Tailwind-style breakpoint class prefix.
-- |
-- | Used for escape hatch integration with Tailwind CSS.
breakpointClass :: Breakpoint -> String
breakpointClass Xs = ""
breakpointClass Sm = "sm:"
breakpointClass Md = "md:"
breakpointClass Lg = "lg:"
breakpointClass Xl = "xl:"
breakpointClass Xxl = "2xl:"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // data attributes
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create a data attribute string.
-- |
-- | ```purescript
-- | dataAttribute "appshell" "header-first"
-- | -- => "data-appshell=\"header-first\""
-- | ```
dataAttribute :: String -> String -> String
dataAttribute name value = "data-" <> name <> "=\"" <> value <> "\""
