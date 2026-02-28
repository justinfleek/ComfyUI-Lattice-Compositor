-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                               // hydrogen // element // sheet
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen Sheet Component
-- |
-- | A slide-out panel that extends from the edge of the viewport.
-- | Similar to a drawer but with more flexibility in sizing and styling.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.Sheet as Sheet
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Basic sheet from right
-- | Sheet.sheet
-- |   [ Sheet.sheetOpen state.showSheet
-- |   , Sheet.side Sheet.SheetRight
-- |   , Sheet.onClose HandleClose
-- |   ]
-- |   [ Sheet.sheetHeader ""
-- |       [ Sheet.sheetTitle "" [ E.text "Settings" ]
-- |       , Sheet.sheetDescription "" [ E.text "Configure your preferences" ]
-- |       ]
-- |   , Sheet.sheetContent "" [ -- Your content here ]
-- |   , Sheet.sheetFooter "" [ Button.button [] [ E.text "Save" ] ]
-- |   ]
-- |
-- | -- Sheet from bottom (like mobile bottom sheet)
-- | Sheet.sheet
-- |   [ Sheet.sheetOpen state.showBottomSheet
-- |   , Sheet.side Sheet.SheetBottom
-- |   , Sheet.sheetSize "h-1/2"
-- |   ]
-- |   [ -- Content ]
-- | ```
module Hydrogen.Element.Compound.Sheet
  ( -- * Sheet Components
    sheet
  , sheetTrigger
  , sheetOverlay
  , sheetContent
  , sheetHeader
  , sheetFooter
  , sheetTitle
  , sheetDescription
  , sheetClose
    -- * Props
  , SheetProps
  , SheetProp
  , defaultProps
    -- * Prop Builders
  , sheetOpen
  , side
  , sheetSize
  , closeOnOverlay
  , showClose
  , className
  , onClose
    -- * Types
  , Side(SheetTop, SheetRight, SheetBottom, SheetLeft)
  ) where

import Prelude
  ( class Eq
  , (<>)
  , not
  )

import Data.Array (foldl)
import Data.Maybe (Maybe(Nothing, Just))
import Hydrogen.Render.Element as E

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // types
-- ═════════════════════════════════════════════════════════════════════════════

-- | Side from which the sheet appears
data Side
  = SheetTop
  | SheetRight
  | SheetBottom
  | SheetLeft

derive instance eqSide :: Eq Side

-- | Get side-specific classes for content positioning
sideContentClasses :: Side -> String
sideContentClasses = case _ of
  SheetTop -> "inset-x-0 top-0 border-b"
  SheetRight -> "inset-y-0 right-0 h-full border-l"
  SheetBottom -> "inset-x-0 bottom-0 border-t"
  SheetLeft -> "inset-y-0 left-0 h-full border-r"

-- | Get side-specific animation classes
sideAnimationClasses :: Side -> String
sideAnimationClasses = case _ of
  SheetTop -> "slide-in-from-top"
  SheetRight -> "slide-in-from-right"
  SheetBottom -> "slide-in-from-bottom"
  SheetLeft -> "slide-in-from-left"

-- | Get default size for each side
defaultSizeForSide :: Side -> String
defaultSizeForSide = case _ of
  SheetTop -> "h-auto max-h-screen"
  SheetRight -> "w-3/4 sm:max-w-sm"
  SheetBottom -> "h-auto max-h-screen"
  SheetLeft -> "w-3/4 sm:max-w-sm"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sheet properties
type SheetProps msg =
  { open :: Boolean
  , side :: Side
  , size :: Maybe String
  , closeOnOverlay :: Boolean
  , showClose :: Boolean
  , className :: String
  , onClose :: Maybe msg
  }

-- | Property modifier
type SheetProp msg = SheetProps msg -> SheetProps msg

-- | Default properties
defaultProps :: forall msg. SheetProps msg
defaultProps =
  { open: false
  , side: SheetRight
  , size: Nothing
  , closeOnOverlay: true
  , showClose: true
  , className: ""
  , onClose: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set open state
sheetOpen :: forall msg. Boolean -> SheetProp msg
sheetOpen o props = props { open = o }

-- | Set side
side :: forall msg. Side -> SheetProp msg
side s props = props { side = s }

-- | Set custom size (width for left/right, height for top/bottom)
sheetSize :: forall msg. String -> SheetProp msg
sheetSize s props = props { size = Just s }

-- | Close on overlay click
closeOnOverlay :: forall msg. Boolean -> SheetProp msg
closeOnOverlay c props = props { closeOnOverlay = c }

-- | Show close button
showClose :: forall msg. Boolean -> SheetProp msg
showClose s props = props { showClose = s }

-- | Add custom class
className :: forall msg. String -> SheetProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set close handler
onClose :: forall msg. msg -> SheetProp msg
onClose handler props = props { onClose = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay classes
overlayClasses :: String
overlayClasses =
  "fixed inset-0 z-50 bg-black/80 animate-in fade-in-0"

-- | Content base classes
contentBaseClasses :: String
contentBaseClasses =
  "fixed z-50 gap-4 bg-background p-6 shadow-lg transition ease-in-out animate-in duration-300"

-- | Header classes
headerClasses :: String
headerClasses =
  "flex flex-col space-y-2"

-- | Footer classes
footerClasses :: String
footerClasses =
  "flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2"

-- | Title classes
titleClasses :: String
titleClasses =
  "text-lg font-semibold text-foreground"

-- | Description classes
descriptionClasses :: String
descriptionClasses =
  "text-sm text-muted-foreground"

-- | Close button classes
closeButtonClasses :: String
closeButtonClasses =
  "absolute right-4 top-4 rounded-sm opacity-70 ring-offset-background transition-opacity hover:opacity-100 focus:outline-none focus:ring-2 focus:ring-ring focus:ring-offset-2 disabled:pointer-events-none"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sheet trigger (for use with uncontrolled pattern)
-- |
-- | A wrapper for the element that opens the sheet.
sheetTrigger :: forall msg. Array (E.Element msg) -> E.Element msg
sheetTrigger children =
  E.span_
    [ E.class_ "inline-block" ]
    children

-- | Sheet overlay (standalone)
-- |
-- | The backdrop behind the sheet.
sheetOverlay :: forall msg. Maybe msg -> E.Element msg
sheetOverlay closeHandler =
  let
    clickHandler = case closeHandler of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    E.div_
      ( [ E.class_ overlayClasses ] <> clickHandler )
      []

-- | Sheet content wrapper (standalone)
-- |
-- | The main content area of the sheet.
sheetContent :: forall msg. String -> Array (E.Element msg) -> E.Element msg
sheetContent customClass children =
  E.div_
    [ E.classes [ contentBaseClasses, customClass ]
    , E.role "dialog"
    ]
    children

-- | Sheet header
-- |
-- | Container for title and description.
sheetHeader :: forall msg. String -> Array (E.Element msg) -> E.Element msg
sheetHeader customClass children =
  E.div_
    [ E.classes [ headerClasses, customClass ] ]
    children

-- | Sheet footer
-- |
-- | Container for action buttons.
sheetFooter :: forall msg. String -> Array (E.Element msg) -> E.Element msg
sheetFooter customClass children =
  E.div_
    [ E.classes [ footerClasses, customClass ] ]
    children

-- | Sheet title
-- |
-- | The sheet's title heading.
sheetTitle :: forall msg. String -> Array (E.Element msg) -> E.Element msg
sheetTitle customClass children =
  E.h2_
    [ E.classes [ titleClasses, customClass ] ]
    children

-- | Sheet description
-- |
-- | The sheet's description text.
sheetDescription :: forall msg. String -> Array (E.Element msg) -> E.Element msg
sheetDescription customClass children =
  E.p_
    [ E.classes [ descriptionClasses, customClass ] ]
    children

-- | Sheet close button
-- |
-- | A close button for the sheet.
sheetClose :: forall msg. Maybe msg -> E.Element msg
sheetClose closeHandler =
  let
    clickHandler = case closeHandler of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    E.button_
      ( [ E.class_ closeButtonClasses
        , E.attr "type" "button"
        , E.ariaLabel "Close"
        ] <> clickHandler
      )
      [ closeIcon ]

-- | Full sheet component
-- |
-- | A slide-out panel with overlay, close button, and content.
-- | Renders nothing when closed.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
sheet :: forall msg. Array (SheetProp msg) -> Array (E.Element msg) -> E.Element msg
sheet propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    sizeClass = case props.size of
      Just s -> s
      Nothing -> defaultSizeForSide props.side
    
    contentCls = 
      contentBaseClasses 
      <> " " <> sideContentClasses props.side
      <> " " <> sideAnimationClasses props.side
      <> " " <> sizeClass
      <> " " <> props.className
    
    overlayHandler = 
      if props.closeOnOverlay
        then props.onClose
        else Nothing
    
    closeBtn = if props.showClose
      then [ sheetClose props.onClose ]
      else []
  in
    if not props.open
      then E.text ""
      else
        E.div_
          [ E.class_ "relative z-50" ]
          [ sheetOverlay overlayHandler
          , E.div_
              [ E.class_ contentCls
              , E.role "dialog"
              , E.attr "aria-modal" "true"
              ]
              ( children <> closeBtn )
          ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // icons
-- ═════════════════════════════════════════════════════════════════════════════

-- | Close (X) icon
closeIcon :: forall msg. E.Element msg
closeIcon =
  E.svg_
    [ E.class_ "h-4 w-4"
    , E.attr "xmlns" "http://www.w3.org/2000/svg"
    , E.attr "viewBox" "0 0 24 24"
    , E.attr "fill" "none"
    , E.attr "stroke" "currentColor"
    , E.attr "stroke-width" "2"
    , E.attr "stroke-linecap" "round"
    , E.attr "stroke-linejoin" "round"
    ]
    [ E.line_ [ E.attr "x1" "18", E.attr "y1" "6", E.attr "x2" "6", E.attr "y2" "18" ]
    , E.line_ [ E.attr "x1" "6", E.attr "y1" "6", E.attr "x2" "18", E.attr "y2" "18" ]
    ]
