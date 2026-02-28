-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                            // hydrogen // element // compound // alert-dialog
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Pure Hydrogen AlertDialog Component
-- |
-- | A modal dialog for confirmations and alerts with action buttons.
-- | Based on WAI-ARIA alertdialog role.
-- | Pure Element — no Halogen dependency.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Element.Compound.AlertDialog as AlertDialog
-- | import Hydrogen.Render.Element as E
-- |
-- | -- Confirmation dialog
-- | AlertDialog.alertDialog
-- |   [ AlertDialog.dialogOpen state.showConfirm
-- |   , AlertDialog.dialogTitle "Are you sure?"
-- |   , AlertDialog.dialogDescription "This action cannot be undone."
-- |   , AlertDialog.confirmLabel "Delete"
-- |   , AlertDialog.cancelLabel "Cancel"
-- |   , AlertDialog.dialogVariant AlertDialog.Destructive
-- |   , AlertDialog.onConfirm HandleConfirm
-- |   , AlertDialog.onCancel HandleCancel
-- |   ]
-- |
-- | -- Info dialog (single action)
-- | AlertDialog.alertDialog
-- |   [ AlertDialog.dialogOpen state.showInfo
-- |   , AlertDialog.dialogTitle "Information"
-- |   , AlertDialog.dialogDescription "Your session will expire in 5 minutes."
-- |   , AlertDialog.confirmLabel "OK"
-- |   , AlertDialog.showCancel false
-- |   , AlertDialog.onConfirm HandleOK
-- |   ]
-- | ```
module Hydrogen.Element.Compound.AlertDialog
  ( -- * AlertDialog Components
    alertDialog
  , alertDialogCustom
  , alertDialogTrigger
  , alertDialogContent
  , alertDialogHeader
  , alertDialogFooter
  , alertDialogTitle
  , alertDialogDescription
  , alertDialogAction
  , alertDialogCancel
    -- * Props
  , AlertDialogProps
  , AlertDialogProp
  , defaultProps
    -- * Prop Builders
  , dialogOpen
  , dialogTitle
  , dialogDescription
  , confirmLabel
  , cancelLabel
  , dialogVariant
  , showCancel
  , closeOnOverlay
  , className
  , onConfirm
  , onCancel
  , onClose
    -- * Variants
  , AlertDialogVariant(Default, Destructive, Warning, Info)
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
--                                                                   // variants
-- ═════════════════════════════════════════════════════════════════════════════

-- | AlertDialog variants
data AlertDialogVariant
  = Default
  | Destructive
  | Warning
  | Info

derive instance eqAlertDialogVariant :: Eq AlertDialogVariant

-- | Get confirm button variant classes
confirmButtonClasses :: AlertDialogVariant -> String
confirmButtonClasses = case _ of
  Default ->
    "bg-primary text-primary-foreground hover:bg-primary/90"
  Destructive ->
    "bg-destructive text-destructive-foreground hover:bg-destructive/90"
  Warning ->
    "bg-yellow-500 text-white hover:bg-yellow-600"
  Info ->
    "bg-blue-500 text-white hover:bg-blue-600"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                      // props
-- ═════════════════════════════════════════════════════════════════════════════

-- | AlertDialog properties
type AlertDialogProps msg =
  { open :: Boolean
  , title :: String
  , description :: String
  , confirmLabel :: String
  , cancelLabel :: String
  , variant :: AlertDialogVariant
  , showCancel :: Boolean
  , closeOnOverlay :: Boolean
  , className :: String
  , onConfirm :: Maybe msg
  , onCancel :: Maybe msg
  , onClose :: Maybe msg
  }

-- | Property modifier
type AlertDialogProp msg = AlertDialogProps msg -> AlertDialogProps msg

-- | Default properties
defaultProps :: forall msg. AlertDialogProps msg
defaultProps =
  { open: false
  , title: ""
  , description: ""
  , confirmLabel: "Confirm"
  , cancelLabel: "Cancel"
  , variant: Default
  , showCancel: true
  , closeOnOverlay: true
  , className: ""
  , onConfirm: Nothing
  , onCancel: Nothing
  , onClose: Nothing
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // prop builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Set open state
dialogOpen :: forall msg. Boolean -> AlertDialogProp msg
dialogOpen o props = props { open = o }

-- | Set title
dialogTitle :: forall msg. String -> AlertDialogProp msg
dialogTitle t props = props { title = t }

-- | Set description
dialogDescription :: forall msg. String -> AlertDialogProp msg
dialogDescription d props = props { description = d }

-- | Set confirm button label
confirmLabel :: forall msg. String -> AlertDialogProp msg
confirmLabel l props = props { confirmLabel = l }

-- | Set cancel button label
cancelLabel :: forall msg. String -> AlertDialogProp msg
cancelLabel l props = props { cancelLabel = l }

-- | Set variant
dialogVariant :: forall msg. AlertDialogVariant -> AlertDialogProp msg
dialogVariant v props = props { variant = v }

-- | Show/hide cancel button
showCancel :: forall msg. Boolean -> AlertDialogProp msg
showCancel s props = props { showCancel = s }

-- | Close on overlay click
closeOnOverlay :: forall msg. Boolean -> AlertDialogProp msg
closeOnOverlay c props = props { closeOnOverlay = c }

-- | Add custom class
className :: forall msg. String -> AlertDialogProp msg
className c props = props { className = props.className <> " " <> c }

-- | Set confirm handler
onConfirm :: forall msg. msg -> AlertDialogProp msg
onConfirm handler props = props { onConfirm = Just handler }

-- | Set cancel handler
onCancel :: forall msg. msg -> AlertDialogProp msg
onCancel handler props = props { onCancel = Just handler }

-- | Set close handler (fired on overlay click)
onClose :: forall msg. msg -> AlertDialogProp msg
onClose handler props = props { onClose = Just handler }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // styling
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overlay classes
overlayClasses :: String
overlayClasses =
  "fixed inset-0 z-50 bg-black/80 animate-in fade-in-0"

-- | Content container classes
contentClasses :: String
contentClasses =
  "fixed left-[50%] top-[50%] z-50 grid w-full max-w-lg translate-x-[-50%] translate-y-[-50%] gap-4 border bg-background p-6 shadow-lg duration-200 animate-in fade-in-0 zoom-in-95 slide-in-from-left-1/2 slide-in-from-top-[48%] sm:rounded-lg"

-- | Header classes
headerClasses :: String
headerClasses =
  "flex flex-col space-y-2 text-center sm:text-left"

-- | Footer classes
footerClasses :: String
footerClasses =
  "flex flex-col-reverse sm:flex-row sm:justify-end sm:space-x-2"

-- | Title classes
titleClasses :: String
titleClasses =
  "text-lg font-semibold"

-- | Description classes
descriptionClasses :: String
descriptionClasses =
  "text-sm text-muted-foreground"

-- | Base button classes
buttonBaseClasses :: String
buttonBaseClasses =
  "inline-flex items-center justify-center whitespace-nowrap rounded-md text-sm font-medium ring-offset-background transition-colors focus-visible:outline-none focus-visible:ring-2 focus-visible:ring-ring focus-visible:ring-offset-2 disabled:pointer-events-none disabled:opacity-50 h-10 px-4 py-2"

-- | Cancel button classes
cancelButtonClasses :: String
cancelButtonClasses =
  "mt-2 sm:mt-0 border border-input bg-background hover:bg-accent hover:text-accent-foreground"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // components
-- ═════════════════════════════════════════════════════════════════════════════

-- | AlertDialog trigger (for use with uncontrolled pattern)
-- |
-- | A wrapper for the element that opens the dialog.
alertDialogTrigger :: forall msg. Array (E.Element msg) -> E.Element msg
alertDialogTrigger children =
  E.span_
    [ E.class_ "inline-block" ]
    children

-- | AlertDialog content wrapper
-- |
-- | The main content container for custom layouts.
alertDialogContent :: forall msg. String -> Array (E.Element msg) -> E.Element msg
alertDialogContent customClass children =
  E.div_
    [ E.classes [ contentClasses, customClass ]
    , E.role "alertdialog"
    , E.attr "aria-modal" "true"
    ]
    children

-- | AlertDialog header
-- |
-- | Container for title and description.
alertDialogHeader :: forall msg. Array (E.Element msg) -> E.Element msg
alertDialogHeader children =
  E.div_
    [ E.class_ headerClasses ]
    children

-- | AlertDialog footer
-- |
-- | Container for action buttons.
alertDialogFooter :: forall msg. Array (E.Element msg) -> E.Element msg
alertDialogFooter children =
  E.div_
    [ E.class_ footerClasses ]
    children

-- | AlertDialog title
-- |
-- | The dialog's title text.
alertDialogTitle :: forall msg. String -> E.Element msg
alertDialogTitle text =
  E.h2_
    [ E.class_ titleClasses
    , E.id_ "alert-dialog-title"
    ]
    [ E.text text ]

-- | AlertDialog description
-- |
-- | The dialog's description text.
alertDialogDescription :: forall msg. String -> E.Element msg
alertDialogDescription text =
  E.p_
    [ E.class_ descriptionClasses
    , E.id_ "alert-dialog-description"
    ]
    [ E.text text ]

-- | AlertDialog action button
-- |
-- | The primary action button (confirm/proceed).
alertDialogAction :: forall msg. 
  { label :: String, variant :: AlertDialogVariant, onClick :: Maybe msg } -> 
  E.Element msg
alertDialogAction opts =
  let
    clickHandler = case opts.onClick of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    E.button_
      ( [ E.classes [ buttonBaseClasses, confirmButtonClasses opts.variant ]
        , E.attr "type" "button"
        ] <> clickHandler
      )
      [ E.text opts.label ]

-- | AlertDialog cancel button
-- |
-- | The secondary action button (cancel/dismiss).
alertDialogCancel :: forall msg. 
  { label :: String, onClick :: Maybe msg } -> 
  E.Element msg
alertDialogCancel opts =
  let
    clickHandler = case opts.onClick of
      Just handler -> [ E.onClick handler ]
      Nothing -> []
  in
    E.button_
      ( [ E.classes [ buttonBaseClasses, cancelButtonClasses ]
        , E.attr "type" "button"
        ] <> clickHandler
      )
      [ E.text opts.label ]

-- | Full AlertDialog with standard layout
-- |
-- | A complete alert dialog with title, description, and action buttons.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
alertDialog :: forall msg. Array (AlertDialogProp msg) -> E.Element msg
alertDialog propMods =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    overlayHandler = 
      if props.closeOnOverlay
        then case props.onClose of
          Just handler -> [ E.onClick handler ]
          Nothing -> case props.onCancel of
            Just handler -> [ E.onClick handler ]
            Nothing -> []
        else []
    
    cancelHandler = case props.onCancel of
      Just handler -> Just handler
      Nothing -> props.onClose
    
    cancelBtn = if props.showCancel
      then [ alertDialogCancel 
               { label: props.cancelLabel
               , onClick: cancelHandler
               }
           ]
      else []
    
    confirmBtn = [ alertDialogAction
                     { label: props.confirmLabel
                     , variant: props.variant
                     , onClick: props.onConfirm
                     }
                 ]
  in
    if not props.open
      then E.text ""
      else
        E.div_
          [ E.class_ "relative z-50" ]
          [ E.div_
              ( [ E.class_ overlayClasses ] <> overlayHandler )
              []
          , E.div_
              [ E.classes [ contentClasses, props.className ]
              , E.role "alertdialog"
              , E.attr "aria-modal" "true"
              , E.ariaLabelledBy "alert-dialog-title"
              , E.ariaDescribedBy "alert-dialog-description"
              ]
              [ alertDialogHeader
                  [ alertDialogTitle props.title
                  , alertDialogDescription props.description
                  ]
              , alertDialogFooter
                  ( cancelBtn <> confirmBtn )
              ]
          ]

-- | AlertDialog with custom content
-- |
-- | An alert dialog that accepts custom content instead of standard layout.
-- | Pure Element — can be rendered to DOM, Halogen, Static HTML, or any target.
alertDialogCustom :: forall msg. 
  Array (AlertDialogProp msg) -> 
  Array (E.Element msg) -> 
  E.Element msg
alertDialogCustom propMods children =
  let
    props = foldl (\p f -> f p) defaultProps propMods
    
    overlayHandler = 
      if props.closeOnOverlay
        then case props.onClose of
          Just handler -> [ E.onClick handler ]
          Nothing -> []
        else []
  in
    if not props.open
      then E.text ""
      else
        E.div_
          [ E.class_ "relative z-50" ]
          [ E.div_
              ( [ E.class_ overlayClasses ] <> overlayHandler )
              []
          , E.div_
              [ E.classes [ contentClasses, props.className ]
              , E.role "alertdialog"
              , E.attr "aria-modal" "true"
              ]
              children
          ]
