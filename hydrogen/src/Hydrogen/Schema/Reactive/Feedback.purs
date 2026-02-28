-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                 // hydrogen // schema // reactive // feedback
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Feedback - notification and messaging atoms.
-- |
-- | Models toast, snackbar, banner, alert, and dialog patterns
-- | for user feedback and system messaging.

module Hydrogen.Schema.Reactive.Feedback
  ( -- * Feedback Type
    FeedbackType(..)
  , isToast
  , isSnackbar
  , isBanner
  , isAlert
  , isDialog
  -- * Feedback Severity
  , FeedbackSeverity(..)
  , isFeedbackSuccess
  , isFeedbackInfo
  , isFeedbackWarning
  , isFeedbackError
  , isFeedbackNeutral
  -- * Feedback Position
  , FeedbackPosition(..)
  , isTopLeft
  , isTopCenter
  , isTopRight
  , isBottomLeft
  , isBottomCenter
  , isBottomRight
  -- * Duration
  , FeedbackDuration(..)
  , isShort
  , isMedium
  , isLong
  , isPersistent
  , durationMs
  -- * Dismissal
  , DismissalMethod(..)
  , isAutoDismiss
  , isManualDismiss
  , isActionDismiss
  , isSwipeDismiss
  -- * Action Button
  , FeedbackAction
  , feedbackAction
  , undoAction
  , retryAction
  , dismissAction
  , actionLabel
  -- * Toast (Molecule)
  , Toast
  , toast
  , successToast
  , errorToast
  , infoToast
  , warningToast
  -- * Snackbar (Molecule)
  , Snackbar
  , snackbar
  , snackbarWithAction
  , snackbarWithUndo
  -- * Banner (Molecule)
  , Banner
  , banner
  , infoBanner
  , warningBanner
  , errorBanner
  -- * Alert (Molecule)
  , Alert
  , alert
  , inlineAlert
  , alertWithActions
  -- * Dialog (Compound)
  , DialogType(..)
  , isConfirmDialog
  , isAlertDialog
  , isPromptDialog
  , Dialog
  , dialog
  , confirmDialog
  , alertDialog
  , destructiveDialog
  -- * Notification Queue (Compound)
  , NotificationQueue
  , emptyQueue
  , enqueue
  , dequeue
  , queueLength
  , currentNotification
  -- * Computed Properties
  , shouldAutoDismiss
  , hasAction
  , isBlocking
  -- * Tooltip (Molecule)
  , TooltipPlacement(..)
  , Tooltip
  , tooltip
  , simpleTooltip
  , interactiveTooltip
  -- * Popover (Molecule)
  , PopoverTrigger(..)
  , Popover
  , popover
  , popoverWithTitle
  , isPopoverOpen
  , openPopover
  , closePopover
  -- * Drawer (Molecule)
  , DrawerPosition(..)
  , Drawer
  , drawer
  , navigationDrawer
  , sidePanelDrawer
  , isDrawerOpen
  , openDrawer
  , closeDrawer
  , toggleDrawer
  -- * Sheet (Molecule)
  , SheetSnapPoint(..)
  , Sheet
  , sheet
  , standardSheet
  , multiDetentSheet
  , isSheetOpen
  , openSheet
  , closeSheet
  , snapSheet
  ) where

import Prelude

import Data.Array (drop, head, length, snoc)
import Data.Maybe (Maybe(Just, Nothing), isJust)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // feedback type
-- ═════════════════════════════════════════════════════════════════════════════

-- | Type of feedback notification
data FeedbackType
  = ToastType      -- ^ Brief, non-blocking notification
  | SnackbarType   -- ^ Brief with optional action
  | BannerType     -- ^ Persistent top/bottom message
  | AlertType      -- ^ Inline alert box
  | DialogType'    -- ^ Modal dialog (named with ' to avoid conflict)

derive instance eqFeedbackType :: Eq FeedbackType
derive instance ordFeedbackType :: Ord FeedbackType

instance showFeedbackType :: Show FeedbackType where
  show ToastType = "toast"
  show SnackbarType = "snackbar"
  show BannerType = "banner"
  show AlertType = "alert"
  show DialogType' = "dialog"

isToast :: FeedbackType -> Boolean
isToast ToastType = true
isToast _ = false

isSnackbar :: FeedbackType -> Boolean
isSnackbar SnackbarType = true
isSnackbar _ = false

isBanner :: FeedbackType -> Boolean
isBanner BannerType = true
isBanner _ = false

isAlert :: FeedbackType -> Boolean
isAlert AlertType = true
isAlert _ = false

isDialog :: FeedbackType -> Boolean
isDialog DialogType' = true
isDialog _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // feedback severity
-- ═════════════════════════════════════════════════════════════════════════════

-- | Severity/intent of feedback
data FeedbackSeverity
  = FeedbackSuccess   -- ^ Operation succeeded
  | FeedbackInfo      -- ^ Informational message
  | FeedbackWarning   -- ^ Warning/caution
  | FeedbackError     -- ^ Error occurred
  | FeedbackNeutral   -- ^ No specific severity

derive instance eqFeedbackSeverity :: Eq FeedbackSeverity
derive instance ordFeedbackSeverity :: Ord FeedbackSeverity

instance showFeedbackSeverity :: Show FeedbackSeverity where
  show FeedbackSuccess = "success"
  show FeedbackInfo = "info"
  show FeedbackWarning = "warning"
  show FeedbackError = "error"
  show FeedbackNeutral = "neutral"

isFeedbackSuccess :: FeedbackSeverity -> Boolean
isFeedbackSuccess FeedbackSuccess = true
isFeedbackSuccess _ = false

isFeedbackInfo :: FeedbackSeverity -> Boolean
isFeedbackInfo FeedbackInfo = true
isFeedbackInfo _ = false

isFeedbackWarning :: FeedbackSeverity -> Boolean
isFeedbackWarning FeedbackWarning = true
isFeedbackWarning _ = false

isFeedbackError :: FeedbackSeverity -> Boolean
isFeedbackError FeedbackError = true
isFeedbackError _ = false

isFeedbackNeutral :: FeedbackSeverity -> Boolean
isFeedbackNeutral FeedbackNeutral = true
isFeedbackNeutral _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // feedback position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Screen position for feedback
data FeedbackPosition
  = TopLeft
  | TopCenter
  | TopRight
  | BottomLeft
  | BottomCenter
  | BottomRight

derive instance eqFeedbackPosition :: Eq FeedbackPosition
derive instance ordFeedbackPosition :: Ord FeedbackPosition

instance showFeedbackPosition :: Show FeedbackPosition where
  show TopLeft = "top-left"
  show TopCenter = "top-center"
  show TopRight = "top-right"
  show BottomLeft = "bottom-left"
  show BottomCenter = "bottom-center"
  show BottomRight = "bottom-right"

isTopLeft :: FeedbackPosition -> Boolean
isTopLeft TopLeft = true
isTopLeft _ = false

isTopCenter :: FeedbackPosition -> Boolean
isTopCenter TopCenter = true
isTopCenter _ = false

isTopRight :: FeedbackPosition -> Boolean
isTopRight TopRight = true
isTopRight _ = false

isBottomLeft :: FeedbackPosition -> Boolean
isBottomLeft BottomLeft = true
isBottomLeft _ = false

isBottomCenter :: FeedbackPosition -> Boolean
isBottomCenter BottomCenter = true
isBottomCenter _ = false

isBottomRight :: FeedbackPosition -> Boolean
isBottomRight BottomRight = true
isBottomRight _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // duration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Display duration for auto-dismissing feedback
data FeedbackDuration
  = DurationShort       -- ^ ~2 seconds
  | DurationMedium      -- ^ ~4 seconds
  | DurationLong        -- ^ ~8 seconds
  | DurationPersistent  -- ^ Never auto-dismiss

derive instance eqFeedbackDuration :: Eq FeedbackDuration
derive instance ordFeedbackDuration :: Ord FeedbackDuration

instance showFeedbackDuration :: Show FeedbackDuration where
  show DurationShort = "short"
  show DurationMedium = "medium"
  show DurationLong = "long"
  show DurationPersistent = "persistent"

isShort :: FeedbackDuration -> Boolean
isShort DurationShort = true
isShort _ = false

isMedium :: FeedbackDuration -> Boolean
isMedium DurationMedium = true
isMedium _ = false

isLong :: FeedbackDuration -> Boolean
isLong DurationLong = true
isLong _ = false

isPersistent :: FeedbackDuration -> Boolean
isPersistent DurationPersistent = true
isPersistent _ = false

-- | Get duration in milliseconds
durationMs :: FeedbackDuration -> Maybe Number
durationMs DurationShort = Just 2000.0
durationMs DurationMedium = Just 4000.0
durationMs DurationLong = Just 8000.0
durationMs DurationPersistent = Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // dismissal
-- ═════════════════════════════════════════════════════════════════════════════

-- | How feedback can be dismissed
data DismissalMethod
  = AutoDismiss     -- ^ Dismissed after duration
  | ManualDismiss   -- ^ Requires explicit close action
  | ActionDismiss   -- ^ Dismissed when action taken
  | SwipeDismiss    -- ^ Can be swiped away (mobile)

derive instance eqDismissalMethod :: Eq DismissalMethod
derive instance ordDismissalMethod :: Ord DismissalMethod

instance showDismissalMethod :: Show DismissalMethod where
  show AutoDismiss = "auto"
  show ManualDismiss = "manual"
  show ActionDismiss = "action"
  show SwipeDismiss = "swipe"

isAutoDismiss :: DismissalMethod -> Boolean
isAutoDismiss AutoDismiss = true
isAutoDismiss _ = false

isManualDismiss :: DismissalMethod -> Boolean
isManualDismiss ManualDismiss = true
isManualDismiss _ = false

isActionDismiss :: DismissalMethod -> Boolean
isActionDismiss ActionDismiss = true
isActionDismiss _ = false

isSwipeDismiss :: DismissalMethod -> Boolean
isSwipeDismiss SwipeDismiss = true
isSwipeDismiss _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // action button
-- ═════════════════════════════════════════════════════════════════════════════

-- | Action button for feedback
type FeedbackAction =
  { label :: String
  , actionId :: String
  , dismissOnAction :: Boolean
  }

-- | Create feedback action
feedbackAction :: String -> String -> Boolean -> FeedbackAction
feedbackAction label actionId dismissOnAction =
  { label, actionId, dismissOnAction }

-- | Standard undo action
undoAction :: FeedbackAction
undoAction = feedbackAction "Undo" "undo" true

-- | Standard retry action
retryAction :: FeedbackAction
retryAction = feedbackAction "Retry" "retry" true

-- | Standard dismiss action
dismissAction :: FeedbackAction
dismissAction = feedbackAction "Dismiss" "dismiss" true

-- | Get action label
actionLabel :: FeedbackAction -> String
actionLabel a = a.label

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // toast molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Toast notification
type Toast =
  { id :: String
  , message :: String
  , severity :: FeedbackSeverity
  , duration :: FeedbackDuration
  , position :: FeedbackPosition
  , dismissible :: Boolean
  }

-- | Create toast
toast :: String -> String -> FeedbackSeverity -> Toast
toast id message severity =
  { id
  , message
  , severity
  , duration: DurationMedium
  , position: BottomCenter
  , dismissible: true
  }

-- | Success toast
successToast :: String -> String -> Toast
successToast id message = toast id message FeedbackSuccess

-- | Error toast
errorToast :: String -> String -> Toast
errorToast id message = (toast id message FeedbackError)
  { duration = DurationLong }

-- | Info toast
infoToast :: String -> String -> Toast
infoToast id message = toast id message FeedbackInfo

-- | Warning toast
warningToast :: String -> String -> Toast
warningToast id message = toast id message FeedbackWarning

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // snackbar molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Snackbar notification (with optional action)
type Snackbar =
  { id :: String
  , message :: String
  , action :: Maybe FeedbackAction
  , duration :: FeedbackDuration
  , position :: FeedbackPosition
  }

-- | Create snackbar
snackbar :: String -> String -> Snackbar
snackbar id message =
  { id
  , message
  , action: Nothing
  , duration: DurationMedium
  , position: BottomCenter
  }

-- | Snackbar with action
snackbarWithAction :: String -> String -> FeedbackAction -> Snackbar
snackbarWithAction id message action =
  (snackbar id message) { action = Just action }

-- | Snackbar with undo action
snackbarWithUndo :: String -> String -> Snackbar
snackbarWithUndo id message = snackbarWithAction id message undoAction

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // banner molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Banner notification (persistent, full-width)
type Banner =
  { id :: String
  , message :: String
  , severity :: FeedbackSeverity
  , dismissible :: Boolean
  , action :: Maybe FeedbackAction
  , position :: FeedbackPosition  -- ^ TopCenter or BottomCenter typically
  }

-- | Create banner
banner :: String -> String -> FeedbackSeverity -> Banner
banner id message severity =
  { id
  , message
  , severity
  , dismissible: true
  , action: Nothing
  , position: TopCenter
  }

-- | Info banner
infoBanner :: String -> String -> Banner
infoBanner id message = banner id message FeedbackInfo

-- | Warning banner
warningBanner :: String -> String -> Banner
warningBanner id message = banner id message FeedbackWarning

-- | Error banner
errorBanner :: String -> String -> Banner
errorBanner id message = (banner id message FeedbackError)
  { dismissible = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // alert molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Inline alert
type Alert =
  { id :: String
  , title :: Maybe String
  , message :: String
  , severity :: FeedbackSeverity
  , dismissible :: Boolean
  , actions :: Array FeedbackAction
  }

-- | Create alert
alert :: String -> String -> FeedbackSeverity -> Alert
alert id message severity =
  { id
  , title: Nothing
  , message
  , severity
  , dismissible: false
  , actions: []
  }

-- | Inline alert (within content)
inlineAlert :: String -> String -> String -> FeedbackSeverity -> Alert
inlineAlert id title message severity =
  (alert id message severity) { title = Just title }

-- | Alert with actions
alertWithActions :: String -> String -> FeedbackSeverity -> Array FeedbackAction -> Alert
alertWithActions id message severity actions =
  (alert id message severity) { actions = actions }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // dialog compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Dialog type
data DialogType
  = ConfirmDialog    -- ^ Yes/No or OK/Cancel
  | AlertDialogType  -- ^ Informational with OK only
  | PromptDialog     -- ^ Requires input

derive instance eqDialogType :: Eq DialogType
derive instance ordDialogType :: Ord DialogType

instance showDialogType :: Show DialogType where
  show ConfirmDialog = "confirm"
  show AlertDialogType = "alert"
  show PromptDialog = "prompt"

isConfirmDialog :: DialogType -> Boolean
isConfirmDialog ConfirmDialog = true
isConfirmDialog _ = false

isAlertDialog :: DialogType -> Boolean
isAlertDialog AlertDialogType = true
isAlertDialog _ = false

isPromptDialog :: DialogType -> Boolean
isPromptDialog PromptDialog = true
isPromptDialog _ = false

-- | Modal dialog
type Dialog =
  { id :: String
  , dialogType :: DialogType
  , title :: String
  , message :: String
  , severity :: FeedbackSeverity
  , confirmLabel :: String
  , cancelLabel :: Maybe String
  , isDestructive :: Boolean
  , isOpen :: Boolean
  }

-- | Create dialog
dialog :: String -> DialogType -> String -> String -> Dialog
dialog id dialogType title message =
  { id
  , dialogType
  , title
  , message
  , severity: FeedbackNeutral
  , confirmLabel: "OK"
  , cancelLabel: Nothing
  , isDestructive: false
  , isOpen: false
  }

-- | Confirm dialog
confirmDialog :: String -> String -> String -> Dialog
confirmDialog id title message =
  (dialog id ConfirmDialog title message)
    { cancelLabel = Just "Cancel"
    , confirmLabel = "Confirm"
    }

-- | Alert dialog
alertDialog :: String -> String -> String -> Dialog
alertDialog id title message = dialog id AlertDialogType title message

-- | Destructive confirm dialog (red confirm button)
destructiveDialog :: String -> String -> String -> Dialog
destructiveDialog id title message =
  (confirmDialog id title message)
    { isDestructive = true
    , severity = FeedbackError
    , confirmLabel = "Delete"
    }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                // notification queue compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Queue of pending notifications
type NotificationQueue =
  { items :: Array Toast
  , maxVisible :: Int
  }

-- | Empty notification queue
emptyQueue :: Int -> NotificationQueue
emptyQueue maxVisible =
  { items: []
  , maxVisible
  }

-- | Add notification to queue
enqueue :: Toast -> NotificationQueue -> NotificationQueue
enqueue item queue =
  queue { items = snoc queue.items item }

-- | Remove oldest notification
dequeue :: NotificationQueue -> NotificationQueue
dequeue queue =
  queue { items = drop 1 queue.items }

-- | Get queue length
queueLength :: NotificationQueue -> Int
queueLength queue = length queue.items

-- | Get current notification (head of queue)
currentNotification :: NotificationQueue -> Maybe Toast
currentNotification queue = head queue.items

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // computed properties
-- ═════════════════════════════════════════════════════════════════════════════

-- | Should auto-dismiss based on duration?
shouldAutoDismiss :: FeedbackDuration -> Boolean
shouldAutoDismiss DurationPersistent = false
shouldAutoDismiss _ = true

-- | Does feedback have an action?
hasAction :: Snackbar -> Boolean
hasAction sb = isJust sb.action

-- | Is feedback blocking (modal)?
isBlocking :: Dialog -> Boolean
isBlocking _ = true  -- Dialogs are always blocking

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // tooltip molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tooltip placement relative to trigger
data TooltipPlacement
  = TooltipTop
  | TooltipTopStart
  | TooltipTopEnd
  | TooltipBottom
  | TooltipBottomStart
  | TooltipBottomEnd
  | TooltipLeft
  | TooltipLeftStart
  | TooltipLeftEnd
  | TooltipRight
  | TooltipRightStart
  | TooltipRightEnd

derive instance eqTooltipPlacement :: Eq TooltipPlacement
derive instance ordTooltipPlacement :: Ord TooltipPlacement

instance showTooltipPlacement :: Show TooltipPlacement where
  show TooltipTop = "top"
  show TooltipTopStart = "top-start"
  show TooltipTopEnd = "top-end"
  show TooltipBottom = "bottom"
  show TooltipBottomStart = "bottom-start"
  show TooltipBottomEnd = "bottom-end"
  show TooltipLeft = "left"
  show TooltipLeftStart = "left-start"
  show TooltipLeftEnd = "left-end"
  show TooltipRight = "right"
  show TooltipRightStart = "right-start"
  show TooltipRightEnd = "right-end"

-- | Tooltip configuration
type Tooltip =
  { content :: String             -- ^ Tooltip text
  , placement :: TooltipPlacement -- ^ Where to show relative to trigger
  , delay :: Number               -- ^ Delay before showing (ms)
  , hideDelay :: Number           -- ^ Delay before hiding (ms)
  , maxWidth :: Number            -- ^ Maximum width (px)
  , arrow :: Boolean              -- ^ Show arrow pointing to trigger
  , interactive :: Boolean        -- ^ Can tooltip be interacted with
  }

-- | Create tooltip
tooltip :: String -> TooltipPlacement -> Tooltip
tooltip content placement =
  { content
  , placement
  , delay: 200.0
  , hideDelay: 100.0
  , maxWidth: 300.0
  , arrow: true
  , interactive: false
  }

-- | Simple tooltip (top placement)
simpleTooltip :: String -> Tooltip
simpleTooltip content = tooltip content TooltipTop

-- | Interactive tooltip (can be hovered)
interactiveTooltip :: String -> TooltipPlacement -> Tooltip
interactiveTooltip content placement = (tooltip content placement)
  { interactive = true
  , hideDelay = 300.0
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // popover molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Popover trigger mode
data PopoverTrigger
  = PopoverClick      -- ^ Open on click
  | PopoverHover      -- ^ Open on hover
  | PopoverFocus      -- ^ Open on focus
  | PopoverManual     -- ^ Controlled externally

derive instance eqPopoverTrigger :: Eq PopoverTrigger
derive instance ordPopoverTrigger :: Ord PopoverTrigger

instance showPopoverTrigger :: Show PopoverTrigger where
  show PopoverClick = "click"
  show PopoverHover = "hover"
  show PopoverFocus = "focus"
  show PopoverManual = "manual"

-- | Popover configuration (richer than tooltip)
type Popover =
  { id :: String                  -- ^ Unique identifier
  , placement :: TooltipPlacement -- ^ Reuse tooltip placement
  , trigger :: PopoverTrigger     -- ^ How to trigger
  , title :: Maybe String         -- ^ Optional title
  , closeButton :: Boolean        -- ^ Show close button
  , closeOnClickOutside :: Boolean -- ^ Close when clicking outside
  , closeOnEscape :: Boolean      -- ^ Close on Escape key
  , offset :: Number              -- ^ Distance from trigger (px)
  , isOpen :: Boolean             -- ^ Current open state
  }

-- | Create popover
popover :: String -> TooltipPlacement -> PopoverTrigger -> Popover
popover id placement trigger =
  { id
  , placement
  , trigger
  , title: Nothing
  , closeButton: true
  , closeOnClickOutside: true
  , closeOnEscape: true
  , offset: 8.0
  , isOpen: false
  }

-- | Popover with title
popoverWithTitle :: String -> String -> TooltipPlacement -> Popover
popoverWithTitle id title placement =
  (popover id placement PopoverClick)
    { title = Just title }

-- | Is popover open?
isPopoverOpen :: Popover -> Boolean
isPopoverOpen p = p.isOpen

-- | Open popover
openPopover :: Popover -> Popover
openPopover p = p { isOpen = true }

-- | Close popover
closePopover :: Popover -> Popover
closePopover p = p { isOpen = false }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // drawer molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Drawer position (which edge it slides from)
data DrawerPosition
  = DrawerLeft
  | DrawerRight
  | DrawerTop
  | DrawerBottom

derive instance eqDrawerPosition :: Eq DrawerPosition
derive instance ordDrawerPosition :: Ord DrawerPosition

instance showDrawerPosition :: Show DrawerPosition where
  show DrawerLeft = "left"
  show DrawerRight = "right"
  show DrawerTop = "top"
  show DrawerBottom = "bottom"

-- | Drawer configuration
type Drawer =
  { id :: String                  -- ^ Unique identifier
  , position :: DrawerPosition    -- ^ Which edge
  , size :: Number                -- ^ Width (left/right) or height (top/bottom) in px
  , title :: Maybe String         -- ^ Optional title
  , hasOverlay :: Boolean         -- ^ Show backdrop overlay
  , closeOnOverlayClick :: Boolean -- ^ Close when clicking overlay
  , closeOnEscape :: Boolean      -- ^ Close on Escape key
  , isOpen :: Boolean             -- ^ Current open state
  , isPush :: Boolean             -- ^ Push content vs overlay
  }

-- | Create drawer
drawer :: String -> DrawerPosition -> Number -> Drawer
drawer id position size =
  { id
  , position
  , size
  , title: Nothing
  , hasOverlay: true
  , closeOnOverlayClick: true
  , closeOnEscape: true
  , isOpen: false
  , isPush: false
  }

-- | Navigation drawer (left, 280px)
navigationDrawer :: String -> Drawer
navigationDrawer id = drawer id DrawerLeft 280.0

-- | Side panel drawer (right, 400px)
sidePanelDrawer :: String -> Drawer
sidePanelDrawer id = drawer id DrawerRight 400.0

-- | Is drawer open?
isDrawerOpen :: Drawer -> Boolean
isDrawerOpen d = d.isOpen

-- | Open drawer
openDrawer :: Drawer -> Drawer
openDrawer d = d { isOpen = true }

-- | Close drawer
closeDrawer :: Drawer -> Drawer
closeDrawer d = d { isOpen = false }

-- | Toggle drawer
toggleDrawer :: Drawer -> Drawer
toggleDrawer d = d { isOpen = not d.isOpen }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // sheet molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Sheet snap point (height detents)
data SheetSnapPoint
  = SheetMinimized    -- ^ Just peek (e.g., 100px)
  | SheetPartial      -- ^ Half height
  | SheetExpanded     -- ^ Full height (minus safe area)
  | SheetCustom Number -- ^ Custom height in pixels

derive instance eqSheetSnapPoint :: Eq SheetSnapPoint

instance showSheetSnapPoint :: Show SheetSnapPoint where
  show SheetMinimized = "minimized"
  show SheetPartial = "partial"
  show SheetExpanded = "expanded"
  show (SheetCustom h) = "custom(" <> show h <> "px)"

-- | Bottom sheet configuration (mobile pattern)
type Sheet =
  { id :: String                      -- ^ Unique identifier
  , title :: Maybe String             -- ^ Optional title
  , snapPoints :: Array SheetSnapPoint -- ^ Available snap heights
  , currentSnap :: SheetSnapPoint     -- ^ Current snap position
  , hasOverlay :: Boolean             -- ^ Show backdrop
  , dismissible :: Boolean            -- ^ Can swipe down to dismiss
  , hasHandle :: Boolean              -- ^ Show drag handle
  , isOpen :: Boolean                 -- ^ Current open state
  }

-- | Create sheet
sheet :: String -> Array SheetSnapPoint -> Sheet
sheet id snapPoints =
  { id
  , title: Nothing
  , snapPoints
  , currentSnap: SheetPartial
  , hasOverlay: true
  , dismissible: true
  , hasHandle: true
  , isOpen: false
  }

-- | Standard bottom sheet (partial/expanded)
standardSheet :: String -> Sheet
standardSheet id = sheet id [SheetPartial, SheetExpanded]

-- | Multi-detent sheet (minimized/partial/expanded)
multiDetentSheet :: String -> Sheet
multiDetentSheet id = sheet id [SheetMinimized, SheetPartial, SheetExpanded]

-- | Is sheet open?
isSheetOpen :: Sheet -> Boolean
isSheetOpen s = s.isOpen

-- | Open sheet to snap point
openSheet :: SheetSnapPoint -> Sheet -> Sheet
openSheet snap s = s { isOpen = true, currentSnap = snap }

-- | Close sheet
closeSheet :: Sheet -> Sheet
closeSheet s = s { isOpen = false }

-- | Snap sheet to point
snapSheet :: SheetSnapPoint -> Sheet -> Sheet
snapSheet snap s = s { currentSnap = snap }
