-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                             // hydrogen // tour // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Navigation and Progress for Product Tours
-- |
-- | This module provides the navigation vocabulary for tour progression:
-- | - Progress indicators (dots, bar, fraction, stepper)
-- | - Button configurations (next, prev, skip, complete)
-- | - Keyboard navigation
-- | - Swipe gesture support
-- |
-- | ## Design Philosophy
-- |
-- | Navigation elements are pure functions producing Element data. They are
-- | completely stateless — all state comes from TourState.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hydrogen.Tour.Navigation as Nav
-- |
-- | -- Progress dots
-- | progressView = Nav.progressDots { current: 2, total: 5, variant: Nav.DotsDefault }
-- |
-- | -- Navigation buttons
-- | buttonsView = Nav.navigationButtons
-- |   { showPrev: true
-- |   , showSkip: true
-- |   , nextLabel: "Continue"
-- |   , prevLabel: "Back"
-- |   , onNext: NextStep
-- |   , onPrev: PrevStep
-- |   }
-- | ```
module Hydrogen.Tour.Navigation
  ( -- * Progress Indicators
    ProgressStyle(..)
  , ProgressVariant(..)
  , ProgressConfig
  , defaultProgressConfig
  , DotSize(..)
  , FractionFormat(..)
  , StepperOrientation(..)
    -- * Progress Builders
  , progressDots
  , progressBar
  , progressFraction
  , progressStepper
    -- * Button Configuration
  , ButtonConfig
  , ButtonStyle(..)
  , ButtonSize(..)
  , ButtonPosition(..)
  , ButtonIcon(..)
  , defaultButtonConfig
    -- * Button Builders
  , nextButton
  , prevButton
  , skipButton
  , completeButton
  , customButton
  , navigationButtons
  , ButtonLayout(..)
    -- * Keyboard Configuration
  , KeyboardConfig
  , defaultKeyboardConfig
  , KeyBinding
  , KeyAction(..)
  , KeyModifier(..)
  , defaultKeyBindings
  , withArrowNav
  , withEscapeDismiss
  , withTabNav
    -- * Swipe Configuration
  , SwipeConfig
  , defaultSwipeConfig
  , SwipeDirection(..)
  , swipeEnabled
    -- * Close Button
  , CloseButtonConfig
  , defaultCloseConfig
  , CloseButtonPosition(..)
  , CloseButtonStyle(..)
    -- * Accessibility
  , A11yConfig
  , LiveRegion(..)
  , defaultA11yConfig
  , screenReaderAnnouncement
  , focusTrapConfig
  , FocusTrapConfig
  , InitialFocus(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)
import Hydrogen.Tour.Types (Pixel(Pixel), Progress, progressCurrent, progressPercent, progressTotal)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // progress indicators
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress indicator style
-- |
-- | Different visual representations of tour progress.
data ProgressStyle
  = ProgressDots ProgressVariant
    -- ^ Dot indicators (one per step)
  | ProgressBar ProgressVariant
    -- ^ Horizontal progress bar
  | ProgressFraction
    -- ^ "2 of 5" text format
  | ProgressStepper
    -- ^ Full stepper with labels
  | ProgressNone
    -- ^ No progress indicator

derive instance eqProgressStyle :: Eq ProgressStyle
derive instance genericProgressStyle :: Generic ProgressStyle _

instance showProgressStyle :: Show ProgressStyle where
  show = genericShow

-- | Progress indicator variant
data ProgressVariant
  = VariantDefault
    -- ^ Standard appearance
  | VariantMinimal
    -- ^ Subtle, low-profile
  | VariantProminent
    -- ^ Bold, attention-grabbing
  | VariantBrand
    -- ^ Uses brand colors

derive instance eqProgressVariant :: Eq ProgressVariant
derive instance ordProgressVariant :: Ord ProgressVariant
derive instance genericProgressVariant :: Generic ProgressVariant _

instance showProgressVariant :: Show ProgressVariant where
  show = genericShow

-- | Progress configuration
type ProgressConfig =
  { style :: ProgressStyle
  , showLabels :: Boolean
    -- ^ Show step labels (for stepper)
  , clickable :: Boolean
    -- ^ Allow clicking to jump to step
  , animated :: Boolean
    -- ^ Animate progress changes
  }

-- | Default progress configuration
defaultProgressConfig :: ProgressConfig
defaultProgressConfig =
  { style: ProgressDots VariantDefault
  , showLabels: false
  , clickable: false
  , animated: true
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // progress builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Configuration for dot progress indicator
type DotsConfig =
  { current :: Int
  , total :: Int
  , variant :: ProgressVariant
  , size :: DotSize
  , spacing :: Pixel
  , clickable :: Boolean
  }

-- | Dot size
data DotSize
  = DotSmall
  | DotMedium
  | DotLarge

derive instance eqDotSize :: Eq DotSize
derive instance genericDotSize :: Generic DotSize _

instance showDotSize :: Show DotSize where
  show = genericShow

-- | Create progress dots element description
progressDots :: Progress -> ProgressVariant -> ProgressDotsElement
progressDots progress variant =
  { current: progressCurrent progress
  , total: progressTotal progress
  , variant
  , activeColor: variantActiveColor variant
  , inactiveColor: variantInactiveColor variant
  , size: DotMedium
  }

-- | Element description for progress dots
type ProgressDotsElement =
  { current :: Int
  , total :: Int
  , variant :: ProgressVariant
  , activeColor :: String
  , inactiveColor :: String
  , size :: DotSize
  }

-- | Create progress bar element description
progressBar :: Progress -> ProgressVariant -> ProgressBarElement
progressBar progress variant =
  { percent: progressPercent progress
  , variant
  , height: Pixel 4
  , animated: true
  }

-- | Element description for progress bar
type ProgressBarElement =
  { percent :: Int
  , variant :: ProgressVariant
  , height :: Pixel
  , animated :: Boolean
  }

-- | Create fraction text element description
progressFraction :: Progress -> ProgressFractionElement
progressFraction progress =
  { current: progressCurrent progress
  , total: progressTotal progress
  , format: FractionOfFormat
  }

-- | Element description for progress fraction
type ProgressFractionElement =
  { current :: Int
  , total :: Int
  , format :: FractionFormat
  }

-- | Fraction format
data FractionFormat
  = FractionOfFormat     -- "2 of 5"
  | FractionSlashFormat  -- "2/5"
  | FractionDashFormat   -- "2 - 5"

derive instance eqFractionFormat :: Eq FractionFormat
derive instance genericFractionFormat :: Generic FractionFormat _

instance showFractionFormat :: Show FractionFormat where
  show = genericShow

-- | Create stepper element description
progressStepper :: Progress -> Array String -> ProgressStepperElement
progressStepper progress labels =
  { current: progressCurrent progress
  , total: progressTotal progress
  , labels
  , showLabels: true
  , orientation: Horizontal
  }

-- | Element description for stepper
type ProgressStepperElement =
  { current :: Int
  , total :: Int
  , labels :: Array String
  , showLabels :: Boolean
  , orientation :: StepperOrientation
  }

-- | Stepper orientation
data StepperOrientation
  = Horizontal
  | Vertical

derive instance eqStepperOrientation :: Eq StepperOrientation
derive instance genericStepperOrientation :: Generic StepperOrientation _

instance showStepperOrientation :: Show StepperOrientation where
  show = genericShow

-- | Get active color for variant
variantActiveColor :: ProgressVariant -> String
variantActiveColor = case _ of
  VariantDefault -> "bg-primary"
  VariantMinimal -> "bg-muted-foreground"
  VariantProminent -> "bg-blue-500"
  VariantBrand -> "bg-brand"

-- | Get inactive color for variant
variantInactiveColor :: ProgressVariant -> String
variantInactiveColor = case _ of
  VariantDefault -> "bg-muted"
  VariantMinimal -> "bg-muted/50"
  VariantProminent -> "bg-blue-200"
  VariantBrand -> "bg-brand/20"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // button configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Button configuration
type ButtonConfig msg =
  { label :: String
  , action :: msg
  , style :: ButtonStyle
  , size :: ButtonSize
  , disabled :: Boolean
  , icon :: Maybe ButtonIcon
  , position :: ButtonPosition
  }

-- | Button visual style
data ButtonStyle
  = ButtonPrimary
    -- ^ Primary action (Next, Continue)
  | ButtonSecondary
    -- ^ Secondary action (Previous)
  | ButtonGhost
    -- ^ Ghost/text button (Skip)
  | ButtonDestructive
    -- ^ Warning action (Leave tour)
  | ButtonOutline
    -- ^ Outlined button

derive instance eqButtonStyle :: Eq ButtonStyle
derive instance genericButtonStyle :: Generic ButtonStyle _

instance showButtonStyle :: Show ButtonStyle where
  show = genericShow

-- | Button size
data ButtonSize
  = ButtonSmall
  | ButtonMedium
  | ButtonLarge

derive instance eqButtonSize :: Eq ButtonSize
derive instance genericButtonSize :: Generic ButtonSize _

instance showButtonSize :: Show ButtonSize where
  show = genericShow

-- | Button position in layout
data ButtonPosition
  = PositionStart
  | PositionCenter
  | PositionEnd

derive instance eqButtonPosition :: Eq ButtonPosition
derive instance genericButtonPosition :: Generic ButtonPosition _

instance showButtonPosition :: Show ButtonPosition where
  show = genericShow

-- | Button icon
data ButtonIcon
  = IconArrowLeft
  | IconArrowRight
  | IconCheck
  | IconX
  | IconSkip
  | IconCustom String

derive instance eqButtonIcon :: Eq ButtonIcon
derive instance genericButtonIcon :: Generic ButtonIcon _

instance showButtonIcon :: Show ButtonIcon where
  show = genericShow

-- | Default button configuration
defaultButtonConfig :: forall msg. String -> msg -> ButtonConfig msg
defaultButtonConfig label action =
  { label
  , action
  , style: ButtonPrimary
  , size: ButtonMedium
  , disabled: false
  , icon: Nothing
  , position: PositionEnd
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // button builders
-- ═════════════════════════════════════════════════════════════════════════════

-- | Create next button
nextButton :: forall msg. String -> msg -> ButtonConfig msg
nextButton label action = (defaultButtonConfig label action)
  { style = ButtonPrimary
  , icon = Just IconArrowRight
  , position = PositionEnd
  }

-- | Create previous button
prevButton :: forall msg. String -> msg -> ButtonConfig msg
prevButton label action = (defaultButtonConfig label action)
  { style = ButtonSecondary
  , icon = Just IconArrowLeft
  , position = PositionStart
  }

-- | Create skip button
skipButton :: forall msg. String -> msg -> ButtonConfig msg
skipButton label action = (defaultButtonConfig label action)
  { style = ButtonGhost
  , icon = Just IconSkip
  , position = PositionStart
  }

-- | Create complete button
completeButton :: forall msg. String -> msg -> ButtonConfig msg
completeButton label action = (defaultButtonConfig label action)
  { style = ButtonPrimary
  , icon = Just IconCheck
  , position = PositionEnd
  }

-- | Create custom button
customButton :: forall msg. String -> msg -> ButtonStyle -> ButtonConfig msg
customButton label action style = (defaultButtonConfig label action) { style = style }

-- | Navigation buttons configuration
type NavigationButtonsConfig msg =
  { showPrev :: Boolean
  , showNext :: Boolean
  , showSkip :: Boolean
  , prevConfig :: Maybe (ButtonConfig msg)
  , nextConfig :: Maybe (ButtonConfig msg)
  , skipConfig :: Maybe (ButtonConfig msg)
  , completeConfig :: Maybe (ButtonConfig msg)
  , layout :: ButtonLayout
  }

-- | Button layout
data ButtonLayout
  = LayoutSpaceBetween
    -- ^ Spread across width
  | LayoutEnd
    -- ^ Aligned to end
  | LayoutStacked
    -- ^ Vertical stack

derive instance eqButtonLayout :: Eq ButtonLayout
derive instance genericButtonLayout :: Generic ButtonLayout _

instance showButtonLayout :: Show ButtonLayout where
  show = genericShow

-- | Build navigation buttons element description
navigationButtons :: forall msg. NavigationButtonsConfig msg -> NavigationElement msg
navigationButtons cfg =
  { buttons: buildButtons cfg
  , layout: cfg.layout
  }

-- | Build button array from config
buildButtons :: forall msg. NavigationButtonsConfig msg -> Array (ButtonConfig msg)
buildButtons cfg =
  (if cfg.showSkip then maybeToArray cfg.skipConfig else []) <>
  (if cfg.showPrev then maybeToArray cfg.prevConfig else []) <>
  (if cfg.showNext then maybeToArray cfg.nextConfig else maybeToArray cfg.completeConfig)
  where
  maybeToArray :: forall a. Maybe a -> Array a
  maybeToArray = case _ of
    Just a -> [a]
    Nothing -> []

-- | Element description for navigation
type NavigationElement msg =
  { buttons :: Array (ButtonConfig msg)
  , layout :: ButtonLayout
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // keyboard configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard navigation configuration
type KeyboardConfig =
  { enabled :: Boolean
  , bindings :: Array KeyBinding
  , trapFocus :: Boolean
    -- ^ Keep focus within tour tooltip
  , announceToScreenReader :: Boolean
  }

-- | Key binding
type KeyBinding =
  { key :: String
    -- ^ Key name (e.g., "ArrowRight", "Escape")
  , action :: KeyAction
  , requireModifier :: Maybe KeyModifier
  }

-- | Key action
data KeyAction
  = KeyNext
  | KeyPrev
  | KeyDismiss
  | KeyComplete
  | KeyGoToStep Int

derive instance eqKeyAction :: Eq KeyAction
derive instance genericKeyAction :: Generic KeyAction _

instance showKeyAction :: Show KeyAction where
  show = genericShow

-- | Key modifier
data KeyModifier
  = ModCtrl
  | ModShift
  | ModAlt
  | ModMeta

derive instance eqKeyModifier :: Eq KeyModifier
derive instance genericKeyModifier :: Generic KeyModifier _

instance showKeyModifier :: Show KeyModifier where
  show = genericShow

-- | Default keyboard configuration
defaultKeyboardConfig :: KeyboardConfig
defaultKeyboardConfig =
  { enabled: true
  , bindings: defaultKeyBindings
  , trapFocus: true
  , announceToScreenReader: true
  }

-- | Default key bindings
defaultKeyBindings :: Array KeyBinding
defaultKeyBindings =
  [ { key: "ArrowRight", action: KeyNext, requireModifier: Nothing }
  , { key: "ArrowLeft", action: KeyPrev, requireModifier: Nothing }
  , { key: "Escape", action: KeyDismiss, requireModifier: Nothing }
  , { key: "Enter", action: KeyNext, requireModifier: Nothing }
  ]

-- | Enable arrow key navigation
withArrowNav :: Boolean -> KeyboardConfig -> KeyboardConfig
withArrowNav enabled cfg =
  let
    arrowBindings :: Array KeyBinding
    arrowBindings =
      [ { key: "ArrowRight", action: KeyNext, requireModifier: Nothing }
      , { key: "ArrowLeft", action: KeyPrev, requireModifier: Nothing }
      ]
    
    filterOutArrows :: Array KeyBinding -> Array KeyBinding
    filterOutArrows = filter (\b -> b.key /= "ArrowRight" && b.key /= "ArrowLeft")
  in
    if enabled
    then cfg { bindings = cfg.bindings <> arrowBindings }
    else cfg { bindings = filterOutArrows cfg.bindings }

-- | Enable escape to dismiss
withEscapeDismiss :: Boolean -> KeyboardConfig -> KeyboardConfig
withEscapeDismiss enabled cfg =
  let
    escBinding :: KeyBinding
    escBinding = { key: "Escape", action: KeyDismiss, requireModifier: Nothing }
    
    filterOutEscape :: Array KeyBinding -> Array KeyBinding
    filterOutEscape = filter (\b -> b.key /= "Escape")
  in
    if enabled
    then cfg { bindings = cfg.bindings <> [escBinding] }
    else cfg { bindings = filterOutEscape cfg.bindings }

-- | Enable tab navigation between steps
withTabNav :: Boolean -> KeyboardConfig -> KeyboardConfig
withTabNav enabled cfg =
  let
    tabBindings :: Array KeyBinding
    tabBindings =
      [ { key: "Tab", action: KeyNext, requireModifier: Nothing }
      , { key: "Tab", action: KeyPrev, requireModifier: Just ModShift }
      ]
    
    filterOutTab :: Array KeyBinding -> Array KeyBinding
    filterOutTab = filter (\b -> b.key /= "Tab")
  in
    if enabled
    then cfg { bindings = cfg.bindings <> tabBindings }
    else cfg { bindings = filterOutTab cfg.bindings }

-- | Filter helper
filter :: forall a. (a -> Boolean) -> Array a -> Array a
filter = filterImpl

foreign import filterImpl :: forall a. (a -> Boolean) -> Array a -> Array a

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // swipe configuration
-- ═════════════════════════════════════════════════════════════════════════════

-- | Swipe gesture configuration
type SwipeConfig =
  { enabled :: Boolean
  , threshold :: Pixel
    -- ^ Minimum swipe distance
  , velocity :: Number
    -- ^ Minimum velocity (px/ms)
  , directions :: Array SwipeDirection
  }

-- | Swipe direction
data SwipeDirection
  = SwipeLeft
  | SwipeRight
  | SwipeUp
  | SwipeDown

derive instance eqSwipeDirection :: Eq SwipeDirection
derive instance genericSwipeDirection :: Generic SwipeDirection _

instance showSwipeDirection :: Show SwipeDirection where
  show = genericShow

-- | Default swipe configuration
defaultSwipeConfig :: SwipeConfig
defaultSwipeConfig =
  { enabled: true
  , threshold: Pixel 50
  , velocity: 0.3
  , directions: [SwipeLeft, SwipeRight]
  }

-- | Enable swipe gestures
swipeEnabled :: Boolean -> SwipeConfig
swipeEnabled enabled = defaultSwipeConfig { enabled = enabled }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // close button
-- ═════════════════════════════════════════════════════════════════════════════

-- | Close button configuration
type CloseButtonConfig =
  { visible :: Boolean
  , position :: CloseButtonPosition
  , style :: CloseButtonStyle
  , label :: String
    -- ^ Accessible label
  }

-- | Close button position
data CloseButtonPosition
  = CloseTopRight
  | CloseTopLeft
  | CloseInHeader

derive instance eqCloseButtonPosition :: Eq CloseButtonPosition
derive instance genericCloseButtonPosition :: Generic CloseButtonPosition _

instance showCloseButtonPosition :: Show CloseButtonPosition where
  show = genericShow

-- | Close button style
data CloseButtonStyle
  = CloseIcon
    -- ^ X icon only
  | CloseText
    -- ^ "Close" text
  | CloseIconWithLabel
    -- ^ Icon + "Close"

derive instance eqCloseButtonStyle :: Eq CloseButtonStyle
derive instance genericCloseButtonStyle :: Generic CloseButtonStyle _

instance showCloseButtonStyle :: Show CloseButtonStyle where
  show = genericShow

-- | Default close button configuration
defaultCloseConfig :: CloseButtonConfig
defaultCloseConfig =
  { visible: true
  , position: CloseTopRight
  , style: CloseIcon
  , label: "Close tour"
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // accessibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Accessibility configuration
type A11yConfig =
  { role :: String
    -- ^ ARIA role for tour container
  , ariaLabel :: String
  , ariaModal :: Boolean
  , liveRegion :: LiveRegion
    -- ^ For screen reader announcements
  , focusTrap :: Boolean
  , restoreFocus :: Boolean
    -- ^ Return focus to original element after tour
  }

-- | Live region assertiveness
data LiveRegion
  = LiveOff
  | LivePolite
  | LiveAssertive

derive instance eqLiveRegion :: Eq LiveRegion
derive instance genericLiveRegion :: Generic LiveRegion _

instance showLiveRegion :: Show LiveRegion where
  show = genericShow

-- | Default accessibility configuration
defaultA11yConfig :: A11yConfig
defaultA11yConfig =
  { role: "dialog"
  , ariaLabel: "Product tour"
  , ariaModal: true
  , liveRegion: LivePolite
  , focusTrap: true
  , restoreFocus: true
  }

-- | Generate screen reader announcement
screenReaderAnnouncement :: Int -> Int -> String -> String
screenReaderAnnouncement current total title =
  "Step " <> show current <> " of " <> show total <> 
  (if title == "" then "" else ": " <> title)

-- | Focus trap configuration
type FocusTrapConfig =
  { enabled :: Boolean
  , returnFocusOnDeactivate :: Boolean
  , initialFocus :: InitialFocus
  , escapeDeactivates :: Boolean
  }

-- | Initial focus target
data InitialFocus
  = FocusFirstTabbable
  | FocusContainer
  | FocusPrimaryButton
  | FocusNone

derive instance eqInitialFocus :: Eq InitialFocus
derive instance genericInitialFocus :: Generic InitialFocus _

instance showInitialFocus :: Show InitialFocus where
  show = genericShow

-- | Default focus trap configuration
focusTrapConfig :: FocusTrapConfig
focusTrapConfig =
  { enabled: true
  , returnFocusOnDeactivate: true
  , initialFocus: FocusPrimaryButton
  , escapeDeactivates: true
  }
