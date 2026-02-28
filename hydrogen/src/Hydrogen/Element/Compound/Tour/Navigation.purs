-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                  // hydrogen // element // tour // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Tour Navigation — UI controls and progress indicators.
-- |
-- | ## Architecture
-- |
-- | Navigation controls how users move through the tour:
-- | - Button layouts (next, prev, skip)
-- | - Progress indicators (dots, bar, numbers)
-- | - Keyboard shortcuts
-- | - Close/dismiss behavior
-- |
-- | ## Schema Mapping
-- |
-- | | Type            | Pillar    | Purpose                              |
-- | |-----------------|-----------|--------------------------------------|
-- | | NavigationStyle | Reactive  | Button layout and appearance         |
-- | | ProgressStyle   | Reactive  | Progress indicator type              |
-- | | ButtonPosition  | Spatial   | Where buttons are placed             |
-- | | CloseButton     | Reactive  | Close/dismiss button configuration   |
-- | | KeyboardConfig  | Gestural  | Keyboard navigation settings         |

module Hydrogen.Element.Compound.Tour.Navigation
  ( -- * Navigation Style
    NavigationStyle
      ( NavMinimal
      , NavStandard
      , NavExpanded
      , NavCompact
      , NavFloating
      , NavDocked
      , NavHidden
      )
  
  -- * Progress Style
  , ProgressStyle
      ( ProgressNone
      , ProgressDots
      , ProgressBar
      , ProgressNumbers
      , ProgressFraction
      , ProgressSteps
      , ProgressCircle
      )
  
  -- * Button Position
  , ButtonPosition
      ( ButtonInTooltip
      , ButtonBelowTooltip
      , ButtonFooter
      , ButtonFloating
      , ButtonInline
      )
  
  -- * Button Variant
  , ButtonVariant
      ( VariantPrimary
      , VariantSecondary
      , VariantGhost
      , VariantLink
      , VariantOutline
      , VariantIcon
      )
  
  -- * Close Mode
  , CloseMode
      ( CloseButton
      , CloseOverlayClick
      , CloseEscape
      , CloseAny
      , CloseNone
      )
  
  -- * Skip Mode
  , SkipMode
      ( SkipAlways
      , SkipAfterSteps
      , SkipNever
      , SkipOnlyLast
      )
  
  -- * Keyboard Key
  , KeyboardKey
      ( KeyArrowRight
      , KeyArrowLeft
      , KeyArrowUp
      , KeyArrowDown
      , KeyEnter
      , KeySpace
      , KeyEscape
      , KeyTab
      , KeyHome
      , KeyEnd
      , KeyN
      , KeyP
      )
  
  -- * Navigation Labels
  , NavigationLabels
  , defaultLabels
  , minimalLabels
  
  -- * Keyboard Config
  , KeyboardConfig
  , defaultKeyboardConfig
  , arrowKeyConfig
  , vimKeyConfig
  , disabledKeyboardConfig
  
  -- * Navigation Config
  , NavigationConfig
  , defaultNavigationConfig
  , minimalNavigationConfig
  , expandedNavigationConfig
  ) where

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                    // imports
-- ═════════════════════════════════════════════════════════════════════════════

import Prelude
  ( class Bounded
  , class Eq
  , class Ord
  , class Show
  , show
  , (<>)
  )

import Data.Maybe (Maybe(Nothing, Just))

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // navigation style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Overall navigation UI style.
data NavigationStyle
  = NavMinimal     -- ^ Just next/skip, no progress
  | NavStandard    -- ^ Next, prev, skip with dots
  | NavExpanded    -- ^ All controls visible, large buttons
  | NavCompact     -- ^ Small controls, icon-only buttons
  | NavFloating    -- ^ Floating nav separate from tooltip
  | NavDocked      -- ^ Docked to screen edge
  | NavHidden      -- ^ No visible navigation (keyboard only)

derive instance eqNavigationStyle :: Eq NavigationStyle
derive instance ordNavigationStyle :: Ord NavigationStyle

instance showNavigationStyle :: Show NavigationStyle where
  show NavMinimal = "minimal"
  show NavStandard = "standard"
  show NavExpanded = "expanded"
  show NavCompact = "compact"
  show NavFloating = "floating"
  show NavDocked = "docked"
  show NavHidden = "hidden"

instance boundedNavigationStyle :: Bounded NavigationStyle where
  bottom = NavMinimal
  top = NavHidden

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // progress style
-- ═════════════════════════════════════════════════════════════════════════════

-- | How progress through the tour is displayed.
data ProgressStyle
  = ProgressNone       -- ^ No progress indicator
  | ProgressDots       -- ^ Dot indicators (most common)
  | ProgressBar        -- ^ Horizontal progress bar
  | ProgressNumbers    -- ^ "Step 2 of 5" text
  | ProgressFraction   -- ^ "2/5" compact text
  | ProgressSteps      -- ^ Step titles list
  | ProgressCircle     -- ^ Circular progress indicator

derive instance eqProgressStyle :: Eq ProgressStyle
derive instance ordProgressStyle :: Ord ProgressStyle

instance showProgressStyle :: Show ProgressStyle where
  show ProgressNone = "none"
  show ProgressDots = "dots"
  show ProgressBar = "bar"
  show ProgressNumbers = "numbers"
  show ProgressFraction = "fraction"
  show ProgressSteps = "steps"
  show ProgressCircle = "circle"

instance boundedProgressStyle :: Bounded ProgressStyle where
  bottom = ProgressNone
  top = ProgressCircle

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // button position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Where navigation buttons are positioned.
data ButtonPosition
  = ButtonInTooltip     -- ^ Inside the tooltip body
  | ButtonBelowTooltip  -- ^ Below the tooltip content
  | ButtonFooter        -- ^ In a fixed footer bar
  | ButtonFloating      -- ^ Floating buttons separate from tooltip
  | ButtonInline        -- ^ Inline with content

derive instance eqButtonPosition :: Eq ButtonPosition
derive instance ordButtonPosition :: Ord ButtonPosition

instance showButtonPosition :: Show ButtonPosition where
  show ButtonInTooltip = "in-tooltip"
  show ButtonBelowTooltip = "below-tooltip"
  show ButtonFooter = "footer"
  show ButtonFloating = "floating"
  show ButtonInline = "inline"

instance boundedButtonPosition :: Bounded ButtonPosition where
  bottom = ButtonInTooltip
  top = ButtonInline

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // button variant
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style variant for buttons.
data ButtonVariant
  = VariantPrimary    -- ^ Filled primary color
  | VariantSecondary  -- ^ Filled secondary color
  | VariantGhost      -- ^ Transparent with hover
  | VariantLink       -- ^ Text link style
  | VariantOutline    -- ^ Bordered outline
  | VariantIcon       -- ^ Icon-only button

derive instance eqButtonVariant :: Eq ButtonVariant
derive instance ordButtonVariant :: Ord ButtonVariant

instance showButtonVariant :: Show ButtonVariant where
  show VariantPrimary = "primary"
  show VariantSecondary = "secondary"
  show VariantGhost = "ghost"
  show VariantLink = "link"
  show VariantOutline = "outline"
  show VariantIcon = "icon"

instance boundedButtonVariant :: Bounded ButtonVariant where
  bottom = VariantPrimary
  top = VariantIcon

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // close mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | How the tour can be closed/dismissed.
data CloseMode
  = CloseButton        -- ^ Close button only
  | CloseOverlayClick  -- ^ Click overlay to close
  | CloseEscape        -- ^ Escape key only
  | CloseAny           -- ^ Any method closes
  | CloseNone          -- ^ Cannot be closed (must complete)

derive instance eqCloseMode :: Eq CloseMode
derive instance ordCloseMode :: Ord CloseMode

instance showCloseMode :: Show CloseMode where
  show CloseButton = "button"
  show CloseOverlayClick = "overlay-click"
  show CloseEscape = "escape"
  show CloseAny = "any"
  show CloseNone = "none"

instance boundedCloseMode :: Bounded CloseMode where
  bottom = CloseButton
  top = CloseNone

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // skip mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | When the skip button is available.
data SkipMode
  = SkipAlways           -- ^ Always show skip
  | SkipAfterSteps Int   -- ^ Show after N steps
  | SkipNever            -- ^ Never show skip
  | SkipOnlyLast         -- ^ Only on last step (as "Finish")

derive instance eqSkipMode :: Eq SkipMode
derive instance ordSkipMode :: Ord SkipMode

instance showSkipMode :: Show SkipMode where
  show SkipAlways = "always"
  show (SkipAfterSteps n) = "after-" <> show n <> "-steps"
  show SkipNever = "never"
  show SkipOnlyLast = "only-last"

instance boundedSkipMode :: Bounded SkipMode where
  bottom = SkipAlways
  top = SkipOnlyLast

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // keyboard key
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard keys for navigation.
data KeyboardKey
  = KeyArrowRight
  | KeyArrowLeft
  | KeyArrowUp
  | KeyArrowDown
  | KeyEnter
  | KeySpace
  | KeyEscape
  | KeyTab
  | KeyHome
  | KeyEnd
  | KeyN
  | KeyP

derive instance eqKeyboardKey :: Eq KeyboardKey
derive instance ordKeyboardKey :: Ord KeyboardKey

instance showKeyboardKey :: Show KeyboardKey where
  show KeyArrowRight = "ArrowRight"
  show KeyArrowLeft = "ArrowLeft"
  show KeyArrowUp = "ArrowUp"
  show KeyArrowDown = "ArrowDown"
  show KeyEnter = "Enter"
  show KeySpace = "Space"
  show KeyEscape = "Escape"
  show KeyTab = "Tab"
  show KeyHome = "Home"
  show KeyEnd = "End"
  show KeyN = "n"
  show KeyP = "p"

instance boundedKeyboardKey :: Bounded KeyboardKey where
  bottom = KeyArrowRight
  top = KeyP

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // navigation labels
-- ═════════════════════════════════════════════════════════════════════════════

-- | Customizable labels for navigation elements.
type NavigationLabels =
  { next :: String
  , prev :: String
  , skip :: String
  , finish :: String
  , close :: String
  , stepOf :: String -> String -> String  -- ^ "Step {1} of {2}"
  }

-- | Default English labels
defaultLabels :: NavigationLabels
defaultLabels =
  { next: "Next"
  , prev: "Previous"
  , skip: "Skip"
  , finish: "Finish"
  , close: "Close"
  , stepOf: \current total -> "Step " <> current <> " of " <> total
  }

-- | Minimal labels (shorter text)
minimalLabels :: NavigationLabels
minimalLabels =
  { next: "Next"
  , prev: "Back"
  , skip: "Skip"
  , finish: "Done"
  , close: "×"
  , stepOf: \current total -> current <> "/" <> total
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // keyboard config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Keyboard navigation configuration.
type KeyboardConfig =
  { enabled :: Boolean
  , nextKeys :: Array KeyboardKey
  , prevKeys :: Array KeyboardKey
  , closeKeys :: Array KeyboardKey
  , firstKeys :: Array KeyboardKey
  , lastKeys :: Array KeyboardKey
  , trapFocus :: Boolean              -- ^ Keep focus within tour
  , autoFocusTooltip :: Boolean       -- ^ Focus tooltip on step change
  }

-- | Default keyboard configuration
defaultKeyboardConfig :: KeyboardConfig
defaultKeyboardConfig =
  { enabled: true
  , nextKeys: [ KeyArrowRight, KeyEnter, KeySpace ]
  , prevKeys: [ KeyArrowLeft ]
  , closeKeys: [ KeyEscape ]
  , firstKeys: [ KeyHome ]
  , lastKeys: [ KeyEnd ]
  , trapFocus: true
  , autoFocusTooltip: true
  }

-- | Arrow key navigation only
arrowKeyConfig :: KeyboardConfig
arrowKeyConfig = defaultKeyboardConfig
  { nextKeys = [ KeyArrowRight, KeyArrowDown ]
  , prevKeys = [ KeyArrowLeft, KeyArrowUp ]
  }

-- | Vim-style navigation (n/p keys)
vimKeyConfig :: KeyboardConfig
vimKeyConfig = defaultKeyboardConfig
  { nextKeys = [ KeyN, KeyArrowRight ]
  , prevKeys = [ KeyP, KeyArrowLeft ]
  }

-- | Disabled keyboard navigation
disabledKeyboardConfig :: KeyboardConfig
disabledKeyboardConfig =
  { enabled: false
  , nextKeys: []
  , prevKeys: []
  , closeKeys: []
  , firstKeys: []
  , lastKeys: []
  , trapFocus: false
  , autoFocusTooltip: false
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // navigation config
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete navigation configuration.
type NavigationConfig =
  { style :: NavigationStyle
  , progress :: ProgressStyle
  , buttonPosition :: ButtonPosition
  , nextVariant :: ButtonVariant
  , prevVariant :: ButtonVariant
  , skipVariant :: ButtonVariant
  , closeMode :: CloseMode
  , skipMode :: SkipMode
  , showClose :: Boolean
  , showPrev :: Boolean
  , showNext :: Boolean
  , showSkip :: Boolean
  , showProgress :: Boolean
  , labels :: NavigationLabels
  , keyboard :: KeyboardConfig
  , clickableProgress :: Boolean      -- ^ Can click progress dots to jump
  , swipeNavigation :: Boolean        -- ^ Swipe left/right on mobile
  }

-- | Default navigation configuration
defaultNavigationConfig :: NavigationConfig
defaultNavigationConfig =
  { style: NavStandard
  , progress: ProgressDots
  , buttonPosition: ButtonBelowTooltip
  , nextVariant: VariantPrimary
  , prevVariant: VariantSecondary
  , skipVariant: VariantGhost
  , closeMode: CloseAny
  , skipMode: SkipAlways
  , showClose: true
  , showPrev: true
  , showNext: true
  , showSkip: true
  , showProgress: true
  , labels: defaultLabels
  , keyboard: defaultKeyboardConfig
  , clickableProgress: true
  , swipeNavigation: true
  }

-- | Minimal navigation configuration
minimalNavigationConfig :: NavigationConfig
minimalNavigationConfig = defaultNavigationConfig
  { style = NavMinimal
  , progress = ProgressNone
  , showPrev = false
  , showProgress = false
  , labels = minimalLabels
  }

-- | Expanded navigation configuration
expandedNavigationConfig :: NavigationConfig
expandedNavigationConfig = defaultNavigationConfig
  { style = NavExpanded
  , progress = ProgressSteps
  , buttonPosition = ButtonFooter
  }
