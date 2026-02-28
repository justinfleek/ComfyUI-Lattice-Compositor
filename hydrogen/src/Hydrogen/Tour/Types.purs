-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                                  // hydrogen // tour // types
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Core type definitions for Product Tours
-- |
-- | This module provides the foundational ADTs for type-safe product tours:
-- | - Identifiers (TourId, StepId)
-- | - Target selection (CSS selectors, test IDs, ARIA roles)
-- | - Placement and positioning
-- | - Tour lifecycle phases
-- |
-- | ## Design Philosophy
-- |
-- | All types are bounded enumerations where possible. Strings are validated
-- | via smart constructors. The goal is that invalid tour configurations
-- | cannot be represented.
module Hydrogen.Tour.Types
  ( -- * Identifiers
    TourId(..)
  , mkTourId
  , StepId(..)
  , mkStepId
    -- * Target Selection
  , Target(..)
  , Selector
  , mkSelector
  , unsafeSelector
  , runSelector
  , TestId
  , mkTestId
  , runTestId
    -- * ARIA Roles
  , AriaRole(..)
  , ariaRoleString
    -- * Placement
  , Side(..)
  , Alignment(..)
  , Placement
  , mkPlacement
  , defaultPlacement
  , oppositeSide
    -- * Dimensions
  , Pixel(..)
  , Milliseconds(..)
    -- * Tour Phase
  , TourPhase(..)
  , isActive
  , isPaused
  , isTerminal
    -- * Progress
  , Progress
  , mkProgress
  , progressCurrent
  , progressTotal
  , progressPercent
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(Just, Nothing))
import Data.Show.Generic (genericShow)
import Data.String as String
import Data.String.CodeUnits as CU

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // identifiers
-- ═════════════════════════════════════════════════════════════════════════════

-- | Unique identifier for a tour
-- |
-- | Tours are identified by a string ID that should be unique within the
-- | application. This ID is used for analytics tracking and persistence.
newtype TourId = TourId String

derive instance eqTourId :: Eq TourId
derive instance ordTourId :: Ord TourId
derive newtype instance showTourId :: Show TourId

-- | Create a tour identifier
-- |
-- | The ID should be a kebab-case string (e.g., "onboarding-flow", "feature-intro").
mkTourId :: String -> TourId
mkTourId = TourId

-- | Unique identifier for a step within a tour
-- |
-- | Step IDs are scoped to their parent tour.
newtype StepId = StepId String

derive instance eqStepId :: Eq StepId
derive instance ordStepId :: Ord StepId
derive newtype instance showStepId :: Show StepId

-- | Create a step identifier
mkStepId :: String -> StepId
mkStepId = StepId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // target selection
-- ═════════════════════════════════════════════════════════════════════════════

-- | Specification for the element a tour step should highlight
-- |
-- | Targets define how to locate the DOM element for spotlight highlighting
-- | and tooltip positioning.
data Target
  = BySelector Selector
    -- ^ CSS selector (validated)
  | ByTestId TestId
    -- ^ data-testid attribute value
  | ByRole AriaRole (Maybe String)
    -- ^ ARIA role with optional accessible name
  | NoTarget
    -- ^ Centered modal with no element attachment

derive instance eqTarget :: Eq Target
derive instance genericTarget :: Generic Target _

instance showTarget :: Show Target where
  show = genericShow

-- | Validated CSS selector
-- |
-- | Selectors are validated at construction time to catch common errors.
newtype Selector = Selector String

derive instance eqSelector :: Eq Selector
derive instance ordSelector :: Ord Selector

instance showSelector :: Show Selector where
  show (Selector s) = "(Selector " <> show s <> ")"

-- | Create a validated CSS selector
-- |
-- | Returns Nothing for obviously invalid selectors (empty, starts with digit, etc.)
mkSelector :: String -> Maybe Selector
mkSelector s =
  let
    trimmed = String.trim s
    startsWithDigit str = case CU.uncons str of
      Just { head: c, tail: _ } -> c >= '0' && c <= '9'
      Nothing -> false
  in
    if String.null trimmed
      then Nothing
    else if startsWithDigit trimmed
      then Nothing
    else Just (Selector trimmed)

-- | Create a selector without validation (use only when certain)
unsafeSelector :: String -> Selector
unsafeSelector = Selector

-- | Extract the selector string
runSelector :: Selector -> String
runSelector (Selector s) = s

-- | Test ID for data-testid attribute targeting
newtype TestId = TestId String

derive instance eqTestId :: Eq TestId
derive instance ordTestId :: Ord TestId

instance showTestId :: Show TestId where
  show (TestId s) = "(TestId " <> show s <> ")"

-- | Create a test ID
mkTestId :: String -> TestId
mkTestId = TestId

-- | Extract the test ID string
runTestId :: TestId -> String
runTestId (TestId s) = s

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // aria roles
-- ═════════════════════════════════════════════════════════════════════════════

-- | ARIA roles for semantic element targeting
-- |
-- | Targeting by ARIA role is more resilient to DOM changes than CSS selectors.
data AriaRole
  = RoleButton
  | RoleLink
  | RoleTextbox
  | RoleCheckbox
  | RoleRadio
  | RoleCombobox
  | RoleListbox
  | RoleOption
  | RoleSwitch
  | RoleSlider
  | RoleSpinbutton
  | RoleSearchbox
  | RoleDialog
  | RoleAlertdialog
  | RoleMenu
  | RoleMenubar
  | RoleMenuitem
  | RoleTab
  | RoleTablist
  | RoleTabpanel
  | RoleTreeitem
  | RoleNavigation
  | RoleMain
  | RoleRegion
  | RoleBanner
  | RoleContentinfo
  | RoleForm
  | RoleSearch
  | RoleComplementary
  | RoleImg
  | RoleArticle
  | RoleCell
  | RoleRow
  | RoleTable
  | RoleGrid

derive instance eqAriaRole :: Eq AriaRole
derive instance ordAriaRole :: Ord AriaRole
derive instance genericAriaRole :: Generic AriaRole _

instance showAriaRole :: Show AriaRole where
  show = genericShow

-- | Convert ARIA role to its string representation
ariaRoleString :: AriaRole -> String
ariaRoleString = case _ of
  RoleButton -> "button"
  RoleLink -> "link"
  RoleTextbox -> "textbox"
  RoleCheckbox -> "checkbox"
  RoleRadio -> "radio"
  RoleCombobox -> "combobox"
  RoleListbox -> "listbox"
  RoleOption -> "option"
  RoleSwitch -> "switch"
  RoleSlider -> "slider"
  RoleSpinbutton -> "spinbutton"
  RoleSearchbox -> "searchbox"
  RoleDialog -> "dialog"
  RoleAlertdialog -> "alertdialog"
  RoleMenu -> "menu"
  RoleMenubar -> "menubar"
  RoleMenuitem -> "menuitem"
  RoleTab -> "tab"
  RoleTablist -> "tablist"
  RoleTabpanel -> "tabpanel"
  RoleTreeitem -> "treeitem"
  RoleNavigation -> "navigation"
  RoleMain -> "main"
  RoleRegion -> "region"
  RoleBanner -> "banner"
  RoleContentinfo -> "contentinfo"
  RoleForm -> "form"
  RoleSearch -> "search"
  RoleComplementary -> "complementary"
  RoleImg -> "img"
  RoleArticle -> "article"
  RoleCell -> "cell"
  RoleRow -> "row"
  RoleTable -> "table"
  RoleGrid -> "grid"

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                  // placement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Side of the target element for tooltip placement
data Side
  = Top
  | Right
  | Bottom
  | Left

derive instance eqSide :: Eq Side
derive instance ordSide :: Ord Side
derive instance genericSide :: Generic Side _

instance showSide :: Show Side where
  show = genericShow

-- | Alignment along the placement axis
data Alignment
  = Start
  | Center
  | End

derive instance eqAlignment :: Eq Alignment
derive instance ordAlignment :: Ord Alignment
derive instance genericAlignment :: Generic Alignment _

instance showAlignment :: Show Alignment where
  show = genericShow

-- | Complete placement specification
-- |
-- | Combines side (which edge of target) with alignment (position along edge).
-- | Following Floating UI conventions.
type Placement =
  { side :: Side
  , align :: Alignment
  }

-- | Create a placement specification
mkPlacement :: Side -> Alignment -> Placement
mkPlacement side align = { side, align }

-- | Default placement (bottom-center)
defaultPlacement :: Placement
defaultPlacement = { side: Bottom, align: Center }

-- | Get the opposite side (for flip fallback)
oppositeSide :: Side -> Side
oppositeSide = case _ of
  Top -> Bottom
  Bottom -> Top
  Left -> Right
  Right -> Left

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // dimensions
-- ═════════════════════════════════════════════════════════════════════════════

-- | Pixel dimension
newtype Pixel = Pixel Int

derive instance eqPixel :: Eq Pixel
derive instance ordPixel :: Ord Pixel
derive newtype instance showPixel :: Show Pixel
derive newtype instance semiringPixel :: Semiring Pixel

-- | Time duration in milliseconds
newtype Milliseconds = Milliseconds Int

derive instance eqMilliseconds :: Eq Milliseconds
derive instance ordMilliseconds :: Ord Milliseconds
derive newtype instance showMilliseconds :: Show Milliseconds
derive newtype instance semiringMilliseconds :: Semiring Milliseconds

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // tour phase
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tour lifecycle states
-- |
-- | Tours progress through a finite state machine:
-- |
-- | ```
-- | Inactive → Active → Completed
-- |              ↓ ↑
-- |           Paused
-- |              ↓
-- |        Skipped/Dismissed
-- | ```
data TourPhase
  = TourInactive
    -- ^ Tour not yet started
  | TourActive Int
    -- ^ Tour active at given step index (0-based)
  | TourPaused Int
    -- ^ Tour paused at step (e.g., waiting for user action)
  | TourCompleted
    -- ^ User completed all steps
  | TourSkipped Int
    -- ^ User skipped at step N
  | TourDismissed Int
    -- ^ User dismissed at step N (closed without completing)

derive instance eqTourPhase :: Eq TourPhase
derive instance genericTourPhase :: Generic TourPhase _

instance showTourPhase :: Show TourPhase where
  show = genericShow

-- | Check if tour is in an active state
isActive :: TourPhase -> Boolean
isActive = case _ of
  TourActive _ -> true
  _ -> false

-- | Check if tour is paused
isPaused :: TourPhase -> Boolean
isPaused = case _ of
  TourPaused _ -> true
  _ -> false

-- | Check if tour is in a terminal state (cannot resume)
isTerminal :: TourPhase -> Boolean
isTerminal = case _ of
  TourCompleted -> true
  TourSkipped _ -> true
  TourDismissed _ -> true
  _ -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                   // progress
-- ═════════════════════════════════════════════════════════════════════════════

-- | Progress through the tour
-- |
-- | Tracks current step and total steps for progress indicators.
type Progress =
  { current :: Int  -- 1-indexed for display
  , total :: Int
  }

-- | Create a progress value
-- |
-- | Current is 1-indexed for user display (Step 1 of 5, not Step 0 of 5).
mkProgress :: Int -> Int -> Progress
mkProgress current total = { current, total }

-- | Get current step (1-indexed)
progressCurrent :: Progress -> Int
progressCurrent p = p.current

-- | Get total steps
progressTotal :: Progress -> Int
progressTotal p = p.total

-- | Get progress as percentage (0-100)
progressPercent :: Progress -> Int
progressPercent p
  | p.total <= 0 = 0
  | otherwise = (p.current * 100) / p.total
