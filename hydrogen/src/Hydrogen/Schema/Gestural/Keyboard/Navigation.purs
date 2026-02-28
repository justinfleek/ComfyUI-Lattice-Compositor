-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                   // hydrogen // schema // gestural // keyboard // navigation
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Navigation - keyboard navigation types and helpers.
-- |
-- | Models directional keyboard navigation for UI traversal.
-- | Supports arrow keys, tab navigation, and vim-style movement.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show, Maybe)
-- | - Data.Maybe (Maybe(Just, Nothing))
-- | - Gestural.Keyboard.Keys (KeyCode, unwrapKeyCode)
-- | - Gestural.Keyboard.Event (KeyEvent)
-- |
-- | ## Dependents
-- | - Component.List (list navigation)
-- | - Component.Menu (menu navigation)
-- | - Component.Grid (2D navigation)
-- | - A11y.Focus (focus management)

module Hydrogen.Schema.Gestural.Keyboard.Navigation
  ( -- * Arrow Direction
    ArrowDirection(ArrowUp, ArrowDown, ArrowLeft, ArrowRight)
  , isHorizontalArrow
  , isVerticalArrow
  , arrowFromCode
  , arrowFromEvent
  , oppositeArrow
    -- * Tab Direction
  , TabDirection(TabForward, TabBackward)
  , tabDirectionFromEvent
  , oppositeTab
    -- * Vim Movement
  , VimMovement(VimUp, VimDown, VimLeft, VimRight)
  , vimFromCode
  , vimFromEvent
  , vimToArrow
    -- * Focus Navigation
  , FocusAction(FocusNext, FocusPrev, FocusFirst, FocusLast, FocusParent)
  , focusActionFromEvent
  ) where

import Prelude

import Data.Maybe (Maybe(Just, Nothing))
import Hydrogen.Schema.Gestural.Keyboard.Keys (KeyCode, unwrapKeyCode)
import Hydrogen.Schema.Gestural.Keyboard.Event (KeyEvent)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // arrow // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction for arrow key navigation
data ArrowDirection
  = ArrowUp
  | ArrowDown
  | ArrowLeft
  | ArrowRight

derive instance eqArrowDirection :: Eq ArrowDirection
derive instance ordArrowDirection :: Ord ArrowDirection

instance showArrowDirection :: Show ArrowDirection where
  show ArrowUp = "ArrowUp"
  show ArrowDown = "ArrowDown"
  show ArrowLeft = "ArrowLeft"
  show ArrowRight = "ArrowRight"

-- | Is horizontal arrow?
isHorizontalArrow :: ArrowDirection -> Boolean
isHorizontalArrow ArrowLeft = true
isHorizontalArrow ArrowRight = true
isHorizontalArrow _ = false

-- | Is vertical arrow?
isVerticalArrow :: ArrowDirection -> Boolean
isVerticalArrow ArrowUp = true
isVerticalArrow ArrowDown = true
isVerticalArrow _ = false

-- | Parse arrow direction from key code
arrowFromCode :: KeyCode -> Maybe ArrowDirection
arrowFromCode kc = case unwrapKeyCode kc of
  "ArrowUp" -> Just ArrowUp
  "ArrowDown" -> Just ArrowDown
  "ArrowLeft" -> Just ArrowLeft
  "ArrowRight" -> Just ArrowRight
  _ -> Nothing

-- | Parse arrow direction from key event
arrowFromEvent :: KeyEvent -> Maybe ArrowDirection
arrowFromEvent ke = arrowFromCode ke.code

-- | Get opposite arrow direction
oppositeArrow :: ArrowDirection -> ArrowDirection
oppositeArrow ArrowUp = ArrowDown
oppositeArrow ArrowDown = ArrowUp
oppositeArrow ArrowLeft = ArrowRight
oppositeArrow ArrowRight = ArrowLeft

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // tab // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Tab navigation direction
data TabDirection
  = TabForward    -- ^ Tab key
  | TabBackward   -- ^ Shift+Tab

derive instance eqTabDirection :: Eq TabDirection
derive instance ordTabDirection :: Ord TabDirection

instance showTabDirection :: Show TabDirection where
  show TabForward = "TabForward"
  show TabBackward = "TabBackward"

-- | Determine tab direction from key event
tabDirectionFromEvent :: KeyEvent -> Maybe TabDirection
tabDirectionFromEvent ke
  | unwrapKeyCode ke.code == "Tab" && ke.modifiers.shift = Just TabBackward
  | unwrapKeyCode ke.code == "Tab" = Just TabForward
  | otherwise = Nothing

-- | Get opposite tab direction
oppositeTab :: TabDirection -> TabDirection
oppositeTab TabForward = TabBackward
oppositeTab TabBackward = TabForward

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // vim // movement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Vim-style movement (hjkl)
data VimMovement
  = VimUp      -- ^ k key
  | VimDown    -- ^ j key
  | VimLeft    -- ^ h key
  | VimRight   -- ^ l key

derive instance eqVimMovement :: Eq VimMovement
derive instance ordVimMovement :: Ord VimMovement

instance showVimMovement :: Show VimMovement where
  show VimUp = "k"
  show VimDown = "j"
  show VimLeft = "h"
  show VimRight = "l"

-- | Parse vim movement from key code
-- |
-- | Only matches when no modifiers are pressed.
vimFromCode :: KeyCode -> Maybe VimMovement
vimFromCode kc = case unwrapKeyCode kc of
  "KeyH" -> Just VimLeft
  "KeyJ" -> Just VimDown
  "KeyK" -> Just VimUp
  "KeyL" -> Just VimRight
  _ -> Nothing

-- | Parse vim movement from key event
-- |
-- | Only matches when no modifiers are pressed.
vimFromEvent :: KeyEvent -> Maybe VimMovement
vimFromEvent ke
  | ke.modifiers.ctrl || ke.modifiers.alt || ke.modifiers.meta = Nothing
  | otherwise = vimFromCode ke.code

-- | Convert vim movement to arrow direction
vimToArrow :: VimMovement -> ArrowDirection
vimToArrow VimUp = ArrowUp
vimToArrow VimDown = ArrowDown
vimToArrow VimLeft = ArrowLeft
vimToArrow VimRight = ArrowRight

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // focus // navigation
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus navigation action
data FocusAction
  = FocusNext     -- ^ Move to next focusable element
  | FocusPrev     -- ^ Move to previous focusable element
  | FocusFirst    -- ^ Move to first focusable element
  | FocusLast     -- ^ Move to last focusable element
  | FocusParent   -- ^ Move to parent container

derive instance eqFocusAction :: Eq FocusAction
derive instance ordFocusAction :: Ord FocusAction

instance showFocusAction :: Show FocusAction where
  show FocusNext = "FocusNext"
  show FocusPrev = "FocusPrev"
  show FocusFirst = "FocusFirst"
  show FocusLast = "FocusLast"
  show FocusParent = "FocusParent"

-- | Determine focus action from key event
-- |
-- | Tab = FocusNext, Shift+Tab = FocusPrev
-- | Ctrl+Home = FocusFirst, Ctrl+End = FocusLast
-- | Escape = FocusParent
focusActionFromEvent :: KeyEvent -> Maybe FocusAction
focusActionFromEvent ke = case unwrapKeyCode ke.code of
  "Tab"
    | ke.modifiers.shift -> Just FocusPrev
    | otherwise -> Just FocusNext
  "Home"
    | ke.modifiers.ctrl -> Just FocusFirst
    | otherwise -> Nothing
  "End"
    | ke.modifiers.ctrl -> Just FocusLast
    | otherwise -> Nothing
  "Escape" -> Just FocusParent
  _ -> Nothing
