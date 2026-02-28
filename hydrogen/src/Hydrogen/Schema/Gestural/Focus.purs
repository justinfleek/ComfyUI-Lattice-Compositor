-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // gestural // focus
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Focus - focus management for accessible keyboard navigation.
-- |
-- | Models focus traps, scopes, roving tabindex, and focus restoration.
-- | Essential for modal dialogs, menu navigation, and complex widgets.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Maybe (Maybe)
-- | - Data.Array (length, head, last)
-- |
-- | ## Dependents
-- | - Component.Modal (focus trapping)
-- | - Component.Menu (roving tabindex)
-- | - Component.Tabs (tab panel focus)
-- | - A11y.* (accessibility patterns)

module Hydrogen.Schema.Gestural.Focus
  ( -- * Focus Origin
    FocusOrigin(FocusMouse, FocusKeyboard, FocusProgram, FocusUnknown)
  , isKeyboardFocus
  , isMouseFocus
  , shouldShowFocusRing
    -- * Focus Direction
  , FocusDirection(FocusForward, FocusBackward, FocusUp, FocusDown, FocusLeft, FocusRight, FocusFirst, FocusLast)
  , isLinearDirection
  , isSpatialDirection
  , reverseDirection
    -- * Focusable Element
  , FocusableElement
  , focusableElement
  , elementId
  , elementTabIndex
  , elementDisabled
  , isFocusable
  , isNaturallyFocusable
    -- * Focus Scope
  , FocusScope
  , focusScope
  , scopeId
  , scopeElements
  , scopeTrapped
  , scopeAutoFocus
  , addToScope
  , removeFromScope
  , firstFocusable
  , lastFocusable
  , nextFocusable
  , prevFocusable
    -- * Orientation
  , Orientation(Horizontal, Vertical, Both)
    -- * Roving Tabindex
  , RovingState
  , initialRovingState
  , rovingCurrentIndex
  , rovingOrientation
  , rovingWrap
  , moveRoving
  , setRovingIndex
  , rovingCurrentElement
    -- * Focus Stack (for restoration)
  , FocusStack
  , emptyFocusStack
  , pushFocus
  , popFocus
  , peekFocus
  , stackDepth
  , clearStack
    -- * Focus State
  , FocusState
  , initialFocusState
  , currentFocus
  , currentFocusOrDefault
  , focusOrigin
  , focusWithin
  , hasFocus
  , setFocus
  , clearFocus
  , updateFocusOrigin
    -- * Focus Utilities
  , autoFocusOrFirst
  , restoreFocusOrDefault
  ) where

import Prelude

import Data.Array (drop, filter, find, findIndex, head, last, length, snoc, take)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe, isJust)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // focus // origin
-- ═════════════════════════════════════════════════════════════════════════════

-- | How focus was obtained
data FocusOrigin
  = FocusMouse     -- ^ Focus via mouse/pointer click
  | FocusKeyboard  -- ^ Focus via keyboard (Tab, arrows)
  | FocusProgram   -- ^ Focus set programmatically
  | FocusUnknown   -- ^ Origin unknown

derive instance eqFocusOrigin :: Eq FocusOrigin
derive instance ordFocusOrigin :: Ord FocusOrigin

instance showFocusOrigin :: Show FocusOrigin where
  show FocusMouse = "mouse"
  show FocusKeyboard = "keyboard"
  show FocusProgram = "program"
  show FocusUnknown = "unknown"

-- | Was focus via keyboard?
isKeyboardFocus :: FocusOrigin -> Boolean
isKeyboardFocus FocusKeyboard = true
isKeyboardFocus _ = false

-- | Was focus via mouse?
isMouseFocus :: FocusOrigin -> Boolean
isMouseFocus FocusMouse = true
isMouseFocus _ = false

-- | Should show focus ring? (keyboard only by default)
shouldShowFocusRing :: FocusOrigin -> Boolean
shouldShowFocusRing = isKeyboardFocus

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // focus // direction
-- ═════════════════════════════════════════════════════════════════════════════

-- | Direction of focus movement
data FocusDirection
  = FocusForward   -- ^ Tab / next in sequence
  | FocusBackward  -- ^ Shift+Tab / previous
  | FocusUp        -- ^ Arrow up (spatial)
  | FocusDown      -- ^ Arrow down (spatial)
  | FocusLeft      -- ^ Arrow left (spatial)
  | FocusRight     -- ^ Arrow right (spatial)
  | FocusFirst     -- ^ Home / first element
  | FocusLast      -- ^ End / last element

derive instance eqFocusDirection :: Eq FocusDirection
derive instance ordFocusDirection :: Ord FocusDirection

instance showFocusDirection :: Show FocusDirection where
  show FocusForward = "forward"
  show FocusBackward = "backward"
  show FocusUp = "up"
  show FocusDown = "down"
  show FocusLeft = "left"
  show FocusRight = "right"
  show FocusFirst = "first"
  show FocusLast = "last"

-- | Is linear direction (tab-based)?
isLinearDirection :: FocusDirection -> Boolean
isLinearDirection FocusForward = true
isLinearDirection FocusBackward = true
isLinearDirection _ = false

-- | Is spatial direction (arrow-based)?
isSpatialDirection :: FocusDirection -> Boolean
isSpatialDirection FocusUp = true
isSpatialDirection FocusDown = true
isSpatialDirection FocusLeft = true
isSpatialDirection FocusRight = true
isSpatialDirection _ = false

-- | Get reverse direction
reverseDirection :: FocusDirection -> FocusDirection
reverseDirection FocusForward = FocusBackward
reverseDirection FocusBackward = FocusForward
reverseDirection FocusUp = FocusDown
reverseDirection FocusDown = FocusUp
reverseDirection FocusLeft = FocusRight
reverseDirection FocusRight = FocusLeft
reverseDirection FocusFirst = FocusLast
reverseDirection FocusLast = FocusFirst

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // focusable // element
-- ═════════════════════════════════════════════════════════════════════════════

-- | A focusable element in the DOM
type FocusableElement =
  { id :: String           -- ^ Element ID
  , tabIndex :: Int        -- ^ Tab index (-1, 0, or positive)
  , disabled :: Boolean    -- ^ Is element disabled
  , hidden :: Boolean      -- ^ Is element hidden
  }

-- | Create focusable element
focusableElement :: String -> Int -> FocusableElement
focusableElement id tabIndex =
  { id
  , tabIndex
  , disabled: false
  , hidden: false
  }

-- | Get element ID
elementId :: FocusableElement -> String
elementId fe = fe.id

-- | Get tab index
elementTabIndex :: FocusableElement -> Int
elementTabIndex fe = fe.tabIndex

-- | Is element disabled?
elementDisabled :: FocusableElement -> Boolean
elementDisabled fe = fe.disabled

-- | Is element focusable?
isFocusable :: FocusableElement -> Boolean
isFocusable fe =
  not fe.disabled && not fe.hidden && fe.tabIndex >= (-1)

-- | Is naturally in tab order? (tabIndex >= 0)
isNaturallyFocusable :: FocusableElement -> Boolean
isNaturallyFocusable fe =
  isFocusable fe && fe.tabIndex >= 0

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // focus // scope
-- ═════════════════════════════════════════════════════════════════════════════

-- | A scope containing focusable elements
type FocusScope =
  { id :: String                      -- ^ Scope identifier
  , elements :: Array FocusableElement -- ^ Elements in scope
  , trapped :: Boolean                 -- ^ Is focus trapped?
  , autoFocus :: Maybe String          -- ^ Element to auto-focus
  , restoreFocus :: Maybe String       -- ^ Element to restore focus to
  }

-- | Create focus scope
focusScope :: String -> Boolean -> FocusScope
focusScope id trapped =
  { id
  , elements: []
  , trapped
  , autoFocus: Nothing
  , restoreFocus: Nothing
  }

-- | Get scope ID
scopeId :: FocusScope -> String
scopeId fs = fs.id

-- | Get scope elements
scopeElements :: FocusScope -> Array FocusableElement
scopeElements fs = fs.elements

-- | Is focus trapped?
scopeTrapped :: FocusScope -> Boolean
scopeTrapped fs = fs.trapped

-- | Get auto-focus element
scopeAutoFocus :: FocusScope -> Maybe String
scopeAutoFocus fs = fs.autoFocus

-- | Add element to scope
addToScope :: FocusableElement -> FocusScope -> FocusScope
addToScope elem fs =
  fs { elements = snoc fs.elements elem }

-- | Remove element from scope by ID
removeFromScope :: String -> FocusScope -> FocusScope
removeFromScope elemId fs =
  fs { elements = filter (\e -> e.id /= elemId) fs.elements }

-- | Get first focusable element
firstFocusable :: FocusScope -> Maybe FocusableElement
firstFocusable fs = head (filter isFocusable fs.elements)

-- | Get last focusable element
lastFocusable :: FocusScope -> Maybe FocusableElement
lastFocusable fs = last (filter isFocusable fs.elements)

-- | Get next focusable element after ID
nextFocusable :: String -> FocusScope -> Maybe FocusableElement
nextFocusable currentId fs =
  let
    focusables = filter isFocusable fs.elements
    idx = findIndex (\e -> e.id == currentId) focusables
  in case idx of
    Just i | i + 1 < length focusables -> 
      head (drop (i + 1) focusables)
    Just _ | fs.trapped -> 
      head focusables  -- Wrap around
    _ -> Nothing

-- | Get previous focusable element before ID
prevFocusable :: String -> FocusScope -> Maybe FocusableElement
prevFocusable currentId fs =
  let
    focusables = filter isFocusable fs.elements
    idx = findIndex (\e -> e.id == currentId) focusables
  in case idx of
    Just i | i > 0 -> 
      last (take i focusables)
    Just _ | fs.trapped -> 
      last focusables  -- Wrap around
    _ -> Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // roving // tabindex
-- ═════════════════════════════════════════════════════════════════════════════

-- | Orientation for roving tabindex
data Orientation = Horizontal | Vertical | Both

derive instance eqOrientation :: Eq Orientation

-- | State for roving tabindex pattern
type RovingState =
  { elements :: Array FocusableElement  -- ^ Elements in group
  , currentIndex :: Int                  -- ^ Currently focused index
  , orientation :: Orientation           -- ^ Navigation orientation
  , wrap :: Boolean                      -- ^ Wrap at ends
  }

-- | Initial roving state
initialRovingState :: Array FocusableElement -> Orientation -> Boolean -> RovingState
initialRovingState elements orientation wrap =
  { elements
  , currentIndex: 0
  , orientation
  , wrap
  }

-- | Get current index
rovingCurrentIndex :: RovingState -> Int
rovingCurrentIndex rs = rs.currentIndex

-- | Get orientation
rovingOrientation :: RovingState -> Orientation
rovingOrientation rs = rs.orientation

-- | Does it wrap?
rovingWrap :: RovingState -> Boolean
rovingWrap rs = rs.wrap

-- | Move focus in direction
moveRoving :: FocusDirection -> RovingState -> RovingState
moveRoving dir rs =
  let
    len = length rs.elements
    newIndex = case dir of
      FocusForward -> moveIndex 1 rs.currentIndex len rs.wrap
      FocusBackward -> moveIndex (-1) rs.currentIndex len rs.wrap
      FocusDown | rs.orientation /= Horizontal -> moveIndex 1 rs.currentIndex len rs.wrap
      FocusUp | rs.orientation /= Horizontal -> moveIndex (-1) rs.currentIndex len rs.wrap
      FocusRight | rs.orientation /= Vertical -> moveIndex 1 rs.currentIndex len rs.wrap
      FocusLeft | rs.orientation /= Vertical -> moveIndex (-1) rs.currentIndex len rs.wrap
      FocusFirst -> 0
      FocusLast -> len - 1
      _ -> rs.currentIndex
  in rs { currentIndex = newIndex }
  where
    moveIndex :: Int -> Int -> Int -> Boolean -> Int
    moveIndex delta current total shouldWrap =
      let next = current + delta
      in if next < 0 then (if shouldWrap then total - 1 else 0)
         else if next >= total then (if shouldWrap then 0 else total - 1)
         else next

-- | Set roving index directly
setRovingIndex :: Int -> RovingState -> RovingState
setRovingIndex idx rs =
  let
    len = length rs.elements
    clampedIdx = if idx < 0 then 0 else if idx >= len then len - 1 else idx
  in rs { currentIndex = clampedIdx }

-- | Get currently focused element
rovingCurrentElement :: RovingState -> Maybe FocusableElement
rovingCurrentElement rs =
  if rs.currentIndex >= 0 && rs.currentIndex < length rs.elements
    then head (drop rs.currentIndex rs.elements)
    else Nothing

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // focus // stack
-- ═════════════════════════════════════════════════════════════════════════════

-- | Stack of focus states for restoration
type FocusStack =
  { stack :: Array String  -- ^ Stack of element IDs
  }

-- | Empty focus stack
emptyFocusStack :: FocusStack
emptyFocusStack = { stack: [] }

-- | Push focus onto stack
pushFocus :: String -> FocusStack -> FocusStack
pushFocus elemId fs = fs { stack = snoc fs.stack elemId }

-- | Pop focus from stack
popFocus :: FocusStack -> { elementId :: Maybe String, stack :: FocusStack }
popFocus fs =
  let
    len = length fs.stack
  in if len == 0
    then { elementId: Nothing, stack: fs }
    else { elementId: last fs.stack, stack: fs { stack = take (len - 1) fs.stack } }

-- | Peek at top of stack without removing
peekFocus :: FocusStack -> Maybe String
peekFocus fs = last fs.stack

-- | Get stack depth
stackDepth :: FocusStack -> Int
stackDepth fs = length fs.stack

-- | Clear the stack
clearStack :: FocusStack -> FocusStack
clearStack _ = emptyFocusStack

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // focus // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete focus state
type FocusState =
  { current :: Maybe String     -- ^ Currently focused element ID
  , origin :: FocusOrigin       -- ^ How focus was obtained
  , within :: Array String      -- ^ Ancestors with focus-within
  , stack :: FocusStack         -- ^ Focus restoration stack
  , timestamp :: Number         -- ^ Last focus change
  }

-- | Initial focus state
initialFocusState :: FocusState
initialFocusState =
  { current: Nothing
  , origin: FocusUnknown
  , within: []
  , stack: emptyFocusStack
  , timestamp: 0.0
  }

-- | Get current focus
currentFocus :: FocusState -> Maybe String
currentFocus fs = fs.current

-- | Get focus origin
focusOrigin :: FocusState -> FocusOrigin
focusOrigin fs = fs.origin

-- | Get elements with focus-within
focusWithin :: FocusState -> Array String
focusWithin fs = fs.within

-- | Does any element have focus?
hasFocus :: FocusState -> Boolean
hasFocus fs = isJust fs.current

-- | Set focus to element
setFocus :: String -> FocusOrigin -> Array String -> Number -> FocusState -> FocusState
setFocus elemId origin ancestors ts fs =
  fs { current = Just elemId
     , origin = origin
     , within = ancestors
     , timestamp = ts
     }

-- | Clear focus
clearFocus :: Number -> FocusState -> FocusState
clearFocus ts fs =
  fs { current = Nothing
     , origin = FocusUnknown
     , within = []
     , timestamp = ts
     }

-- | Update focus origin (without changing element)
updateFocusOrigin :: FocusOrigin -> FocusState -> FocusState
updateFocusOrigin origin fs = fs { origin = origin }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // focus // utilities
-- ═════════════════════════════════════════════════════════════════════════════

-- | Get current focus or a default element ID
-- |
-- | Returns the currently focused element ID, or falls back to
-- | the provided default if no element is focused.
currentFocusOrDefault :: String -> FocusState -> String
currentFocusOrDefault defaultId fs =
  fromMaybe defaultId fs.current

-- | Get auto-focus element or first focusable in scope
-- |
-- | Returns the auto-focus element if set, otherwise returns
-- | the first focusable element in the scope.
autoFocusOrFirst :: FocusScope -> Maybe FocusableElement
autoFocusOrFirst fs =
  case fs.autoFocus of
    Just autoId -> find (\e -> e.id == autoId) fs.elements
    Nothing -> firstFocusable fs

-- | Get restore focus element or default
-- |
-- | Returns the element to restore focus to from the stack,
-- | or the default if the stack is empty.
restoreFocusOrDefault :: String -> FocusState -> String
restoreFocusOrDefault defaultId fs =
  fromMaybe defaultId (peekFocus fs.stack)
