-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                             // hydrogen // schema // gestural // context-menu
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | ContextMenu - right-click and long-press context menu patterns.
-- |
-- | Models context menu triggering, positioning, and keyboard navigation.
-- | Supports nested submenus and accessibility requirements.
-- |
-- | ## Dependencies
-- | - Prelude (Eq, Ord, Show)
-- | - Data.Maybe (Maybe)
-- | - Data.Array (length, head, last)
-- |
-- | ## Dependents
-- | - Component.ContextMenu (context menu component)
-- | - Component.Dropdown (dropdown menus)

module Hydrogen.Schema.Gestural.ContextMenu
  ( -- * Context Trigger
    ContextTrigger(RightClick, LongPress, Keyboard, Custom)
    -- * Menu Item Type
  , MenuItemType(Normal, Separator, Submenu)
  , isRightClick
  , isLongPress
  , isKeyboardTrigger
    -- * Menu Position
  , MenuPosition(AtPointer, AtElement, AtPoint, Centered)
  , positionAtPointer
  , positionAtElement
  , positionAtPoint
    -- * Menu Placement
  , MenuPlacement
  , menuPlacement
  , placementX
  , placementY
  , placementWidth
  , placementHeight
  , adjustForViewport
    -- * Menu Item
  , MenuItem
  , menuItem
  , menuItemSeparator
  , menuItemSubmenu
  , itemId
  , itemLabel
  , itemDisabled
  , itemChecked
  , hasSubmenu
  , isSeparator
    -- * Menu State
  , MenuState(MenuClosed, MenuOpening, MenuOpen, MenuClosing)
  , isMenuOpen
  , isMenuTransitioning
    -- * Submenu State
  , SubmenuState
  , noSubmenu
  , openSubmenu
  , submenuId
  , submenuParentId
  , submenuLevel
  , isSubmenuOpen
    -- * Context Menu State
  , ContextMenuState
  , initialContextMenuState
  , menuTrigger
  , menuPosition
  , menuItems
  , currentHighlight
  , openMenu
  , closeMenu
  , highlightItem
  , highlightNext
  , highlightPrev
  , activateHighlighted
  , openSubmenuFor
  , closeSubmenu
  ) where

import Prelude

import Data.Array (drop, findIndex, head, length)
import Data.Maybe (Maybe(Just, Nothing), fromMaybe)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                         // context // trigger
-- ═════════════════════════════════════════════════════════════════════════════

-- | How context menu was triggered
data ContextTrigger
  = RightClick    -- ^ Right mouse button
  | LongPress     -- ^ Touch long press
  | Keyboard      -- ^ Menu key or Shift+F10
  | Custom        -- ^ Custom trigger

derive instance eqContextTrigger :: Eq ContextTrigger
derive instance ordContextTrigger :: Ord ContextTrigger

instance showContextTrigger :: Show ContextTrigger where
  show RightClick = "rightclick"
  show LongPress = "longpress"
  show Keyboard = "keyboard"
  show Custom = "custom"

-- | Was triggered by right click?
isRightClick :: ContextTrigger -> Boolean
isRightClick RightClick = true
isRightClick _ = false

-- | Was triggered by long press?
isLongPress :: ContextTrigger -> Boolean
isLongPress LongPress = true
isLongPress _ = false

-- | Was triggered by keyboard?
isKeyboardTrigger :: ContextTrigger -> Boolean
isKeyboardTrigger Keyboard = true
isKeyboardTrigger _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // menu // position
-- ═════════════════════════════════════════════════════════════════════════════

-- | Where to position the menu
data MenuPosition
  = AtPointer Number Number   -- ^ At pointer coordinates
  | AtElement String          -- ^ Anchored to element
  | AtPoint Number Number     -- ^ At specific point
  | Centered                  -- ^ Centered in viewport

derive instance eqMenuPosition :: Eq MenuPosition

instance showMenuPosition :: Show MenuPosition where
  show (AtPointer x y) = "pointer(" <> show x <> "," <> show y <> ")"
  show (AtElement id) = "element(" <> id <> ")"
  show (AtPoint x y) = "point(" <> show x <> "," <> show y <> ")"
  show Centered = "centered"

-- | Position at pointer location
positionAtPointer :: Number -> Number -> MenuPosition
positionAtPointer = AtPointer

-- | Position anchored to element
positionAtElement :: String -> MenuPosition
positionAtElement = AtElement

-- | Position at specific point
positionAtPoint :: Number -> Number -> MenuPosition
positionAtPoint = AtPoint

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // menu // placement
-- ═════════════════════════════════════════════════════════════════════════════

-- | Calculated menu placement on screen
type MenuPlacement =
  { x :: Number        -- ^ Left position
  , y :: Number        -- ^ Top position
  , width :: Number    -- ^ Menu width
  , height :: Number   -- ^ Menu height
  }

-- | Create menu placement
menuPlacement :: Number -> Number -> Number -> Number -> MenuPlacement
menuPlacement x y width height = { x, y, width, height }

-- | Get placement X
placementX :: MenuPlacement -> Number
placementX mp = mp.x

-- | Get placement Y
placementY :: MenuPlacement -> Number
placementY mp = mp.y

-- | Get placement width
placementWidth :: MenuPlacement -> Number
placementWidth mp = mp.width

-- | Get placement height
placementHeight :: MenuPlacement -> Number
placementHeight mp = mp.height

-- | Adjust placement to fit within viewport
adjustForViewport :: Number -> Number -> MenuPlacement -> MenuPlacement
adjustForViewport viewportWidth viewportHeight mp =
  let
    adjustedX = if mp.x + mp.width > viewportWidth
                then max 0.0 (viewportWidth - mp.width)
                else mp.x
    adjustedY = if mp.y + mp.height > viewportHeight
                then max 0.0 (viewportHeight - mp.height)
                else mp.y
  in mp { x = adjustedX, y = adjustedY }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // menu // item
-- ═════════════════════════════════════════════════════════════════════════════

-- | Menu item type
data MenuItemType = Normal | Separator | Submenu

derive instance eqMenuItemType :: Eq MenuItemType

-- | A single menu item
type MenuItem =
  { id :: String               -- ^ Unique identifier
  , label :: String            -- ^ Display text
  , itemType :: MenuItemType   -- ^ Item type
  , disabled :: Boolean        -- ^ Is disabled
  , checked :: Maybe Boolean   -- ^ Checkbox/radio state
  , shortcut :: Maybe String   -- ^ Keyboard shortcut text
  , submenuId :: Maybe String  -- ^ Submenu ID if has submenu
  }

-- | Create normal menu item
menuItem :: String -> String -> MenuItem
menuItem id label =
  { id
  , label
  , itemType: Normal
  , disabled: false
  , checked: Nothing
  , shortcut: Nothing
  , submenuId: Nothing
  }

-- | Create separator item
menuItemSeparator :: String -> MenuItem
menuItemSeparator id =
  { id
  , label: ""
  , itemType: Separator
  , disabled: true
  , checked: Nothing
  , shortcut: Nothing
  , submenuId: Nothing
  }

-- | Create submenu item
menuItemSubmenu :: String -> String -> String -> MenuItem
menuItemSubmenu id label subId =
  { id
  , label
  , itemType: Submenu
  , disabled: false
  , checked: Nothing
  , shortcut: Nothing
  , submenuId: Just subId
  }

-- | Get item ID
itemId :: MenuItem -> String
itemId mi = mi.id

-- | Get item label
itemLabel :: MenuItem -> String
itemLabel mi = mi.label

-- | Is item disabled?
itemDisabled :: MenuItem -> Boolean
itemDisabled mi = mi.disabled

-- | Get checked state
itemChecked :: MenuItem -> Maybe Boolean
itemChecked mi = mi.checked

-- | Does item have submenu?
hasSubmenu :: MenuItem -> Boolean
hasSubmenu mi = mi.itemType == Submenu

-- | Is item a separator?
isSeparator :: MenuItem -> Boolean
isSeparator mi = mi.itemType == Separator

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // menu // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Menu visibility state
data MenuState
  = MenuClosed
  | MenuOpening
  | MenuOpen
  | MenuClosing

derive instance eqMenuState :: Eq MenuState
derive instance ordMenuState :: Ord MenuState

instance showMenuState :: Show MenuState where
  show MenuClosed = "closed"
  show MenuOpening = "opening"
  show MenuOpen = "open"
  show MenuClosing = "closing"

-- | Is menu open?
isMenuOpen :: MenuState -> Boolean
isMenuOpen MenuOpen = true
isMenuOpen _ = false

-- | Is menu transitioning?
isMenuTransitioning :: MenuState -> Boolean
isMenuTransitioning MenuOpening = true
isMenuTransitioning MenuClosing = true
isMenuTransitioning _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // submenu // state
-- ═════════════════════════════════════════════════════════════════════════════

-- | State of nested submenu
type SubmenuState =
  { id :: Maybe String         -- ^ Submenu ID
  , parentItemId :: Maybe String  -- ^ Parent menu item
  , level :: Int               -- ^ Nesting level (0 = root)
  }

-- | No submenu open
noSubmenu :: SubmenuState
noSubmenu = { id: Nothing, parentItemId: Nothing, level: 0 }

-- | Open submenu
openSubmenu :: String -> String -> Int -> SubmenuState
openSubmenu id parentItemId level =
  { id: Just id, parentItemId: Just parentItemId, level }

-- | Get submenu ID
submenuId :: SubmenuState -> Maybe String
submenuId ss = ss.id

-- | Get parent item ID
submenuParentId :: SubmenuState -> Maybe String
submenuParentId ss = ss.parentItemId

-- | Get submenu level
submenuLevel :: SubmenuState -> Int
submenuLevel ss = ss.level

-- | Is submenu open?
isSubmenuOpen :: SubmenuState -> Boolean
isSubmenuOpen ss = case ss.id of
  Just _ -> true
  Nothing -> false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                      // context // menu state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Complete context menu state
type ContextMenuState =
  { state :: MenuState              -- ^ Open/closed state
  , trigger :: Maybe ContextTrigger -- ^ How menu was triggered
  , position :: MenuPosition        -- ^ Where menu is positioned
  , items :: Array MenuItem         -- ^ Menu items
  , highlightedIndex :: Int         -- ^ Currently highlighted item
  , submenu :: SubmenuState         -- ^ Submenu state
  , timestamp :: Number             -- ^ Last update
  }

-- | Initial context menu state
initialContextMenuState :: ContextMenuState
initialContextMenuState =
  { state: MenuClosed
  , trigger: Nothing
  , position: Centered
  , items: []
  , highlightedIndex: (-1)
  , submenu: noSubmenu
  , timestamp: 0.0
  }

-- | Get menu trigger
menuTrigger :: ContextMenuState -> Maybe ContextTrigger
menuTrigger cms = cms.trigger

-- | Get menu position
menuPosition :: ContextMenuState -> MenuPosition
menuPosition cms = cms.position

-- | Get menu items
menuItems :: ContextMenuState -> Array MenuItem
menuItems cms = cms.items

-- | Get currently highlighted item
currentHighlight :: ContextMenuState -> Maybe MenuItem
currentHighlight cms =
  if cms.highlightedIndex >= 0 && cms.highlightedIndex < length cms.items
    then head (drop cms.highlightedIndex cms.items)
    else Nothing

-- | Open context menu
openMenu :: ContextTrigger -> MenuPosition -> Array MenuItem -> Number -> ContextMenuState -> ContextMenuState
openMenu trigger position items ts _ =
  { state: MenuOpen
  , trigger: Just trigger
  , position
  , items
  , highlightedIndex: (-1)
  , submenu: noSubmenu
  , timestamp: ts
  }

-- | Close context menu
closeMenu :: Number -> ContextMenuState -> ContextMenuState
closeMenu ts cms =
  cms { state = MenuClosed
      , trigger = Nothing
      , highlightedIndex = (-1)
      , submenu = noSubmenu
      , timestamp = ts
      }

-- | Highlight specific item by index
highlightItem :: Int -> ContextMenuState -> ContextMenuState
highlightItem idx cms =
  let
    len = length cms.items
    clampedIdx = if idx < 0 then (-1) else if idx >= len then len - 1 else idx
  in cms { highlightedIndex = clampedIdx }

-- | Highlight next item (skip separators)
highlightNext :: ContextMenuState -> ContextMenuState
highlightNext cms =
  let
    len = length cms.items
    startIdx = cms.highlightedIndex + 1
    nextIdx = findNextNonSeparator startIdx cms.items len
  in cms { highlightedIndex = nextIdx }
  where
    findNextNonSeparator :: Int -> Array MenuItem -> Int -> Int
    findNextNonSeparator idx items len =
      if idx >= len then fromMaybe (-1) (findFirstNonSeparator items)
      else case head (drop idx items) of
        Just item | not (isSeparator item) -> idx
        Just _ -> findNextNonSeparator (idx + 1) items len
        Nothing -> (-1)
    
    findFirstNonSeparator :: Array MenuItem -> Maybe Int
    findFirstNonSeparator items = findIndex (not <<< isSeparator) items

-- | Highlight previous item (skip separators)
highlightPrev :: ContextMenuState -> ContextMenuState
highlightPrev cms =
  let
    len = length cms.items
    startIdx = if cms.highlightedIndex <= 0 then len - 1 else cms.highlightedIndex - 1
    prevIdx = findPrevNonSeparator startIdx cms.items
  in cms { highlightedIndex = prevIdx }
  where
    findPrevNonSeparator :: Int -> Array MenuItem -> Int
    findPrevNonSeparator idx items =
      if idx < 0 then fromMaybe (-1) (findLastNonSeparator items)
      else case head (drop idx items) of
        Just item | not (isSeparator item) -> idx
        Just _ -> findPrevNonSeparator (idx - 1) items
        Nothing -> (-1)
    
    findLastNonSeparator :: Array MenuItem -> Maybe Int
    findLastNonSeparator items =
      let len = length items
      in findLastHelper (len - 1) items
    
    findLastHelper :: Int -> Array MenuItem -> Maybe Int
    findLastHelper idx items =
      if idx < 0 then Nothing
      else case head (drop idx items) of
        Just item | not (isSeparator item) -> Just idx
        _ -> findLastHelper (idx - 1) items

-- | Activate currently highlighted item
activateHighlighted :: ContextMenuState -> Maybe MenuItem
activateHighlighted cms = currentHighlight cms

-- | Open submenu for highlighted item
openSubmenuFor :: MenuItem -> Int -> ContextMenuState -> ContextMenuState
openSubmenuFor item level cms = case item.submenuId of
  Just subId -> cms { submenu = openSubmenu subId item.id level }
  Nothing -> cms

-- | Close current submenu
closeSubmenu :: ContextMenuState -> ContextMenuState
closeSubmenu cms = cms { submenu = noSubmenu }
