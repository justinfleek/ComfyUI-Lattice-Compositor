-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                         // hydrogen // schema // reactive // focus-management
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | FocusManagement - keyboard navigation and focus state atoms.
-- |
-- | Models focus rings, focus traps, roving tabindex, and
-- | focus scope management for accessible interfaces.

module Hydrogen.Schema.Reactive.FocusManagement
  ( -- * Focus Visibility
    FocusVisibility(..)
  , isFocusVisible
  , isFocusHidden
  , shouldShowRing
  -- * Focus Origin
  , FocusOrigin(..)
  , isKeyboardOrigin
  , isMouseOrigin
  , isTouchOrigin
  , isProgrammaticOrigin
  -- * Focus Ring Style
  , FocusRingStyle(..)
  , isOutlineRing
  , isShadowRing
  , isBorderRing
  -- * Focus Ring (Molecule)
  , FocusRing
  , focusRing
  , defaultFocusRing
  , accessibleFocusRing
  , highContrastFocusRing
  , invertedFocusRing
  , noFocusRing
  , withRingColor
  , withRingWidth
  , withRingOffset
  , withTwoRing
  -- * Focus Trap Mode
  , FocusTrapMode(..)
  , isHardTrap
  , isSoftTrap
  , isNoTrap
  -- * Focus Trap (Molecule)
  , FocusTrap
  , focusTrap
  , hardTrap
  , softTrap
  , disabledTrap
  , isTrapActive
  , shouldReturnFocus
  -- * Roving Tabindex
  , RovingTabindex
  , rovingTabindex
  , initRoving
  , rovingFocusIndex
  , rovingMoveNext
  , rovingMovePrev
  , rovingMoveFirst
  , rovingMoveLast
  , isRovingFocused
  -- * Focus Scope (Compound)
  , FocusScope
  , focusScope
  , defaultScope
  , modalScope
  , scopeWithTrap
  , isScopeActive
  , scopeFocusedId
  ) where

import Prelude

import Data.Maybe (Maybe(Nothing), isJust)

import Hydrogen.Schema.Color.RGB (RGBA, rgba)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // focus visibility
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus indicator visibility mode
data FocusVisibility
  = FocusVisible    -- ^ Always show focus indicator
  | FocusHidden     -- ^ Never show focus indicator
  | FocusAuto       -- ^ Show only for keyboard navigation (:focus-visible)

derive instance eqFocusVisibility :: Eq FocusVisibility
derive instance ordFocusVisibility :: Ord FocusVisibility

instance showFocusVisibility :: Show FocusVisibility where
  show FocusVisible = "visible"
  show FocusHidden = "hidden"
  show FocusAuto = "auto"

isFocusVisible :: FocusVisibility -> Boolean
isFocusVisible FocusVisible = true
isFocusVisible _ = false

isFocusHidden :: FocusVisibility -> Boolean
isFocusHidden FocusHidden = true
isFocusHidden _ = false

-- | Should show focus ring based on visibility and origin?
shouldShowRing :: FocusVisibility -> FocusOrigin -> Boolean
shouldShowRing FocusVisible _ = true
shouldShowRing FocusHidden _ = false
shouldShowRing FocusAuto origin = isKeyboardOrigin origin

-- ═════════════════════════════════════════════════════════════════════════════
--                                                               // focus origin
-- ═════════════════════════════════════════════════════════════════════════════

-- | How focus was acquired
data FocusOrigin
  = KeyboardOrigin     -- ^ Focus via Tab or arrow keys
  | MouseOrigin        -- ^ Focus via mouse click
  | TouchOrigin        -- ^ Focus via touch
  | ProgrammaticOrigin -- ^ Focus via JavaScript

derive instance eqFocusOrigin :: Eq FocusOrigin
derive instance ordFocusOrigin :: Ord FocusOrigin

instance showFocusOrigin :: Show FocusOrigin where
  show KeyboardOrigin = "keyboard"
  show MouseOrigin = "mouse"
  show TouchOrigin = "touch"
  show ProgrammaticOrigin = "programmatic"

isKeyboardOrigin :: FocusOrigin -> Boolean
isKeyboardOrigin KeyboardOrigin = true
isKeyboardOrigin _ = false

isMouseOrigin :: FocusOrigin -> Boolean
isMouseOrigin MouseOrigin = true
isMouseOrigin _ = false

isTouchOrigin :: FocusOrigin -> Boolean
isTouchOrigin TouchOrigin = true
isTouchOrigin _ = false

isProgrammaticOrigin :: FocusOrigin -> Boolean
isProgrammaticOrigin ProgrammaticOrigin = true
isProgrammaticOrigin _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // focus ring style
-- ═════════════════════════════════════════════════════════════════════════════

-- | Visual style of focus indicator
data FocusRingStyle
  = OutlineRing    -- ^ CSS outline (default, doesn't affect layout)
  | ShadowRing     -- ^ Box shadow (can be inset)
  | BorderRing     -- ^ Border change (affects layout)

derive instance eqFocusRingStyle :: Eq FocusRingStyle
derive instance ordFocusRingStyle :: Ord FocusRingStyle

instance showFocusRingStyle :: Show FocusRingStyle where
  show OutlineRing = "outline"
  show ShadowRing = "shadow"
  show BorderRing = "border"

isOutlineRing :: FocusRingStyle -> Boolean
isOutlineRing OutlineRing = true
isOutlineRing _ = false

isShadowRing :: FocusRingStyle -> Boolean
isShadowRing ShadowRing = true
isShadowRing _ = false

isBorderRing :: FocusRingStyle -> Boolean
isBorderRing BorderRing = true
isBorderRing _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // focus ring molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus ring appearance configuration
-- |
-- | ## Research Findings: Accessible Focus Indicators
-- |
-- | **WCAG 2.2 Focus Appearance (Level AAA):**
-- | - Focus indicator must have 3:1 contrast against adjacent colors
-- | - Minimum 2px thickness
-- | - Must be visible on both light and dark backgrounds
-- |
-- | **Two-Ring Pattern (Figma, VS Code):**
-- | - Inner ring: Dark color (e.g., #000000)
-- | - Outer ring: Light color (e.g., #ffffff)
-- | - Guarantees contrast on ANY background
-- |
-- | **Figma's "0px hack":**
-- | - Focus rings outside auto-layout bounds via 0px spread shadow
-- | - Prevents layout shift when focus appears
type FocusRing =
  { style :: FocusRingStyle
  , color :: RGBA             -- ^ Primary ring color (Schema atom)
  , width :: Number           -- ^ Ring width in pixels
  , offset :: Number          -- ^ Gap between element and ring in pixels
  , visibility :: FocusVisibility
  , enabled :: Boolean
  -- Two-ring pattern for accessibility
  , twoRingEnabled :: Boolean -- ^ Enable two-ring contrast pattern
  , innerColor :: RGBA        -- ^ Inner ring color (typically dark)
  , outerColor :: RGBA        -- ^ Outer ring color (typically light)
  , innerWidth :: Number      -- ^ Inner ring width
  , outerWidth :: Number      -- ^ Outer ring width
  }

-- | Create focus ring
focusRing :: FocusRingStyle -> RGBA -> Number -> Number -> FocusRing
focusRing style color width offset =
  { style
  , color
  , width
  , offset
  , visibility: FocusAuto
  , enabled: true
  , twoRingEnabled: false
  , innerColor: rgba 0 0 0 100       -- Black, fully opaque
  , outerColor: rgba 255 255 255 100 -- White, fully opaque
  , innerWidth: 2.0
  , outerWidth: 2.0
  }

-- | Default focus ring (blue outline, auto visibility)
-- |
-- | Uses a standard blue (#0066ff = rgb 0 102 255) that works on most backgrounds.
defaultFocusRing :: FocusRing
defaultFocusRing = focusRing OutlineRing (rgba 0 102 255 100) 2.0 2.0

-- | Accessible two-ring focus indicator
-- |
-- | Uses dark inner ring + light outer ring for contrast on any background.
-- | Meets WCAG 2.2 Focus Appearance requirements.
accessibleFocusRing :: FocusRing
accessibleFocusRing = (focusRing OutlineRing (rgba 0 102 255 100) 2.0 2.0)
  { twoRingEnabled = true
  , innerColor = rgba 0 102 255 100   -- Brand blue inner
  , outerColor = rgba 255 255 255 100 -- White outer for contrast
  , innerWidth = 2.0
  , outerWidth = 1.0
  }

-- | High contrast focus ring (maximum visibility)
-- |
-- | Black + white rings for extreme visibility in high contrast mode.
highContrastFocusRing :: FocusRing
highContrastFocusRing = (focusRing OutlineRing (rgba 0 0 0 100) 3.0 2.0)
  { twoRingEnabled = true
  , innerColor = rgba 0 0 0 100       -- Black inner
  , outerColor = rgba 255 255 255 100 -- White outer
  , innerWidth = 2.0
  , outerWidth = 2.0
  }

-- | Inverted focus ring for dark backgrounds
-- |
-- | White inner + dark outer for dark mode interfaces.
invertedFocusRing :: FocusRing
invertedFocusRing = (focusRing OutlineRing (rgba 255 255 255 100) 2.0 2.0)
  { twoRingEnabled = true
  , innerColor = rgba 255 255 255 100 -- White inner
  , outerColor = rgba 0 0 0 100       -- Black outer
  , innerWidth = 2.0
  , outerWidth = 1.0
  }

-- | No focus ring (accessibility concern - use sparingly)
noFocusRing :: FocusRing
noFocusRing = defaultFocusRing { enabled = false }

-- | Set ring color
withRingColor :: RGBA -> FocusRing -> FocusRing
withRingColor color ring = ring { color = color }

-- | Set ring width
withRingWidth :: Number -> FocusRing -> FocusRing
withRingWidth width ring = ring { width = width }

-- | Set ring offset
withRingOffset :: Number -> FocusRing -> FocusRing
withRingOffset offset ring = ring { offset = offset }

-- | Enable two-ring pattern with specified colors
withTwoRing :: RGBA -> RGBA -> FocusRing -> FocusRing
withTwoRing innerCol outerCol ring = ring
  { twoRingEnabled = true
  , innerColor = innerCol
  , outerColor = outerCol
  }

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // focus trap mode
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus trap behavior
data FocusTrapMode
  = HardTrap   -- ^ Focus cannot leave trap (modal dialogs)
  | SoftTrap   -- ^ Focus returns to trap after leaving (panels)
  | NoTrap     -- ^ No trapping behavior

derive instance eqFocusTrapMode :: Eq FocusTrapMode
derive instance ordFocusTrapMode :: Ord FocusTrapMode

instance showFocusTrapMode :: Show FocusTrapMode where
  show HardTrap = "hard"
  show SoftTrap = "soft"
  show NoTrap = "none"

isHardTrap :: FocusTrapMode -> Boolean
isHardTrap HardTrap = true
isHardTrap _ = false

isSoftTrap :: FocusTrapMode -> Boolean
isSoftTrap SoftTrap = true
isSoftTrap _ = false

isNoTrap :: FocusTrapMode -> Boolean
isNoTrap NoTrap = true
isNoTrap _ = false

-- ═════════════════════════════════════════════════════════════════════════════
--                                                        // focus trap molecule
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus trap configuration
type FocusTrap =
  { mode :: FocusTrapMode
  , active :: Boolean
  , returnFocusOnDeactivate :: Boolean
  , initialFocusId :: Maybe String
  , finalFocusId :: Maybe String       -- ^ Where to return focus
  , clickOutsideDeactivates :: Boolean
  , escapeDeactivates :: Boolean
  }

-- | Create focus trap
focusTrap :: FocusTrapMode -> FocusTrap
focusTrap mode =
  { mode
  , active: true
  , returnFocusOnDeactivate: true
  , initialFocusId: Nothing
  , finalFocusId: Nothing
  , clickOutsideDeactivates: false
  , escapeDeactivates: true
  }

-- | Hard trap for modals
hardTrap :: FocusTrap
hardTrap = (focusTrap HardTrap)
  { clickOutsideDeactivates = false
  , escapeDeactivates = false
  }

-- | Soft trap for panels
softTrap :: FocusTrap
softTrap = (focusTrap SoftTrap)
  { clickOutsideDeactivates = true
  , escapeDeactivates = true
  }

-- | Disabled trap
disabledTrap :: FocusTrap
disabledTrap = (focusTrap NoTrap) { active = false }

-- | Is trap currently active?
isTrapActive :: FocusTrap -> Boolean
isTrapActive trap = trap.active && not (isNoTrap trap.mode)

-- | Should return focus when deactivated?
shouldReturnFocus :: FocusTrap -> Boolean
shouldReturnFocus trap = trap.returnFocusOnDeactivate && isJust trap.finalFocusId

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // roving tabindex
-- ═════════════════════════════════════════════════════════════════════════════

-- | Roving tabindex state for composite widgets (toolbars, menus, listboxes)
type RovingTabindex =
  { focusedIndex :: Int        -- ^ Currently focused item (has tabindex=0)
  , itemCount :: Int           -- ^ Total number of items
  , wrap :: Boolean            -- ^ Wrap at boundaries
  , vertical :: Boolean        -- ^ Use up/down arrows (vs left/right)
  }

-- | Create roving tabindex state
rovingTabindex :: Int -> Int -> Boolean -> Boolean -> RovingTabindex
rovingTabindex focusedIndex itemCount wrap vertical =
  { focusedIndex: clampIndex focusedIndex itemCount
  , itemCount
  , wrap
  , vertical
  }
  where
  clampIndex :: Int -> Int -> Int
  clampIndex idx count
    | count <= 0 = 0
    | idx < 0 = 0
    | idx >= count = count - 1
    | otherwise = idx

-- | Initialize roving state
initRoving :: Int -> RovingTabindex
initRoving count = rovingTabindex 0 count true false

-- | Get currently focused index
rovingFocusIndex :: RovingTabindex -> Int
rovingFocusIndex rt = rt.focusedIndex

-- | Move to next item
rovingMoveNext :: RovingTabindex -> RovingTabindex
rovingMoveNext rt
  | rt.itemCount <= 0 = rt
  | rt.focusedIndex >= rt.itemCount - 1 = 
      if rt.wrap 
        then rt { focusedIndex = 0 }
        else rt
  | otherwise = rt { focusedIndex = rt.focusedIndex + 1 }

-- | Move to previous item
rovingMovePrev :: RovingTabindex -> RovingTabindex
rovingMovePrev rt
  | rt.itemCount <= 0 = rt
  | rt.focusedIndex <= 0 = 
      if rt.wrap 
        then rt { focusedIndex = rt.itemCount - 1 }
        else rt
  | otherwise = rt { focusedIndex = rt.focusedIndex - 1 }

-- | Move to first item
rovingMoveFirst :: RovingTabindex -> RovingTabindex
rovingMoveFirst rt = rt { focusedIndex = 0 }

-- | Move to last item
rovingMoveLast :: RovingTabindex -> RovingTabindex
rovingMoveLast rt
  | rt.itemCount <= 0 = rt
  | otherwise = rt { focusedIndex = rt.itemCount - 1 }

-- | Is specific index the focused one?
isRovingFocused :: Int -> RovingTabindex -> Boolean
isRovingFocused idx rt = idx == rt.focusedIndex

-- ═════════════════════════════════════════════════════════════════════════════
--                                                       // focus scope compound
-- ═════════════════════════════════════════════════════════════════════════════

-- | Focus scope - manages focus within a region
type FocusScope =
  { id :: String                -- ^ Unique scope identifier
  , active :: Boolean           -- ^ Is this scope currently active
  , trap :: FocusTrap           -- ^ Focus trapping configuration
  , ring :: FocusRing           -- ^ Focus ring appearance
  , focusedElementId :: Maybe String  -- ^ Currently focused element
  , lastFocusedId :: Maybe String     -- ^ Last focused element (for restoration)
  , parentScopeId :: Maybe String     -- ^ Parent scope (for nesting)
  }

-- | Create focus scope
focusScope :: String -> FocusTrap -> FocusRing -> FocusScope
focusScope id trap ring =
  { id
  , active: true
  , trap
  , ring
  , focusedElementId: Nothing
  , lastFocusedId: Nothing
  , parentScopeId: Nothing
  }

-- | Default focus scope (no trap)
defaultScope :: String -> FocusScope
defaultScope id = focusScope id disabledTrap defaultFocusRing

-- | Modal focus scope (hard trap)
modalScope :: String -> FocusScope
modalScope id = focusScope id hardTrap defaultFocusRing

-- | Add trap to existing scope
scopeWithTrap :: FocusTrap -> FocusScope -> FocusScope
scopeWithTrap trap scope = scope { trap = trap }

-- | Is scope active?
isScopeActive :: FocusScope -> Boolean
isScopeActive scope = scope.active

-- | Get focused element ID in scope
scopeFocusedId :: FocusScope -> Maybe String
scopeFocusedId scope = scope.focusedElementId
