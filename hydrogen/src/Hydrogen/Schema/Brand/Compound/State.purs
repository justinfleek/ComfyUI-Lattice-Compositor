-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                           // hydrogen // schema // brand // compound // state
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Interactive State System for Brand Compounds.
-- |
-- | ## Design Philosophy
-- |
-- | Every interactive component has multiple states. Each state can specify
-- | different visual properties, animations, haptics, and sounds. States
-- | compose to define the complete interactive experience.
-- |
-- | ## State Categories
-- |
-- | - **Interactive**: hover, active, focus, disabled
-- | - **Validation**: valid, invalid, pending
-- | - **Loading**: loading, success, error
-- | - **Selection**: selected, checked, indeterminate
-- |
-- | ## At Billion-Agent Scale
-- |
-- | State transitions must be deterministic. Given the same input state
-- | and event, all agents must compute the same output state. This module
-- | defines the state vocabulary; resolution happens at render time.

module Hydrogen.Schema.Brand.Compound.State
  ( -- * Interactive State
    InteractiveState(..)
  , interactiveStateToString
  , interactiveStateFromString
  , allInteractiveStates
  , isEnabledState
  , isDisabledState
  
  -- * Validation State
  , ValidationState(..)
  , validationStateToString
  , validationStateFromString
  , allValidationStates
  
  -- * Loading State
  , LoadingState(..)
  , loadingStateToString
  , loadingStateFromString
  , allLoadingStates
  
  -- * Selection State
  , SelectionState(..)
  , selectionStateToString
  , selectionStateFromString
  , allSelectionStates
  
  -- * State Layer
  , StateLayer
  , mkStateLayer
  , emptyStateLayer
  , defaultStateLayer
  , stateLayerDefault
  , stateLayerHover
  , stateLayerActive
  , stateLayerFocus
  , stateLayerDisabled
  
  -- * State Transitions
  , StateTransition(..)
  , transitionToString
  , allTransitions
  
  -- * Combined State
  , ComponentState
  , mkComponentState
  , defaultComponentState
  ) where

import Prelude
  ( class Eq
  , class Ord
  , class Show
  , (==)
  , (/=)
  , (||)
  )

import Data.Maybe (Maybe(Just, Nothing))
import Data.String (toLower, trim)

import Hydrogen.Schema.Brand.Compound.PropertyRef (ColorRef, ShadowRef, DurationRef, EasingRef, HapticRef, SoundRef)

-- ═════════════════════════════════════════════════════════════════════════════
--                                                          // interactive state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Interactive states for components.
-- |
-- | These represent the pointer/keyboard interaction states.
data InteractiveState
  = StateDefault      -- ^ Normal resting state
  | StateHover        -- ^ Pointer over element
  | StateActive       -- ^ Being pressed/clicked
  | StateFocus        -- ^ Keyboard focused
  | StateFocusVisible -- ^ Keyboard focus with visible ring
  | StateDisabled     -- ^ Not interactive
  | StateReadOnly     -- ^ Visible but not editable
  | StatePressed      -- ^ Held down (distinct from active)
  | StateDragging     -- ^ Being dragged

derive instance eqInteractiveState :: Eq InteractiveState
derive instance ordInteractiveState :: Ord InteractiveState

instance showInteractiveState :: Show InteractiveState where
  show = interactiveStateToString

-- | Convert interactive state to string.
interactiveStateToString :: InteractiveState -> String
interactiveStateToString = case _ of
  StateDefault -> "default"
  StateHover -> "hover"
  StateActive -> "active"
  StateFocus -> "focus"
  StateFocusVisible -> "focus-visible"
  StateDisabled -> "disabled"
  StateReadOnly -> "read-only"
  StatePressed -> "pressed"
  StateDragging -> "dragging"

-- | Parse interactive state from string.
interactiveStateFromString :: String -> Maybe InteractiveState
interactiveStateFromString s = case toLower (trim s) of
  "default" -> Just StateDefault
  "hover" -> Just StateHover
  "active" -> Just StateActive
  "focus" -> Just StateFocus
  "focus-visible" -> Just StateFocusVisible
  "focusvisible" -> Just StateFocusVisible
  "disabled" -> Just StateDisabled
  "read-only" -> Just StateReadOnly
  "readonly" -> Just StateReadOnly
  "pressed" -> Just StatePressed
  "dragging" -> Just StateDragging
  _ -> Nothing

-- | All interactive states.
allInteractiveStates :: Array InteractiveState
allInteractiveStates =
  [ StateDefault
  , StateHover
  , StateActive
  , StateFocus
  , StateFocusVisible
  , StateDisabled
  , StateReadOnly
  , StatePressed
  , StateDragging
  ]

-- | Is this an enabled state?
isEnabledState :: InteractiveState -> Boolean
isEnabledState s = s /= StateDisabled

-- | Is this a disabled state?
isDisabledState :: InteractiveState -> Boolean
isDisabledState s = s == StateDisabled || s == StateReadOnly

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // validation state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Validation states for form components.
data ValidationState
  = ValidationNone      -- ^ No validation applied
  | ValidationPristine  -- ^ Never modified
  | ValidationDirty     -- ^ Has been modified
  | ValidationTouched   -- ^ Has been focused and blurred
  | ValidationValid     -- ^ Passes validation
  | ValidationInvalid   -- ^ Fails validation
  | ValidationPending   -- ^ Validation in progress

derive instance eqValidationState :: Eq ValidationState
derive instance ordValidationState :: Ord ValidationState

instance showValidationState :: Show ValidationState where
  show = validationStateToString

-- | Convert validation state to string.
validationStateToString :: ValidationState -> String
validationStateToString = case _ of
  ValidationNone -> "none"
  ValidationPristine -> "pristine"
  ValidationDirty -> "dirty"
  ValidationTouched -> "touched"
  ValidationValid -> "valid"
  ValidationInvalid -> "invalid"
  ValidationPending -> "pending"

-- | Parse validation state from string.
validationStateFromString :: String -> Maybe ValidationState
validationStateFromString s = case toLower (trim s) of
  "none" -> Just ValidationNone
  "pristine" -> Just ValidationPristine
  "dirty" -> Just ValidationDirty
  "touched" -> Just ValidationTouched
  "valid" -> Just ValidationValid
  "invalid" -> Just ValidationInvalid
  "pending" -> Just ValidationPending
  _ -> Nothing

-- | All validation states.
allValidationStates :: Array ValidationState
allValidationStates =
  [ ValidationNone
  , ValidationPristine
  , ValidationDirty
  , ValidationTouched
  , ValidationValid
  , ValidationInvalid
  , ValidationPending
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                              // loading state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Loading states for async operations.
data LoadingState
  = LoadingIdle       -- ^ No loading activity
  | LoadingPending    -- ^ About to load
  | LoadingLoading    -- ^ Currently loading
  | LoadingSuccess    -- ^ Load completed successfully
  | LoadingError      -- ^ Load failed
  | LoadingStale      -- ^ Data may be outdated

derive instance eqLoadingState :: Eq LoadingState
derive instance ordLoadingState :: Ord LoadingState

instance showLoadingState :: Show LoadingState where
  show = loadingStateToString

-- | Convert loading state to string.
loadingStateToString :: LoadingState -> String
loadingStateToString = case _ of
  LoadingIdle -> "idle"
  LoadingPending -> "pending"
  LoadingLoading -> "loading"
  LoadingSuccess -> "success"
  LoadingError -> "error"
  LoadingStale -> "stale"

-- | Parse loading state from string.
loadingStateFromString :: String -> Maybe LoadingState
loadingStateFromString s = case toLower (trim s) of
  "idle" -> Just LoadingIdle
  "pending" -> Just LoadingPending
  "loading" -> Just LoadingLoading
  "success" -> Just LoadingSuccess
  "error" -> Just LoadingError
  "stale" -> Just LoadingStale
  _ -> Nothing

-- | All loading states.
allLoadingStates :: Array LoadingState
allLoadingStates =
  [ LoadingIdle
  , LoadingPending
  , LoadingLoading
  , LoadingSuccess
  , LoadingError
  , LoadingStale
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Selection states for selectable components.
data SelectionState
  = SelectionNone          -- ^ Not selected
  | SelectionSelected      -- ^ Currently selected
  | SelectionChecked       -- ^ Checkbox/toggle is on
  | SelectionUnchecked     -- ^ Checkbox/toggle is off
  | SelectionIndeterminate -- ^ Partial selection
  | SelectionExpanded      -- ^ Accordion/tree expanded
  | SelectionCollapsed     -- ^ Accordion/tree collapsed

derive instance eqSelectionState :: Eq SelectionState
derive instance ordSelectionState :: Ord SelectionState

instance showSelectionState :: Show SelectionState where
  show = selectionStateToString

-- | Convert selection state to string.
selectionStateToString :: SelectionState -> String
selectionStateToString = case _ of
  SelectionNone -> "none"
  SelectionSelected -> "selected"
  SelectionChecked -> "checked"
  SelectionUnchecked -> "unchecked"
  SelectionIndeterminate -> "indeterminate"
  SelectionExpanded -> "expanded"
  SelectionCollapsed -> "collapsed"

-- | Parse selection state from string.
selectionStateFromString :: String -> Maybe SelectionState
selectionStateFromString s = case toLower (trim s) of
  "none" -> Just SelectionNone
  "selected" -> Just SelectionSelected
  "checked" -> Just SelectionChecked
  "on" -> Just SelectionChecked
  "unchecked" -> Just SelectionUnchecked
  "off" -> Just SelectionUnchecked
  "indeterminate" -> Just SelectionIndeterminate
  "partial" -> Just SelectionIndeterminate
  "expanded" -> Just SelectionExpanded
  "open" -> Just SelectionExpanded
  "collapsed" -> Just SelectionCollapsed
  "closed" -> Just SelectionCollapsed
  _ -> Nothing

-- | All selection states.
allSelectionStates :: Array SelectionState
allSelectionStates =
  [ SelectionNone
  , SelectionSelected
  , SelectionChecked
  , SelectionUnchecked
  , SelectionIndeterminate
  , SelectionExpanded
  , SelectionCollapsed
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // state layer
-- ═════════════════════════════════════════════════════════════════════════════

-- | State layer — property overrides for a specific state.
-- |
-- | Each interactive state can override visual properties, motion,
-- | haptic feedback, and sound. Properties not specified inherit
-- | from the base/default state.
type StateLayer =
  { -- Visual overrides
    background :: Maybe ColorRef
  , foreground :: Maybe ColorRef
  , border :: Maybe ColorRef
  , shadow :: Maybe ShadowRef
  
  -- Motion overrides
  , transitionDuration :: Maybe DurationRef
  , transitionEasing :: Maybe EasingRef
  
  -- Feedback
  , haptic :: Maybe HapticRef
  , sound :: Maybe SoundRef
  }

-- | Create a state layer with all properties specified.
mkStateLayer
  :: Maybe ColorRef
  -> Maybe ColorRef
  -> Maybe ColorRef
  -> Maybe ShadowRef
  -> Maybe DurationRef
  -> Maybe EasingRef
  -> Maybe HapticRef
  -> Maybe SoundRef
  -> StateLayer
mkStateLayer bg fg border shadow dur easing haptic sound =
  { background: bg
  , foreground: fg
  , border: border
  , shadow: shadow
  , transitionDuration: dur
  , transitionEasing: easing
  , haptic: haptic
  , sound: sound
  }

-- | Empty state layer (all Nothing).
emptyStateLayer :: StateLayer
emptyStateLayer =
  { background: Nothing
  , foreground: Nothing
  , border: Nothing
  , shadow: Nothing
  , transitionDuration: Nothing
  , transitionEasing: Nothing
  , haptic: Nothing
  , sound: Nothing
  }

-- | Default state layer (alias for empty).
defaultStateLayer :: StateLayer
defaultStateLayer = emptyStateLayer

-- | Get default state properties.
stateLayerDefault :: StateLayer -> Maybe ColorRef
stateLayerDefault sl = sl.background

-- | Get hover state properties.
stateLayerHover :: StateLayer -> Maybe ColorRef
stateLayerHover sl = sl.background

-- | Get active state properties.
stateLayerActive :: StateLayer -> Maybe ColorRef
stateLayerActive sl = sl.background

-- | Get focus state properties.
stateLayerFocus :: StateLayer -> Maybe ColorRef
stateLayerFocus sl = sl.border

-- | Get disabled state properties.
stateLayerDisabled :: StateLayer -> Maybe ColorRef
stateLayerDisabled sl = sl.background

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // state transition
-- ═════════════════════════════════════════════════════════════════════════════

-- | State transitions that can occur.
data StateTransition
  = TransitionEnter      -- ^ Entering a state
  | TransitionLeave      -- ^ Leaving a state
  | TransitionToggle     -- ^ Toggling between states
  | TransitionImmediate  -- ^ No animation

derive instance eqStateTransition :: Eq StateTransition
derive instance ordStateTransition :: Ord StateTransition

instance showStateTransition :: Show StateTransition where
  show = transitionToString

-- | Convert transition to string.
transitionToString :: StateTransition -> String
transitionToString = case _ of
  TransitionEnter -> "enter"
  TransitionLeave -> "leave"
  TransitionToggle -> "toggle"
  TransitionImmediate -> "immediate"

-- | All transition types.
allTransitions :: Array StateTransition
allTransitions =
  [ TransitionEnter
  , TransitionLeave
  , TransitionToggle
  , TransitionImmediate
  ]

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // combined state
-- ═════════════════════════════════════════════════════════════════════════════

-- | Combined component state.
-- |
-- | Components can be in multiple state categories simultaneously.
-- | For example, a button can be both hovered AND valid.
type ComponentState =
  { interactive :: InteractiveState
  , validation :: ValidationState
  , loading :: LoadingState
  , selection :: SelectionState
  }

-- | Create a component state.
mkComponentState
  :: InteractiveState
  -> ValidationState
  -> LoadingState
  -> SelectionState
  -> ComponentState
mkComponentState interactive validation loading selection =
  { interactive
  , validation
  , loading
  , selection
  }

-- | Default component state (all defaults).
defaultComponentState :: ComponentState
defaultComponentState =
  { interactive: StateDefault
  , validation: ValidationNone
  , loading: LoadingIdle
  , selection: SelectionNone
  }
