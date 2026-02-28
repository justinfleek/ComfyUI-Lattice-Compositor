-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
--                                    // hydrogen // schema // reactive // flags
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

-- | Flags - boolean state atoms for reactive systems.
-- |
-- | Every interactive element has boolean states. These atoms are the
-- | foundation for composing interactive behavior.
-- |
-- | All types are suffixed with `Flag` to distinguish them from ADT
-- | constructors in other modules (e.g., `SelectedFlag` vs `Selected`
-- | constructor in SelectionState).

module Hydrogen.Schema.Reactive.Flags
  ( -- * Core Interactive Flags
    EnabledFlag(..)
  , DisabledFlag(..)
  , VisibleFlag(..)
  , HiddenFlag(..)
  , FocusedFlag(..)
  , HoveredFlag(..)
  , PressedFlag(..)
  , ActiveFlag(..)
  -- * Selection Flags
  , SelectedFlag(..)
  , CheckedFlag(..)
  , IndeterminateFlag(..)
  , ExpandedFlag(..)
  , CollapsedFlag(..)
  , OpenFlag(..)
  -- * Data Flags
  , LoadingFlag(..)
  , LoadedFlag(..)
  , RefreshingFlag(..)
  , StaleFlag(..)
  , EmptyFlag(..)
  , BusyFlag(..)
  -- * Form Flags
  , PristineFlag(..)
  , DirtyFlag(..)
  , TouchedFlag(..)
  , UntouchedFlag(..)
  , ValidFlag(..)
  , InvalidFlag(..)
  , RequiredFlag(..)
  , ReadOnlyFlag(..)
  -- * Drag Flags
  , DraggingFlag(..)
  , DragOverFlag(..)
  , DropTargetFlag(..)
  -- * Media Flags
  , PlayingFlag(..)
  , PausedFlag(..)
  , MutedFlag(..)
  , BufferingFlag(..)
  , FullscreenFlag(..)
  -- * Connection Flags
  , OnlineFlag(..)
  , OfflineFlag(..)
  , ReconnectingFlag(..)
  -- * Presence Flags
  , MountedFlag(..)
  , EnteringFlag(..)
  , ExitingFlag(..)
  , AnimatingFlag(..)
  ) where

import Prelude

-- ═════════════════════════════════════════════════════════════════════════════
--                                                     // core interactive flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Element can receive interaction
newtype EnabledFlag = EnabledFlag Boolean
derive instance eqEnabledFlag :: Eq EnabledFlag
derive newtype instance showEnabledFlag :: Show EnabledFlag

-- | Element cannot receive interaction
newtype DisabledFlag = DisabledFlag Boolean
derive instance eqDisabledFlag :: Eq DisabledFlag
derive newtype instance showDisabledFlag :: Show DisabledFlag

-- | Element is rendered and takes space
newtype VisibleFlag = VisibleFlag Boolean
derive instance eqVisibleFlag :: Eq VisibleFlag
derive newtype instance showVisibleFlag :: Show VisibleFlag

-- | Element is not rendered or takes no space
newtype HiddenFlag = HiddenFlag Boolean
derive instance eqHiddenFlag :: Eq HiddenFlag
derive newtype instance showHiddenFlag :: Show HiddenFlag

-- | Element has keyboard focus
newtype FocusedFlag = FocusedFlag Boolean
derive instance eqFocusedFlag :: Eq FocusedFlag
derive newtype instance showFocusedFlag :: Show FocusedFlag

-- | Pointer is over element
newtype HoveredFlag = HoveredFlag Boolean
derive instance eqHoveredFlag :: Eq HoveredFlag
derive newtype instance showHoveredFlag :: Show HoveredFlag

-- | Element is being pressed (mousedown/touchstart)
newtype PressedFlag = PressedFlag Boolean
derive instance eqPressedFlag :: Eq PressedFlag
derive newtype instance showPressedFlag :: Show PressedFlag

-- | Element is in active/current state (active tab, current step)
newtype ActiveFlag = ActiveFlag Boolean
derive instance eqActiveFlag :: Eq ActiveFlag
derive newtype instance showActiveFlag :: Show ActiveFlag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                            // selection flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Item is selected in a list/grid
newtype SelectedFlag = SelectedFlag Boolean
derive instance eqSelectedFlag :: Eq SelectedFlag
derive newtype instance showSelectedFlag :: Show SelectedFlag

-- | Checkbox/toggle is checked
newtype CheckedFlag = CheckedFlag Boolean
derive instance eqCheckedFlag :: Eq CheckedFlag
derive newtype instance showCheckedFlag :: Show CheckedFlag

-- | Checkbox has partial selection (some children selected)
newtype IndeterminateFlag = IndeterminateFlag Boolean
derive instance eqIndeterminateFlag :: Eq IndeterminateFlag
derive newtype instance showIndeterminateFlag :: Show IndeterminateFlag

-- | Accordion/tree/disclosure is expanded
newtype ExpandedFlag = ExpandedFlag Boolean
derive instance eqExpandedFlag :: Eq ExpandedFlag
derive newtype instance showExpandedFlag :: Show ExpandedFlag

-- | Accordion/tree/disclosure is collapsed
newtype CollapsedFlag = CollapsedFlag Boolean
derive instance eqCollapsedFlag :: Eq CollapsedFlag
derive newtype instance showCollapsedFlag :: Show CollapsedFlag

-- | Dropdown/popover/modal is open
newtype OpenFlag = OpenFlag Boolean
derive instance eqOpenFlag :: Eq OpenFlag
derive newtype instance showOpenFlag :: Show OpenFlag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // data flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Data is being fetched
newtype LoadingFlag = LoadingFlag Boolean
derive instance eqLoadingFlag :: Eq LoadingFlag
derive newtype instance showLoadingFlag :: Show LoadingFlag

-- | Data has been successfully fetched
newtype LoadedFlag = LoadedFlag Boolean
derive instance eqLoadedFlag :: Eq LoadedFlag
derive newtype instance showLoadedFlag :: Show LoadedFlag

-- | Data is being refetched (stale-while-revalidate)
newtype RefreshingFlag = RefreshingFlag Boolean
derive instance eqRefreshingFlag :: Eq RefreshingFlag
derive newtype instance showRefreshingFlag :: Show RefreshingFlag

-- | Cached data may be outdated
newtype StaleFlag = StaleFlag Boolean
derive instance eqStaleFlag :: Eq StaleFlag
derive newtype instance showStaleFlag :: Show StaleFlag

-- | No data present (empty state)
newtype EmptyFlag = EmptyFlag Boolean
derive instance eqEmptyFlag :: Eq EmptyFlag
derive newtype instance showEmptyFlag :: Show EmptyFlag

-- | Operation in progress (form submit, action)
newtype BusyFlag = BusyFlag Boolean
derive instance eqBusyFlag :: Eq BusyFlag
derive newtype instance showBusyFlag :: Show BusyFlag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // form flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Field has never been modified
newtype PristineFlag = PristineFlag Boolean
derive instance eqPristineFlag :: Eq PristineFlag
derive newtype instance showPristineFlag :: Show PristineFlag

-- | Field has been modified from initial value
newtype DirtyFlag = DirtyFlag Boolean
derive instance eqDirtyFlag :: Eq DirtyFlag
derive newtype instance showDirtyFlag :: Show DirtyFlag

-- | Field has been focused and blurred
newtype TouchedFlag = TouchedFlag Boolean
derive instance eqTouchedFlag :: Eq TouchedFlag
derive newtype instance showTouchedFlag :: Show TouchedFlag

-- | Field has never been focused
newtype UntouchedFlag = UntouchedFlag Boolean
derive instance eqUntouchedFlag :: Eq UntouchedFlag
derive newtype instance showUntouchedFlag :: Show UntouchedFlag

-- | Field passes validation
newtype ValidFlag = ValidFlag Boolean
derive instance eqValidFlag :: Eq ValidFlag
derive newtype instance showValidFlag :: Show ValidFlag

-- | Field fails validation
newtype InvalidFlag = InvalidFlag Boolean
derive instance eqInvalidFlag :: Eq InvalidFlag
derive newtype instance showInvalidFlag :: Show InvalidFlag

-- | Field must have a value
newtype RequiredFlag = RequiredFlag Boolean
derive instance eqRequiredFlag :: Eq RequiredFlag
derive newtype instance showRequiredFlag :: Show RequiredFlag

-- | Field is visible but not editable
newtype ReadOnlyFlag = ReadOnlyFlag Boolean
derive instance eqReadOnlyFlag :: Eq ReadOnlyFlag
derive newtype instance showReadOnlyFlag :: Show ReadOnlyFlag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                 // drag flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Element is being dragged
newtype DraggingFlag = DraggingFlag Boolean
derive instance eqDraggingFlag :: Eq DraggingFlag
derive newtype instance showDraggingFlag :: Show DraggingFlag

-- | Dragged item is over this element
newtype DragOverFlag = DragOverFlag Boolean
derive instance eqDragOverFlag :: Eq DragOverFlag
derive newtype instance showDragOverFlag :: Show DragOverFlag

-- | Element can receive drops
newtype DropTargetFlag = DropTargetFlag Boolean
derive instance eqDropTargetFlag :: Eq DropTargetFlag
derive newtype instance showDropTargetFlag :: Show DropTargetFlag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                                // media flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Media is playing
newtype PlayingFlag = PlayingFlag Boolean
derive instance eqPlayingFlag :: Eq PlayingFlag
derive newtype instance showPlayingFlag :: Show PlayingFlag

-- | Media is paused
newtype PausedFlag = PausedFlag Boolean
derive instance eqPausedFlag :: Eq PausedFlag
derive newtype instance showPausedFlag :: Show PausedFlag

-- | Audio is muted
newtype MutedFlag = MutedFlag Boolean
derive instance eqMutedFlag :: Eq MutedFlag
derive newtype instance showMutedFlag :: Show MutedFlag

-- | Media is buffering
newtype BufferingFlag = BufferingFlag Boolean
derive instance eqBufferingFlag :: Eq BufferingFlag
derive newtype instance showBufferingFlag :: Show BufferingFlag

-- | Media is in fullscreen mode
newtype FullscreenFlag = FullscreenFlag Boolean
derive instance eqFullscreenFlag :: Eq FullscreenFlag
derive newtype instance showFullscreenFlag :: Show FullscreenFlag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                           // connection flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Network connection is available
newtype OnlineFlag = OnlineFlag Boolean
derive instance eqOnlineFlag :: Eq OnlineFlag
derive newtype instance showOnlineFlag :: Show OnlineFlag

-- | No network connection
newtype OfflineFlag = OfflineFlag Boolean
derive instance eqOfflineFlag :: Eq OfflineFlag
derive newtype instance showOfflineFlag :: Show OfflineFlag

-- | Attempting to restore connection
newtype ReconnectingFlag = ReconnectingFlag Boolean
derive instance eqReconnectingFlag :: Eq ReconnectingFlag
derive newtype instance showReconnectingFlag :: Show ReconnectingFlag

-- ═════════════════════════════════════════════════════════════════════════════
--                                                             // presence flags
-- ═════════════════════════════════════════════════════════════════════════════

-- | Component is mounted in DOM
newtype MountedFlag = MountedFlag Boolean
derive instance eqMountedFlag :: Eq MountedFlag
derive newtype instance showMountedFlag :: Show MountedFlag

-- | Component is entering (enter animation)
newtype EnteringFlag = EnteringFlag Boolean
derive instance eqEnteringFlag :: Eq EnteringFlag
derive newtype instance showEnteringFlag :: Show EnteringFlag

-- | Component is exiting (exit animation)
newtype ExitingFlag = ExitingFlag Boolean
derive instance eqExitingFlag :: Eq ExitingFlag
derive newtype instance showExitingFlag :: Show ExitingFlag

-- | Any animation is in progress
newtype AnimatingFlag = AnimatingFlag Boolean
derive instance eqAnimatingFlag :: Eq AnimatingFlag
derive newtype instance showAnimatingFlag :: Show AnimatingFlag
